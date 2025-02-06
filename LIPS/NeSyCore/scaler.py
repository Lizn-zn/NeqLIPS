from typing import Tuple, List, Dict
from sympy import Expr

import ast
import json
import random
from wrapt_timeout_decorator import timeout
from concurrent import futures
from multiprocessing import Manager

from sympy import symbols, Symbol, solve
from sympy import I, Not
from sympy import nsimplify, simplify
from sympy.simplify.powsimp import powsimp, powdenest

from . import parser
from . import utils
from .problem import Problem

from ..logger_config import default_logger

from ..logger_config import default_logger

class Scaler:
    def __init__(
        self, scale_limit: int, smt_config: str, init_test: str, scale_equality: bool, num_threads: int, logger=None
    ):
        # set the scale limit
        self.scale_limit = scale_limit
        # Initialize SMT configuration
        self.initialize_smt_config(smt_config)
        # set test cases
        self.init_test = init_test
        # set check config
        self.scale_equality = scale_equality  # check the equality condition for scaling
        # set the number of thread
        self.num_threads = num_threads
        # set logger
        self.logger = logger or default_logger
        # load scaling lemmas
        self.load_scaling_lemmas()
        # use shared memory for caching
        manager = Manager()
        self.cache_pattern_match = manager.dict()  # (premise, lemma_in) -> pattern results
        self.cache_check_validity = manager.dict()  # (lemma_out - ref_expr) -> bool
        self.test_cases = manager.list() # initial test cases list
        self.cycle_lemma_out = manager.list()  # skip cycle results if the problem is cycle form
        # initialize problem
        self.sym_cons = None

    def initialize_smt_config(self, smt_config: str):
        """Initialize the SMT configuration."""
        if not smt_config:
            smt_config = {}
        else:
            smt_config = ast.literal_eval(smt_config)

        self.smt_solvers = smt_config.get("smt_solvers", ["z3"])
        self.smt_level = smt_config.get("smt_level", 0)
        self.smt_timeout = smt_config.get("smt_timeout", 2)
        self.smt_update = smt_config.get("smt_update", True)

    def load_scaling_lemmas(self):
        """Load scaling lemmas from the JSON file."""
        try:
            with open("LIPS/Library/ScalingLib.json", "r") as file:
                self.scaling_lemmas = json.load(file)
            self.scaling_lemmas.pop("LEMMA_NAME_VERSION_DIRECTION_VARS", None)
        except FileNotFoundError:
            self.logger.error("Error: ScalingLib.json file not found.")
            self.scaling_lemmas = {}
        except json.JSONDecodeError:
            self.logger.error("Error: Failed to decode ScalingLib.json file.")
            self.scaling_lemmas = {}

    def set_test_cases(self, problem: Problem):
        """Set the test cases for the given problem

        Args:
            problem (LIPS.Problem): the problem to be proved

        Raises:
            ValueError: if the test cases cannot be generated automatically
        """
        a, b, c, d, e = symbols("a b c d e")
        ## auto: whether to generate the test cases automatically
        ## negative test cases could improve efficiency
        if self.init_test == "auto":
            if problem.assumption == []:
                self.test_cases.append({v: random.randint(1, 5) for v in [a, b, c, d, e]})
                if problem.positivity == []:
                    self.test_cases.append({v: -random.randint(1, 5) for v in [a, b, c, d, e]})
            else:
                code = parser.sympy2smt(self.sym_cons)
                ok, msg = utils.smtsolve(code, self.smt_solvers, self.smt_timeout)
                result = parser.parse_smt_model(msg)
                if result is not None:
                    self.test_cases.append(result)
        else:
            result = parser.parse_math_dict(self.init_test)
            self.test_cases.append(result)
        if not self.test_cases:
            raise ValueError("The test cases cannot be generated automatically, must set it manually")
        self.logger.info(f"Set test cases for scaling: {self.test_cases}")

    def set_problem(self, problem: Problem):
        """Set the problem to be proved, pass useful arguments

        Args:
            problem (LIPS.Problem): the problem to be proved
        """
        str_cons = problem.assumption + problem.positivity
        self.sym_cons = [parser.lean2sympy(c) for c in str_cons]
        self.set_test_cases(problem)
        self.is_cycle = problem.is_cycle
        self.cycle_mappings = problem.cycle_mappings
        # set the equality condition if needed
        # we first sympy solve it, if failed we apply smt instead
        if self.scale_equality:
            equal_cons = [parser.lean2sympy(a) for a in problem.equality_assumption]
            concl = problem.conclusion.replace("≤", "=")  # replace neq into eq
            concl = parser.lean2sympy(concl)
            vars = list(concl.free_symbols)
            x = Symbol("x", positive=True, real=True)
            var_subs = {v: x for v in vars}
            inst_concl = concl.xreplace(var_subs)
            if inst_concl == True: # it means that the equality condition is trivial if variable is cycle
                result = [{x : random.randint(1, 5)}]
            else:
                result = solve(
                [c.xreplace(var_subs) for c in equal_cons] + [inst_concl], x, dict=True
                )  # may have multiple solution
                result = [res for res in result if not res[x].has(I)] # remove the complex solution
            if result != []:
                self.equality_case = {v: result[-1][x] for v in vars}
                self.logger.info(f"Set equality condition case: {self.equality_case}")
            else:
                concl = Not(concl, evaluate=False)  # smt solver will autoly add the negation
                code = parser.sympy2smt(self.sym_cons, concl)
                ok, msg = utils.smtsolve(code, self.smt_solvers, self.smt_timeout)
                result = parser.parse_smt_model(msg)
                if result is not None:
                    self.equality_case = result  # dict
                else:
                    self.equality_case = {}
                if self.equality_case != {}:
                    self.logger.info(f"Set equality condition case: {self.equality_case}")
                else:
                    self.logger.info(f"Failed to set equality condition case {msg}")

    @timeout(10)
    def check_by_test(
        self,
        rel_test: Expr,
        k_expr: Expr,
        ref_expr: Expr,
        lemma_in_expr: Expr,
        lemma_out_expr: Expr,
        conditions: List[str],
    ) -> bool:
        """
        Check the scaled expression using previsouly saved test cases
            (1) whether the scaled inequality lemma_out <= ref_expr holds
            (2) whether the scaling is trivial, i.e., lemma_in == lemma_outis
            (3) (Optional) whether the equality condition being consistent
            (4) (Optional) whether the cycle condition holds

        Args:
            rel_test (sympy.Expr): the relation expression used for testing
            k_expr (sympy.Expr): the scaling factor (should be nonnegative)
            ref_expr (sympy.Expr): the reference expression
            input_expr (sympy.Expr): the instantiated input expression of scaling lemma
            output_expr (sympy.Expr): the instantiated output expression of scaling lemma
            conditions (List[str]): the list of equality conditions to be checked

        Returns:
            Bool: whether the scaled expression is valid
        """
        if self.test_cases == "auto":  # check test cases
            raise ValueError("The test cases are not set properly")
        for case in self.test_cases:
            k_val = k_expr.evalf(subs=case)
            if k_val < 0:
                return False, "The scaling factor is negative"
            rel_val = ref_expr.evalf(subs=case)
            rel_func = rel_test(rel_val)
            eval_input_val = lemma_in_expr.evalf(subs=case)
            eval_output_val = lemma_out_expr.evalf(subs=case)
            if eval_input_val.has(I) or eval_output_val.has(I):
                cond1 = False
            else:
                try:
                    # expect output_val `rel`` compare_val
                    cond1 = rel_func(eval_output_val)
                except Exception as e:
                    cond1 = False
            if not cond1:
                msg = f"Test case {case} is the counterexample"
                break
        # expect input_expr != output_expr
        if not cond1:
            return False, msg
        cond2 = not utils.sympy_equal(lemma_in_expr, lemma_out_expr)
        if not cond2:
            return False, "Trivial scaling"
        # expect equality condition
        if self.scale_equality and self.equality_case != {}:
            equality_val = (ref_expr - lemma_out_expr).evalf(subs=self.equality_case)
            cond3 = nsimplify(equality_val) == 0
            if not cond3:
                return False, f"Equality condition failed"
        # expect scaling condition
        # if self.condition_check > 0:
        # cond4 = True
        return True, "Test check Pass!"

    @timeout(30)
    def check_by_verify(
        self,
        rel_verify: Expr,
        ref_expr: Expr,
        lemma_in_expr: Expr,
        lemma_out_expr: Expr,
    ) -> Tuple[bool, str]:
        """check the scaled expression using the SMT solver

        Args:
            rel_verify (sympy.Expr): the relation expression used for verification
            rel_expr (sympy.Expr): the reference expression
            input_expr (sympy.Expr): the instantiated input expression of scaling lemma
            output_expr (sympy.Expr): the instantiated output expression of scaling lemma

        Returns:
            Bool: whether the scaled expression is valid
            str: the counterexample if the scaled expression is invalid
        """
        if self.sym_cons is None:  # NOTE: sym_cons could be []
            raise ValueError("The problem constraints are not set properly")
        rel_func = rel_verify(ref_expr)
        concl = rel_func(lemma_out_expr)
        if concl == True:  # trivial
            return True, "trivial"
        else:
            code = parser.sympy2smt(self.sym_cons, concl)
            ok, msg = utils.smtsolve(code, self.smt_solvers, self.smt_timeout)
            smt_res = parser.parse_smt_result(ok, self.smt_level)
            if str(ok) == "sat":  # save test case
                return False, msg
            if smt_res > 0:
                return True, msg
            else:
                return False, msg

    def instantiate(self, pattern: Dict[str, str], premise: str) -> Tuple[str, str, str, List[str]]:
        """instantiate the input and output expressions of scaling lemma using pattern
            there could be some cycle dup in the scaling,
                e.g., 2ab + c ^ 2 <=> 2bc + a ^ 2, if the original problem is cycle

        Args:
            pattern (Dict[str, str]): the pattern to be used
            premise (str): the scaling lemma to be used

        Returns:
            Tuple[str, str, str, List[str]]: the type of scaling, the instantiated input expression,
                and the instantiated output expression, and the cycled output expression (if so)
        """
        content = self.scaling_lemmas[premise]
        lemma_in, lemma_out, var_lst = (
            content["input"],
            content["output"],
            content["var"],
        )
        dtype = content["type"]
        orig_var_dict = {v: Symbol(v) for v in ["a", "b", "c", "d", "e"]}
        targ_var_dict = {v: Symbol(v) for v in var_lst}
        lemma_in_expr = parser.wrap_parse_expr(lemma_in, targ_var_dict)
        lemma_out_expr = parser.wrap_parse_expr(lemma_out, targ_var_dict)
        # instantiate the lemma_in and lemma_out using pattern
        subs = {targ_var_dict[k]: parser.wrap_parse_expr(v, orig_var_dict) for k, v in pattern.items()}
        lemma_in_inst = utils.sympy_replace(lemma_in_expr, subs)
        lemma_out_inst = utils.sympy_replace(lemma_out_expr, subs)
        if self.is_cycle:
            mappings = self.cycle_mappings
            cycle_lemma_out_insts = [str(lemma_out_inst.xreplace(mapping)) for mapping in mappings]
        else:
            cycle_lemma_out_insts = []
        lemma_in_inst = str(lemma_in_inst)
        lemma_out_inst = str(lemma_out_inst)
        return dtype, lemma_in_inst, lemma_out_inst, cycle_lemma_out_insts

    def check(
        self,
        pattern: Dict[str, str],
        lemma_in_inst: str,
        lemma_out_inst: str,
        reference: str,
        ttype: str,
        conditions: List[str],
    ) -> Tuple[bool, str]:
        """check the validity of the scaling via first testing the scaled expression and then (if passed) verifying it

        Args:
            pattern (Dict[str, str]): the pattern to be used
            lemma_in_inst (str): the instantiated input expression of scaling lemma
            lemma_out_inst (str): the instantiated output expression of scaling lemma
            reference (str): the reference expression
            ttype (str): the type of scaling, either "right" or "left"
            var_lst (List[str]): the list of lemma variables to be pattern matched
            conditions (List[str]): the list of equality conditions to be checked

        Returns:
            Bool: whether the scaling is valid
            str: the counterexample if the scaling is invalid
        """
        # translate lemma_in, lemma_out, and ref_expr into sympy.Expr
        orig_var_dict = {v: Symbol(v) for v in ["a", "b", "c", "d", "e"]}
        k_expr = parser.lean2sympy(pattern["k"], local_dict=orig_var_dict)
        ref_expr = parser.lean2sympy(reference, local_dict=orig_var_dict)
        lemma_in_inst = parser.wrap_parse_expr(lemma_in_inst, orig_var_dict)
        lemma_out_inst = parser.wrap_parse_expr(lemma_out_inst, orig_var_dict)
        # check cache
        check_key = str(lemma_out_inst - ref_expr)
        if check_key in self.cache_check_validity:
            msg = "cached results"
            return self.cache_check_validity[check_key], msg
        ## check the validity of the scaling
        ## we set tol = 1e-8 for the floating point comparison
        if ttype == "right":
            # fmt: off
            def rel_test(y):
                return lambda x: ((y - x) <= 1e-8)
            def rel_verify(y):
                return (lambda x: (powsimp(powdenest(y - x, force=True), force=True)) <= 0)
        elif ttype == "left":
            # fmt: off
            def rel_test(y):
                return lambda x: ((x - y) <= 1e-8)
            def rel_verify(y):
                return (lambda x: (powsimp(powdenest(x - y, force=True), force=True)) <= 0)
        try:
            ok, msg = self.check_by_test(rel_test, k_expr, ref_expr, lemma_in_inst, lemma_out_inst, conditions)
        except Exception as exc:
            ok = False
            msg = str(exc)
        if ok == True:
            try:
                ok, msg = self.check_by_verify(rel_verify, ref_expr, lemma_in_inst, lemma_out_inst)
            except Exception as exc:
                ok = False
                msg = str(exc)
        self.cache_check_validity[check_key] = ok
        return ok, msg

    def scale(self, neq: str, premise: str) -> List[str]:
        """Scale the given inequality using the given scaling lemma

        Args:
            neq (str): the inequality to be scaled
            premise (str): the scaling lemma to be used

        Returns:
            List[str]: the list of Lean 4 tactics for scaling
        """
        if "≤" not in neq:  # check the format
            raise ValueError(f"The inequality should be in the form of lhs ≤ rhs, but got: {neq}")
        if premise not in self.scaling_lemmas.keys():  # check the premise
            raise ValueError(f"Please select a valid theorem, received `{premise}`")

        lhs, rhs = neq.split("≤", 1)
        # load the lemma
        content = self.scaling_lemmas[premise]
        lemma_in, lemma_out, dtype, var_lst = (
            content["input"],
            content["output"],
            content["type"],
            content["var"],
        )
        eqality_condition = content["condition"]
        if dtype == "right":
            scale_in, ref_expr = rhs.strip(), lhs.strip()
            part_arg = rf"(left := {lhs.strip()})"
        elif dtype == "left":
            scale_in, ref_expr = lhs.strip(), rhs.strip()
            part_arg = rf"(right := {rhs.strip()})"
        # pattern match
        if (premise, scale_in) in self.cache_pattern_match:  #
            patterns = self.cache_pattern_match[(premise, scale_in)]
        else:
            patterns = utils.pattern(scale_in, lemma_in, var_lst)
            # save into cache
            self.cache_pattern_match[(premise, scale_in)] = patterns
        self.logger.info(f"TOTALLY HAVE {len(patterns)} tactics FOR SCALES {premise}")
        lemma_application = []
        for pattern in patterns:
            dtype, lemma_in_inst, lemma_out_inst, cycle_lemma_out_insts = self.instantiate(pattern, premise)
            if (dtype, lemma_out_inst) in self.cycle_lemma_out:
                self.logger.info(f"CHECKING {premise} {pattern} \n==> {dtype} {lemma_out_inst} DUPLICATE!")
                continue
            else:
                self.cycle_lemma_out.extend([(dtype, lemma_out_inst)] + [(dtype, c) for c in cycle_lemma_out_insts])
                lemma_application.append((pattern, lemma_in_inst, lemma_out_inst))
        # check the validity of scaling
        tactics = []
        for pattern, lemma_in_inst, lemma_out_inst in lemma_application:
            ok, msg = self.check(
                pattern,
                lemma_in_inst,
                lemma_out_inst,
                ref_expr,
                dtype,
                eqality_condition,
            )
            if ok == True:
                tactic = rf"scale {premise}"
                for p, v in pattern.items():
                    val = parser.str2lean(v)
                    tactic += rf" ({p} := {val})"
                tactic += f" {part_arg}"
                tactics.append(tactic)
            else:
                if msg != "":  # add to test cases
                    result = parser.parse_smt_model(msg)
                    if result != {} and result not in self.test_cases:
                        self.test_cases.append(result)
                else:
                    continue
            self.logger.info(f"CHECKING {premise} {pattern} ==> {ok}, DETAILS: {msg}")
        self.logger.info(f"THE RESULTS OF FILTERING {len(patterns)} ==> {len(tactics)}")
        return tactics

    def parallel_guess(self, neq: str, premise: str) -> List[Dict[str, str]]:
        """parallel pattern matching for given inequality

        Args:
            neq (str): the inequality to be scaled
            premise (str): the scaling lemma to be used

        Returns:
            List[Dict[str, str]]: the list of patterns
        """
        if premise not in self.scaling_lemmas.keys():  # check the premise
            raise ValueError(f"Please select a valid theorem, received `{premise}`")
        lhs, rhs = neq.split("≤", 1)
        # load the lemma
        content = self.scaling_lemmas[premise]
        lemma_in, lemma_out, dtype, var_lst = (
            content["input"],
            content["output"],
            content["type"],
            content["var"],
        )
        eqality_condition = content["condition"]
        if dtype == "right":
            scale_in, ref_expr = rhs.strip(), lhs.strip()
        elif dtype == "left":
            scale_in, ref_expr = lhs.strip(), rhs.strip()
        # pattern match
        if (scale_in, premise) in self.cache_pattern_match:
            patterns = self.cache_pattern_match[(scale_in, premise)]
        else:
            patterns = utils.pattern(scale_in, lemma_in, var_lst)
            self.cache_pattern_match[(scale_in, premise)] = patterns
        return patterns

    def parallel_check(
        self,
        neq: str,
        premise: str,
        lemma_in_inst: str,
        lemma_out_inst: str,
        pattern: Dict[str, str],
    ) -> Tuple[bool, str]:
        """parallel check for the validity of scaling

        Args:
            neq (str): the inequality to be scaled
            premise (str): the scaling lemma to be used
            lemma_in_inst (str): the instantiated input expression of scaling lemma
            lemma_out_inst (str): the instantiated output expression of scaling lemma
            pattern (Dict[str, str]): the pattern to be checked

        Returns:
            Tuple[bool, str]: whether the scaling is valid and the counterexample if the scaling is invalid
        """
        lhs, rhs = neq.split("≤", 1)
        # load the lemma
        content = self.scaling_lemmas[premise]
        dtype = content["type"]
        eqality_condition = content["condition"]
        if dtype == "right":
            scale_in, ref_expr = rhs.strip(), lhs.strip()
        elif dtype == "left":
            scale_in, ref_expr = lhs.strip(), rhs.strip()
        ok, msg = self.check(pattern, lemma_in_inst, lemma_out_inst, ref_expr, dtype, eqality_condition)
        return ok, msg

    @timeout(1800)
    def parallel_scale(self, neq: str) -> List[str]:
        """parallel scaling for given inequality

        Args:
            neq (str): the inequality to be scaled

        Returns:
            List[str]: the list of tactics
        """
        if "≤" not in neq:  # check the format
            raise ValueError(f"The inequality should be in the form of lhs ≤ rhs, but got: {neq}")

        premise_list = self.scaling_lemmas.keys()
        self.logger.info(f"START SCALING ...")

        # parallel generate patterns
        parallel_executor = futures.ProcessPoolExecutor(max_workers=self.num_threads)
        pattern_results, futures_to_premise = {}, {}
        num_patterns = 0
        for premise in premise_list:
            future = parallel_executor.submit(self.parallel_guess, neq, premise)
            futures_to_premise[future] = premise
        for future in futures.as_completed(futures_to_premise):
            premise = futures_to_premise[future]
            try:
                patterns = future.result()
                pattern_results[premise] = patterns[: self.scale_limit]
                num_patterns += len(patterns)
                self.logger.debug(f"TOTALLY HAVE {len(patterns)} tactics FOR SCALES {premise}")
            except Exception as exc:
                self.logger.error(f"Pattern match for {neq} of premise {premise} generated an exception: {exc}")
        parallel_executor.shutdown(wait=True)
        self.logger.info(f"PATTERN MATCHING FINISH! TOTALLY HAVE {num_patterns} PATTERNS FOR SCALES")

        # parallel instantiate
        parallel_executor = futures.ProcessPoolExecutor(max_workers=self.num_threads)
        inst_results, features_to_premise = {}, {}
        num_inst = 0
        for premise in premise_list:
            for pattern in pattern_results[premise]:
                future = parallel_executor.submit(self.instantiate, pattern, premise)
                features_to_premise[future] = (premise, pattern)
        for future in futures.as_completed(features_to_premise):
            premise, pattern = features_to_premise[future]
            try:
                dtype, lemma_in_inst, lemma_out_inst, cycle_lemma_out_insts = future.result()
                inst_results[(premise, str(pattern.items()))] = (
                    dtype,
                    lemma_in_inst,
                    lemma_out_inst,
                    cycle_lemma_out_insts,
                )
                num_inst += 1
                self.logger.debug(f"INSTANTIATING {premise} {pattern} ==> {dtype} {lemma_out_inst}")
            except Exception as exc:
                self.logger.error(f"Instantiate premise {premise} with pattern {pattern} generated an exception: {exc}")
        parallel_executor.shutdown(wait=True)
        self.logger.info(f"INSTANTIATION FINISH! TOTALLY HAVE {num_inst} INSTANTIATIONS")

        # parallel check
        parallel_executor = futures.ProcessPoolExecutor(max_workers=self.num_threads // len(self.smt_solvers))
        check_results, features_to_premise = {}, {}
        num_check = 0
        for premise in premise_list:
            for pattern in pattern_results[premise]:
                pattern_key = (premise, str(pattern.items()))
                if pattern_key not in inst_results:
                    continue
                dtype, lemma_in_inst, lemma_out_inst, cycle_lemma_out_insts = inst_results[pattern_key]
                current_output = (dtype, lemma_out_inst)
                if current_output in self.cycle_lemma_out:
                    self.logger.debug(f"CHECKING {premise} {pattern} \n==> {dtype} {lemma_out_inst} DUPLICATE!")
                    continue
                cycle_outputs = [(dtype, lemma_out_inst)] + [(dtype, c) for c in cycle_lemma_out_insts]
                self.cycle_lemma_out.extend(cycle_outputs)
                future = parallel_executor.submit(
                    self.parallel_check, neq, premise, lemma_in_inst, lemma_out_inst, pattern
                )
                features_to_premise[future] = (premise, pattern)
        for future in futures.as_completed(features_to_premise):
            premise, pattern = features_to_premise[future]
            dtype, lemma_in_inst, lemma_out_inst, cycle_lemma_out_insts = inst_results[(premise, str(pattern.items()))]
            try:
                ok, msg = future.result()
                check_results[(premise, str(pattern.items()))] = (
                    ok,
                    msg,
                )  # pattern is dict, cannot used as dict's key
                if self.smt_update and self.smt_level < 1 and msg == "no counter example exists":  # update smt_level
                    self.logger.info("update the smt level to 1")
                    self.smt_level = 1
                elif msg != "":  # add to test cases
                    try:
                        result = parser.parse_smt_model(msg)
                    except Exception as exc:
                        self.logger.error(f"Parse smt model {msg} generated an exception: {exc}")
                    if result != {} and result not in self.test_cases:
                        self.test_cases.append(result)
                num_check += 1
                self.logger.debug(f"CHECKING {premise} {pattern} \n==> {ok} {lemma_out_inst}, DETAILS: {msg}")
            except Exception as exc:
                self.logger.error(f"Check premise {premise} with pattern {pattern} generated an exception: {exc}")
        parallel_executor.shutdown(wait=True)
        self.logger.info(f"Update the size of test cases to {len(self.test_cases)}")
        self.logger.info(f"CHECKING FINISH! TOTALLY HAVE {num_check} CHECKS")

        # collect results
        tactics = []
        for premise in premise_list:
            for pattern in pattern_results[premise]:
                pattern_key = (premise, str(pattern.items()))
                if pattern_key not in check_results:
                    continue
                ok, msg = check_results[pattern_key]
                if ok == True:
                    lhs, rhs = neq.split("≤", 1)
                    content = self.scaling_lemmas[premise]
                    dtype = content["type"]
                    part_arg = rf"(left := {lhs.strip()})" if dtype == "right" else rf"(right := {rhs.strip()})"
                    tactic = rf"scale {premise}"
                    for p, v in pattern.items():
                        val = parser.str2lean(v)
                        tactic += rf" ({p} := {val})"
                    tactic += f" {part_arg}"
                    tactics.append(tactic)
        self.logger.info(f"THE RESULTS OF FILTERING {len(features_to_premise)} ==> {len(tactics)}")
        return tactics
