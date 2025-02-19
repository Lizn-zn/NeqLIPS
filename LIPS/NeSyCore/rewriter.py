from typing import Tuple, List, Dict
from sympy import Expr

import ast
import json
from wrapt_timeout_decorator import timeout
from concurrent import futures
from sympy import Add, fraction, Symbol, Rational, Eq, Le, Lt, Ge
from sympy import sympify, simplify, factor, lcm, sqrt
from sympy import symbols, solve, diff, poly, reduce_inequalities
from sympy.simplify.powsimp import powsimp, powdenest

from . import parser
from . import utils
from .llm import LLM
from .problem import Problem

from ..logger_config import default_logger, setup_logger


class Rewriter:
    def __init__(
        self,
        rewrite_limit: int,
        llm: LLM,
        smt_config: str = "",
        sym_rewrite: int = 0,
        num_threads: int = 1,
        logger=None,
    ):
        # Set the number of rewrite repeat
        self.rewrite_limit = rewrite_limit
        # Set LLM
        self.llm = llm
        # Initialize SMT configuration
        self.initialize_smt_config(smt_config)
        # Load rewriting tactics
        self.load_rewriting_tactics()
        # Set logger
        self.logger = logger or default_logger
        # Set the number of threads
        self.num_threads = num_threads
        # Set prompts
        self.rw_prompt = (
            "### Task\n"
            "Your task is {prompt}\n"
            "### Notice\n"
            "1. Please reason step by step\n"
            "2. Only four operators, add, sub, multiply, and division, can be used, and should NOT introduce new variables\n"
            "3. Put the final results within \\boxed{{}}, e.g., \\boxed{{x + 1/y - z}}\n"
            "### Response\n"
            "User:"
            "{problem}\n"
            "Assistant:\n"
        )
        self.rwa_prompt = (
            "### Task\n"
            "Your task is to use the condition {condition}, {prompt}\n"
            "### Notice\n"
            "1. Please reason step by step\n"
            "2. Only four operators, add, sub, multiply, and division, can be used, and should NOT introduce new variables\n"
            "3. Put the final results within \\boxed{{}}, e.g., \\boxed{{x + 1/y - z}}\n"
            "### Response\n"
            "User:"
            "{problem}\n"
            "Assistant:\n"
        )

        # Initialize problem
        self.problem = None
        self.equality_assumption = None

        # whether close the LLM
        self.all_sym = sym_rewrite

    def initialize_smt_config(self, smt_config: str):
        """Initialize the SMT configuration."""
        if not smt_config:
            smt_config = {}
        else:
            smt_config = ast.literal_eval(smt_config)

        self.smt_solvers = smt_config.get("smt_solvers", ["z3"])
        self.smt_level = smt_config.get("smt_level", 0)
        self.smt_timeout = smt_config.get("smt_timeout", 2)

    def load_rewriting_tactics(self):
        """Load rewriting tactics from the JSON file."""
        try:
            with open("LIPS/Library/RewritingLib.json", "r") as file:
                self.rewriting_tactics = json.load(file)
            self.rewriting_tactics.pop("REWRITE_NAME", None)
        except FileNotFoundError:
            self.logger.error("Error: RewritingLib.json file not found.")
            self.rewriting_tactics = {}
        except json.JSONDecodeError:
            self.logger.error("Error: Failed to decode RewritingLib.json file.")
            self.rewriting_tactics = {}

    def set_problem(self, problem: Problem):
        """Set the problem to be proved

        Args:
            problem (LIPS.Problem): the problem to be proved
        """
        str_cons = problem.assumption + problem.positivity
        self.sym_cons = [parser.lean2sympy(c) for c in str_cons]
        self.equality_assumption = problem.equality_assumption
        self.inequality_assumption = problem.inequality_assumption
        self.is_cycle = problem.is_cycle
        self.cycle_mappings = problem.cycle_mappings

    def rewrite_without_assumption(self, neq: str, premise: str) -> List[str]:
        """Rewrite the expression without using any assumption

        Args:
            neq (str): the expression to be rewritten
            premise (str): the premise to be used

        Returns:
            List[str]: the tactics to rewrite the expression
        """
        content = self.rewriting_tactics[premise]
        prompt = content["prompt"]
        tactic = content["tactic"]
        sym_only = content["sym_only"]

        lhs, rhs = neq.split("≤", 1)
        orig_expr = f"{lhs.strip()} - ({rhs.strip()})"
        tactics = []

        if not sym_only and self.all_sym == False:
            select_prompt = self.rw_prompt.format(prompt=prompt, problem=orig_expr)
            for i in range(self.rewrite_limit):
                answers = self.llm.adaptive_response(select_prompt, 4)
                self.logger.debug(f"Rewrite ({i}-th try) of {premise}: \n {orig_expr} -> {answers}")

                # Parse and normalize answers
                answers = [a for a in answers if a.strip() != ""]
                if answers:
                    str_expr, sympy_expr, simp_expr = utils.sympy_simp(parser.lean2str(orig_expr))
                    str_expr_ans, sympy_expr_ans, simp_expr_ans = utils.sympy_simp(answers[-1])

                    if str_expr and str_expr_ans and utils.sympy_equal(simp_expr_ans, simp_expr):
                        sympy_expr_rearrange = utils.normalize(sympy_expr_ans)
                        new_neq = parser.sympy2lean(sympy_expr_rearrange)
                        tactics.append(f"{tactic} {orig_expr.strip()} = {new_neq.strip()}")
                        self.logger.debug(f"Check {premise} result: Rewrite without assumption success")
                        break
                    else:
                        self.logger.debug(
                            f"Check {premise} result: LLM rewrite failed. The result cannot pass the sympy equal test"
                        )

        if not tactics:
            tactics = self.rewrite_with_sympy(neq, premise)

        return tactics

    def rewrite_with_assumption(self, neq: str, premise: str) -> List[str]:
        """Rewrite the expression with given assumption

        Args:
            neq (str): the expression to be rewritten
            premise (str): the premise to be used

        Returns:
            List[str]: the tactics to rewrite the expression
        """
        if self.equality_assumption is None:  # no assumption
            return []

        content = self.rewriting_tactics[premise]
        prompt = content["prompt"]
        tactic = content["tactic"]
        sym_only = content["sym_only"]

        lhs, rhs = neq.split("≤", 1)
        orig_expr = f"{lhs.strip()} - ({rhs.strip()})"
        tactics = []

        if not sym_only and self.all_sym == False:
            select_prompt = self.rwa_prompt.format(prompt=prompt, problem=orig_expr, condition=self.equality_assumption)
            for i in range(self.rewrite_limit):
                answers = self.llm.adaptive_response(select_prompt)
                self.logger.debug(f"Rewrite ({i}-th try) of {premise}: \n {orig_expr} -> {answers}")

                # Parse and normalize answers
                answers = [a for a in answers if a.strip() != ""]
                if answers:
                    str_expr, sympy_expr, simp_expr = utils.sympy_simp(parser.lean2str(orig_expr))
                    str_expr_ans, sympy_expr_ans, simp_expr_ans = utils.sympy_simp(answers[-1])

                if str_expr is None or str_expr_ans is None:
                    raise ValueError(f"Parse failed for {answers[-1]} or {orig_expr}")

                concl = Eq(simp_expr_ans, simp_expr)
                code = parser.sympy2smt(self.sym_cons, concl)
                ok, msg = utils.smtsolve(code, self.smt_solvers, self.smt_timeout)

                if str(ok) == "unsat":
                    sympy_expr_rearrange = utils.normalize(sympy_expr_ans)
                    new_neq = parser.sympy2lean(sympy_expr_rearrange)
                    tactics.append(f"{tactic} {orig_expr.strip()} = {new_neq.strip()}")
                    self.logger.debug(f"Check {premise} result: Rewrite without assumption success")
                    break
                else:
                    self.logger.debug(
                        f"Check {premise} result: LLM rewrite failed. The result The SMT result is `{msg}`"
                    )

        if not tactics:
            tactics = self.rewrite_with_sympy(neq, premise)

        return tactics

    def rewrite_with_inequation(self, neq: str, premise: str) -> List[str]:
        """Rewrite the expression with given inequation

        Args:
            neq (str): the expression to be rewritten
            premise (str): the premise to be used

        Returns:
            List[str]: the tactics to rewrite the expression
        """
        content = self.rewriting_tactics[premise]
        prompt, tactic, sym_only = (
            content["prompt"],
            content["tactic"],
            content["sym_only"],
        )
        tactics = []
        if sym_only == False and self.all_sym == False:
            raise NotImplementedError(f"llm rewrite with inequation is not supported yet")
        if tactics == []:
            tactics = self.rewrite_with_sympy(neq, premise)
        return tactics

    def rewrite(self, neq: str, premise: str) -> List[str]:
        """Rewrite the expression

        Args:
            neq (str): the expression to be rewritten
            premise (str): the premise to be used

        Returns:
            List[str]: the tactics to rewrite the expression
        """
        if "≤" not in neq:
            raise ValueError(f"The problem should be in the form of lhs ≤ rhs, but got: {neq}")
        if premise not in self.rewriting_tactics.keys():  # check the premise
            raise ValueError(f"Please select a valid tactic, received `{premise}`")
        content = self.rewriting_tactics[premise]
        dtype = content["type"]
        if dtype == "rewrite_without_assumption":
            return self.rewrite_without_assumption(neq, premise)
        elif dtype == "rewrite_with_assumption":
            return self.rewrite_with_assumption(neq, premise)
        elif dtype == "rewrite_with_inequation":
            return self.rewrite_with_inequation(neq, premise)
        else:
            raise NotImplementedError(f"Unknown type: {dtype}")

    @timeout(1800)
    def parallel_rewrite(self, neq: str) -> List[str]:
        """Rewrite the expression in parallel

        Args:
            neq (str): the expression to be rewritten

        Returns:
            List[str]: the tactics to rewrite the expression
        """
        if "≤" not in neq:
            raise ValueError(f"The problem should be in the form of lhs ≤ rhs, but got: {neq}")
        premise_list = self.rewriting_tactics.keys()
        parallel_executor = futures.ProcessPoolExecutor(max_workers=self.num_threads)
        futures_to_premise = {}
        for premise in premise_list:
            future = parallel_executor.submit(self.rewrite, neq, premise)
            futures_to_premise[future] = premise
        tactics = []
        for future in futures.as_completed(futures_to_premise):
            premise = futures_to_premise[future]
            try:
                tactic = future.result()
                tactics += tactic
            except Exception as exc:
                self.logger.error(f"Rewrite of {premise} generated an exception: {exc}")
        parallel_executor.shutdown(wait=True)
        tactics = list(set(tactics))  # remove duplicates
        self.logger.info(f"REWRITE FINISH! TOTALLY HAVE {len(tactics)} REWRITES")
        return tactics

    """
    The following methods are for rewriting with sympy
    """

    def rewrite_with_sympy(self, neq: str, premise: str) -> List[str]:
        """Rewrite the expression using sympy-based tactics

        Args:
            neq (str): the expression to be rewritten
            premise (str): the premise to be used

        Returns:
            List[str]: the tactics to rewrite the expression
        """
        sym_rewriting_tactics = {
            "simplify_wo_assumption": self.sym_simplify,
            "mul_expand": self.sym_mul_expand,
            "exp_expand": self.sym_exp_expand,
            "factor": self.sym_factor,
            "fraction_reduce": self.sym_frac_reduce,
            "fraction_apart": self.sym_frac_apart,
            "fraction_together": self.sym_frac_together,
            "cancel_denominators": self.sym_cancel_denom,
            "cancel_numerators": self.sym_cancel_numer,
            "cancel_power": self.sym_cancel_power,
            "cancel_factor": self.sym_cancel_factor,
            "tangent_line": self.sym_tangent_line,
            "equal_value": self.sym_equal_value,
            "pqr_method": self.sym_pqr_method,
        }
        if premise in sym_rewriting_tactics:
            return sym_rewriting_tactics[premise](neq)
        return []

    def expr_decompose(self, expr: Expr) -> List[Expr]:
        """Decompose the expression into a list of terms

        Args:
            expr (Expr): the expression to be decomposed

        Returns:
            List[Expr]: the list of terms
        """
        return list(expr.args) if expr.is_Add else [expr]

    @timeout(10)
    def sym_simplify(self, neq: str) -> List[str]:
        """Simplify the expression, e.g., a + b - b -> a

        Args:
            neq (str): the expression to be simplified

        Returns:
            List[str]: the tactics to simplify the expression
        """
        # move all terms to left
        lhs, rhs = neq.split("≤", 1)
        lhs, rhs = lhs.strip(), rhs.strip()
        orig_expr = f"{lhs.strip()} - ({rhs.strip()})"
        a, b, c, d, e = symbols("a b c d e", positive=True)  # NOTE: should not using global variables
        sympy_expr = parser.lean2sympy(orig_expr, local_dict={"a": a, "b": b, "c": c, "d": d, "e": e})
        try:
            sympy_expr = powsimp(powdenest(sympy_expr, force=True), force=True)
            sympy_expr = simplify(sympy_expr, force=True)
        except Exception as e:
            self.logger.error(f"simplify failed for {orig_expr}, due to {e}")
            return []
        # rearrange the expression
        if utils.cal_ops(sympy_expr) > 1280:
            self.logger.debug(f"simplify canceled for {orig_expr}, due to too many ops")
            return []
        sympy_expr = utils.normalize(sympy_expr)
        new_expr = parser.sympy2lean(sympy_expr)
        tactics = [f"llm_simplify {orig_expr.strip()} = {new_expr.strip()}"]
        self.logger.debug(f"Symbolic Simplify finished \n==> Get {orig_expr} = {new_expr}")
        return tactics

    @timeout(10)
    def sym_mul_expand(self, neq: str) -> List[str]:
        """Expand the expression, e.g., (a + b) ^ 2 -> a ^ 2 + 2ab + b ^ 2

        Args:
            neq (str): the expression to be expanded

        Returns:
            List[str]: the tactics to expand the expression
        """
        # move all terms to left
        lhs, rhs = neq.split("≤", 1)
        lhs, rhs = lhs.strip(), rhs.strip()
        orig_expr = f"{lhs.strip()} - ({rhs.strip()})"
        # simplify original expr
        sympy_expr = parser.lean2sympy(orig_expr)
        try:
            sympy_expr = (
                sympy_expr.expand()
            )  # power_base=False, power_exp=False, mul=True, multinomial=False, force=True
        except Exception as e:
            self.logger.error(f"mul_expand failed for {orig_expr}, due to {e}")
            return []
        if utils.cal_ops(sympy_expr) > 1280:
            self.logger.debug(f"mul_expand canceled for {orig_expr}, due to too many ops")
            return []
        sympy_expr = utils.normalize(sympy_expr)
        new_expr = parser.sympy2lean(sympy_expr)
        tactics = [f"llm_mul_expand {orig_expr.strip()} = {new_expr.strip()}"]
        self.logger.debug(f"Symbolic Mul_expand finished \n==> Get {orig_expr} = {new_expr}")
        return tactics

    @timeout(10)
    def sym_exp_expand(self, neq: str) -> List[str]:
        """Expand the expression, e.g., (a * b) ^ r -> a ^ r * b ^ r
        Compared with sym_expand, this tactic will not expand the expression (a + b) * (b + c)
        and thus ((a + b) * (b + c)) ^ 2 -> (a + b) ^ 2 * (b + c) ^ 2
        but sym_expand will expand it to (ab + b^2 + bc + c) ^ 2

        Args:
            neq (str): the expression to be separated

        Returns:
            List[str]: the tactics to separate the expression
        """
        # move all terms to left
        lhs, rhs = neq.split("≤", 1)
        lhs, rhs = lhs.strip(), rhs.strip()
        orig_expr = f"{lhs.strip()} - ({rhs.strip()})"
        # simplify original expr
        sympy_expr = parser.lean2sympy(orig_expr)
        try:
            sympy_expr = sympy_expr.expand(power_base=True, mul=False, force=True)
        except Exception as e:
            self.logger.error(f"mul_expand failed for {orig_expr}, due to {e}")
            return []
        if utils.cal_ops(sympy_expr) > 1280:
            self.logger.debug(f"exp_expand canceled for {orig_expr}, due to too many ops")
            return []
        sympy_expr = utils.normalize(sympy_expr)
        new_expr = parser.sympy2lean(sympy_expr)
        tactics = [f"llm_exp_expand {orig_expr.strip()} = {new_expr.strip()}"]
        self.logger.debug(f"Symbolic Exp_expand finished \n==> Get {orig_expr} = {new_expr}")
        return tactics

    @timeout(10)
    def sym_factor(self, neq: str) -> List[str]:
        """Factorize the expression, e.g., (a ^ 2 + 2ab + b ^ 2) / c + d / c -> (a + b) ^ 2 / c + d / c

        Args:
            neq (str): the expression to be factorized

        Returns:
            List[str]: the tactics to factorize the expression
        """
        # move all terms to left
        lhs, rhs = neq.split("≤", 1)
        lhs, rhs = lhs.strip(), rhs.strip()
        orig_expr = f"{lhs.strip()} - ({rhs.strip()})"
        # simplify original expr
        sympy_expr = parser.lean2sympy(orig_expr)
        # try to eliminate brackets first
        sympy_expr = simplify(sympy_expr, evaluate=True)
        new_args = []
        for a in self.expr_decompose(sympy_expr):
            new_args.append(factor(a))
        sympy_expr = Add(*new_args, evaluate=True)
        if utils.cal_ops(sympy_expr) > 1280:
            self.logger.debug(f"factor canceled for {orig_expr}, due to too many ops")
            return []
        sympy_expr = utils.normalize(sympy_expr)
        new_expr = parser.sympy2lean(sympy_expr)
        tactics = [f"llm_factor {orig_expr.strip()} = {new_expr.strip()}"]
        self.logger.debug(f"Symbolic Factor finished \n==> Get {orig_expr} = {new_expr}")
        return tactics

    @timeout(10)
    def sym_frac_reduce(self, neq: str) -> List[str]:
        """Reduce the expression, e.g., (a + b ^ 2) / b -> a / b + b

        Args:
            neq (str): the expression to be reduced

        Returns:
            List[str]: the tactics to reduce the expression
        """
        # move all terms to left
        lhs, rhs = neq.split("≤", 1)
        lhs, rhs = lhs.strip(), rhs.strip()
        orig_expr = f"{lhs.strip()} - ({rhs.strip()})"
        # simplify original expr
        sympy_expr = parser.lean2sympy(orig_expr, evaluate=True)
        # NOTE: simplify tends to put brackets together
        args = self.expr_decompose(sympy_expr)
        new_args = []
        for a in args:
            numer, denom = a.as_numer_denom()
            if denom == 1:  # non-fractional case
                new_args.append(a)
            else:
                # extract addition term iteratively
                numer = simplify(numer)
                denom = simplify(denom)
                k = 0
                while True:
                    new_numer = numer.extract_additively(denom)
                    if new_numer is None:
                        break
                    else:
                        numer = new_numer
                        k += 1
                if k != 0:
                    new_args.append(k)
                    new_args.append(numer / denom)
                    continue
                numer = simplify(-numer)  # use negative term
                while True:
                    new_numer = numer.extract_additively(denom)
                    if new_numer is None:
                        break
                    else:
                        numer = new_numer
                        k -= 1
                if k != 0:
                    new_args.append(k)
                    new_args.append(-numer / denom)
                    continue
                # if all of the above failed
                new_args.append(a)
        sympy_expr = Add(*new_args, evaluate=True)
        if utils.cal_ops(sympy_expr) > 1280:
            self.logger.debug(f"frac_reduce canceled for {orig_expr}, due to too many ops")
            return []
        sympy_expr = utils.normalize(sympy_expr)
        new_expr = parser.sympy2lean(sympy_expr)
        tactics = [f"llm_frac_reduce {orig_expr.strip()} = {new_expr.strip()}"]
        self.logger.debug(f"Symbolic Frac_reduce finished \n==> Get {orig_expr} = {new_expr}")
        return tactics

    @timeout(10)
    def sym_frac_apart(self, neq: str) -> List[str]:
        """Separate the expression, e.g., (a + c + d ^ 2) / b -> a / b + c / b + d ^ 2 / b

        Args:
            neq (str): the expression to be separated

        Returns:
            List[str]: the tactics to separate the expression
        """
        # move all terms to left
        lhs, rhs = neq.split("≤", 1)
        lhs, rhs = lhs.strip(), rhs.strip()
        orig_expr = f"{lhs.strip()} - ({rhs.strip()})"
        # simplify lhs
        sympy_expr = parser.lean2sympy(orig_expr, evaluate=True)
        # NOTE: simplify tends to put brackets together
        args = self.expr_decompose(sympy_expr)
        new_args = []
        for a in args:
            numer, denom = a.as_numer_denom()
            if denom == 1:
                new_args.append(a)
            else:
                numers = self.expr_decompose(numer)
                new_args = new_args + [n / denom for n in numers]
        sympy_expr = Add(*new_args, evaluate=True)
        if utils.cal_ops(sympy_expr) > 1280:
            self.logger.debug(f"frac_apart canceled for {orig_expr}, due to too many ops")
            return []
        sympy_expr = utils.normalize(sympy_expr)
        new_expr = parser.sympy2lean(sympy_expr)
        tactics = [f"llm_frac_apart {orig_expr.strip()} = {new_expr.strip()}"]
        self.logger.debug(f"Symbolic Frac_apart finished \n==> Get {orig_expr} = {new_expr}")
        return tactics

    @timeout(10)
    def sym_frac_together(self, neq: str) -> List[str]:
        """Combine the expression, e.g., a / b + c / d + c / b -> (a + c) / b + c / d

        Args:
            neq (str): the expression to be combined

        Returns:
            List[str]: the tactics to combine the expression
        """
        # move all terms to left
        lhs, rhs = neq.split("≤", 1)
        lhs, rhs = lhs.strip(), rhs.strip()
        orig_expr = f"{lhs.strip()} - ({rhs.strip()})"
        tactics = []
        # simplify lhs
        sympy_expr = parser.lean2sympy(orig_expr, evaluate=True)
        # NOTE: simplify tends to put brackets together
        args = self.expr_decompose(sympy_expr)
        common_denominator_terms = {}
        for a in args:
            numer, denom = a.as_numer_denom()
            denom = denom.expand()
            if denom in common_denominator_terms:
                common_denominator_terms[denom] += numer
            else:
                common_denominator_terms[denom] = numer
        new_args = []
        for denom, numer in common_denominator_terms.items():
            new_args.append(sympify(numer, evaluate=True) / denom)
        sympy_expr = Add(*new_args, evaluate=True)
        if utils.cal_ops(sympy_expr) > 1280:
            self.logger.debug(f"frac_together canceled for {orig_expr}, due to too many ops")
            return []
        sympy_expr = utils.normalize(sympy_expr)
        new_expr = parser.sympy2lean(sympy_expr)
        tactics = [f"llm_frac_together {orig_expr.strip()} = {new_expr.strip()}"]
        self.logger.debug(f"Symbolic Frac_together finished \n==> Get {orig_expr} = {new_expr}")
        return tactics

    @timeout(10)
    def sym_cancel_denom(self, neq: str) -> List[str]:
        """Cancel the denominators, e.g., a / b - a / c -> a * (c - b) / (b * c)

        Args:
            neq (str): the expression to be denom canceled

        Returns:
            List[str]: the tactics to denom cancel the expression
        """
        lhs, rhs = neq.split("≤", 1)
        lhs, rhs = lhs.strip(), rhs.strip()
        orig_expr = f"({lhs}) - ({rhs})"
        sympy_expr = parser.lean2sympy(orig_expr)
        numer, denom = sympy_expr.as_numer_denom()
        if denom == 1:
            self.logger.debug(f"cancel_denom skipped, due to denom = 1")
            return []
        else:
            if utils.cal_ops(numer) > 1280:
                self.logger.debug(f"cancel_denom canceled for {orig_expr}, due to too many ops")
                return []
            numer = utils.normalize(numer)
            new_expr = f"({parser.sympy2lean(numer)}) / ({parser.sympy2lean(denom)})"
            tactics = [f"llm_cancel_denom {orig_expr} = {new_expr}"]
            self.logger.debug(f"Symbolic Cancel_denom finished \n==> Get {orig_expr} = {new_expr}")
            return tactics

    @timeout(10)
    def sym_cancel_numer(self, neq: str) -> List[str]:
        """Cancel the numerators, e.g., a / b - c / b -> 1 / (b / a) - 1 / (b / c)

        Args:
            neq (str): the expression to be numer canceled

        Returns:
            List[str]: the tactics to numer cancel the expression
        """
        lhs, rhs = neq.split("≤", 1)
        lhs, rhs = lhs.strip(), rhs.strip()
        orig_expr = f"({lhs}) - ({rhs})"
        sympy_expr = parser.lean2sympy(orig_expr, evaluate=True)
        args = self.expr_decompose(sympy_expr)
        new_args = []
        for a in args:
            numer, denom = a.as_numer_denom()
            new_numer = denom
            k = 0
            while True:
                tmp_numer = new_numer.extract_additively(numer)
                if tmp_numer is None:
                    break
                else:
                    new_numer = tmp_numer
                    k += 1
            if k == 0:
                new_args.append(a)
            else:
                new_args.append(1 / Rational(k) - (new_numer / (k * denom)))
        sympy_expr = Add(*new_args, evaluate=True)
        if utils.cal_ops(sympy_expr) > 128:
            self.logger.debug(f"cancel_numer canceled for {orig_expr}, due to too many ops")
            return []
        sympy_expr = utils.normalize(sympy_expr)
        new_expr = parser.sympy2lean(sympy_expr)
        tactics = [f"llm_cancel_numer {orig_expr.strip()} = {new_expr.strip()}"]
        self.logger.debug(f"Symbolic Cancel_numer finished \n==> Get {orig_expr} = {new_expr}")
        return tactics

    @timeout(10)
    def sym_cancel_power(self, neq: str) -> List[str]:
        """Cancel the powers, e.g., a ^ 2 <= b ^ 2 -> a <= b
        NOTE: this tactic is built upon the inequality

        Args:
            neq (str): the expression to be power canceled

        Returns:
            List[str]: the tactics to power cancel the expression
        """
        lhs, rhs = neq.split("≤", 1)
        lhs, rhs = lhs.strip(), rhs.strip()
        sympy_lhs = parser.lean2sympy(lhs)
        sympy_rhs = parser.lean2sympy(rhs)
        if sympy_lhs.is_Mul:
            lhs_exps = []
            for e in sympy_lhs.args:
                if len(e.free_symbols) == 0:
                    continue
                if e.is_Pow:
                    lhs_exps.append(fraction(e.exp))
                else:
                    lhs_exps.append(fraction(1))
        elif sympy_lhs.is_Pow:
            lhs_exps = [fraction(sympy_lhs.exp)]
        else:
            lhs_exps = []
        if sympy_rhs.is_Mul:
            rhs_exps = []
            for e in sympy_rhs.args:
                if len(e.free_symbols) == 0:
                    continue
                if e.is_Pow:
                    rhs_exps.append(fraction(e.exp))
                else:
                    rhs_exps.append(fraction(1))
        elif sympy_rhs.is_Pow:
            rhs_exps = [fraction(sympy_rhs.exp)]
        else:
            rhs_exps = []
        exps = set(lhs_exps + rhs_exps)
        if len(exps) == 0:
            tactics = []
            self.logger.debug(f"Symbolic Cancel_power finished \n==> Get exp = None")
        elif len(exps) == 1:
            exp = exps.pop()[1]
            if exp == 1:
                tactics = []
            else:
                tactics = [f"llm_cancel_power {exp}"]
        else:
            # e[1] is the denominator
            exp = lcm(*[e[1] for e in set(lhs_exps + rhs_exps)])
            if exp == 1:
                tactics = []
            else:
                tactics = [f"llm_cancel_power {exp}"]
        return tactics

    @timeout(10)
    def sym_cancel_factor(self, neq: str) -> List[str]:
        """Cancel the factors, e.g., a ^ 2 * c + 2abc + b ^ 2 * c -> c * (a + b) ^ 2

        Args:
            neq (str): the expression to be factor canceled

        Returns:
            List[str]: the tactics to factor cancel the expression
        """
        lhs, rhs = neq.split("≤", 1)
        lhs, rhs = lhs.strip(), rhs.strip()
        orig_expr = f"({lhs}) - ({rhs})"
        sympy_expr = parser.lean2sympy(orig_expr)
        sympy_expr = factor(sympy_expr)
        if utils.cal_ops(sympy_expr) > 1280:
            self.logger.debug(f"cancel_factor canceled for {orig_expr}, due to too many ops")
            return []
        if sympy_expr.is_Mul:  # we must handle neg notation
            neg = True
            sympy_expr = -sympy_expr
            subexprs = []
            args = sympy_expr.args
            for a in args[:-1]:
                term = utils.normalize(a)
                if neg == True:  # insert the -1
                    neg_a = utils.normalize(-a)
                    if str(term).count("-") >= str(neg_a).count("-"):
                        term = neg_a
                        neg = False
                subexprs.append(parser.sympy2lean(term))
            if neg == True:  # add -1 to the last term if neg is True
                term = utils.normalize(-args[-1])
                subexprs.append(parser.sympy2lean(term))
            else:
                term = utils.normalize(args[-1])
                subexprs.append(parser.sympy2lean(term))
            new_expr = " * ".join([f"({s})" for s in subexprs])
            self.logger.debug(f"Symbolic Cancel_factor finished \n==> Get {orig_expr} = {new_expr}")
            tactics = [f"llm_cancel_factor {orig_expr} = {new_expr}"]
        else:
            self.logger.debug(f"cancel_factor skipped, due to not failed to factor")
            tactics = []
        return tactics

    @timeout(10)
    def sym_tangent_line(self, neq: str) -> List[str]:
        """Use the tangent line to rewrite the expression

        Args:
            neq (str): the expression to be tangent line

        Returns:
            List[str]: the tactics to tangent line the expression
        """
        lhs, rhs = neq.split("≤", 1)
        lhs, rhs = lhs.strip(), rhs.strip()
        expr = f"0 ≤ ({rhs}) - ({lhs})"
        _, rearranged_expr = expr.split("≤", 1)
        a, b, c, d, e = symbols("a b c d e")  # NOTE: should not using global variables
        orig_expr = parser.lean2sympy(rearranged_expr, local_dict={"a": a, "b": b, "c": c, "d": d, "e": e})
        var_sum, num_vars = sum(orig_expr.free_symbols), len(orig_expr.free_symbols)
        eq_ass = []
        for x in self.equality_assumption:
            eq_ass.append(parser.lean2sympy(x))
        res = utils.single_var_solve(eq_ass, var_sum)
        if var_sum not in res:
            degree = utils.get_degree(orig_expr)
            if degree != float("inf"):  # the problem is homogeneous
                res = {var_sum: num_vars}
        if res == {} or var_sum not in res:
            return []
        expr = utils.make_independent(orig_expr, res)
        args = self.expr_decompose(expr)
        is_independent = all([len(x.free_symbols) <= 1 for x in args])
        is_cycle = all([expr.equals(expr.xreplace(maps)) for maps in self.cycle_mappings])
        if not is_independent or not is_cycle:
            return []
        for x_ in set([res[var_sum] / num_vars, 1]):
            fun = Add(*[x for x in args if x.has(a)])
            dfun = diff(fun, a)
            new_fun = fun.subs(a, x_) + dfun.subs(a, x_) * (a - x_)
            ### check by smt, whether f(x) >= f(x_) + dfun(x_) * (x - x_) holds
            concl = fun >= new_fun
            code = parser.sympy2smt(self.sym_cons, concl)
            ok, msg = utils.smtsolve(code, self.smt_solvers, self.smt_timeout)
            if str(ok) == "unsat":
                """check the validaty after applying the tangent line
                fun(a) is the single variable function (only w.r.t. a)
                fun + Add(*[fun.subs(s, simultaneous=True) for s in self.cycle_mappings]) is the entire function (w.r.t. all variables)
                since we may have residual terms, i.e., sympy_expr - (fun + Add(*[fun.subs(s, simultaneous=True) for s in self.cycle_mappings]))
                we need to check the validaty of the residual terms when substitute the fun by new_fun
                """
                delta_expr = orig_expr - (fun + Add(*[fun.subs(s, simultaneous=True) for s in self.cycle_mappings]))
                sympy_expr = (
                    delta_expr + new_fun + Add(*[new_fun.subs(s, simultaneous=True) for s in self.cycle_mappings])
                )
                sympy_expr = simplify(sympy_expr)
                new_concl = sympy_expr >= 0
                code = parser.sympy2smt(self.sym_cons, new_concl)
                ok, msg = utils.smtsolve(code, self.smt_solvers, self.smt_timeout)
                if str(ok) == "unsat":
                    sympy_expr = utils.normalize(sympy_expr)
                    new_expr = parser.sympy2lean(sympy_expr)
                    return [f"sym_tangent_line {new_expr.strip()} ≤ {rearranged_expr.strip()}"]
        return []

    def sym_equal_value(self, neq: str) -> List[str]:
        """Use the equal value (n-1 EV) method to rewrite the expression

        Args:
            neq (str): the expression to be equal value

        Returns:
            List[str]: the tactics to equal value the expression
        """
        lhs, rhs = neq.split("≤", 1)
        lhs, rhs = lhs.strip(), rhs.strip()
        expr = f"0 ≤ ({rhs}) - ({lhs})"
        _, rearranged_expr = expr.split("≤", 1)
        a, b, c, d, e = symbols("a b c d e")  # NOTE: should not using global variables
        sympy_expr = parser.lean2sympy(rearranged_expr, local_dict={"a": a, "b": b, "c": c, "d": d, "e": e})
        var_sum, num_vars = sum(sympy_expr.free_symbols), len(sympy_expr.free_symbols)
        expr_vars = [a, b, c, d, e][:num_vars]
        eq_ass = []
        for x in self.equality_assumption:
            eq_ass.append(parser.lean2sympy(x))
        res = utils.single_var_solve(eq_ass, var_sum)
        if var_sum not in res:
            degree = utils.get_degree(sympy_expr)
            if degree != float("inf"):  # the problem is homogeneous
                res = {var_sum: num_vars}
        if res == {} or var_sum not in res:
            return []
        expr = utils.make_independent(sympy_expr, res)
        is_independent = all([len(x.free_symbols) <= 1 for x in self.expr_decompose(expr)])
        is_cycle = all([expr.equals(expr.xreplace(maps)) for maps in self.cycle_mappings])
        if not is_independent or not is_cycle:
            return []
        ### Check exactly one inflection point
        fun = Add(*[x for x in args if x.has(a)])
        ddfun = fun.diff(a).diff(a)
        if (a > 0) in self.sym_cons or (a >= 0) in self.sym_cons:
            x = Symbol("x", real=True, positive=True)
        else:
            x = Symbol("x", real=True)
        sols = solve(ddfun.subs(a, x), x)
        if len(sols) != 1:
            return []
        t = expr_vars[-1]
        t_ = (res[var_sum] - t) / (num_vars - 1)
        for x_ in expr_vars[:-1]:
            sympy_expr = sympy_expr.subs(x_, t_)
        sympy_expr = simplify(sympy_expr)
        concl = sympy_expr >= 0
        code = parser.sympy2smt(self.sym_cons, concl)
        ok, msg = utils.smtsolve(code, self.smt_solvers, self.smt_timeout)
        if str(ok) == "unsat":
            sympy_expr = utils.normalize(sympy_expr)
            new_expr = parser.sympy2lean(sympy_expr)
            return [f"sym_equal_value 0 ≤ {new_expr.strip()}"]
        return []

    def sym_pqr_method(self, neq: str) -> List[str]:
        """Use the pqr method to rewrite the expression
            (1) determine whether the expression can be converted into pqr format
            (2) if so, check c = 0 and a = b

        Args:
            neq (str): the expression to be pqr method

        Returns:
            List[str]: the tactics to pqr method the expression
        """
        lhs, rhs = neq.split("≤", 1)
        lhs, rhs = lhs.strip(), rhs.strip()
        a, b, c, d, e = parser.get_symbols()
        p, q, r = parser.get_pqr()
        lhs_expr = parser.lean2sympy(lhs, local_dict={"a": a, "b": b, "c": c, "d": d, "e": e})
        rhs_expr = parser.lean2sympy(rhs, local_dict={"a": a, "b": b, "c": c, "d": d, "e": e})
        if utils.has_var_denom(lhs_expr - rhs_expr):  # denominator should be constant
            return []
        if not lhs_expr.free_symbols.issubset({a, b, c}) or not rhs_expr.free_symbols.issubset({a, b, c}):  # only support 3 variables
            return []
        if not all(
            [(x > 0) in self.sym_cons or (x >= 0) in self.sym_cons for x in [a, b, c]]
        ):  # only support positive variables
            return []
        lhs = lhs_expr.expand()
        lhs_coeffs = sorted(set(poly(lhs, gens=[a, b, c]).coeffs()))
        pqr_format = []
        for t, map_t in parser.pqr_mappings.items():
            t = t.expand()
            k = 0
            for coeff in lhs_coeffs:
                tmp_expr = lhs.extract_additively((coeff * t))
                if tmp_expr is None:
                    break
                else:
                    k = coeff
            if k > 0:
                lhs = lhs.extract_additively((k * t).expand()).expand()
                pqr_format.append(k * map_t)
        if not utils.is_const(lhs):  # cannot be convert to pqr format
            return []
        lhs_pqr = Add(*pqr_format)
        rhs = rhs_expr.expand()
        rhs_coeffs = sorted(set(poly(rhs, gens=[a, b, c]).coeffs()))
        pqr_format = []
        for t, map_t in parser.pqr_mappings.items():
            t = t.expand()
            k = 0
            for coeff in rhs_coeffs:
                tmp_expr = rhs.extract_additively((coeff * t))
                if tmp_expr is None:
                    break
                else:
                    k = coeff
            if k > 0:
                rhs = rhs.extract_additively((k * t).expand()).expand()
                pqr_format.append(k * map_t)
        if not utils.is_const(rhs):  # cannot be convert to pqr format
            return []
        rhs_pqr = Add(*pqr_format)
        pqr_expr = poly(lhs_pqr - rhs_pqr, gens=[r])
        # solve p, q, r
        eq_ass = []
        for x in self.equality_assumption:
            eq_ass.append(parser.lean2sympy(x))
        for x, y in zip([p, q, r], [a + b + c, a * b + b * c + a * c, a * b * c]):
            res = utils.single_var_solve(eq_ass, y)
            if res != {} and utils.is_const(res[y]):
                pqr_expr = pqr_expr.replace(x, res[y])
        A, B, C = pqr_expr.nth(2), pqr_expr.nth(1), pqr_expr.nth(0)
        a_pos, b_pos, c_pos = symbols("a_ b_ c_", positive=True)
        if Ge(A, 0) == True:
            new_expr = None
            rearranged_expr = (lhs_expr - rhs_expr)
            """Check if an expression is provable by single variable (default positive)
            1) for homogeneous expression, convert to single variable
            2) for non-homogeneous expression with equations, make it homogeneous
            """
            degree = utils.get_degree(rearranged_expr)
            if degree == float("inf") and eq_ass != []:
                delta_expr = eq_ass[0].lhs / eq_ass[0].rhs
                delta_degree = utils.get_degree(delta_expr)
                if delta_degree != float("inf"):
                    rearranged_expr = utils.make_homogeneous(rearranged_expr, delta_expr, delta_degree)
                    degree = utils.get_degree(rearranged_expr)
            if degree != float("inf"):
                constant = rearranged_expr.xreplace({c: 0})
                constant = constant.xreplace({b : 1, a : a_pos})
                if reduce_inequalities(constant <= 0) == True: # no counter example
                    new_expr = simplify(rearranged_expr.xreplace({c: b}))
            elif len(eq_ass) > 0: 
                """
                if there are equations, check c = 0 and reduce b by a
                """
                eq_ass_ceq0 = [eq.xreplace({a: a_pos, b: b_pos, c: 0}) for eq in eq_ass]
                res = utils.single_var_solve(eq_ass_ceq0, b_pos)
                if res != {}: # replace b_pos by a_pos
                    b_val = res[b_pos]
                    constant = rearranged_expr.xreplace({a: a_pos, b: b_val, c: 0})
                    if reduce_inequalities(constant <= 0) == True: # no counter example
                        eq_ass_ceqb = [eq.xreplace({c: b_pos, a: a_pos, b: b_pos}) for eq in eq_ass]
                        res = utils.single_var_solve(eq_ass_ceqb, b_pos)
                        if res != {}: # replace b_pos by a_pos
                            new_expr = rearranged_expr.xreplace({c: b}).xreplace({b: res[b_pos], a: a_pos})
                        else:
                            res = utils.single_var_solve(eq_ass_ceqb, a_pos)
                            if res != {}: # replace a_pos by a
                                """
                                new_expr <= 0 and a_val > 0 should be true
                                a_val and new_expr are in the different sign
                                """
                                new_expr = rearranged_expr.xreplace({c: b}).xreplace({b: b_pos, a: res[a_pos]}) * res[a_pos]
                                numer, denom = new_expr.as_numer_denom()
                                new_expr = numer * denom
                if new_expr is not None and reduce_inequalities(new_expr <= 0) != True:
                    new_expr = None
                else:
                    new_expr = new_expr.xreplace({a_pos: a, b_pos: b, c_pos: c})
            if new_expr is not None:
                sympy_expr = utils.normalize(new_expr)
                sympy_expr = parser.sympy2lean(sympy_expr)
                return [f"sym_pqr_method {sympy_expr.strip()} ≤ 0"]            
        elif Lt(A, 0) == True:
            Delta = B**2 - 4 * A * C
            concl = simplify(Delta.xreplace({p: a + b + c, q: a * b + b * c + a * c})) <= 0
            code = parser.sympy2smt(self.sym_cons, concl)
            ok, msg = utils.smtsolve(code, self.smt_solvers, self.smt_timeout)
            if str(ok) == "unsat":
                sympy_expr = utils.normalize(concl)
                new_expr = parser.sympy2lean(sympy_expr)
                return [f"sym_pqr_method {sympy_expr.strip()} ≤ 0"]
        return []
