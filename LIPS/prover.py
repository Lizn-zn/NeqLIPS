from typing import Tuple, List, Dict
from sympy import Expr, Gt, Le, Eq

import os
import subprocess
import json
import ast
from sympy import symbols, sympify, simplify
from sympy.simplify.powsimp import powsimp, powdenest
from wrapt_timeout_decorator import timeout

from .LeanIO import LeanIO
from .NeSyCore import parser
from .NeSyCore import utils
from .NeSyCore.problem import Problem
from .NeSyCore.llm import LLM
from .NeSyCore.rewriter import Rewriter
from .NeSyCore.ranker import Ranker
from .NeSyCore.scaler import Scaler

from .logger_config import setup_logger


class Prover:
    def __init__(self, args):
        # Set the configuration
        self.configure(args)

        # Initialize the save directory
        self.json_file = os.path.join(self.save_dir, "proof.json")
        self.log_file = os.path.join(self.save_dir, "proof.log")
        self.logger = setup_logger(log_file=self.log_file, log_level=args.log_level.upper())

        # Initialize components
        self.initialize_modules()
        self.initialize_smt_config(self.smt_config)

        # Initialize problem
        self.problem = None
        self.finish_state = None

        # Initialize the covered steps and the covered goals
        self.cover_steps = []

    def configure(self, args):
        """Set the configuration attributes."""
        for key, value in vars(args).items():
            setattr(self, key, value)
            
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

    def initialize_modules(self):
        """Initialize the modules of the Prover."""
        self.leanio = LeanIO(self.math_dir, self.repl_dir, self.force_rebuild, self.logger)
        self.llm = LLM(self.oai_version, self.temperature, self.top_p, self.max_tokens, self.logger)
        self.scaler = Scaler(
            self.scale_limit,
            self.smt_config,
            self.init_test,
            self.scale_equality,
            self.num_threads,
            self.logger,
        )
        self.rewriter = Rewriter(
            self.rewrite_limit,
            self.llm,
            self.smt_config,
            self.sym_rewrite,
            self.num_threads,
            self.logger,
        )
        self.ranker = Ranker(
            self.llm,
            self.focus_ops,
            self.norm_goal,
            self.rank_size,
            self.logger,
        )

    def __str__(self):
        """
        Return the configuration of the prover
        """
        try:
            configs = (
                "LeanLM configuration: \n"
                f"oai details: {self.oai_version}\n"
                f"llm generation details: temperature={self.temperature}, top_p={self.top_p}, max_tokens={self.max_tokens}\n"
                f"smt config: {self.smt_config}\n"
                f"initial test case: {self.init_test}\n"
                f"save directory: {self.save_dir}\n"
                # f"Problem Property: \n"
                # f"is_cycle: {self.problem.is_cycle}\n"
                # f"ranker: {self.ranker}\n"
                # f"debug mode: {self.debug}\n"
            )
        except:
            raise KeyError("LeanLM configuration is not set properly")
        return configs

    def save_json(self):
        """
        Save the proof tree to a json file
        """
        # get the golden path from root to the finish state
        if self.finish_state is not None:
            golden_path = self.leanio.get_trace_idx(self.finish_state)
        else:
            golden_path = []
        if self.json_file is not None:
            tree_json = self.leanio.to_dict(nid=None, golden_path=golden_path)
            with open(self.json_file, "w", encoding="utf-8") as json_file:
                json.dump(tree_json, json_file, ensure_ascii=False, indent=2)

    def set_problem(self, problem: str):
        """
        Set the problem from the input (string)
        """
        if self.problem is not None:
            raise TypeError("The problem has been declared, please create a new Prover")
        self.leanio.build("import Math")
        self.leanio.build("open Real")
        # thm.build("set_option maxHeartbeats 1000000000")
        self.leanio.build("local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))")
        proof_state = self.leanio.build(problem)
        goals = self.leanio.get_goals(proof_state)
        if len(goals) > 1:
            raise NotImplementedError("Multiple goals are not supported yet")

        # set positivities and assumptions
        self.problem = Problem(goals[0])
        self.problem.check_cycle()
        # make the expression homogeneous
        if self.check_homogeneous == True:   
            neq = self.problem.conclusion
            if self.is_homogeneous(neq):
                tactics = self.intro_by_homogeneous(neq)
            else:
                tactics = self.make_by_homogeneous(neq)
            if tactics != []:
                proof_state = self.leanio.apply(tactics[0], proof_state)
            
        self.ranker.set_problem(self.problem)
        self.scaler.set_problem(self.problem)
        self.rewriter.set_problem(self.problem)

        # update proof state
        self.update_state([proof_state])
    
    """
    The following are the homogeneous operators
    """
    def is_homogeneous(self, neq: str) -> bool:
        """Check if the problem is homogeneous
        """
        lhs, rhs = neq.split("≤", 1)
        orig_expr = parser.lean2sympy(lhs) - parser.lean2sympy(rhs)
        return utils.get_degree(orig_expr) != float("inf")

    def intro_by_homogeneous(self, neq: str) -> List[str]:
        """Introduce the assumption by the homogeneous
        """
        equality_assumption = self.problem.equality_assumption
        if equality_assumption != []:
            return []
        lhs, rhs = neq.split("≤", 1)
        orig_expr = parser.lean2sympy(lhs) - parser.lean2sympy(rhs)
        if utils.get_degree(orig_expr) != float("inf"): # the problem is originally homogeneous
            var_lst = list(orig_expr.free_symbols)
            var_sum = parser.sympy2lean(sum(var_lst))
            eq_assume = f"{var_sum} = {len(var_lst)}"
            self.logger.info(f"The problem is initially homogeneous, introduce the assumption {eq_assume}")
            self.problem.update_constraint(eq_assume)
            return [f"intro_by_homogeneous {eq_assume}"]
        else:
            return []

    def make_by_homogeneous(self, neq: str) -> List[str]:
        """Make the expression homogeneous

        Args:
            neq (str): the expression to be made homogeneous
            intro_assume (bool): whether to introduce the assumption
        Returns:
            List[str]: the tactics to make the expression homogeneous
        """
        equality_assumption = self.problem.equality_assumption
        inequality_assumption = self.problem.inequality_assumption
        constraints = [parser.lean2sympy(c) for c in self.problem.assumption + self.problem.positivity]
        lhs, rhs = neq.split("≤", 1)
        orig_expr = parser.lean2sympy(lhs) - parser.lean2sympy(rhs)
        if utils.get_degree(orig_expr) != float("inf"): # the problem is originally homogeneous
            return []
        self.logger.info("The problem is non-homogeneous, make it homogeneous previously")
        # build delta_expr and delta_degree from equality_assumption and inequality_assumption
        delta_degree = float('inf')
        if equality_assumption != []:
            assume = equality_assumption[0]
            lhs, rhs = assume.split("=", 1)
            lhs_expr = parser.lean2sympy(lhs)
            rhs_expr = parser.lean2sympy(rhs)
            delta_expr = lhs_expr / rhs_expr
            delta_degree = utils.get_degree(delta_expr)
        elif inequality_assumption != []:
            assume = inequality_assumption[0]
            # Define all possible inequality operators
            operators = ["≤",  "≥", ">", "<"]
            # Find the operator in the assumption
            operator = next((op for op in operators if op in assume), None)
            if operator:
                lhs, rhs = assume.split(operator, 1)
                lhs, rhs = lhs.strip(), rhs.strip()
            else:
                self.logger.error(f"No valid inequality operator found in assumption: {assume}")
                return []
            lhs_expr = parser.lean2sympy(lhs)
            rhs_expr = parser.lean2sympy(rhs)
            delta_expr = lhs_expr / rhs_expr
            delta_degree = utils.get_degree(delta_expr)
        if delta_degree == float('inf') or delta_degree == 0:
            return []
        # make the expression homogeneous
        sympy_expr = utils.make_homogeneous(orig_expr, delta_expr, delta_degree)
        if utils.get_degree(sympy_expr) == float("inf"): # failed to make homogeneous
            self.logger.info("Make homogeneous failed")
            return []
        concl = Le(orig_expr, 0)
        condition = Le(sympy_expr, 0)
        try:
            code = parser.sympy2smt(constraints + [condition], concl)
            ok, msg = utils.smtsolve(code, self.smt_solvers, self.smt_timeout)
        except TimeoutError as exc:
            ok, msg = "error", exc

        if str(ok) == "unsat":
            sympy_expr_rearrange = utils.normalize(sympy_expr)
            new_neq = parser.sympy2lean(sympy_expr_rearrange)
            tactics = [f"make_homogeneous {new_neq} ≤ 0"]
            self.logger.info("Make homogeneous success")
        else:
            tactics = []
            self.logger.info(f"LLM make homogeneity failed for {orig_expr} ≤ 0, got incorrect or unprovable format answer {sympy_expr} ≤ 0")
            self.logger.info(f"The SMT result is `{msg}`")

        return tactics
    
    """
    The following are the operators for the proof state
    """
    def update_state(self, proof_states: List[int]):
        """
        Update the proof states
        """
        subgoals = []
        for ps in proof_states:
            goals = self.leanio.get_goals(ps)
            if len(goals) > 1:
                raise NotImplementedError("Multiple goals are not supported yet")
            else:
                subgoals.append(goals[0].split("⊢", 1)[1])
        self.ranker.update(proof_states, subgoals)

    def rank_state(self):
        """
        Rank the proof states
        """
        self.ranker.rank()

    def get_next(self) -> int:
        """
        Rank the candidates, and get the next proof states and subgoals
        """
        return self.ranker.get_next()

    def get_steps(self, proof_state: int) -> List[str]:
        """Get the Lean 4 tactic steps for the current proof state

        Args:
            proof_state (int): The proof state to get the steps for

        Returns:
            List[str]: The list of Lean 4 tactic steps
        """
        goals = self.leanio.get_goals(proof_state)
        trace = self.leanio.print_trace(proof_state)
        # pftree = self.leanio.get_proof_tree()
        if len(goals) > 1:
            raise NotImplementedError("Multiple goals are not supported yet")
        self.logger.info(f"Start from a new goal: {goals[0]}")
        if self.prover_vb > 0:
            # print(f"Current search tree: " + "\n" + f"{pftree}")
            print(f"Current trace: " "\n" + f"{trace}")
            print(f"Current goals: " + "\n" + f"{goals[0]}")
        g = goals[0]
        neq = g.split("⊢", 1)[1]
        try:
            scaling_tactics = self.scaler.parallel_scale(neq)
        except TimeoutError as exc:
            print(f"scaling encounters timeout {exc}")
            raise exc

        prev_steps = trace.split("\n  ")[::-1]
        if any([not prev_steps[i].startswith("llm") for i in range(min(len(prev_steps), self.rewrite_length))]):
            try:
                rewriting_tactics = self.rewriter.parallel_rewrite(neq)
            except TimeoutError as exc:
                print(f"rewriting encounters timeout {exc}")
                rewriting_tactics = []
        else:
            rewriting_tactics = []
        return scaling_tactics + rewriting_tactics

    def get_state(self, proof_state: int, tactics: List[str]) -> List[int]:
        """
        Apply the tactics to the proof states
        """
        neq = self.leanio.get_goals(proof_state)
        success_tactics = []
        generated_proof_states = []
        for tactic in tactics:
            if (neq, tactic) in self.cover_steps:
                if self.prover_vb:
                    print(f"{tactic} failed because it has been covered")
                continue
            else:
                self.cover_steps.append((neq, tactic))
            new_proof_state = self.leanio.apply(tactic, proof_state)
            if new_proof_state == proof_state:
                if self.prover_vb:
                    print(f"{tactic} failed because it cannot be applied")
                continue
            try:
                goal_probe, new_proof_state, msg = self.check_state(new_proof_state)
            except TimeoutError:
                goals = self.leanio.get_goals(proof_state)
                goal_probe = 0
                if self.prover_vb:
                    print(f"{tactic} failed because it gets a timeout error for state checking of {goals}")
                pass
            if goal_probe == -1:  # illegal goals
                self.leanio.remove_step(new_proof_state)
                if self.prover_vb:
                    print(f"{tactic} failed: {msg}")
                continue
            elif goal_probe == 1:
                self.finish_proof(new_proof_state)
                return None  # finish the proof
            if self.prover_vb:
                print(f"{new_proof_state}: {tactic} success to push forward the proof")
            success_tactics.append(tactic)
            generated_proof_states.append(new_proof_state)
        return generated_proof_states

    @timeout(30)
    def check_state(self, proof_state: int) -> Tuple[int, int, str]:
        """
        -1: if the inequality does contain >=, then it is illegal
        -1: if the inequality have multiple goals (to be implemented in the future)
        -1: if the goal is not a valid inequality (e.g., non-cycle structure)
        0: the goals are legal
        1: the goals are all proved
        """
        goals = self.leanio.get_goals(proof_state)
        if len(goals) == 0:
            return 1, proof_state, "no goal exists"
        elif len(goals) > 1:
            return -1, proof_state, "multiple goals exist"
        g = goals[0]
        if not "≤" in g.split("⊢", 1)[1]:  # remove unnormalized goals
            return -1, proof_state, "unexpected goal encountered"
        neq = g.split("⊢", 1)[1]
        orig_lhs, orig_rhs = neq.split("≤", 1)
        a, b, c, d, e = symbols("a b c d e", real=True)
        lhs = sympify(
            parser.lean2sympy(orig_lhs, local_dict={"a": a, "b": b, "c": c, "d": d, "e": e}),
            evaluate=True,
        )
        rhs = sympify(
            parser.lean2sympy(orig_rhs, local_dict={"a": a, "b": b, "c": c, "d": d, "e": e}),
            evaluate=True,
        )
        if lhs is None or rhs is None:
            return -1, proof_state, "invalid goal"
        expr = powsimp(powdenest(lhs - rhs, force=True), force=True)
        if utils.has_var_power(expr):
            return -1, proof_state, "remove goal containing variable power"
        if self.check_cycle == True and self.problem.is_cycle == True:
            vars = list(expr.free_symbols)
            cycle_mappings = []
            for d in range(1, len(vars)):
                cycle_mappings.extend([{vars[idx]: vars[(idx + d) % len(vars)] for idx in range(len(vars))}])
            is_new_state_cycle = all([utils.sympy_equal(expr, expr.xreplace(s)) for s in cycle_mappings])
            if not is_new_state_cycle:
                return -1, proof_state, "remove non-cycle structure"
        if utils.is_const(str(expr)):
            orig_expr = f"{orig_lhs} - {orig_rhs}"
            next_proof_state = self.leanio.apply(f"sym_simplify {orig_expr.strip()} = {str(expr).strip()}", proof_state)
            next_proof_state = self.leanio.apply("try close", next_proof_state)
            goals = self.leanio.get_goals(next_proof_state)
            if len(goals) == 0:
                return 1, next_proof_state, "finish the proof"
            else:
                if next_proof_state != proof_state:
                    self.leanio.remove_step(next_proof_state)
        if utils.cal_depth(expr) <= 3 or utils.cal_calculating(expr, [1, 1, 1, 1, 1]) <= 8 or utils.is_const(lhs):
            next_proof_state = self.leanio.apply("try close", proof_state)
            goals = self.leanio.get_goals(next_proof_state)
            if len(goals) == 0:
                return 1, next_proof_state, "finish the proof"
            else:
                if next_proof_state != proof_state:
                    self.leanio.remove_step(next_proof_state)
        return 0, proof_state, "legal new state"

    @timeout(10)
    def probe_state(self, proof_state: int) -> int:
        """
        Check if the proof state is provable using smt solver
        if the proof state is unprovable, then remove the proof state
        """
        goals = self.leanio.get_goals(proof_state)
        if len(goals) > 1:
            raise NotImplementedError("Multiple goals are not supported yet")
        neq = goals[0].split("⊢", 1)[1]
        lhs, rhs = neq.split("≤", 1)
        lhs = parser.lean2sympy(lhs)
        rhs = parser.lean2sympy(rhs)
        conds = self.problem.positivity + self.problem.assumption
        concl = powsimp(powdenest(lhs - rhs, force=True), force=True) <= 0
        if concl == True:
            smt_res, msg = 1, "Trivial"
        else:
            assumptions = [parser.lean2sympy(a) for a in conds]
            code = parser.sympy2smt(assumptions, concl)
            ok, msg = utils.smtsolve(
                code,
                smt_solvers=self.scaler.smt_solvers,
                smt_timeout=self.scaler.smt_timeout,
            )
            smt_res = parser.parse_smt_result(ok, self.scaler.smt_level)
            if smt_res <= 0:
                self.leanio.remove_step(proof_state)
        if self.prover_vb > 0:
            print(f"Probing the proof state: {neq} with the result: {msg}")
        return smt_res, msg
    
    
    def close_by_sym(self):
        """
        Close the proof state by SOS
        """
        ps_lst = [self.ranker.init_ps, self.ranker.best_ps]
        gs_lst = [self.ranker.init_goal, self.ranker.best_goal]
        for ps, gs in zip(ps_lst, gs_lst):
            print("SOS try to prove the goal: ", gs)
            if not self.leanio.exist_step(ps):
                continue
            # make the problem homogeneous
            tactics = self.make_by_homogeneous(gs)
            if tactics != []:
                ps = self.leanio.apply(tactics[0], ps)
                gs = self.leanio.get_goals(ps)[0]
                gs = gs.split("⊢", 1)[1]
            sym_cons = [parser.lean2sympy(c) for c in self.problem.assumption + self.problem.positivity]
            sym_goal = parser.lean2sympy(gs)
            code = parser.sympy2smt(sym_cons, sym_goal)
            ok, msg = utils.sosprove(code, ["tsds", "schd"], 15)
            print(f"The results of sos prover: {msg}")
            if ok == True:
                new_proof_state = self.leanio.apply("closed_by_sos", ps)
                self.finish_proof(new_proof_state)
                return True
        for ps, gs in zip(ps_lst, gs_lst):
            # check by positivity
            print("SMT try to prove the goal: ", gs)
            if not self.leanio.exist_step(ps):
                continue
            next_ps = self.leanio.apply("smt_decide!", ps)
            goals = self.leanio.get_goals(next_ps)
            if len(goals) == 0:
                self.finish_proof(next_ps)
                return True
        return False
    
    def finish_proof(self, ps):
        self.finish_state = ps
        print("FINISH!!!")
        print("The FINAL PROOF IS AS FOLLOWS")
        print(self.leanio.print_trace(ps))
        self.save_json()

    def clean(self):
        try:
            subprocess.run(["pkill", "-9", "mserver"], check=False, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            subprocess.run(["pkill", "-9", "mtsolve"], check=False, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            subprocess.run(["pkill", "-9", "wolframscript"], check=False, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            subprocess.run(["pkill", "-9", "WolframKernel"], check=False, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        except subprocess.CalledProcessError as e:
            pass
