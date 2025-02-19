from typing import Tuple, List, Dict
from sympy import Expr

import numpy as np
from sympy import symbols, count_ops, Symbol, S
from wrapt_timeout_decorator import timeout

from . import parser
from . import utils
from .llm import LLM
from .problem import Problem

from ..logger_config import default_logger, setup_logger

class Ranker:
    def __init__(self, llm: LLM, ops: str, norm_goal: int, size: int, logger=None):
        self.llm = llm
        self.ops = ops
        self.norm_goal = norm_goal
        self.rank_size = size
        self.logger = logger or default_logger
        # initial the focus ops and its weight
        weights = [1] * 5 + [0] + [0]
        ops_mapping = {"+": 0, "-": 1, "*": 2, "/": 3, "^": 4, "d": 5, "m": 6}
        for op in ops:
            if op in ["+", "-", "*", "/", "^"]:
                weights[ops_mapping[op]] = 0 # encourage the usage of the focus ops
            elif op in ["d"]:
                weights[ops_mapping[op]] = 1 # encourage the decoupling
            elif op in ["m"]:
                weights[ops_mapping[op]] = 1 # encourage the homogeneous
        self.weights = weights
        # initial the list of proof state
        self.num_candidates = 0  # it could be > self.rank_size
        self.proof_states = []
        self.subgoals, self.norm_goals = [], []
        self.init_ps, self.init_goal = -1, ""
        self.best_cost, self.best_ps, self.best_goal = float('inf'), -1, ""
        self.costs_pair = {} # (ps, goal) -> cost

    def set_problem(self, problem: Problem):
        """
        Set the problem from the input (string)
        """
        self.problem_prompt = (
            "\n".join(problem.positivity + problem.assumption) + "\n⊢ " + problem.conclusion
        )

    def update(self, proof_states: list[int], subgoals: list[str]):
        """
        Update the proof states and subgoals
        """
        if self.init_ps == -1 and self.init_goal == "":
            self.init_ps, self.init_goal = proof_states[0], subgoals[0]
        for ps, gs in zip(proof_states, subgoals):
            norm_g = self.norm_state(gs)
            if norm_g in self.norm_goals: # remove duplicate
                self.logger.info(f"Remove duplicate goal {ps} : {norm_g}")
                continue
            else:
                self.norm_goals.append(norm_g)
                self.proof_states.append(ps)
                self.subgoals.append(gs)
                self.costs_pair.update({(ps, gs): -1})

    def get_next(self):
        """
        Get the next proof states and subgoals
        """
        if len(self.proof_states) == 0 or len(self.subgoals) == 0:
            return -1
        ps = self.proof_states.pop(0)
        gs = self.subgoals.pop(0)
        self.costs_pair.pop((ps, gs))
        return ps
    
    def norm_state(self, concl) -> str:
        """
        normalize the goal, e.g., '(c ^ 2 + 1) * b * c ≤ c ^ 2 * sqrt (c ^ 2 + 1) * sqrt (b ^ 2 + 1)'
        use sympy to alleviate the add commutative issue, i.e., ensure a + b and b + a is the same result
        """
        a, b, c, d, e = symbols("a b c d e")
        lhs, rhs = concl.split("≤", 1)
        try:
            lhs = parser.lean2sympy(lhs, local_dict={"a": a, "b": b, "c": c, "d": d, "e": e}, evaluate=self.norm_goal)
            rhs = parser.lean2sympy(rhs, local_dict={"a": a, "b": b, "c": c, "d": d, "e": e}, evaluate=self.norm_goal)
        except:
            print(lhs, rhs)
            raise ValueError("cannot parse the goal")
        norm_g = str(lhs) + " ≤ " + str(rhs)
        return norm_g

    @timeout(300)
    def cal_complexity(self, lhs: Expr, rhs: Expr):
        score = 0
        lhs_args = list(lhs.args) if lhs.is_Add else [lhs]
        rhs_args = list(rhs.args) if rhs.is_Add else [rhs]
        if any(x != 0 for x in self.weights[0:5]): ## calculating
            lhs_calculating = utils.cal_calculating(lhs, self.weights[0:5])
            rhs_calculating = utils.cal_calculating(rhs, self.weights[0:5])
            score += lhs_calculating + rhs_calculating
        if self.weights[5] != 0: ## decoupling
            lhs_decoupling = [utils.cal_decoupling(a) for a in lhs_args]
            rhs_decoupling = [utils.cal_decoupling(a) for a in rhs_args]
            decoupling = max(lhs_decoupling) + min(lhs_decoupling) + max(rhs_decoupling) + min(rhs_decoupling)
            score += decoupling * self.weights[5]
        if self.weights[6] != 0: ## homogeneous
            degree = utils.get_degree(lhs - rhs)
            if degree == float("inf"):
                homogeneity = 1000 # penalty for non-homogeneous
            else:
                lhs_homogeneous = [utils.cal_homogeneous(a) for a in lhs_args]
                rhs_homogeneous = [utils.cal_homogeneous(a) for a in rhs_args]
                homogeneity = (max(lhs_homogeneous) - min(lhs_homogeneous)) / (abs(max(lhs_homogeneous)) + 1) \
                        + (max(rhs_homogeneous) - min(rhs_homogeneous)) / (abs(max(rhs_homogeneous)) + 1)
                homogeneity = homogeneity * 30.0 # normalize the score
            score += homogeneity * self.weights[6] 
        return int(score)

    def rank_by_complexity(self):
        """
        rank the goals by the complexity of the expression
        Some subgoals may have equal cost, and thus we determine num_condidates instead of directly using rank_size
        """
        if len(self.proof_states) <= 1 or len(self.subgoals) <= 1:
            return self.proof_states, self.subgoals
        for ps, gs in zip(self.proof_states, self.subgoals):
            if self.costs_pair[(ps, gs)] != -1:
                continue
            lhs, rhs = gs.split("≤", 1)
            lhs, rhs = parser.lean2sympy(lhs), parser.lean2sympy(rhs)
            try:
                cost = self.cal_complexity(lhs, rhs)
            except Exception as exc:
                self.logger.error(f"cal complexity error {exc} for the expression {lhs} <= {rhs}")
                cost = 10000
            self.costs_pair.update({(ps, gs) : cost})  
            has_var_denom = 1 if utils.has_var_denom(lhs - rhs) else 0
            if self.best_cost > cost + 10000 * has_var_denom: # save the best proof state and goal
                self.best_cost = cost + 10000 * has_var_denom
                self.best_ps, self.best_goal = ps, gs
        flatten_costs_pair = sorted(self.costs_pair.items(), key=lambda x: x[1])
        val = flatten_costs_pair[: self.rank_size][-1][1]
        num_candidates = len([c for c in flatten_costs_pair if c[1] <= val])
        self.num_candidates = num_candidates
        self.proof_states = [c[0][0] for c in flatten_costs_pair]
        self.subgoals = [c[0][1] for c in flatten_costs_pair]
        self.logger.info("RANK by Complexity")
        # for i in range(min(num_candidates, len(self.costs_pair))):
        for i in range(len(self.costs_pair)):
            self.logger.info(f"Rank: {flatten_costs_pair[i][1]}, Proof State: {flatten_costs_pair[i][0][0]}, Goal: {flatten_costs_pair[i][0][1]}")
        return self.proof_states, self.subgoals

    def rank_by_llm(self):
        if len(self.proof_states) <= 1 or len(self.subgoals) <= 1:
            return self.proof_states, self.subgoals
        prompt = (
            "### Task\n"
            "I am trying to prove the original inequality\n"
            "{problem}\n"
            "and have transformed it into the following inequalities\n"
            "Your task is to rank the given transformation results in a descent order\n"
            "### Notice\n"
            "1. Please reason step by step\n"
            "2. More meaningful transformation results, i.e., those that reduce the difficulty of proving, should be ranked higher.\n"
            "3. Put the index of selected inequality within \\boxed{{}}, e.g., \\boxed{{(1),(2),(3)}}\n"
            "### Response\n"
            "User:\n"
            "{proof}\n"
            "Assistant:\n"
        )
        prompt = prompt.format(
            problem=self.problem_prompt,
            proof="\n".join(f"({id}) : {prob}" for id, prob in enumerate(self.subgoals[0 : self.num_candidates])),
        )
        idxs = self.llm.adaptive_response(prompt, 2)
        idxs = (",".join(idxs)).split(",")
        try:
            tmp_res = []
            max_index = len(self.subgoals) - 1
            # project to len(goals) and parse the int index
            for neq in idxs:
                ind = int(neq.strip().strip("()"))
                ind = min(ind, max_index)
                if ind not in tmp_res:
                    tmp_res.append(ind)
            idxs = tmp_res
        except (ValueError, IndexError):
            self.logger.error(f"Invalid index {neq}, please select a valid index")
            idxs = [i for i in range(len(self.subgoals))]
        selected_ps = [self.proof_states[i] for i in idxs]
        remaining_ps = [ps for i, ps in enumerate(self.proof_states) if i not in idxs]
        self.proof_states = selected_ps + remaining_ps
        selected_goals = [self.subgoals[i] for i in idxs]
        remaining_goals = [g for i, g in enumerate(self.subgoals) if i not in idxs]
        self.subgoals = selected_goals + remaining_goals
        self.logger.info("RANK by LLM")
        for idx in range(min(len(self.subgoals), self.num_candidates)):
            self.logger.info(f"No.{idx}: {self.subgoals[idx]}")

    def rank(self):
        """
        rank the goals by combining the complexity and llm
        """
        self.rank_by_complexity()
        self.rank_by_llm()
