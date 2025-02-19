"""
used to define the problem
"""
from sympy import Symbol, symbols, solve
from sympy import Not

from . import parser
from . import utils

class Problem:
    def __init__(self, problem):
        """
        problem is stated as the form of "assumption ⊢ goal"
        """
        self.set_problem(problem)
        self.is_cycle = False
        self.cycle_mappings = []
        self.equality_case = {}
        
    def __str__(self):
        return self.problem
    
    def set_problem(self, problem):
        """
        get assumption from the goal, e.g.,
        theorem Example_1d6 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (h : a * b * c = 1) : ...
        note: update to now, we only support only one assumption and one goal
        problem's attribute is set as follows:
        - positivity: list of positivity assumption
        - assumption: list of non-positivity assumptions, where
            - equality_assumption: list of equality assumption
            - inequality_assumption: list of inequality assumption
        - conclusion: goal
        """
        self.problem = problem
        assume, concl = problem.split("⊢", 1)
        positivities, assumptions = [], []
        neq_ass, eq_ass = [], []
        for a in assume.split("\n"):
            value = a.split(":")[-1]
            if value.strip() == "":
                continue
            elif "≥ 0" in value or "> 0" in value or "≠ 0" in value:
                positivities.append(value.strip())
            elif any(v in value for v in ["="]):
                eq_ass.append(value.strip())
                assumptions.append(value.strip())
            elif any(v in value for v in ["≠", "≤", "<", "≥", ">"]):
                neq_ass.append(value.strip())
                assumptions.append(value.strip())
        self.positivity = positivities
        self.assumption = assumptions
        self.equality_assumption = eq_ass
        self.inequality_assumption = neq_ass
        self.conclusion = concl.strip()
        
    def update_constraint(self, constraint: str):
        """
        update the constraint like "a + b + c = 3"
        """
        if "≥ 0" in constraint or "> 0" in constraint or "≠ 0" in constraint:
            self.positivities.append(constraint.strip())
        elif any(v in constraint for v in ["="]):
            self.equality_assumption.append(constraint.strip())
            self.assumption.append(constraint.strip())
        elif any(v in constraint for v in ["≠", "≤", "<", "≥", ">"]):
            self.inequality_assumption.append(constraint.strip())
            self.assumption.append(constraint.strip())
        else:
            raise ValueError(f"Invalid constraint: {constraint}")
    
    def check_cycle(self):
        """
        check if the problem is a cycle inequality
        """
        lhs, rhs = self.conclusion.split("≤", 1)
        expr = parser.lean2sympy(f"({lhs}) - ({rhs})")
        vars = list(expr.free_symbols)
        self.cycle_mappings = []
        for d in range(1, len(vars)):
            self.cycle_mappings.extend([{vars[idx]: vars[(idx + d) % len(vars)] for idx in range(len(vars))}])
        self.is_cycle = all([utils.sympy_equal(expr, expr.xreplace(s)) for s in self.cycle_mappings])
        return self.is_cycle
        
