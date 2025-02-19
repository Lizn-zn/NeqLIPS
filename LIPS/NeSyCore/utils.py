from typing import Tuple, List, Dict
from sympy import Expr

import warnings
import numpy as np
from wrapt_timeout_decorator import timeout
from sympy import sympify, simplify, nsimplify
from sympy import symbols, count_ops, Symbol, Function, S
from sympy import Integer, I, Pow, Eq
from sympy import solve
from sympy.simplify.powsimp import powsimp, powdenest

import pyegg
import mtsolver

from . import parser
from .converter import Converter


def sympy_equal(expr1: Expr, expr2: Expr):
    """
    Compare two sympy expressions
    """
    try:
        if expr1.free_symbols != expr2.free_symbols:
            return False
        vars = expr1.free_symbols
        vals = np.random.random(len(vars))
        try:
            expr1_val = expr1.evalf(subs={v: val for (v, val) in zip(vars, vals)})
            expr2_val = expr2.evalf(subs={v: val for (v, val) in zip(vars, vals)})
            if expr1_val.has(I) or expr2_val.has(I):
                val_not_equal = False
            else:
                val_not_equal = not np.allclose(float(expr1_val), float(expr2_val))
        except Exception as e:
            # print(expr1, expr2, expr1_val, expr2_val)
            warnings.warn(f"Val equal {expr1} = {expr2} error in sympy_equal")
            val_not_equal = False
        if val_not_equal:
            return False
        # return simplify(powsimp(expr1, force=True) - powsimp(expr2, force=True), force=True) == 0 # this is too slow
        return powsimp(expr1, force=True).equals(powsimp(expr2, force=True))
    except Exception as exc:
        warnings.warn(f"sympy equal error {exc} for {expr1} = {expr2}")
        return False


def sympy_simp(expr: str) -> Tuple[str, Expr, Expr]:
    """Parse and simplify a sympy expression

    Args:
        expr (str): the expression to be parsed and simplified

    Returns:
        Tuple[str, Expr, Expr]: the original expression, the sympy expression, and the simplified expression
    """
    str_expr = expr
    sympy_expr = parser.str2sympy(expr)
    if sympy_expr is None:
        return None, None, None
    else:
        try:
            simp_expr = sympify(sympy_expr, evaluate=True)
        except:
            return None, None, None
        return str_expr, sympy_expr, simp_expr
    
@timeout(10)
def sympy_replace(expr: Expr, subs: Dict[Expr, Expr]) -> Expr:
    """Replace the variables in an expression, but with time limit
    """
    try:
        return expr.xreplace(subs)
    except TimeoutError as e:
        raise TimeoutError(f"Timeout when replacing {expr} with {subs}")


def is_const(expr: Expr) -> bool:
    """A tricky way to check if an expression is constant

    Args:
        expr (Expr): the expression to be checked

    Returns:
        bool: True if the expression is constant, False otherwise
    """
    return not any([x in str(expr) for x in ["a", "b", "c", "d", "e"]])


@timeout(60)
def smtsolve(code: str, smt_solvers: List[str], smt_timeout: int) -> Tuple[bool, str]:
    smts = {}
    for s in smt_solvers:
        if s not in [
            "z3",
            "cvc5",
            "sysol",
            "syopt",
            "mplrc",
            "mplbt",
            "mmard",
            "mmafi",
        ]:
            raise ValueError("Invalid solver")
        else:
            smts[s] = {"timeout": smt_timeout}
    ok, msg = mtsolver.solve(code, solvers=smts)
    return ok, msg

@timeout(60)
def sosprove(code, smt_solvers, smt_timeout) -> Tuple[bool, str]:
    smts = {}
    for s in smt_solvers:
        if s not in [
            "tsds",
            "schd",
        ]:
            raise ValueError("Invalid solver")
        else:
            smts[s] = {"timeout": smt_timeout}
    ok, msg = mtsolver.prove(code, solvers=smts)
    return ok, msg

@timeout(60)
def single_var_solve(exprs: List[Expr], var: Expr) -> Expr:
    """Solve an expression with single variable
    """
    try:
        solutions = solve(exprs, var, dict=True)
        # Return the unique solution if exactly one exists, otherwise empty dict
        return solutions[0] if len(solutions) == 1 else {}
    except:
        return {}

def get_degree(expr: Expr) -> int:
    """Get the degree of an expression

    Args:
        expr (Expr): the expression

    Returns:
        int: the degree of the expression
        if non-homogeneous, return float('inf')
    """
    func, args = expr.func, expr.args
    if func.is_Symbol:
        degree = 1
    elif func.is_Number:
        degree = 0
    elif func.is_Mul:
        degree = sum([get_degree(arg) for arg in args])
    elif func.is_Pow:
        base, exp = args
        if exp.is_constant():
            degree = get_degree(base) * exp
        else:
            degree = float('inf')
    elif func.is_Add:
        degrees = set([nsimplify(get_degree(arg)) for arg in args])
        if len(degrees) == 1:
            degree = degrees.pop()
        else:
            degree = float('inf')
    else:
        raise ValueError(f"Unsupported function {expr}")
    if degree == -float("inf"): # non-homogeneous, return inf
        degree = float("inf")
    return degree
        
def make_homogeneous(expr: Expr, delta: Expr, delta_degree: int) -> Expr:
    """Make an expression homogeneous
    
    Args:
        expr (Expr): the expression to be made homogeneous
        delta (Expr): the delta variable
        delta_degree (int): the degree of delta
        
    Returns:
        Expr: the homogeneous expression
    """
    func, args = expr.func, expr.args
    if func.is_Symbol or func.is_Number:
        return expr
    elif not func.is_Add:
        new_args = [make_homogeneous(arg, delta, delta_degree) for arg in args]
    else:
        args = [make_homogeneous(arg, delta, delta_degree) for arg in args]
        degrees = [get_degree(arg) for arg in args]
        max_degree = max(degrees)
        new_args = []
        for idx, arg in enumerate(args):
            if degrees[idx] < max_degree:
                new_degree = nsimplify((max_degree - degrees[idx]) / delta_degree)
                new_args.append(arg * delta ** new_degree)
            else:
                new_args.append(arg)
    return func(*new_args)

def has_var_denom(expr: Expr) -> bool:
    """Check if an expression has a variable in the denominator
    """
    numer, denom = expr.as_numer_denom()
    if len(denom.free_symbols) > 0:
        return True
    else:
        return any([has_var_power(arg) for arg in expr.args])
    
def has_var_power(expr: Expr) -> bool:
    """Check if an expression has a variable in the power
    """
    if expr.is_Symbol or expr.is_Number:
        return False
    else:
        if expr.is_Pow:
            base, exp = expr.args
            if is_const(exp):
                return False
            else:
                return True
        else:
            return any([has_var_power(arg) for arg in expr.args])
                
def make_rearrange(expr: Expr) -> Expr:
    """Make an expression rearranged
    
    Args:
        expr (Expr): the expression to be rearranged
        
    Returns:
        Expr: the rearranged expression
    """
    neg = Function("-") # placeholder fun
    func, args = expr.func, expr.args
    if func.is_Symbol or func.is_Number:
        return expr
    elif not func.is_Add:
        new_args = [make_rearrange(arg) for arg in args]
    else:
        pos_args, neg_args = [], []
        for arg in args:
            try:
                neg_a = arg.extract_multiplicatively(-1)  # return None if cannot extract
                if neg_a and str(neg_a).count("-") < str(arg).count("-"):
                    neg_args.append(neg(make_rearrange(neg_a)))
                else:
                    pos_args.append(make_rearrange(arg))
            except Exception as e:
                print(f"failed to rearrange for {arg}, due to {e}")
                pos_args.append(make_rearrange(arg))
        new_args = pos_args + neg_args
    return func(*new_args, evaluate=False)

def normalize(expr: Expr) -> Expr:
    """Normalize the expression
    """
    # rearrange -a + b to b - a
    rearranged_expr = make_rearrange(expr)
    ## rearrange ((a+b) ^ -2) to 1 / (a+b)^2 
    ## Note, it is not the best fix because it may introduce additional term like 1**2
    ## c.f., https://github.com/sympy/sympy/issues/19435
    # norm_expr = rearranged_expr.replace(lambda x : x.is_Pow and x.exp.is_Rational and x.exp < 0, lambda a : Symbol("1") / Pow(a.base, -a.exp, evaluate=False))
    norm_expr = rearranged_expr.replace(lambda x : x.is_Pow and x.exp.is_Rational and x.exp < 0, lambda a : 1 / Symbol(f"({Pow(a.base, -a.exp, evaluate=True)})"))
    return norm_expr

def make_independent(expr: Expr, equality: Dict[Expr, Expr]) -> Expr:
    """Make an expression independent by substituting the equality assumption
       for example, sqrt (a + b - c) -> sqrt (3 - 2 * c) using the equality assumption a + b + c = 3
    
    Args:
        expr (Expr): the expression to be made independent
        equality (Dict[Expr, Expr]): the equality assumption
        
    Returns:
        Expr: the independent expression
    """
    eq_ass, eq_val = next(iter(equality.items()))
    subs = [{eq_ass - v: eq_val - v} for v in expr.free_symbols] \
                + [{v - eq_ass: v - eq_val} for v in expr.free_symbols]
    if len(expr.free_symbols) <= 1:
        return expr
    else:
        func, args = expr.func, expr.args
        for sub in subs:
            eq, val = next(iter(sub.items()))   
            new_expr = 0
            for _ in range(5):
                res = expr.extract_additively(eq)
                if res is not None:
                    new_expr += val
                    expr = res
                else:       
                    new_expr += expr
                    break
            if len(new_expr.free_symbols) <= 1:
                return new_expr
        return func(*[make_independent(arg, equality) for arg in args])

@timeout(30)
def cal_depth(expr: Expr, max_depth=3) -> int:
    """Compute the depth of an expression

    Args:
        expr (Expr): the expression to be computed
        max_depth (int, optional): the maximum depth. Defaults to 3 (will return 1-4).

    Returns:
        int: the depth of the expression
    """
    # expr = simplify(powsimp(powdenest(expr, force=True), force=True))
    expr = powsimp(powdenest(expr, force=True), force=True) # remove simplify for efficiency
    args = [expr]
    depth = 0
    while args:
        depth += 1
        args = [a for arg in args for a in arg.args]
        if depth > max_depth:
            break
    return depth

@timeout(30)
def cal_ops(expr: Expr) -> int:
    """Compute the number of ops in an expression

    Args:
        expr (Expr): the expression to be computed

    Returns:
        int: the number of ops in the expression
    """
    complexity = count_ops(expr, visual=False)
    return complexity

@timeout(30)
def cal_decoupling(expr: Expr, max_depth=3) -> int:
    """Compute the decoupling of an expression

    Args:
        expr (Expr): the expression to be computed
        max_depth (int, optional): the maximum depth. Defaults to 3 (will return 1-4).

    Returns:
        int: the depth of the expression
    """
    args = [expr]
    score, depth = 0, 0
    while args:            
        score += sum([len(arg.free_symbols) for arg in args])
        if all([len(arg.free_symbols) <= 1 for arg in args]):
            break
        else:
            depth += 1
            args = [a for arg in args for a in arg.args]
        if depth > max_depth:
            break
    return score

@timeout(30)
def cal_homogeneous(expr: Expr, max_depth=3) -> List[int]:
    """Compute the degree of an expression, 
       just compute the degree of the first layer of the expression
       for example sqrt(a + b - c) -> 1/2 and sqrt(sqrt(a) + sqrt(b) - sqrt(c)) -> 1/2

    Args:
        expr (Expr): the expression to be computed

    Returns:
        int: the degree of the expression
    """
    if max_depth == 0:
        score = 1
    else:
        max_depth -= 1
        if is_const(expr):
            score = 0
        elif expr.is_Symbol:
            score = 1
        elif expr.is_Pow:
            score = expr.exp
        elif expr.is_Mul:
            score = sum([cal_homogeneous(arg, max_depth) for arg in expr.args])
        elif expr.is_Add:
            score = max([cal_homogeneous(arg, max_depth) for arg in expr.args])
    return score
        

@timeout(30)
def cal_calculating(expr: Expr, weights: List[int]) -> int:
    ADD, SUB, MUL, DIV, POW = symbols("ADD SUB MUL DIV POW")
    complexity = count_ops(expr, visual=True)
    complexity = complexity.subs({x: w for x, w in zip([ADD, SUB, MUL, DIV, POW], weights)})
    # Every other operation gets a weight of 0 (the default)
    # note that ops distinguish neg and sub
    complexity = complexity.replace(Symbol, type(S.One))
    return complexity

def pattern(scale_in: str, lemma_in: str, var_lst: str) -> List[Dict[str, str]]:
    """
    Pattern match for given scaling lemma
    Rust interface for egg's pattern match
    NOTE In egg, we constraint the e-graph's node by 2048, which can be roughly finished in 120s

    Args:
        scale_in (str): the input expression to be scaled
        lemma_in (str): the input expression of scaling lemma
        var_lst (list[str]): the list of lemma variables to be pattern matched
    Returns:
        List[Dict[str, str]]: list of all patterns
    """
    converter = Converter()
    scale_in_prefix = converter.infix2prefix(parser.lean2str(scale_in))
    lemma_in_prefix = converter.infix2prefix(parser.lean2str(lemma_in))
    lemma_in_prefix = parser.replace_variables(lemma_in_prefix, var_lst)
    patterns_lst = pyegg.rs_match(scale_in_prefix, lemma_in_prefix)
    patterns = []
    for p in patterns_lst:
        try:
            var_maps = {v: converter.prefix2infix(p[v]) for v in var_lst}
        except Exception as exc:
            print("error pattern convertion: ", p)
            raise exc
        if filter(var_maps, var_lst) == False:
            continue
        else:
            patterns.append(var_maps)
    return patterns


def filter(pattern: Dict[str, str], var_lst: List[str]) -> bool:
    """Check whether the pattern is valid
        1) the pattern except [j, k, l] should not be zero
        2) the pattern except [k, l] should not all zero

    Args:
        pattern (Dict[str, str]): the pattern to be checked

    Returns:
        Bool: whether the pattern is valid
    """
    if all([not any([x in pattern[v] for x in ["a", "b", "c", "d", "e"]]) for v in var_lst if v not in ["k", "l"]]):
        return False
    if any([pattern[v] == "0" for v in var_lst if v not in ["k", "l"] and "j" not in v]):
        return False
    return True

    