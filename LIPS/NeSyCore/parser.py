import re
import warnings
from sympy import Not, Expr, smtlib_code, sympify
from sympy import evaluate, init_printing, sstr
from sympy.parsing.latex import parse_latex
from sympy.parsing.sympy_parser import parse_expr
from sympy.core.parameters import distribute
from sympy.parsing.sympy_parser import (
    standard_transformations,
    implicit_multiplication_application,
    convert_xor,
)
from sympy import symbols

transformations = (
    standard_transformations + (implicit_multiplication_application,) + (convert_xor,)
)

a, b, c, d, e = symbols("a b c d e")

def get_symbols():
    return a, b, c, d, e

def extract_boxed_answers(text):
    answers = []
    for piece in text.split("boxed{")[1:]:
        n = 0
        for i in range(len(piece)):
            if piece[i] == "{":
                n += 1
            elif piece[i] == "}":
                n -= 1
                if n < 0:
                    if i + 1 < len(piece) and piece[i + 1] == "%":
                        answers.append(piece[: i + 1])
                    else:
                        answers.append(piece[:i])
                    break
    return answers

def wrap_parse_expr(expr: str, local_dict={}, evaluate=False):
    try:
        sympy_expr = parse_expr(expr, local_dict=local_dict, transformations=transformations, evaluate=evaluate)
        return sympy_expr
    except Exception as e:
        # warnings.warn(f"WARN: Fail to parse the expression {expr}, due to {e}")
        # print(expr)
        # print(e)
        return None
    
def wrap_parse_latex(expr: str):
    try:
        with evaluate(False) and distribute(False):
            sympy_expr = parse_latex(expr, backend="antlr")
        return sympy_expr
    except Exception as e:
        # warnings.warn(f"WARN: Fail to parse the expression {expr}, due to {e}")
        # print(expr)
        # print(e)
        return None

def str2sympy(expr: str):
    if "\\" in expr or "{" in expr or "}" in expr:
        expr = wrap_parse_latex(expr)
        init_printing(order="none")
        expr = sstr(expr, order="none")
    res = wrap_parse_expr(expr)
    if res is None:
        res = wrap_parse_latex(expr)
    return res

def lean2str(expr: str) -> str:
    # rewrite sqrt 2 as sqrt(2)
    pattern = r"sqrt\s+(\w+)"
    replacement = r"sqrt(\1)"
    expr = re.sub(pattern, replacement, expr)
    expr = expr.replace("sqrt ", "sqrt")
    # remove ↑
    expr = expr.replace("↑", "")
    # change ^ to **
    expr = expr.replace("^", "**")
    # change = to ==
    expr = expr.replace("=", "==")
    expr = expr.replace("≤", "<=")
    expr = expr.replace("≥", ">=")
    expr = expr.replace("≠", "!=")
    return expr

def str2lean(expr:str) -> str:
    expr = expr.replace("sqrt", "sqrt ")
    return expr

def sympy2lean(expr: Expr):
    """
    Translate each Sympy term back to LEAN term
    """
    subs = {
        "**": " ^ ",
        "<=": "≤",
        "sqrt": "sqrt ",
        "²": "^ 2",
        # for better print
        "/": " / ", 
        "*": " * ", 
    }
    try:
        init_printing(order="none")
        expr = sstr(expr, order="none")
    except Exception as e:
        raise e
    for old, new in subs.items():
        expr = expr.replace(old, new)
    return expr

def replace_variables(prefix_target, variables):
    """
    add ? to each pattern match variable
    """
    pattern = r'\b(' + '|'.join(re.escape(v) for v in variables) + r')\b'
    return re.sub(pattern, lambda match: f"?{match.group(1)}", prefix_target)

def lean2sympy(expr: str, local_dict: dict={}, evaluate=False):
    """
    Convert a Lean expression to a sympy expression
    """
    expr = lean2str(expr)
    expr = wrap_parse_expr(expr, local_dict, evaluate)
    return expr

def sympy2smt(conds: list[Expr], concl: Expr=None):
    """
    Convert sympy expressions to SMTLIB code
    """
    # negate the conclusion
    if concl is not None:
        concl = Not(concl, evaluate=False)
        code = smtlib_code(conds+[concl])
    else:
        code = smtlib_code(conds)
    code += "\n(check-sat)\n(get-model)\n(exit)"
    return code

def parse_smt_result(result, smt_level=1):
    """
    Parse the SMT result and return a flag based on the input result.    
    """
    result_mapping = {
        "sat": -1,
        "unsat": 1,
        "timeout": 0,
        "unknown": 0
    }
    
    # Get flag based on result, default to -2 if result is unrecognized
    flag = result_mapping.get(str(result).strip(), -2)
    return -1 if flag < smt_level else 1

def parse_smt_model(msg):
    """
    Parse the SMT model, return a dict of variable assignments like {a: 1.0, b: 1.0, c: 1.0}
    TODO: Note that mathematica solver mmafi and mmard are not supported currently
    """
    if len(msg) > 48: # ignore too long counter examples
        return {}
    elif not msg.startswith("[") or not msg.endswith("]"):
        return {}
    results = {}
    pattern = r'(\w+)\s*(?::=|=|==)\s*([^,]+)'
    matches = re.findall(pattern, str(msg).strip("[]"))
    try:
        exec_res = {var: sympify(value, rational=True) for var, value in matches}
    except Exception as exc:
        return {}
    for x in [a, b, c, d, e]:
        if str(x) not in exec_res:
            continue
        else:
            results[x] = exec_res[str(x)]
    return results       


def parse_math_dict(msg):
    # Remove the curly braces and split by comma
    items = msg.strip('{}').split(',')
    result = {}
    key_replace = {"a": a, "b": b, "c": c, "d": d, "e": e}
    for item in items:
        key, value = item.split(':')
        key = key_replace[key.strip()]
        # Use sympify to evaluate mathematical expressions
        value = sympify(value.strip(), rational=True)
        result[key] = value
    return result


def cycle_sum(expr: Expr):
    cycle_mappings = [{a : b, b : c, c : a}, {a : c, c : b, b : a}]
    sum_expr = expr
    for mapping in cycle_mappings:
        sum_expr += expr.xreplace(mapping)
    return sympify(sum_expr, evaluate=True)

def cycle_prod(expr: Expr):
    cycle_mappings = [{a : b, b : c, c : a}, {a : c, c : b, b : a}]
    prod_expr = expr
    for mapping in cycle_mappings:
        prod_expr *= expr.xreplace(mapping)
    return sympify(prod_expr, evaluate=True)
    
# https://aritra-12.github.io/pdfs/The_pqr_handout%20(1).pdf
p, q, r = symbols("p q r", positive=True)

def get_pqr():
    return p, q, r

pqr_mappings = {
    cycle_sum(a)   : p,
    cycle_sum(a ** 2) : p ** 2 - 2 * q,
    cycle_sum(a ** 3) : p ** 3 - 3 * p * q + 3 * r,
    cycle_sum(a ** 4) : p ** 4 - 4 * p ** 2 * q + 4 * p * r + 2 * q ** 2,
    cycle_sum(a ** 5) : p ** 5 - 5 * p ** 3 * q + 5 * p ** 2 * r + 5 * p * q ** 2 + 5 * q * r,
    cycle_sum(a ** 6) : p ** 6 - 6 * p ** 4 * q + 6 * p ** 3 * r + 9 * p ** 2 * q ** 2 - 2 * q ** 3 - 12 * p * q * r + 3 * r ** 2,
    
    cycle_sum(a * b)                 : q,
    cycle_sum((a * b) ** 2)          : q ** 2 - 2 * p * r,
    cycle_sum((a * b) ** 3)          : q ** 3 - 3 * p * q * r + 3 * r ** 2,
    cycle_sum((a * b) ** 4)          : q ** 4 - 4 * p * q ** 2 * r + 2 * p ** 2 * r ** 2 + 4 * q * r ** 2,
    cycle_sum((a * b) ** 5)          : q ** 5 - 5 * p * q ** 3 * r + 5 * p ** 2 * q * r ** 2 + 5 * q ** 2 * r ** 2 - 5 * p * r ** 3,
    cycle_sum(a ** 2 * b + a * b ** 2)      : p * q - 3 * r,
    cycle_sum(a ** 3 * b + a * b ** 3)      : p ** 2 * q - 2 * q ** 2 - p * r,
    cycle_sum(a ** 4 * b + a * b ** 4)      : p ** 3 * q - 3 * p * q ** 2 - p ** 2 * r + 5 * q * r,
    cycle_sum(a ** 5 * b + a * b ** 5)      : p ** 4 * q - p ** 3 * r - 4 * p ** 2 * q ** 2 + 7 * p * q * r + 2 * q ** 3 - 3 * r ** 2,
    
    cycle_sum(a ** 2 * b * c)          : p * r,
    cycle_sum(a ** 3 * b * c)          : p ** 2 * r - 2 * q * r,
    cycle_sum(a ** 4 * b * c)          : p ** 3 * r - 3 * p * q * r + 3 * r ** 2,
    cycle_sum(a ** 2 * b ** 2 * c)        : q * r,
    cycle_sum(a ** 3 * b ** 2 * c + a ** 3 * b * c ** 2) : p * q * r - 3 * r ** 2,
    cycle_sum(a ** 3 * b ** 2 + a ** 2 * b ** 3) : p * q ** 2 - 2 * p ** 2 * r - q * r,
    
    cycle_sum(a ** 4 * b ** 2 + a ** 2 * b ** 4)          : p ** 2 * q ** 2 - 2 * q ** 3 - 2 * p ** 3 * r + 4 * p * q * r - 3 * r ** 2,
    cycle_sum(a ** 4 * b ** 3 + a ** 3 * b ** 4)          : p * q ** 3 - 3 * p ** 2 * q * r + 5 * p * r ** 2 - q ** 2 * r,
    cycle_sum((a + b) * (b + c))                          : p ** 2 + q,
    cycle_sum((1 + a) * (1 + b))                          : 2 * p + q + 3,
    cycle_sum((1 + a) ** 2 * (1 + b) ** 2)                : 2 * p ** 2 + 2 * p * q - 2 * p * r + q ** 2 + 4 * q - 6 * r + 3,
    cycle_sum((a + b) ** 2 * (b + c) ** 2)                : p ** 4 - p ** 2 * q + q ** 2 - 4 * p * r,
    cycle_sum((a ** 2 + a * b + b ** 2) * (b ** 2 + b * c + c ** 2)) : p ** 4 - 3 * p ** 2 * q + 3 * q ** 2,

    cycle_prod(a)                                          : r,
    cycle_prod(a ** 2)                                     : r ** 2,
    cycle_prod(a + b)                                      : p * q - r,
    cycle_prod(1 + a)                                      : 1 + p + q + r,
    cycle_prod(1 + a ** 2)                                 : p ** 2 + q ** 2 + r ** 2 - 2 * p * r - 2 * q + 1,
    cycle_prod(1 + a ** 3)                                 : p ** 3 + q ** 3 + r ** 3 - 3 * p * q * r - 3 * p * q - 3 * r ** 2 + 3 * r + 1,
    cycle_prod(a ** 2 + a * b + b ** 2)                    : p ** 2 * q ** 2 - 3 * q ** 3 - p ** 3 * r,

    # Two complex product expressions
    cycle_prod((a ** 3 * b + b ** 3 * c + c ** 3 * a) * (a * b ** 3 + b * c ** 3 + c * a ** 3)) : p ** 5 * r - 5 * p ** 3 * q * r + p * q ** 2 * r + 7 * p ** 2 * r ** 2 + q ** 4,
    cycle_prod((a ** 2 * b + b ** 2 * c + c ** 2 * a) * (a * b ** 2 + b * c ** 2 + c * a ** 2)) : p ** 3 * r + 9 * r ** 2 - 6 * p * q * r + q ** 3,

    cycle_prod((a - b) ** 2)                               : -4 * p ** 3 * r + p ** 2 * q ** 2 + 18 * p * q * r - 4 * q ** 3 - 27 * r ** 2,

    # additional
    cycle_sum(a * b) * cycle_sum(a) * cycle_prod(a)        : p * q * r,
    cycle_prod(a) * cycle_sum(a * b) ** 2                  : r * q ** 2,
}
