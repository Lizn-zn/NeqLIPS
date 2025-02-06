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