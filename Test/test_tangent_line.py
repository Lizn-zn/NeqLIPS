from LIPS import Rewriter, LLM, utils, parser
from default_args import parse_args
from sympy.abc import *
from sympy import Eq, Add, Ge, sqrt, Gt

args = parse_args()
llm = LLM(args.oai_version, args.temperature, args.top_p, args.max_tokens)
rewriter = Rewriter(1, llm, args.smt_config, args.num_threads, args.rewriter_vb)

def test_tangent_line1():
    problem = "1 / (2 * a + b + c) ^ 2 + 1 / (a + 2 * b + c) ^ 2 + 1 / (a + b + 2 * c) ^ 2 ≤ 3 / 16"
    rewriter.equality_assumption = ["a + b + c = 1 / a + 1 / b + 1 / c"]
    rewriter.sym_cons = [Gt(a, 0), Gt(b, 0), Gt(c, 0), Eq(a + b + c, 1 / a + 1 / b + 1 / c)]
    rewriter.cycle_mappings = [{a: b, b: c, c: a}, {a: c, b: a, c: b}]
    res = rewriter.sym_tangent_line(problem)
    assert res == []
    
def test_tangent_line2():
    problem = "1 / (3 * a + 2 * b + 2 * c) + 1 / (2 * a + 3 * b + 2 * c) + 1 / (2 * a + 2 * b + 3 * c) ≤ 1 / (3 - 2 * c) + 1 / (3 - 2 * a) + 1 / (3 - 2 * b)"
    rewriter.equality_assumption = ["a + b + c = 1"]
    rewriter.sym_cons = [Gt(a, 0), Gt(b, 0), Gt(c, 0), Eq(a + b + c, 1)]
    rewriter.cycle_mappings = [{a: b, b: c, c: a}, {a: c, b: a, c: b}]
    res = rewriter.sym_tangent_line(problem)
    assert res == ['sym_tangent_line 1 / (a + 2) + 1 / (b + 2) + 1 / (c + 2) + 27 * a / 49 + 27 * b / 49 + 27 * c / 49 - (27 / 49) - (1 / (2 * a + 2 * b + 3 * c)) - (1 / (2 * a + 3 * b + 2 * c)) - (1 / (3 * a + 2 * b + 2 * c)) ≤ (1 / (3 - 2 * c) + 1 / (3 - 2 * a) + 1 / (3 - 2 * b)) - (1 / (3 * a + 2 * b + 2 * c) + 1 / (2 * a + 3 * b + 2 * c) + 1 / (2 * a + 2 * b + 3 * c))']

    