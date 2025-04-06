# Test script for the LeanIO class.
import time
import pytest
from LIPS import LeanIO

def test_LeanIO():
    lean_io = LeanIO(math_dir="./Neq/math", repl_dir="./Neq/repl", force_rebuild=True)
    output = lean_io.get_lean_version() 
    expected_output = "Lean (version 4.15.0, x86_64-unknown-linux-gnu, commit 11651562caae, Release)"
    assert output == expected_output, f"Expected: {expected_output}, Got: {output}"

def test_tactics():
    lean_io = LeanIO(math_dir="./Neq/math", repl_dir="./Neq/repl", force_rebuild=False)
    lean_io.build("import Math")
    lean_io.build("open Real")
    lean_io.build("local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))")
    ps = lean_io.build("theorem lean_workbook_plus_12681 (a b c x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) (h : abs (a * x ^ 2 + b * x + c) ≤ 1) : abs (2 * a * x + b) ≤ 4  := by sorry")
    assert ps == 0, f"Fail to declare the theorem"
    ps = lean_io.apply("cases' le_total 0 (2 * a * x + b) with h₂ h₂", ps)
    assert ps == 1, f"Fail to apply the tactic"

def test_build():
    lean_io = LeanIO(math_dir="./Neq/math", repl_dir="./Neq/repl", force_rebuild=False)
    lean_io.build("import Math")
    lean_io.build("open Real")
    lean_io.build("local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))")
    ps = lean_io.build("theorem P20 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : 2 * (a + b + c) ≤ (a * b + b * c + c * a)) (h' : a + b + c ≥ 6) : 3 / 5 ≤ (a - 1) ^ 2 / (a ^ 2 + 1) + (b - 1) ^ 2 / (b ^ 2 + 1) + (c - 1) ^ 2 / (c ^ 2 + 1) := by sorry")
    assert ps == 0, f"Fail to declare the theorem"
    
def test_tactics1():
    lean_io = LeanIO(math_dir="./Neq/math", repl_dir="./Neq/repl", force_rebuild=False)
    lean_io.build("import Math")
    lean_io.build("open Real")
    lean_io.build("local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))")
    ps = lean_io.build("theorem P4 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a ^ 3 * b * c + b ^ 3 * c * a + c ^ 3 * a * b ≤ a ^ 5 + b ^ 5 + c ^ 5 := by sorry")
    tactic = "llm_simplify a ^ 3 * b * c + b ^ 3 * c * a + c ^ 3 * a * b  - ( a ^ 5 + b ^ 5 + c ^ 5) = c * a * b * (c ^ 2 + a ^ 2 + b ^ 2) - (c ^ 5) - (b ^ 5) - (a ^ 5)"
    ps = lean_io.apply(tactic, ps)
    assert ps == 1, f"Fail to apply the tactic"

def test_leansmt():
    lean_io = LeanIO(math_dir="./Neq/math", repl_dir="./Neq/repl", force_rebuild=False)
    lean_io.build("import Math")
    lean_io.build("open Real")
    lean_io.build("local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))")
    ps = lean_io.build("theorem Example_1d2a {a b c : ℝ} : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by sorry")
    assert ps == 0, f"Fail to declare the theorem"
    ps = lean_io.apply("smt_show", ps)
    assert ps == 1, f"Fail to apply the tactic smt_show"
    ps = lean_io.apply("smt_decide!", ps)
    assert lean_io.get_goals(ps) == [], f"Fail to solve the goal by lean-smt"

def test_leanio1():
    lean_io = LeanIO(math_dir="./Neq/math", repl_dir="./Neq/repl", force_rebuild=True)
    lean_io.build("import Math")
    lean_io.build("open Real")
    lean_io.build("local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))")
    ps = lean_io.build("theorem P1 {a b c : ℝ} : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by sorry")
    ps = lean_io.apply("scale Rearrange_cycle_mul_right_3vars (u := a) (v := b) (w := c) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := 1) (l := 0) (left := a * b + b * c + c * a)", ps)
    goals = lean_io.get_goals(ps)
    assert ps == 1, f"Fail to apply the tactic"
    assert len(goals) == 0, f"Fail to prove the goal"
    
def test_leanio2():
    lean_io = LeanIO(math_dir="./Neq/math", repl_dir="./Neq/repl", force_rebuild=False)
    lean_io.build("import Math")
    lean_io.build("open Real")
    lean_io.build("local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))")
    ps = lean_io.build("theorem PExample {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : 1 / (a + 2) + 1 / (b + 2) + 1 / (c + 2) ≤ 1 / (6 * sqrt (a * b) + c) + 1 / (6 * sqrt (b * c) + a) + 1 / (6 * sqrt (c * a) + b) := by sorry")
    ps = lean_io.apply("make_homogeneous 1 / (2 * a + 2 * b + 3 * c) + 1 / (2 * a + 3 * b + 2 * c) + 1 / (3 * a + 2 * b + 2 * c) - (1 / (a + 6 * sqrt (b * c))) - (1 / (b + 6 * sqrt (a * c))) - (1 / (c + 6 * sqrt (a * b))) ≤ 0", ps)
    ps_ = lean_io.apply("scale Cauchy_Schwarz_sqrt_left_3vars (u1 := 1) (u2 := 1) (u3 := 1) (v1 := (1 / (((2 * a) + (2 * b)) + (3 * c)))) (v2 := (1 / (((2 * a) + (3 * b)) + (2 * c)))) (v3 := (1 / (((3 * a) + (2 * b)) + (2 * c)))) (k := 1) (l := 0) (right := 1 / (c + 6 * sqrt(a * b)) + 1 / (b + 6 * sqrt(a * c)) + 1 / (a + 6 * sqrt(b * c)))", ps)
    ps = lean_io.apply("scale AM_GM_div_cycle_normal_right_2vars (u1 := a) (u2 := c) (u3 := c) (v1 := b) (v2 := a) (v3 := b) (i1 := 6) (i2 := 6) (i3 := 6) (j1 := c) (j2 := b) (j3 := a) (k := 1) (l := 0) (left := 1 / (2 * a + 2 * b + 3 * c) + 1 / (2 * a + 3 * b + 2 * c) + 1 / (3 * a + 2 * b + 2 * c))", ps)
    ps = lean_io.apply("llm_cancel_numer 1 / (2 * a + 2 * b + 3 * c) + 1 / (2 * a + 3 * b + 2 * c) + 1 / (3 * a + 2 * b + 2 * c) - (1 / (6 * (a + b) / 2 + c) + 1 / (6 * (c + a) / 2 + b) + 1 / (6 * (c + b) / 2 + a)) = (a + b - (2 * c)) / ((2 * a + 2 * b + 3 * c) * (3 * a + 3 * b + c)) + (a + c - (2 * b)) / ((2 * a + 3 * b + 2 * c) * (3 * a + b + 3 * c)) + (b + c - (2 * a)) / ((a + 3 * b + 3 * c) * (3 * a + 2 * b + 2 * c))", ps)
    ps = lean_io.apply("llm_factor (a + b - 2 * c) / ((2 * a + 2 * b + 3 * c) * (3 * a + 3 * b + c)) + (a + c - 2 * b) / ((2 * a + 3 * b + 2 * c) * (3 * a + b + 3 * c)) + (b + c - 2 * a) / ((a + 3 * b + 3 * c) * (3 * a + 2 * b + 2 * c)) - (0) = (a + b - (2 * c)) / ((2 * a + 2 * b + 3 * c) * (3 * a + 3 * b + c)) + (a + c - (2 * b)) / ((2 * a + 3 * b + 2 * c) * (3 * a + b + 3 * c)) - ((2 * a - (b) - (c)) / ((3 * a + 2 * b + 2 * c) * (a + 3 * b + 3 * c)))", ps)
    ps = lean_io.apply("llm_simplify (a + b - 2 * c) / ((2 * a + 2 * b + 3 * c) * (3 * a + 3 * b + c)) + (a + c - 2 * b) / ((2 * a + 3 * b + 2 * c) * (3 * a + b + 3 * c)) - ((2 * a - b - c) / ((3 * a + 2 * b + 2 * c) * (a + 3 * b + 3 * c))) = (3 * a + 3 * b - (2)) / ((2 * a + 2 * b + 1) * (-(a) - (b) + 3)) + (1 - (3 * b)) / ((b + 2) * (-(2 * b) + 3)) - ((3 * a - (1)) / ((a + 2) * (-(2 * a) + 3)))", ps)
    ps = lean_io.apply("llm_simplify (3 * a + 3 * b - 2) / ((2 * a + 2 * b + 1) * (-a - b + 3)) + (1 - 3 * b) / ((b + 2) * (-(2 * b) + 3)) - ((3 * a - 1) / ((a + 2) * (-(2 * a) + 3))) = (1 - (3 * b)) / ((b + 2) * (-(2 * b) + 3)) + (1 - (3 * c)) / ((c + 2) * (-(2 * c) + 3)) - ((3 * a - (1)) / ((a + 2) * (-(2 * a) + 3)))", ps)
    ps = lean_io.apply("sym_tangent_line 27 * a / 49 + 27 * b / 49 + 27 * c / 49 - (27 / 49) ≤ ((3 * a - 1) / ((a + 2) * (-(2 * a) + 3))) - ((1 - 3 * b) / ((b + 2) * (-(2 * b) + 3)) + (1 - 3 * c) / ((c + 2) * (-(2 * c) + 3)))", ps)
    ps = lean_io.apply("try close", ps)
    goals = lean_io.get_goals(ps)
    assert len(goals) == 0, f"Fail to prove the goal"

