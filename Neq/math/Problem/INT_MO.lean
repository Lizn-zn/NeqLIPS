import Mathlib
import Math
import Smt

open Real

set_option maxHeartbeats 0

set_option linter.unusedVariables false
set_option by_axiom true
#eval use_axiom

macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))


theorem P1 {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h : a * b + b * c + c * d + d * a = 1) : 1 / 3 ≤ a ^ 3 / (b + c + d) + b ^ 3 / (c + d + a) + c ^ 3 / (d + a + b) + d ^ 3 / (a + b + c) := by
  make_homogeneous a * b / 3 + b * c / 3 + c * d / 3 + d * a / 3 - (d ^ 3 / (a + b + c)) - (c ^ 3 / (a + b + d)) - (b ^ 3 / (a + c + d)) - (a ^ 3 / (b + c + d)) ≤ 0
  scale Titu_variant2_right_4vars (u1 := a) (u2 := b) (u3 := c) (u4 := d) (v1 := ((b + c) + d)) (v2 := ((a + c) + d)) (v3 := ((a + b) + d)) (v4 := ((a + b) + c)) (r := 3) (k := 1) (l := 0) (left := a * b / 3 + b * c / 3 + c * d / 3 + d * a / 3)
  llm_cancel_denom (a * b / 3 + b * c / 3 + c * d / 3 + d * a / 3) - ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 / (a * (b + c + d) + b * (a + c + d) + c * (a + b + d) + d * (a + b + c))) = ((a * b + a * d + b * c + c * d) * (a * (b + c + d) + b * (a + c + d) + c * (a + b + d) + d * (a + b + c)) - (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2)) / (3 * a * (b + c + d) + 3 * b * (a + c + d) + 3 * c * (a + b + d) + 3 * d * (a + b + c))
  scale Rearrange_cycle_mul_left_4vars (u1 := d) (u2 := a) (u3 := b) (u4 := c) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := ((((a * ((b + c) + d)) + (b * ((a + c) + d))) + (c * ((a + b) + d))) + (d * ((a + b) + c)))) (l := 0) (right := 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2)
  llm_cancel_factor ((a * (b + c + d) + b * (a + c + d) + c * (a + b + d) + d * (a + b + c)) * (d * d + a * a + b * b + c * c)) - (3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2) = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (2 * a * b + 2 * a * c + 2 * a * d + 2 * b * c + 2 * b * d + 2 * c * d - (3 * a ^ 2) - (3 * b ^ 2) - (3 * c ^ 2) - (3 * d ^ 2))
  scale weighted_Power_Mean_Rgt1_right_3vars (u := d) (v := c) (w := b) (i1 := 3) (i2 := 3) (i3 := 3) (r := 2) (k := 1) (l := (3 * (a ^ 2))) (left := 2 * a * b + 2 * a * c + 2 * a * d + 2 * b * c + 2 * b * d + 2 * c * d)
  llm_simplify 2 * a * b + 2 * a * c + 2 * a * d + 2 * b * c + 2 * b * d + 2 * c * d - ((3 * d + 3 * c + 3 * b) ^ 2 / 9 + 3 * a ^ 2) = (b + c + d) ^ 2 / (3) - ((sqrt (3) * a - ((b + c + d) / (sqrt (3)))) ^ 2) - (b ^ 2 + c ^ 2 + d ^ 2)
  llm_simplify (b + c + d) ^ 2 / 3 - (b ^ 2 + c ^ 2 + d ^ 2 + (sqrt 3 * a - (b + c + d) / sqrt 3) ^ 2) = 2 * a * (b + c + d) - (b ^ 2) - (c ^ 2) - (d ^ 2) - (3 * a ^ 2)
  scale Jensen_pow_Rgt1_right_3vars (u := c) (v := b) (w := d) (r := 2) (k := 1) (l := (3 * (a ^ 2))) (left := 2 * a * (b + c + d))
  scale AM_GM_normal_right_2vars (u := (3 * ((((c + b) + d) / 3) ^ 2))) (v := (3 * (a ^ 2))) (k := 1) (l := 0) (left := 2 * a * (b + c + d))
  sym_simplify 2 * a * (b + c + d)  -  2 * sqrt(3 * ((c + b + d) / 3) ^ 2 * 3 * a ^ 2) = 0
  try close

theorem P2  {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : 2 / 3 ≤ a / (b + 2 * c + 3 * d) + b / (c + 2 * d + 3 * a) + c / (d + 2 * a + 3 * b) + d / (a + 2 * b + 3 * c) := by
  intro_by_homogeneous a + b + c + d = 4
  scale Titu_variant1_right_4vars (u1 := a) (u2 := b) (u3 := c) (u4 := d) (v1 := ((b + (2 * c)) + (3 * d))) (v2 := ((c + (2 * d)) + (3 * a))) (v3 := ((d + (2 * a)) + (3 * b))) (v4 := ((a + (2 * b)) + (3 * c))) (k := 1) (l := 0) (left := 2 / 3)
  llm_cancel_factor (2 / 3) - ((a + b + c + d) ^ 2 / (a * (b + 2 * c + 3 * d) + b * (c + 2 * d + 3 * a) + c * (d + 2 * a + 3 * b) + d * (a + 2 * b + 3 * c))) = (1 / 12) * (1 / (a * b + a * c + a * d + b * c + b * d + c * d)) * (2 * a * b + 2 * a * c + 2 * a * d + 2 * b * c + 2 * b * d + 2 * c * d - (3 * a ^ 2) - (3 * b ^ 2) - (3 * c ^ 2) - (3 * d ^ 2))
  llm_simplify 2 * a * b + 2 * a * c + 2 * a * d + 2 * b * c + 2 * b * d + 2 * c * d - (3 * d ^ 2 + 3 * c ^ 2 + 3 * b ^ 2 + 3 * a ^ 2) = 2 * (a * (b + c + d) + b * (c + d) + c * d) - (3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 + 3 * d ^ 2)
  scale weighted_Power_Mean_Rgt1_right_3vars (u := a) (v := b) (w := c) (i1 := 3) (i2 := 3) (i3 := 3) (r := 2) (k := 1) (l := (3 * (d ^ 2))) (left := 2 * (a * (b + c + d) + b * (c + d) + c * d))
  llm_factor 2 * (a * (b + c + d) + b * (c + d) + c * d) - ((3 * a + 3 * b + 3 * c) ^ 2 / 9 + 3 * d ^ 2) = 2 * d * (a + b + c) - (a ^ 2 + b ^ 2 + c ^ 2 + 3 * d ^ 2)
  scale Jensen_pow_Rgt1_right_3vars (u := a) (v := b) (w := c) (r := 2) (k := 1) (l := (3 * (d ^ 2))) (left := 2 * d * (a + b + c))
  scale AM_GM_normal_right_2vars (u := (3 * ((((a + b) + c) / 3) ^ 2))) (v := (3 * (d ^ 2))) (k := 1) (l := 0) (left := 2 * d * (a + b + c))
  sym_simplify 2 * d * (a + b + c)  -  2 * sqrt(3 * ((a + b + c) / 3) ^ 2 * 3 * d ^ 2) = 0
  try close

theorem P3 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : 3 / 2 ≤ 1 / (c ^ 3 * (a + b)) + 1 / (a ^ 3 * (b + c)) + 1 / (b ^ 3 * (c + a)) := by
  make_homogeneous 3 / 2 - ((a * b * c) ^ (4 / 3) / ((a + b) * (c ^ 3))) - ((a * b * c) ^ (4 / 3) / ((a + c) * (b ^ 3))) - ((a * b * c) ^ (4 / 3) / ((a ^ 3) * (b + c))) ≤ 0
  llm_cancel_factor 3 / 2 - ((a * b * c) ^ (4 / 3) / (a ^ 3 * (b + c)) + (a * b * c) ^ (4 / 3) / ((a + c) * b ^ 3) + (a * b * c) ^ (4 / 3) / ((a + b) * c ^ 3)) = 3 / (2) - ((a * b * c) ^ (4 / (3)) * (1 / ((a ^ 3 * (b + c))) + 1 / ((b ^ 3 * (a + c))) + 1 / ((c ^ 3 * (a + b)))))
  llm_exp_expand 3 / 2 - ((a * b * c) ^ (4 / 3) * (1 / (a ^ 3 * (b + c)) + 1 / (b ^ 3 * (a + c)) + 1 / (c ^ 3 * (a + b)))) = 3 / 2 - (a ^ (4 / 3) * b ^ (4 / 3) * c ^ (4 / 3) * (1 / ((a + b) * (c ^ 3)) + 1 / ((a + c) * (b ^ 3)) + 1 / ((a ^ 3) * (b + c))))
  llm_factor 3 / 2 - (a ^ (4 / 3) * b ^ (4 / 3) * c ^ (4 / 3) * (1 / ((a + b) * c ^ 3) + 1 / ((a + c) * b ^ 3) + 1 / (a ^ 3 * (b + c)))) = 3 / (2) - ((a ^ 3 * b ^ 3 / (a + b) + a ^ 3 * c ^ 3 / (a + c) + b ^ 3 * c ^ 3 / (b + c)) / (a ^ (5 / (3)) * b ^ (5 / (3)) * c ^ (5 / (3))))
  llm_simplify 3 / 2 - ((a ^ 3 * b ^ 3 / (a + b) + a ^ 3 * c ^ 3 / (a + c) + b ^ 3 * c ^ 3 / (b + c)) / (a ^ (5 / 3) * b ^ (5 / 3) * c ^ (5 / 3))) = 3 / (2) - (((a * b + a * c + b * c) * (a ^ 3 * b ^ 3 + a ^ 3 * c ^ 3 + b ^ 3 * c ^ 3) + a ^ 3 * b ^ 3 * c ^ 2 + a ^ 3 * c ^ 3 * b ^ 2 + b ^ 3 * c ^ 3 * a ^ 2) / ((a * b * c) ^ (5 / (3)) * (a + b) * (a + c) * (b + c)))
  llm_simplify 3 / 2 - (((a * b + a * c + b * c) * (a ^ 3 * b ^ 3 + a ^ 3 * c ^ 3 + b ^ 3 * c ^ 3) + a ^ 3 * b ^ 3 * c ^ 2 + a ^ 3 * c ^ 3 * b ^ 2 + b ^ 3 * c ^ 3 * a ^ 2) / ((a * b * c) ^ (5 / 3) * (a + b) * (a + c) * (b + c))) = 3 / (2) - ((a * b + a * c + b * c) * (a ^ 3 * b ^ 3 + a ^ 3 * c ^ 3 + b ^ 3 * c ^ 3 + a ^ 2 * b ^ 2 * c ^ 2) / ((a * b * c) ^ (5 / (3)) * (a + b) * (a + c) * (b + c)))
  scale AM_GM_normal_right_3vars (u := (a * b)) (v := (a * c)) (w := (b * c)) (k := ((((((a ^ 3) * (b ^ 3)) + ((a ^ 3) * (c ^ 3))) + ((b ^ 3) * (c ^ 3))) + (((a ^ 2) * (b ^ 2)) * (c ^ 2))) * (1 / ((((((a * b) * c) ^ (5 / 3)) * (a + b)) * (a + c)) * (b + c))))) (l := 0) (left := 3 / 2)
  llm_exp_expand 3 / 2 - (3 * (a ^ 3 * b ^ 3 + a ^ 3 * c ^ 3 + b ^ 3 * c ^ 3 + a ^ 2 * b ^ 2 * c ^ 2) * (1 / ((a * b * c) ^ (5 / 3) * (a + b) * (a + c) * (b + c))) * (a * b * a * c * b * c) ^ (1 / 3)) = 3 / 2 - (3 * (a ^ 3 * b ^ 3 + a ^ 3 * c ^ 3 + b ^ 3 * c ^ 3 + a ^ 2 * b ^ 2 * c ^ 2) / ((a + b) * (a + c) * (a) * (b + c) * (b) * (c)))
  llm_cancel_denom 3 / 2 - (3 * (a ^ 3 * b ^ 3 + a ^ 3 * c ^ 3 + b ^ 3 * c ^ 3 + a ^ 2 * b ^ 2 * c ^ 2) / ((a + b) * (a + c) * a * (b + c) * b * c)) = (3 * (a + b) * (a + c) * a * (b + c) * b * c - (6 * (a ^ 3 * b ^ 3 + a ^ 3 * c ^ 3 + b ^ 3 * c ^ 3 + a ^ 2 * b ^ 2 * c ^ 2))) / (2 * a * b * c * (a + b) * (a + c) * (b + c))
  llm_exp_expand 3 * (a + b) * (a + c) * a * (b + c) * b * c - (6 * (a ^ 3 * b ^ 3 + a ^ 3 * c ^ 3 + b ^ 3 * c ^ 3 + a ^ 2 * b ^ 2 * c ^ 2)) = 3 * a ^ 3 * b ^ 2 * c + 3 * a ^ 3 * b * c ^ 2 + 3 * a ^ 2 * b * c ^ 3 + 3 * a ^ 2 * b ^ 3 * c + 3 * a * b ^ 3 * c ^ 2 + 3 * a * b ^ 2 * c ^ 3 - (6 * a ^ 3 * b ^ 3) - (6 * a ^ 3 * c ^ 3) - (6 * b ^ 3 * c ^ 3)
  scale Muirhead_normal_Qeq1_left_2vars (u := b) (v := c) (p := 2) (k := (3 * (a ^ 3))) (l := (((((3 * (a ^ 2)) * b) * (c ^ 3)) + (((3 * (a ^ 2)) * (b ^ 3)) * c)) + ((((3 * a) * (b ^ 3)) * (c ^ 2)) + (((3 * a) * (b ^ 2)) * (c ^ 3))))) (right := 6 * b ^ 3 * c ^ 3 + 6 * a ^ 3 * c ^ 3 + 6 * a ^ 3 * b ^ 3)
  scale Muirhead_normal_Qeq1_left_2vars (u := a) (v := c) (p := 2) (k := (3 * (b ^ 3))) (l := ((((3 * a) * (b ^ 2)) * (c ^ 3)) + (((3 * (a ^ 3)) * ((b ^ 3) + (c ^ 3))) + (((3 * (a ^ 2)) * b) * (c ^ 3))))) (right := 6 * b ^ 3 * c ^ 3 + 6 * a ^ 3 * c ^ 3 + 6 * a ^ 3 * b ^ 3)
  scale Muirhead_normal_Qeq1_left_2vars (u := b) (v := a) (p := 2) (k := ((c ^ 3) * 3)) (l := (((3 * (b ^ 3)) * ((a ^ 3) + (c ^ 3))) + ((3 * (a ^ 3)) * ((b ^ 3) + (c ^ 3))))) (right := 6 * b ^ 3 * c ^ 3 + 6 * a ^ 3 * c ^ 3 + 6 * a ^ 3 * b ^ 3)
  try close

theorem P4 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : a * b / (a ^ 5 + a * b + b ^ 5) + b * c / (b ^ 5 + b * c + c ^ 5) + c * a / (c ^ 5 + c * a + a ^ 5) ≤ 1 := by
  scale Muirhead_Qeq0_div_onestep_left_2vars (u := a) (v := b) (p := 5) (i := 1) (j := (a * b)) (k := (a * b)) (l := (((b * c) / (((b ^ 5) + (b * c)) + (c ^ 5))) + ((c * a) / (((c ^ 5) + (c * a)) + (a ^ 5))))) (right := 1)
  scale Muirhead_Qeq0_div_onestep_left_2vars (u := c) (v := a) (p := 5) (i := 1) (j := (c * a)) (k := (c * a)) (l := (((a * b) * (1 / ((((a ^ 4) * b) + ((b ^ 4) * a)) + (a * b)))) + ((b * c) / (((b ^ 5) + (b * c)) + (c ^ 5))))) (right := 1)
  llm_factor c * a * (1 / (c ^ 4 * a + a ^ 4 * c + c * a)) + a * b * (1 / (a ^ 4 * b + b ^ 4 * a + a * b)) + b * c / (b ^ 5 + b * c + c ^ 5) - (1) = 1 / ((a ^ 3 + b ^ 3 + 1)) + 1 / ((a ^ 3 + c ^ 3 + 1)) + b * c / (b ^ 5 + b * c + c ^ 5) - (1)
  scale Muirhead_Qeq0_div_onestep_left_2vars (u := b) (v := c) (p := 5) (i := 1) (j := (b * c)) (k := (b * c)) (l := ((1 / (((a ^ 3) + (b ^ 3)) + 1)) + (1 / (((a ^ 3) + (c ^ 3)) + 1)))) (right := 1)
  llm_frac_reduce b * c * (1 / (b ^ 4 * c + c ^ 4 * b + b * c)) + 1 / (a ^ 3 + b ^ 3 + 1) + 1 / (a ^ 3 + c ^ 3 + 1) - (1) = 1 / ((a ^ 3 + b ^ 3 + 1)) + 1 / ((a ^ 3 + c ^ 3 + 1)) + 1 / ((b ^ 3 + c ^ 3 + 1)) - (1)
  scale Muirhead_Qeq0_div_onestep_left_2vars (u := a) (v := b) (p := 3) (i := 1) (j := 1) (k := 1) (l := ((1 / (((a ^ 3) + (c ^ 3)) + 1)) + (1 / (((b ^ 3) + (c ^ 3)) + 1)))) (right := 1)
  scale Muirhead_Qeq0_div_onestep_left_2vars (u := a) (v := c) (p := 3) (i := 1) (j := 1) (k := 1) (l := ((1 / ((((a ^ 2) * b) + ((b ^ 2) * a)) + 1)) + (1 / (((b ^ 3) + (c ^ 3)) + 1)))) (right := 1)
  scale Muirhead_Qeq0_div_onestep_left_2vars (u := b) (v := c) (p := 3) (i := 1) (j := 1) (k := 1) (l := ((1 / ((((a ^ 2) * c) + ((c ^ 2) * a)) + 1)) + (1 / ((((a ^ 2) * b) + ((b ^ 2) * a)) + 1)))) (right := 1)
  llm_simplify 1 / (b ^ 2 * c + c ^ 2 * b + 1) + 1 / (a ^ 2 * c + c ^ 2 * a + 1) + 1 / (a ^ 2 * b + b ^ 2 * a + 1) - (1) = 0

theorem P5 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
  intro_by_homogeneous a + b + c = 3
  llm_cancel_factor (1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c)) - (1 / (a * b * c)) = (1 / (a)) * (1 / (b)) * (1 / (c)) * (1 / (a ^ 3 + a * b * c + b ^ 3)) * (1 / (a ^ 3 + a * b * c + c ^ 3)) * (1 / (a * b * c + b ^ 3 + c ^ 3)) * (2 * a ^ 2 * b ^ 2 * c ^ 5 + 2 * a ^ 2 * b ^ 5 * c ^ 2 + 2 * a ^ 5 * b ^ 2 * c ^ 2 - (a ^ 3 * b ^ 6) - (a ^ 3 * c ^ 6) - (a ^ 6 * b ^ 3) - (a ^ 6 * c ^ 3) - (b ^ 3 * c ^ 6) - (b ^ 6 * c ^ 3))
  scale Muirhead_Req0_onestep_right_3vars (u := a) (v := c) (w := b) (p := 6) (q := 3) (k := 1) (l := (((b ^ 6) * (c ^ 3)) + (((a ^ 6) * (b ^ 3)) + ((a ^ 3) * (c ^ 6))))) (left := 2 * a ^ 2 * b ^ 2 * c ^ 5 + 2 * a ^ 2 * b ^ 5 * c ^ 2 + 2 * a ^ 5 * b ^ 2 * c ^ 2)
  scale Muirhead_Req0_onestep_right_3vars (u := a) (v := b) (w := c) (p := 6) (q := 3) (k := 1) (l := ((((a ^ 5) * (c ^ 4)) + ((c ^ 5) * (b ^ 4))) + ((b ^ 5) * (a ^ 4)))) (left := 2 * a ^ 2 * b ^ 2 * c ^ 5 + 2 * a ^ 2 * b ^ 5 * c ^ 2 + 2 * a ^ 5 * b ^ 2 * c ^ 2)
  scale AM_GM_square_right_2vars (u := (b ^ 2)) (v := (c ^ 2)) (k := (a ^ 5)) (l := ((((b ^ 5) * (c ^ 4)) + ((c ^ 5) * (a ^ 4))) + (((c ^ 5) * (b ^ 4)) + ((b ^ 5) * (a ^ 4))))) (left := 2 * a ^ 2 * b ^ 2 * c ^ 5 + 2 * a ^ 2 * b ^ 5 * c ^ 2 + 2 * a ^ 5 * b ^ 2 * c ^ 2)
  scale AM_GM_square_right_2vars (u := (a ^ 2)) (v := (b ^ 2)) (k := (c ^ 5)) (l := (((b ^ 5) * (a ^ 4)) + ((((2 * (a ^ 5)) * (b ^ 2)) * (c ^ 2)) + ((b ^ 5) * (c ^ 4))))) (left := 2 * a ^ 2 * b ^ 2 * c ^ 5 + 2 * a ^ 2 * b ^ 5 * c ^ 2 + 2 * a ^ 5 * b ^ 2 * c ^ 2)
  scale AM_GM_square_right_2vars (u := (a ^ 2)) (v := (c ^ 2)) (k := (b ^ 5)) (l := ((((2 * (a ^ 5)) * (b ^ 2)) * (c ^ 2)) + (((2 * (c ^ 5)) * (a ^ 2)) * (b ^ 2)))) (left := 2 * a ^ 2 * b ^ 2 * c ^ 5 + 2 * a ^ 2 * b ^ 5 * c ^ 2 + 2 * a ^ 5 * b ^ 2 * c ^ 2)

theorem P6 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : 3 / 4 ≤ a ^ 3 / ((1 + b) * (1 + c)) + b ^ 3 / ((1 + c) * (1 + a)) + c ^ 3 / ((1 + a) * (1 + b)) := by
  llm_cancel_denom 3 / 4 - (a ^ 3 / ((1 + b) * (1 + c)) + b ^ 3 / ((1 + c) * (1 + a)) + c ^ 3 / ((1 + a) * (1 + b))) = (3 * (1 + a) * (1 + b) * (1 + c) - (4 * (a ^ 3 * (1 + a) + b ^ 3 * (1 + b) + c ^ 3 * (1 + c)))) / (4 * (a + 1) * (b + 1) * (c + 1))
  llm_cancel_factor 3 * (1 + a) * (1 + b) * (1 + c) - (4 * (a ^ 3 * (1 + a) + b ^ 3 * (1 + b) + c ^ 3 * (1 + c))) = 3 * (1 + a) * (1 + b) * (1 + c) - (4 * a ^ 3) - (4 * a ^ 4) - (4 * b ^ 3) - (4 * b ^ 4) - (4 * c ^ 3) - (4 * c ^ 4)
  scale AM_GM_cubic_right_3vars (u := b) (v := a) (w := c) (k := 4) (l := ((4 * (a ^ 4)) + ((4 * (b ^ 4)) + (4 * (c ^ 4))))) (left := 3 * (1 + a) * (1 + b) * (1 + c))
  llm_exp_expand 3 * (1 + a) * (1 + b) * (1 + c) - (12 * b * a * c + 4 * a ^ 4 + 4 * b ^ 4 + 4 * c ^ 4) = 3 + 3 * a + 3 * b + 3 * c + 3 * a * b + 3 * a * c + 3 * b * c - (9 * a * b * c) - (4 * a ^ 4) - (4 * b ^ 4) - (4 * c ^ 4)
  scale Schur_x2y_left_3vars (u := c) (v := a) (w := b) (k := 3) (l := 3) (right := 4 * c ^ 4 + 4 * b ^ 4 + 4 * a ^ 4 + 9 * a * b * c)
  llm_simplify 3 * (c ^ 2 * a + a ^ 2 * b + b ^ 2 * c + 3) + 3 - (4 * c ^ 4 + 4 * b ^ 4 + 4 * a ^ 4 + 9 * a * b * c) = 3 * (c ^ 2 * a + a ^ 2 * b + b ^ 2 * c) + 3 - (4 * c ^ 4 + 4 * b ^ 4 + 4 * a ^ 4)
  llm_simplify 3 * (c ^ 2 * a + a ^ 2 * b + b ^ 2 * c) + 3 - (4 * c ^ 4 + 4 * b ^ 4 + 4 * a ^ 4) = 6 + 3 * c ^ 2 * a + 3 * a ^ 2 * b + 3 * b ^ 2 * c - (3 + 4 * a ^ 4 + 4 * b ^ 4 + 4 * c ^ 4)
  scale AM_GM_square_left_2vars (u := (c ^ 2)) (v := a) (k := 3) (l := (6 + (((3 * (a ^ 2)) * b) + ((3 * (b ^ 2)) * c)))) (right := 3 + 4 * a ^ 4 + 4 * b ^ 4 + 4 * c ^ 4)
  llm_frac_apart 3 * ((c ^ 2) ^ 2 + a ^ 2) / 2 + 6 + 3 * a ^ 2 * b + 3 * b ^ 2 * c - (3 + 4 * a ^ 4 + 4 * b ^ 4 + 4 * c ^ 4) = 3 + 3 * a ^ 2 / (2) + 3 * a ^ 2 * b + 3 * b ^ 2 * c - (4 * a ^ 4) - (4 * b ^ 4) - (5 * c ^ 4 / 2)
  scale AM_GM_square_left_2vars (u := (a ^ 2)) (v := 1) (k := (3 * (1 / 2))) (l := (3 + (((3 * (a ^ 2)) * b) + ((3 * (b ^ 2)) * c)))) (right := 5 * c ^ 4 / 2 + 4 * b ^ 4 + 4 * a ^ 4)
  llm_cancel_denom (3 / 2 * ((a ^ 2) ^ 2 + 1) / 2 + 3 + 3 * a ^ 2 * b + 3 * b ^ 2 * c) - (5 * c ^ 4 / 2 + 4 * b ^ 4 + 4 * a ^ 4) = (30 + 24 * b * a ^ 2 + 24 * c * b ^ 2 - (32 * b ^ 4) - (26 * a ^ 4) - (20 * c ^ 4)) / (8)
  scale AM_GM_square_left_2vars (u := c) (v := (b ^ 2)) (k := 24) (l := (30 + ((24 * b) * (a ^ 2)))) (right := 20 * c ^ 4 + 26 * a ^ 4 + 32 * b ^ 4)
  llm_cancel_factor 24 * (c ^ 2 + (b ^ 2) ^ 2) / 2 + 30 + 24 * b * a ^ 2 - (20 * c ^ 4 + 26 * a ^ 4 + 32 * b ^ 4) = 12 * c ^ 2 + 24 * b * a ^ 2 + 30 - (20 * c ^ 4) - (26 * a ^ 4) - (20 * b ^ 4)
  scale AM_GM_square_left_2vars (u := (c ^ 2)) (v := 1) (k := 12) (l := (((24 * b) * (a ^ 2)) + 30)) (right := 20 * b ^ 4 + 26 * a ^ 4 + 20 * c ^ 4)
  llm_simplify 12 * ((c ^ 2) ^ 2 + 1) / 2 + 24 * b * a ^ 2 + 30 - (20 * b ^ 4 + 26 * a ^ 4 + 20 * c ^ 4) = 24 * b * a ^ 2 + 36 - (14 * c ^ 4) - (20 * b ^ 4) - (26 * a ^ 4)
  scale AM_GM_square_left_2vars (u := b) (v := (a ^ 2)) (k := 24) (l := 36) (right := 26 * a ^ 4 + 20 * b ^ 4 + 14 * c ^ 4)
  llm_mul_expand 24 * (b ^ 2 + (a ^ 2) ^ 2) / 2 + 36 - (26 * a ^ 4 + 20 * b ^ 4 + 14 * c ^ 4) = 12 * b ^ 2 + 36 - (14 * a ^ 4) - (20 * b ^ 4) - (14 * c ^ 4)
  llm_cancel_factor (12 * b ^ 2 + 36) - (14 * c ^ 4 + 20 * b ^ 4 + 14 * a ^ 4) = (2) * (18 + 6 * b ^ 2 - (10 * b ^ 4) - (7 * a ^ 4) - (7 * c ^ 4))
  scale AM_GM_square_left_2vars (u := (b ^ 2)) (v := 1) (k := 6) (l := 18) (right := 7 * c ^ 4 + 7 * a ^ 4 + 10 * b ^ 4)
  llm_cancel_denom 6 * ((b ^ 2) ^ 2 + 1) / 2 + 18 - (7 * c ^ 4 + 7 * a ^ 4 + 10 * b ^ 4) = 21 - (7 * b ^ 4) - (7 * c ^ 4) - (7 * a ^ 4)
  scale AM_GM_square_right_2vars (u := (a ^ 2)) (v := (c ^ 2)) (k := 7) (l := (7 * (b ^ 4))) (left := 21)
  llm_cancel_factor 21 - (14 * a ^ 2 * c ^ 2 + 7 * b ^ 4) = 7 * (3 - (2 * a ^ 2 * c ^ 2) - (b ^ 4))
  llm_simplify 3 - (b ^ 4 + 2 * a ^ 2 * c ^ 2) = 3 - (b ^ 4) - (2 / (b ^ 2))
  scale weighted_AM_GM_normal_right_2vars (u := (1 / (b ^ 2))) (v := (b ^ 4)) (i1 := 2) (i2 := 1) (k := 1) (l := 0) (left := 3)
  sym_simplify 3  -  3 * ((1 / b ^ 2) ^ 2 * b ^ 4) ^ (1 / 3) = 0
  try close

theorem P7 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 1 := by
  llm_mul_expand (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) - (1) = 2 * a + 2 * b + 2 * c + 2 / (a) + 2 / (b) + 2 / (c) + a * b * c + 1 / ((a) * (b) * (c)) - (5) - (a * b) - (a * c) - (a / (c)) - (b * c) - (b / (a)) - (c / (b)) - (1 / ((a) * (b))) - (1 / ((a) * (c))) - (1 / ((b) * (c)))
  llm_simplify 2 * a + 2 * b + 2 * c + 2 / a + 2 / b + 2 / c + a * b * c + 1 / (a * b * c) - (1 / (b * c) + 1 / (a * c) + 1 / (a * b) + c / b + b / a + b * c + a / c + a * c + a * b + 5) = a + b + c + 2 / (a) + 2 / (b) + 2 / (c) - (3) - (a * b) - (a * c) - (a / (c)) - (b * c) - (b / (a)) - (c / (b))
  llm_simplify a + b + c + 2 / a + 2 / b + 2 / c - (c / b + b / a + b * c + a / c + a * c + a * b + 3) = a + b + c + a * b + a * c + b * c - (3) - (a / (c)) - (b / (a)) - (c / (b))
  scale Schur_x2y_left_3vars (u := a) (v := b) (w := c) (k := 1) (l := 0) (right := c / b + b / a + a / c + 3)
  llm_simplify a ^ 2 * b + b ^ 2 * c + c ^ 2 * a + 3 - (c / b + b / a + a / c + 3) = 0

theorem P8 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 1 ≤ a / sqrt (a ^ 2 + 8 * b * c) + b / sqrt (b ^ 2 + 8 * a * c) + c / sqrt (c ^ 2 + 8 * a * b) := by
  intro_by_homogeneous a + b + c = 3
  scale Holder_2R_div_variant1_right_3vars (u1 := a) (u2 := b) (u3 := c) (v1 := sqrt (((a ^ 2) + ((8 * b) * c)))) (v2 := sqrt (((b ^ 2) + ((8 * a) * c)))) (v3 := sqrt (((c ^ 2) + ((8 * a) * b)))) (k := 1) (l := 0) (left := 1)
  llm_cancel_power 2
  llm_cancel_factor (1) - ((a + b + c) ^ 3 / (a * (a ^ 2 + 8 * b * c) + b * (b ^ 2 + 8 * a * c) + c * (c ^ 2 + 8 * a * b))) = (3) * (1 / (a ^ 3 + 24 * a * b * c + b ^ 3 + c ^ 3)) * (6 * a * b * c - (a * b ^ 2) - (a * c ^ 2) - (b * a ^ 2) - (b * c ^ 2) - (c * a ^ 2) - (c * b ^ 2))
  scale AM_GM_normal_right_6vars (u1 := (c * (b ^ 2))) (u2 := (c * (a ^ 2))) (u3 := (b * (c ^ 2))) (u4 := (b * (a ^ 2))) (u5 := (a * (c ^ 2))) (u6 := (a * (b ^ 2))) (k := 1) (l := 0) (left := 6 * a * b * c)
  sym_simplify 6 * a * b * c  -  6 * (c * b ^ 2 * c * a ^ 2 * b * c ^ 2 * b * a ^ 2 * a * c ^ 2 * a * b ^ 2) ^ (1 / 6) = 0
  try close

theorem P9 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) + (b + c + 2 * a) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) + (c + a + 2 * b) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) ≤ 8 := by
  intro_by_homogeneous a + b + c = 3
  llm_simplify (a + b + 2 * c) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) + (b + c + 2 * a) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) + (c + a + 2 * b) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) - (8) = (6 - (a) - (b)) ^ 2 / (3 * (a + b) ^ 2 - (12 * (a + b)) + 18) + (3 + a) ^ 2 / (3 * a ^ 2 - (6 * a) + 9) + (3 + b) ^ 2 / (3 * b ^ 2 - (6 * b) + 9) - (8)
  llm_factor (6 - a - b) ^ 2 / (3 * (a + b) ^ 2 - 12 * (a + b) + 18) + (3 + a) ^ 2 / (3 * a ^ 2 - 6 * a + 9) + (3 + b) ^ 2 / (3 * b ^ 2 - 6 * b + 9) - (8) = (((a + b) ^ 2 + 36 - (12 * (a + b))) / ((a + b) ^ 2 - (4 * (a + b)) + 6) + (a + 3) ^ 2 / (a ^ 2 - (2 * a) + 3) + (b + 3) ^ 2 / (b ^ 2 - (2 * b) + 3)) / (3) - (8)
  llm_simplify (((a + b) ^ 2 + 36 - 12 * (a + b)) / ((a + b) ^ 2 - 4 * (a + b) + 6) + (a + 3) ^ 2 / (a ^ 2 - 2 * a + 3) + (b + 3) ^ 2 / (b ^ 2 - 2 * b + 3)) / 3 - (8) = (a + b - (6)) ^ 2 / (3 * ((a + b) ^ 2 - (4 * (a + b)) + 6)) + (a + 3) ^ 2 / (3 * (a ^ 2 - (2 * a) + 3)) + (b + 3) ^ 2 / (3 * (b ^ 2 - (2 * b) + 3)) - (8)
  llm_simplify (a + b - 6) ^ 2 / (3 * ((a + b) ^ 2 - 4 * (a + b) + 6)) + (a + 3) ^ 2 / (3 * (a ^ 2 - 2 * a + 3)) + (b + 3) ^ 2 / (3 * (b ^ 2 - 2 * b + 3)) - (8) = (a + 3) ^ 2 / (3 * (a ^ 2 - (2 * a) + 3)) + (b + 3) ^ 2 / (3 * (b ^ 2 - (2 * b) + 3)) + (c + 3) ^ 2 / (3 * (c ^ 2 - (2 * c) + 3)) - (8)
  sym_tangent_line 4 - (4 * a / 3) - (4 * b / 3) - (4 * c / 3) ≤ (8) - ((a + 3) ^ 2 / (3 * (a ^ 2 - 2 * a + 3)) + (b + 3) ^ 2 / (3 * (b ^ 2 - 2 * b + 3)) + (c + 3) ^ 2 / (3 * (c ^ 2 - 2 * c + 3)))
  try close

theorem P10 {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : 1 ≤ a / (a ^ 3 + 63 * b * c * d) ^ (1 / 3) + b / (b ^ 3 + 63 * c * d * a) ^ (1 / 3) + c / (c ^ 3 + 63 * d * a * b) ^ (1 / 3) + d / (d ^ 3 + 63 * a * b * c) ^ (1 / 3) := by
  intro_by_homogeneous a + b + c + d = 4
  scale Holder_2R_div_variant1_right_4vars (u1 := a) (u2 := b) (u3 := c) (u4 := d) (v1 := (((a ^ 3) + (((63 * b) * c) * d)) ^ (1 / 3))) (v2 := (((b ^ 3) + (((63 * c) * d) * a)) ^ (1 / 3))) (v3 := (((c ^ 3) + (((63 * d) * a) * b)) ^ (1 / 3))) (v4 := (((d ^ 3) + (((63 * a) * b) * c)) ^ (1 / 3))) (k := 1) (l := 0) (left := 1)
  llm_mul_expand 1 - (((a + b + c + d) ^ 4 / (a * ((a ^ 3 + 63 * b * c * d) ^ (1 / 3)) ^ 3 + b * ((b ^ 3 + 63 * c * d * a) ^ (1 / 3)) ^ 3 + c * ((c ^ 3 + 63 * d * a * b) ^ (1 / 3)) ^ 3 + d * ((d ^ 3 + 63 * a * b * c) ^ (1 / 3)) ^ 3)) ^ (1 / 3)) = 1 - (((a + b + c + d) ^ 4 / (a ^ 4 + 252 * a * b * c * d + b ^ 4 + c ^ 4 + d ^ 4)) ^ (1 / ((3))))
  llm_cancel_power 3
  llm_cancel_denom 1 - ((a + b + c + d) ^ 4 / (a ^ 4 + 252 * a * b * c * d + b ^ 4 + c ^ 4 + d ^ 4)) = (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 + 252 * a * b * c * d - ((a + b + c + d) ^ 4)) / (a ^ 4 + 252 * a * b * c * d + b ^ 4 + c ^ 4 + d ^ 4)
  llm_simplify a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 + 252 * a * b * c * d - ((a + b + c + d) ^ 4) = a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 + 252 * a * b * c * d - (256)
  make_homogeneous a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 + 252 * a * b * c * d - (256 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 4) ≤ 0
  closed_by_sos

theorem P11 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b + b * c + c * a = 1): (1 / a + 6 * b) ^ (1 / 3) + (1 / b + 6 * c) ^ (1 / 3) + (1 / c + 6 * a) ^ (1 / 3) ≤ 1 / (a * b * c) := by
  make_homogeneous (6 * a + (a * b + b * c + c * a) / (c)) ^ (1 / 3) + (6 * b + (a * b + b * c + c * a) / (a)) ^ (1 / 3) + (6 * c + (a * b + b * c + c * a) / (b)) ^ (1 / 3) - ((a * b + b * c + c * a) ^ (5 / 3) / ((a) * (b) * (c))) ≤ 0
  scale weighted_Power_Mean_Rlt1_left_3vars (u := ((6 * a) + ((((a * b) + (b * c)) + (c * a)) / c))) (v := ((6 * b) + ((((a * b) + (b * c)) + (c * a)) / a))) (w := ((6 * c) + ((((a * b) + (b * c)) + (c * a)) / b))) (i1 := 1) (i2 := 1) (i3 := 1) (r := (1 / 3)) (k := 1) (l := 0) (right := (a * b + b * c + c * a) ^ (5 / 3) / (a * b * c))
  llm_mul_expand (6 * a + (a * b + b * c + c * a) / c + 6 * b + (a * b + b * c + c * a) / a + 6 * c + (a * b + b * c + c * a) / b) ^ (1 / 3) * 3 ^ (2 / 3) - ((a * b + b * c + c * a) ^ (5 / 3) / (a * b * c)) = 3 ^ (2 / 3) * (8 * a + 8 * b + 8 * c + a * b / (c) + a * c / (b) + b * c / (a)) ^ (1 / 3) - ((a * b + a * c + b * c) ^ (2 / 3) / (a)) - ((a * b + a * c + b * c) ^ (2 / 3) / (b)) - ((a * b + a * c + b * c) ^ (2 / 3) / (c))
  scale AM_GM_normal_right_3vars (u := (((((a * b) + (a * c)) + (b * c)) ^ (2 / 3)) / c)) (v := (((((a * b) + (a * c)) + (b * c)) ^ (2 / 3)) / b)) (w := (((((a * b) + (a * c)) + (b * c)) ^ (2 / 3)) / a)) (k := 1) (l := 0) (left := 3 ^ (2 / 3) * (8 * a + 8 * b + 8 * c + a * b / c + a * c / b + b * c / a) ^ (1 / 3))
  llm_factor 3 ^ (2 / 3) * (8 * a + 8 * b + 8 * c + a * b / c + a * c / b + b * c / a) ^ (1 / 3) - (3 * ((a * b + a * c + b * c) ^ (2 / 3) / c * ((a * b + a * c + b * c) ^ (2 / 3) / b) * ((a * b + a * c + b * c) ^ (2 / 3) / a)) ^ (1 / 3)) = 3 ^ (2 / 3) * (8 * a + 8 * b + 8 * c + a * b / (c) + a * c / (b) + b * c / (a)) ^ (1 / 3) - (3 * (2 * a + 2 * b + 2 * c + a * b / (c) + a * c / (b) + b * c / (a)) ^ (1 / 3))
  llm_cancel_power 3
  llm_cancel_factor ((3 ^ (2 / 3) * (8 * a + 8 * b + 8 * c + a * b / c + a * c / b + b * c / a) ^ (1 / 3)) ^ 3) - ((3 * (2 * a + 2 * b + 2 * c + a * b / c + a * c / b + b * c / a) ^ (1 / 3)) ^ 3) = (18) * (1 / (a)) * (1 / (b)) * (1 / (c)) * (a * b * c ^ 2 + a * c * b ^ 2 + b * c * a ^ 2 - (a ^ 2 * b ^ 2) - (a ^ 2 * c ^ 2) - (b ^ 2 * c ^ 2))
  scale Rearrange_cycle_mul_left_3vars (u := (a * c)) (v := (b * c)) (w := (a * b)) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := 1) (l := 0) (right := b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2 + a ^ 2 * b ^ 2)

theorem P12 {a b c : ℝ} : sqrt ((a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)) ^ 2) ≤ 9 / (16 * sqrt 2) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  sorry

theorem P13 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1 / a + 1 / b + 1 / c) : 1 / (2 * a + b + c) ^ 2 + 1 / (2 * b + c + a) ^ 2 + 1 / (2 * c + a + b) ^ 2 ≤ 3 / 16 := by
  scale AM_GM_div_cycle_normal_left_2vars (u1 := (2 * a)) (u2 := (2 * b)) (u3 := (2 * c)) (v1 := (b + c)) (v2 := (c + a)) (v3 := (a + b)) (i1 := (((2 * a) + b) + c)) (i2 := (((2 * b) + c) + a)) (i3 := (((2 * c) + a) + b)) (j1 := 0) (j2 := 0) (j3 := 0) (k := 1) (l := 0) (right := 3 / 16)
  scale AM_GM_div_cycle_normal_left_2vars (u1 := (2 * a)) (u2 := (2 * b)) (u3 := (2 * c)) (v1 := (b + c)) (v2 := (c + a)) (v3 := (a + b)) (i1 := (2 * sqrt (((2 * a) * (b + c))))) (i2 := (2 * sqrt (((2 * b) * (c + a))))) (i3 := (sqrt (((2 * c) * (a + b))) * 2)) (j1 := 0) (j2 := 0) (j3 := 0) (k := 1) (l := 0) (right := 3 / 16)
  llm_cancel_denom 1 / (4 * sqrt(2 * a * (b + c)) * sqrt(2 * a * (b + c))) + 1 / (4 * sqrt(2 * b * (c + a)) * sqrt(2 * b * (c + a))) + 1 / (2 * sqrt(2 * c * (a + b)) * 2 * sqrt(2 * c * (a + b))) - (3 / 16) = (2 * b * (c + a) * c * (a + b) + 2 * a * (b + c) * c * (a + b) + 2 * a * (b + c) * b * (c + a) - (3 * a * (b + c) * b * (c + a) * c * (a + b))) / (16 * a * b * c * (a + b) * (a + c) * (b + c))
  sym_pqr_method 2 * a * b ^ 3 * (a * b ^ 2 + b * a ^ 2 - (a ^ 3) - (b ^ 3)) / (2 * a + b) ≤ 0
  llm_cancel_factor (2 * a * b ^ 3 * (a * b ^ 2 + b * a ^ 2 - a ^ 3 - b ^ 3) / (2 * a + b)) - (0) = (2) * (a) * (b ^ 3) * ((a - (b)) ^ 2) * (1 / (2 * a + b)) * (-(a) - (b))
  try close

theorem P14 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : 1 / 3 ≤ (1 / (a ^ 5 * (b + 2 * c) ^ 2)) + (1 / (b ^ 5 * (c + 2 * a) ^ 2)) + (1 / (c ^ 5 * (a + 2 * b) ^ 2)) := by
  make_homogeneous 1 / 3 - ((a * b * c) ^ (7 / 3) / (((2 * a + c) ^ 2) * (b ^ 5))) - ((a * b * c) ^ (7 / 3) / (((a + 2 * b) ^ 2) * (c ^ 5))) - ((a * b * c) ^ (7 / 3) / (((b + 2 * c) ^ 2) * (a ^ 5))) ≤ 0
  scale Holder_2R_pq_div_variant1_right_3vars (u1 := 1) (u2 := 1) (u3 := 1) (v1 := (b + (2 * c))) (v2 := (a + (2 * b))) (v3 := ((2 * a) + c)) (w1 := a) (w2 := c) (w3 := b) (p := 2) (q := 5) (k := (((a * b) * c) ^ (7 / 3))) (l := 0) (left := 1 / 3)
  llm_factor 1 / 3 - ((a * b * c) ^ (7 / 3) * (((1 / a ^ 3) ^ (1 / 3) + (1 / c ^ 3) ^ (1 / 3) + (1 / b ^ 3) ^ (1 / 3)) ^ 3 / ((b + 2 * c) * a + (a + 2 * b) * c + (2 * a + c) * b) ^ 2)) = 1 / 3 - ((a * b * c) ^ (7 / 3) * ((1 / (a ^ 3)) ^ (1 / 3) + (1 / (b ^ 3)) ^ (1 / 3) + (1 / (c ^ 3)) ^ (1 / 3)) ^ 3 / (9 * ((a * b + a * c + b * c) ^ 2)))
  llm_simplify 1 / 3 - ((a * b * c) ^ (7 / 3) * ((1 / a ^ 3) ^ (1 / 3) + (1 / b ^ 3) ^ (1 / 3) + (1 / c ^ 3) ^ (1 / 3)) ^ 3 / (9 * (a * b + a * c + b * c) ^ 2)) = (3 * a ^ 3 * b ^ 3 * c ^ 3 - ((a * b * c) ^ (7 / 3) * (a * b + a * c + b * c))) / (9 * (a ^ 3) * (b ^ 3) * (c ^ 3))
  llm_cancel_denom (3 * a ^ 3 * b ^ 3 * c ^ 3 - (a * b * c) ^ (7 / 3) * (a * b + a * c + b * c)) / (9 * a ^ 3 * b ^ 3 * c ^ 3) - (0) = 1 / ((3)) - ((a * b + a * c + b * c) / (9 * (a * b * c) ^ (2 / (3))))
  scale AM_GM_normal_right_3vars (u := (a * b)) (v := (a * c)) (w := (b * c)) (k := (1 / (9 * (((a * b) * c) ^ (2 / 3))))) (l := 0) (left := 1 / 3)
  sym_simplify 1 / 3  -  3 * (1 / (9 * (a * b * c) ^ (2 / 3))) * (a * b * a * c * b * c) ^ (1 / 3) = 0
  try close

theorem P15 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a ^ 2 + b ^ 2 + c ^ 2 + (a + b + c) ^ 2 ≤ 4) : 3 ≤ (a * b + 1) / (a + b) ^ 2 + (b * c + 1) / (b + c) ^ 2 + (c * a + 1) / (c + a) ^ 2 := by
  make_homogeneous 3 - ((a ^ 2 / 4 + b ^ 2 / 4 + c ^ 2 / 4 + (a + b + c) ^ 2 / 4 + a * b) / ((a + b) ^ 2)) - ((a ^ 2 / 4 + b ^ 2 / 4 + c ^ 2 / 4 + (a + b + c) ^ 2 / 4 + a * c) / ((a + c) ^ 2)) - ((a ^ 2 / 4 + b ^ 2 / 4 + c ^ 2 / 4 + (a + b + c) ^ 2 / 4 + b * c) / ((b + c) ^ 2)) ≤ 0
  llm_cancel_factor (3) - ((a ^ 2 / 4 + b ^ 2 / 4 + c ^ 2 / 4 + (a + b + c) ^ 2 / 4 + b * c) / (b + c) ^ 2 + (a ^ 2 / 4 + b ^ 2 / 4 + c ^ 2 / 4 + (a + b + c) ^ 2 / 4 + a * c) / (a + c) ^ 2 + (a ^ 2 / 4 + b ^ 2 / 4 + c ^ 2 / 4 + (a + b + c) ^ 2 / 4 + a * b) / (a + b) ^ 2) = (1 / 2) * (1 / ((a + b) ^ 2)) * (1 / ((a + c) ^ 2)) * (1 / ((b + c) ^ 2)) * (a ^ 2 + b ^ 2 + c ^ 2 + 3 * a * b + 3 * a * c + 3 * b * c) * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 - (a ^ 4) - (b ^ 4) - (c ^ 4))
  scale Rearrange_cycle_mul_right_3vars (u := (c ^ 2)) (v := (b ^ 2)) (w := (a ^ 2)) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := 1) (l := 0) (left := a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2)

theorem P16 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (h : a + b + c = 1) : 1 / (a ^ 2 - 4 * a + 9) + 1 / (b ^ 2 - 4 * b + 9) + 1 / (c ^ 2 - 4 * c + 9) ≤ 7 / 18 := by
  sym_tangent_line 1 / 18 - (a / 18) - (b / 18) - (c / 18) ≤ (7 / 18) - (1 / (a ^ 2 - 4 * a + 9) + 1 / (b ^ 2 - 4 * b + 9) + 1 / (c ^ 2 - 4 * c + 9))
  try close

theorem P17 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 2 / 3 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ (b ^ 3 + 3 * c ^ 3) / (5 * b + c) + (c ^ 3 + 3 * a ^ 3) / (5 * c + a) + (a ^ 3 + 3 * b ^ 3) / (5 * a + b) := by
  intro_by_homogeneous a + b + c = 3
  llm_mul_expand 2 / 3 * (a ^ 2 + b ^ 2 + c ^ 2) - ((b ^ 3 + 3 * c ^ 3) / (5 * b + c) + (c ^ 3 + 3 * a ^ 3) / (5 * c + a) + (a ^ 3 + 3 * b ^ 3) / (5 * a + b)) = 2 * a ^ 2 / 3 + 2 * b ^ 2 / 3 + 2 * c ^ 2 / 3 - (a ^ 3 / (5 * a + b)) - (b ^ 3 / (5 * b + c)) - (c ^ 3 / (a + 5 * c)) - (3 * b ^ 3 / (5 * a + b)) - (3 * c ^ 3 / (5 * b + c)) - (3 * a ^ 3 / (a + 5 * c))
  scale Titu_variant2_right_3vars (u1 := a) (u2 := c) (u3 := b) (v1 := (a + (5 * c))) (v2 := ((5 * b) + c)) (v3 := ((5 * a) + b)) (r := 3) (k := 3) (l := (((c ^ 3) / (a + (5 * c))) + (((b ^ 3) / ((5 * b) + c)) + ((a ^ 3) / ((5 * a) + b))))) (left := 2 * a ^ 2 / 3 + 2 * b ^ 2 / 3 + 2 * c ^ 2 / 3)
  scale Titu_variant2_right_3vars (u1 := b) (u2 := a) (u3 := c) (v1 := ((5 * b) + c)) (v2 := ((5 * a) + b)) (v3 := (a + (5 * c))) (r := 3) (k := 1) (l := (3 * (((((a ^ 2) + (c ^ 2)) + (b ^ 2)) ^ 2) / (((a * (a + (5 * c))) + (c * ((5 * b) + c))) + (b * ((5 * a) + b)))))) (left := 2 * a ^ 2 / 3 + 2 * b ^ 2 / 3 + 2 * c ^ 2 / 3)
  llm_cancel_factor (2 * a ^ 2 / 3 + 2 * b ^ 2 / 3 + 2 * c ^ 2 / 3) - ((b ^ 2 + a ^ 2 + c ^ 2) ^ 2 / (b * (5 * b + c) + a * (5 * a + b) + c * (a + 5 * c)) + 3 * ((a ^ 2 + c ^ 2 + b ^ 2) ^ 2 / (a * (a + 5 * c) + c * (5 * b + c) + b * (5 * a + b)))) = (2 / 3) * (1 / (a ^ 2 + 5 * a * b + 5 * a * c + b ^ 2 + 5 * b * c + c ^ 2)) * (1 / (5 * a ^ 2 + a * b + a * c + 5 * b ^ 2 + b * c + 5 * c ^ 2)) * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + a * c + b * c - (a ^ 2) - (b ^ 2) - (c ^ 2)) * (19 * a ^ 2 + 19 * b ^ 2 + 19 * c ^ 2 + 5 * a * b + 5 * a * c + 5 * b * c)
  scale Rearrange_cycle_mul_right_3vars (u := c) (v := b) (w := a) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := 1) (l := 0) (left := a * b + a * c + b * c)

theorem P18 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (h : a + b + c = 1) : 1 / 2 ≤ a / (9 * b * c + 4 * (b - c) ^ 2 + 1) + b / (9 * c * a + 4 * (c - a) ^ 2 + 1) + c / (9 * a * b + 4 * (a - b) ^ 2 + 1) := by
  make_homogeneous 1 / 2 - (a * (a + b + c) / (9 * b * c + 4 * (b - (c)) ^ 2 + (a + b + c) ^ 2)) - (b * (a + b + c) / (9 * a * c + 4 * (c - (a)) ^ 2 + (a + b + c) ^ 2)) - (c * (a + b + c) / (9 * a * b + 4 * (a - (b)) ^ 2 + (a + b + c) ^ 2)) ≤ 0
  scale Titu_variant1_right_3vars (u1 := c) (u2 := b) (u3 := a) (v1 := ((((9 * a) * b) + (4 * ((a - b) ^ 2))) + (((a + b) + c) ^ 2))) (v2 := ((((9 * a) * c) + (4 * ((c - a) ^ 2))) + (((a + b) + c) ^ 2))) (v3 := ((((9 * b) * c) + (4 * ((b - c) ^ 2))) + (((a + b) + c) ^ 2))) (k := ((a + b) + c)) (l := 0) (left := 1 / 2)
  llm_cancel_factor (1 / 2) - ((a + b + c) * ((c + b + a) ^ 2 / (c * (9 * a * b + 4 * (a - b) ^ 2 + (a + b + c) ^ 2) + b * (9 * a * c + 4 * (c - a) ^ 2 + (a + b + c) ^ 2) + a * (9 * b * c + 4 * (b - c) ^ 2 + (a + b + c) ^ 2)))) = (1 / 2) * (1 / (a ^ 3 + 7 * a ^ 2 * b + 7 * a ^ 2 * c + 7 * a * b ^ 2 + 9 * a * b * c + 7 * a * c ^ 2 + b ^ 3 + 7 * b ^ 2 * c + 7 * b * c ^ 2 + c ^ 3)) * (a * b ^ 2 + a * c ^ 2 + b * a ^ 2 + b * c ^ 2 + c * a ^ 2 + c * b ^ 2 - (a ^ 3) - (b ^ 3) - (c ^ 3) - (3 * a * b * c))
  scale Schur_Teq1_left_3vars (u := a) (v := c) (w := b) (k := 1) (l := 0) (right := 3 * a * b * c + c ^ 3 + b ^ 3 + a ^ 3)

theorem P19 {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h : a + b + c + d = 4) : 2 / 3 ≤ a / (b ^ 3 + 4) + b / (c ^ 3 + 4) + c / (d ^ 3 + 4) + d / (a ^ 3 + 4) := by
  llm_cancel_denom (2 / 3) - (a / (b ^ 3 + 4) + b / (c ^ 3 + 4) + c / (d ^ 3 + 4) + d / (a ^ 3 + 4)) = (2 * (4 + a ^ 3) * (4 + b ^ 3) * (4 + c ^ 3) * (4 + d ^ 3) - (3 * a * (4 + a ^ 3) * (4 + c ^ 3) * (4 + d ^ 3)) - (3 * b * (4 + a ^ 3) * (4 + b ^ 3) * (4 + d ^ 3)) - (3 * c * (4 + a ^ 3) * (4 + b ^ 3) * (4 + c ^ 3)) - (3 * d * (4 + b ^ 3) * (4 + c ^ 3) * (4 + d ^ 3))) / (3 * (4 + a ^ 3) * (4 + b ^ 3) * (4 + c ^ 3) * (4 + d ^ 3))
  make_homogeneous 2 * (a ^ 3 + 4 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 3) * (b ^ 3 + 4 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 3) * (c ^ 3 + 4 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 3) * (d ^ 3 + 4 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 3) - (3 * a * (a / 4 + b / 4 + c / 4 + d / 4) ^ 2 * (a ^ 3 + 4 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 3) * (c ^ 3 + 4 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 3) * (d ^ 3 + 4 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 3)) - (3 * b * (a / 4 + b / 4 + c / 4 + d / 4) ^ 2 * (a ^ 3 + 4 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 3) * (b ^ 3 + 4 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 3) * (d ^ 3 + 4 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 3)) - (3 * c * (a / 4 + b / 4 + c / 4 + d / 4) ^ 2 * (a ^ 3 + 4 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 3) * (b ^ 3 + 4 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 3) * (c ^ 3 + 4 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 3)) - (3 * d * (a / 4 + b / 4 + c / 4 + d / 4) ^ 2 * (b ^ 3 + 4 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 3) * (c ^ 3 + 4 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 3) * (d ^ 3 + 4 * (a / 4 + b / 4 + c / 4 + d / 4) ^ 3)) ≤ 0
  closed_by_sos

theorem P20 {a b c d : ℝ} (ha : a - b ≥ 0) (hb : b - c ≥ 0) (hc : c - d ≥ 0) (hd : d > 0) (h : a + b + c + d = 1) : (a + 2 * b + 3 * c + 4 * d) * a ^ a * b ^ b * c ^ c * d ^ d ≤ 1 := by
  sorry
