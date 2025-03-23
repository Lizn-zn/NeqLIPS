import Mathlib
import Math

open Real

set_option maxHeartbeats 0

set_option linter.unusedVariables false
set_option by_axiom true
#eval use_axiom

macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

theorem P1 {a b c : ℝ} : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  scale Rearrange_cycle_mul_right_3vars (u := a) (v := b) (w := c) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := 1) (l := 0) (left := a * b + b * c + c * a)

theorem P2 {a b c : ℝ} : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ a ^ 4 + b ^ 4 + c ^ 4 := by
  scale Rearrange_cycle_mul_left_3vars (u := (c * a)) (v := (a * b)) (w := (b * c)) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := 1) (l := 0) (right := a ^ 4 + b ^ 4 + c ^ 4)
  scale Rearrange_cycle_mul_left_3vars (u := (c * c)) (v := (a * a)) (w := (b * b)) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := 1) (l := 0) (right := a ^ 4 + b ^ 4 + c ^ 4)

theorem P3 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a ^ 2 * b + b ^ 2 * c + c ^ 2 * a ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
  scale AM_GM_cubic_left_3vars (u := a) (v := a) (w := b) (k := 1) (l := (((b ^ 2) * c) + ((c ^ 2) * a))) (right := a ^ 3 + b ^ 3 + c ^ 3)
  llm_cancel_factor (a ^ 3 + a ^ 3 + b ^ 3) / 3 + b ^ 2 * c + c ^ 2 * a - (a ^ 3 + b ^ 3 + c ^ 3) = b ^ 2 * c + a * c ^ 2 - (c ^ 3) - (a ^ 3 / 3) - (2 * b ^ 3 / 3)
  llm_simplify b ^ 2 * c + a * c ^ 2 - (2 * b ^ 3 / 3 + a ^ 3 / 3 + c ^ 3) = c * a * c + b * b * c - (c ^ 3) - (a ^ 3 / 3) - (2 * b ^ 3 / 3)
  llm_cancel_denom c * a * c + b * b * c - (2 * b ^ 3 / 3 + a ^ 3 / 3 + c ^ 3) = (-3 * c ^ 3 - a ^ 3 - 2 * b ^ 3 + 3 * a * c ^ 2 + 3 * b ^ 2 * c) / 3
  scale AM_GM_cubic_left_3vars (u := c) (v := c) (w := a) (k := 3) (l := (((3 * (b ^ 2)) * c) + (((-(3) * (c ^ 3)) - (a ^ 3)) - (2 * (b ^ 3))))) (right := 0)
  scale AM_GM_cubic_left_3vars (u := b) (v := b) (w := c) (k := 3) (l := ((((-(3) * (c ^ 3)) - (a ^ 3)) - (2 * (b ^ 3))) + ((3 * (((c ^ 3) + (c ^ 3)) + (a ^ 3))) / 3))) (right := 0)

theorem P4 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a ^ 3 * b * c + b ^ 3 * c * a + c ^ 3 * a * b ≤ a ^ 5 + b ^ 5 + c ^ 5 := by
  scale Muirhead_QReq1_left_3vars (u := a) (v := b) (w := c) (p := 3) (k := 1) (l := 0) (right := a ^ 5 + b ^ 5 + c ^ 5)
  scale Muirhead_Qeq1Req0_left_3vars (u := a) (v := b) (w := c) (p := 4) (k := 1) (l := 0) (right := a ^ 5 + b ^ 5 + c ^ 5)

theorem P5 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a * b * c) * (a * b + b * c + c * a) ≤ a ^ 3 * b * c + b ^ 3 * c * a + c ^ 3 * a * b := by
  llm_cancel_factor (a * b * c * (a * b + b * c + c * a)) - (a ^ 3 * b * c + b ^ 3 * c * a + c ^ 3 * a * b) = (a)*(b)*(c)*(b * c + a * c + a * b - (a ^ 2) - (b ^ 2) - (c ^ 2))
  scale Rearrange_cycle_mul_right_3vars (u := c) (v := b) (w := a) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := 1) (l := 0) (left := b * c + a * c + a * b)

theorem P6 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a ^ 2 * b ^ 2 * c) + (b ^ 2 * c ^ 2 * a) + (c ^ 2 * a ^ 2 * b) ≤ a ^ 5 + b ^ 5 + c ^ 5 := by
  scale Muirhead_Req1_left_3vars (u := a) (v := b) (w := c) (p := 2) (q := 2) (k := 1) (l := 0) (right := a ^ 5 + b ^ 5 + c ^ 5)
  scale Muirhead_Req0_left_3vars (u := a) (v := b) (w := c) (p := 3) (q := 2) (k := 1) (l := 0) (right := a ^ 5 + b ^ 5 + c ^ 5)

theorem P7 {a b c : ℝ} (h : a * b * c = 1) : a + b + c ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  llm_simplify a + b + c - (a ^ 2 + b ^ 2 + c ^ 2) = 1 / (a * b) + b + a - (b ^ 2) - (a ^ 2) - (1 / (a * b) ^ 2)
  llm_cancel_denom 1 / (a * b) + b + a - (1 / (a * b) ^ 2 + a ^ 2 + b ^ 2) = (a * b - 1 * 1) / ((a * b) ^ 2) + b + a - (b ^ 2) - (a ^ 2)
  llm_factor (a * b - 1) / (a * b) ^ 2 + b + a - (a ^ 2 + b ^ 2) = (a * b - 1 * 1) / ((a * b) ^ 2) - (a * (a - 1 * 1)) - (b * (b - 1 * 1))
  llm_cancel_factor (a * b - 1) / (a * b) ^ 2 - (b * (b - 1) + a * (a - 1)) = (a * b - 1 * 1) / ((a * b) ^ 2) + (a + b - a ^ 2 - b ^ 2)
  llm_simplify (a * b - 1) / (a * b) ^ 2 + (a + b - a ^ 2 - b ^ 2) - (0) = b + a + c * (1 - c) - (b ^ 2) - (a ^ 2)
  scale AM_GM_square_left_2vars (u := b) (v := 1) (k := 1) (l := (a + (c * (1 - c)))) (right := a ^ 2 + b ^ 2)
  llm_cancel_denom (b ^ 2 + 1) / 2 + a + c * (1 - c) - (a ^ 2 + b ^ 2) = (-2 * c ^ 2 + 2 * c + 2 * a - 2 * a ^ 2 + 1 - b ^ 2) / 2
  llm_cancel_denom -2 * c ^ 2 + 2 * c + 2 * a - 2 * a ^ 2 + 1 - (b ^ 2) = (1 - b) * (1 + b) + 2 * a * (1 - a) + 2 * c - (2 * c ^ 2)
  scale AM_GM_square_left_2vars (u := 1) (v := c) (k := 2) (l := (((1 - b) * (1 + b)) + ((2 * a) * (1 - a)))) (right := 2 * c ^ 2)
  llm_cancel_factor 2 * (1 + c ^ 2) / 2 + (1 - b) * (1 + b) + 2 * a * (1 - a) - (2 * c ^ 2) = 2 * a + 2 - (c ^ 2) - (b ^ 2) - (2 * a ^ 2)
  scale AM_GM_square_left_2vars (u := a) (v := 1) (k := 2) (l := 2) (right := 2 * a ^ 2 + b ^ 2 + c ^ 2)
  llm_simplify 2 * (a ^ 2 + 1) / 2 + 2 - (2 * a ^ 2 + b ^ 2 + c ^ 2) = 3 - (a ^ 2 + b ^ 2 + c ^ 2)
  scale AM_GM_normal_right_3vars (u := (a ^ 2)) (v := (b ^ 2)) (w := (c ^ 2)) (k := 1) (l := 0) (left := 3)
  llm_simplify 3 - (3 * (a ^ 2 * b ^ 2 * c ^ 2) ^ (1 / 3)) = 0

theorem P8 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0): a ^ 4 * b ^ 3 + b ^ 4 * c ^ 3 + c ^ 4 * a ^ 3 ≤ a ^ 7 + b ^ 7 + c ^ 7 := by
  scale Muirhead_Req0_left_3vars (u := a) (v := b) (w := c) (p := 4) (q := 3) (k := 1) (l := 0) (right := a ^ 7 + b ^ 7 + c ^ 7)

theorem P9 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : (1 / a) + (1 / b) + (1 / c) ≤ 3 + 2 * (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) := by
  make_homogeneous (a + b + c) / c + (a + b + c) / b + (a + b + c) / a - (3) - (2 * (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c)) ≤ 0
  llm_cancel_factor (a + b + c) / c + (a + b + c) / b + (a + b + c) / a - (2 * (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) + 3) = (-2 * (c ^ 3 + a ^ 3 + b ^ 3) + b * c ^ 2 + a * c ^ 2 + b ^ 2 * c + a * b ^ 2 + a ^ 2 * b + a ^ 2 * c) / ((a * b * c))
  llm_frac_apart -2 * (c ^ 3 + a ^ 3 + b ^ 3) + b * c ^ 2 + a * c ^ 2 + b ^ 2 * c + a * b ^ 2 + a ^ 2 * b + a ^ 2 * c - (0) = a ^ 2 * b + a * b ^ 2 + a ^ 2 * c + b ^ 2 * c + a * c ^ 2 + b * c ^ 2 - (2 * c ^ 3) - (2 * a ^ 3) - (2 * b ^ 3)
  scale Schur_Teq1_left_3vars (u := a) (v := b) (w := c) (k := 1) (l := 0) (right := 2 * b ^ 3 + 2 * a ^ 3 + 2 * c ^ 3)
  scale AM_GM_cubic_left_3vars (u := a) (v := b) (w := c) (k := 3) (l := (((a ^ 3) + (b ^ 3)) + (c ^ 3))) (right := 2 * b ^ 3 + 2 * a ^ 3 + 2 * c ^ 3)

theorem P10 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0): a + b + c ≤ (a ^ 3) / (b * c) + (b ^ 3) / (c * a) + (c ^ 3) / (a * b) := by
  llm_cancel_denom a + b + c - (a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b)) = ((-a ^ 4 - b ^ 4 - c ^ 4) + b * a * c ^ 2 + a * b ^ 2 * c + c * a ^ 2 * b) / ((c * a * b))
  scale Rearrange_cycle_mul_left_3vars (u := (a * c)) (v := (b * c)) (w := (b * a)) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := 1) (l := ((-((a ^ 4)) - (b ^ 4)) - (c ^ 4))) (right := 0)
  scale Rearrange_cycle_mul_left_3vars (u := (a ^ 2)) (v := (c ^ 2)) (w := (b ^ 2)) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := 1) (l := ((-((a ^ 4)) - (b ^ 4)) - (c ^ 4))) (right := 0)

theorem P11 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hp : a * b + a * c + b * c = a * b * c) (hq : 27 ≤ a * b * c) : 64 ≤ (a + 1) * (b + 1) * (c + 1) := by
  llm_simplify 64 - ((a + 1) * (b + 1) * (c + 1)) = 63 - (2 * a * b * c) - (a) - (b) - (c)
  scale AM_HM_normal_right_3vars (u := c) (v := b) (w := a) (k := 1) (l := (((2 * a) * b) * c)) (left := 63)
  llm_simplify 63 - (9 / (1 / c + 1 / b + 1 / a) + 2 * a * b * c) = 54 - (c * 2 * a * b)

theorem P12 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a ≤ 2) : 6 ≤ 2 * (a * b + 1) / (a + b) ^ 2 + 2 * (b * c + 1) / (b + c) ^ 2 + 2 * (c * a + 1) / (c + a) ^ 2 := by
  make_homogeneous 6 - (2 * 1 * (a ^ 2 / 2 + b ^ 2 / 2 + c ^ 2 / 2 + a * c / 2 + b * c / 2 + 3 * a * b / 2) / (a + b) ^ 2) - (2 * 1 * (a ^ 2 / 2 + b ^ 2 / 2 + c ^ 2 / 2 + a * b / 2 + b * c / 2 + 3 * a * c / 2) / (a + c) ^ 2) - (2 * 1 * (a ^ 2 / 2 + b ^ 2 / 2 + c ^ 2 / 2 + a * b / 2 + a * c / 2 + 3 * b * c / 2) / (b + c) ^ 2) ≤ 0
  llm_frac_together 6 - (2 * (a ^ 2 / 2 + b ^ 2 / 2 + c ^ 2 / 2 + a * b / 2 + a * c / 2 + 3 * b * c / 2) / (b + c) ^ 2 + 2 * (a ^ 2 / 2 + b ^ 2 / 2 + c ^ 2 / 2 + a * b / 2 + b * c / 2 + 3 * a * c / 2) / (a + c) ^ 2 + 2 * (a ^ 2 / 2 + b ^ 2 / 2 + c ^ 2 / 2 + a * c / 2 + b * c / 2 + 3 * a * b / 2) / (a + b) ^ 2) = 6 - (1 * (a ^ 2 + b ^ 2 + c ^ 2 + a * c + b * c + 3 * a * b) / (a + b) ^ 2 + 1 * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + 3 * a * c) / (a + c) ^ 2 + 1 * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + a * c + 3 * b * c) / (b + c) ^ 2)
  llm_cancel_factor (6) - ((a ^ 2 + b ^ 2 + c ^ 2 + a * c + b * c + 3 * a * b) / (a + b) ^ 2 + (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + 3 * a * c) / (a + c) ^ 2 + (a ^ 2 + b ^ 2 + c ^ 2 + a * b + a * c + 3 * b * c) / (b + c) ^ 2) = (1 / (a + b) ^ 2) * (1 / (a + c) ^ 2) * (1 / (b + c) ^ 2) * (a ^ 2 + b ^ 2 + c ^ 2 + 3 * a * b + 3 * a * c + 3 * b * c) * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 - (a ^ 4) - (b ^ 4) - (c ^ 4))
  scale Rearrange_cycle_mul_right_3vars (u := (c ^ 2)) (v := (b ^ 2)) (w := (a ^ 2)) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := 1) (l := 0) (left := a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2)

theorem P13 {a b c d : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (h : a * b * c * d = 1) : a + b + c + d ≤ a ^ 4 * b + b ^ 4 * c + c ^ 4 * d + d ^ 4 * a := by
  make_homogeneous a * b * c * d ^ 2 + a * b * d * c ^ 2 + a * c * d * b ^ 2 + b * c * d * a ^ 2 - (a * d ^ 4) - (b * a ^ 4) - (c * b ^ 4) - (d * c ^ 4) ≤ 0
  scale Muirhead_QRSeq1_left_4vars (u1 := b) (u2 := c) (u3 := d) (u4 := a) (p := 2) (k := 1) (l := 0) (right := d * c ^ 4 + c * b ^ 4 + b * a ^ 4 + a * d ^ 4)
  scale Muirhead_QReq1Seq0_left_4vars (u1 := b) (u2 := c) (u3 := d) (u4 := a) (p := 3) (k := 1) (l := 0) (right := d * c ^ 4 + c * b ^ 4 + b * a ^ 4 + a * d ^ 4)
  scale AM_GM_square_left_2vars (u := (b ^ 2)) (v := (b ^ 2)) (k := c) (l := ((((c ^ 4) * d) + ((d ^ 4) * a)) + ((a ^ 4) * b))) (right := d * c ^ 4 + c * b ^ 4 + b * a ^ 4 + a * d ^ 4)

theorem P14 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1 / a + 1 / b + 1 / c) : 1 / (2 * a + b + c) ^ 2 + 1 / (a + 2 * b + c) ^ 2 + 1 / (a + b + 2 * c) ^ 2 ≤ 3 / 16 := by
  scale Jensen_square_div_left_3vars (u := (((2 * a) + b) + c)) (v := ((a + (2 * b)) + c)) (w := ((a + b) + (2 * c))) (k := 1) (l := 0) (right := 3 / 16)
  llm_cancel_factor 27 / (2 * a + b + c + a + 2 * b + c + a + b + 2 * c) ^ 2 - (3 / 16) = 1 * (27 - (3 * (a + b + c) ^ 2)) / (16 * (a + b + c) ^ 2)
  scale AM_HM_normal_right_3vars (u := a) (v := b) (w := c) (k := (((a + b) + c) * 3)) (l := 0) (left := 27)
  llm_simplify 27 - ((a + b + c) * 3 * (9 / (1 / a + 1 / b + 1 / c))) = 0

theorem P15 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) ≤ (1 / a + 1 / b + 1 / c) := by
  llm_cancel_factor 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) - (1 / a + 1 / b + 1 / c) = 2 * 1 / (a + b) + 2 * 1 / (a + c) + 2 * 1 / (b + c) - (1 / a) - (1 / b) - (1 / c)
  scale AM_GM_div_left_2vars (u := a) (v := b) (i := 1) (j := 0) (k := 2) (l := ((2 / (a + c)) + (2 / (b + c)))) (right := 1 / c + 1 / b + 1 / a)
  scale AM_HM_div_left_2vars (u := a) (v := c) (k := 2) (l := ((2 * (1 / (2 * sqrt ((a * b))))) + (2 / (b + c)))) (right := 1 / c + 1 / b + 1 / a)
  scale AM_HM_div_left_2vars (u := c) (v := b) (k := 2) (l := (((2 * ((1 / a) + (1 / c))) / 4) + (2 * (1 / (2 * sqrt ((a * b))))))) (right := 1 / c + 1 / b + 1 / a)
  llm_simplify 2 * (1 / c + 1 / b) / 4 + 2 * (1 / a + 1 / c) / 4 + 2 * (1 / (2 * sqrt(a * b))) - (1 / c + 1 / b + 1 / a) = 1 / sqrt (a * b) - (1 / (2 * a)) - (1 / (2 * b))
  llm_cancel_factor 1 / sqrt(a * b) - (1 / (2 * b) + 1 / (2 * a)) = 1 ^ 2 * (2 * sqrt (a * b) - (a + b)) / (2 * a * b)
  scale AM_GM_normal_left_2vars (u := a) (v := b) (k := 2) (l := 0) (right := a + b)

theorem P16 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 9 / (a + b + c) ≤ 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) := by
  llm_frac_reduce 9 / (a + b + c) - (2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))) = 9 * 1 / (a + b + c) - (2 * 1 / (a + b)) - (2 * 1 / (a + c)) - (2 * 1 / (b + c))
  scale Titu_variant1_right_3vars (u1 := 2) (u2 := 2) (u3 := 2) (v1 := (b + c)) (v2 := (a + c)) (v3 := (a + b)) (k := 1) (l := 0) (left := 9 / (a + b + c))
  llm_simplify 9 / (a + b + c) - (36 / (2 * (b + c) + 2 * (a + c) + 2 * (a + b))) = 0

theorem P17 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h1 : a + b > c) (h2 : a + c > b) (hc : b + c > a): sqrt (a + b - c) + sqrt (b + c - a) + sqrt (c + a - b) ≤ sqrt (a) + sqrt (b) + sqrt (c) := by
  scale Karamata_sqrt_cycle_left_3vars (u := b) (v := a) (w := c) (k := 1) (l := 0) (right := sqrt a + sqrt b + sqrt c)

theorem P18 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 3) : 6 ≤ 18 / ((3 - c) * (4 - c)) + 18 / ((3 - b) * (4 - b)) + 18 / ((3 - a) * (4 - a)) + 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  sym_tangent_line 13 * a / 2 + 13 * b / 2 + 13 * c / 2 - (21 / 2) ≤ (18 / ((3 - c) * (4 - c)) + 18 / ((3 - b) * (4 - b)) + 18 / ((3 - a) * (4 - a)) + 2 * (a ^ 2 + b ^ 2 + c ^ 2)) - (6)
  llm_frac_together 0 - (13 * a / 2 + 13 * b / 2 + 13 * c / 2 - 21 / 2) = 21 / 2 - (13 * a) / 2 - (13 * b) / 2 - (13 * c) / 2

theorem P19 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 3) : 3 / 5 ≤ (3 - 2 * a) ^ 2 / (a ^ 2 + (3 - a) ^ 2) + (3 - 2 * b) ^ 2 / (b ^ 2 + (3 - b) ^ 2) + (3 - 2 * c) ^ 2 / (c ^ 2 + (3 - c) ^ 2) := by
  sym_tangent_line 54 / 25 - (18 * a / 25) - (18 * b / 25) - (18 * c / 25) ≤ ((3 - 2 * a) ^ 2 / (a ^ 2 + (3 - a) ^ 2) + (3 - 2 * b) ^ 2 / (b ^ 2 + (3 - b) ^ 2) + (3 - 2 * c) ^ 2 / (c ^ 2 + (3 - c) ^ 2)) - (3 / 5)
  llm_simplify 0 - (54 / 25 - 18 * a / 25 - 18 * b / 25 - 18 * c / 25) = -(54) / 25 + 18 * a / 25 + 18 * b / 25 + 18 * c / 25

theorem P20 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : 2 * (a + b + c) ≤ (a * b + b * c + c * a)) : 3 / 5 ≤ (a - 1) ^ 2 / (a ^ 2 + 1) + (b - 1) ^ 2 / (b ^ 2 + 1) + (c - 1) ^ 2 / (c ^ 2 + 1) := by
  make_homogeneous 3 / 5 - ((a - ((a * b + a * c + b * c) / (2 * (a + b + c)))) ^ 2 / (a ^ 2 + (a * b + a * c + b * c) ^ 2 / (4 * ((a + b + c) ^ 2)))) - ((b - ((a * b + a * c + b * c) / (2 * (a + b + c)))) ^ 2 / (b ^ 2 + (a * b + a * c + b * c) ^ 2 / (4 * ((a + b + c) ^ 2)))) - ((c - ((a * b + a * c + b * c) / (2 * (a + b + c)))) ^ 2 / (c ^ 2 + (a * b + a * c + b * c) ^ 2 / (4 * ((a + b + c) ^ 2)))) ≤ 0
  scale Titu_normal_right_3vars (u1 := (c - ((((a * b) + (a * c)) + (b * c)) / (2 * ((a + b) + c))))) (u2 := (b - ((((a * b) + (a * c)) + (b * c)) / (2 * ((a + b) + c))))) (u3 := (a - ((((a * b) + (a * c)) + (b * c)) / (2 * ((a + b) + c))))) (v1 := ((c ^ 2) + (((((a * b) + (a * c)) + (b * c)) ^ 2) / (4 * (((a + b) + c) ^ 2))))) (v2 := ((b ^ 2) + (((((a * b) + (a * c)) + (b * c)) ^ 2) / (4 * (((a + b) + c) ^ 2))))) (v3 := ((a ^ 2) + (((((a * b) + (a * c)) + (b * c)) ^ 2) / (4 * (((a + b) + c) ^ 2))))) (k := 1) (l := 0) (left := 3 / 5)
  llm_simplify 3 / 5 - ((c - (a * b + a * c + b * c) / (2 * (a + b + c)) + (b - (a * b + a * c + b * c) / (2 * (a + b + c))) + (a - (a * b + a * c + b * c) / (2 * (a + b + c)))) ^ 2 / (c ^ 2 + (a * b + a * c + b * c) ^ 2 / (4 * (a + b + c) ^ 2) + b ^ 2 + (a * b + a * c + b * c) ^ 2 / (4 * (a + b + c) ^ 2) + a ^ 2 + (a * b + a * c + b * c) ^ 2 / (4 * (a + b + c) ^ 2))) = 4 * (a * b + a * c + b * c - (a ^ 2) - (b ^ 2) - (c ^ 2)) / (5 * (2 * a ^ 2 + 3 * a * b + 3 * a * c + 2 * b ^ 2 + 3 * b * c + 2 * c ^ 2))
  llm_frac_reduce 4 * (a * b + a * c + b * c - a ^ 2 - b ^ 2 - c ^ 2) / (5 * (2 * a ^ 2 + 3 * a * b + 3 * a * c + 2 * b ^ 2 + 3 * b * c + 2 * c ^ 2)) - (0) = -2 * ((a - (b)) ^ 2 + (b - (c)) ^ 2 + (c - (a)) ^ 2) / (10 * a ^ 2 + 15 * a * b + 15 * a * c + 10 * b ^ 2 + 15 * b * c + 10 * c ^ 2)
  llm_cancel_factor -2 * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / (10 * a ^ 2 + 15 * a * b + 15 * a * c + 10 * b ^ 2 + 15 * b * c + 10 * c ^ 2) - (0) = -2 * ((a - (b)) ^ 2 + (b - (c)) ^ 2 + (c - (a)) ^ 2) / (10 * a ^ 2 + 15 * a * b + 15 * a * c + 10 * b ^ 2 + 15 * b * c + 10 * c ^ 2)

theorem P21 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 1 ≤ a / sqrt (a ^ 2 + 8 * b * c) + b / sqrt (b ^ 2 + 8 * a * c) + c / sqrt (c ^ 2 + 8 * a * b) := by
  intro_by_homogeneous a + b + c = 3
  scale weighted_Jensen_sqrt_div_right_3vars (u := ((a ^ 2) + ((8 * b) * c))) (v := ((b ^ 2) + ((8 * a) * c))) (w := ((c ^ 2) + ((8 * a) * b))) (i1 := a) (i2 := b) (i3 := c) (k := 1) (l := 0) (left := 1)
  llm_mul_expand 1 - (sqrt(a + b + c) ^ 3 / sqrt(a * (a ^ 2 + 8 * b * c) + b * (b ^ 2 + 8 * a * c) + c * (c ^ 2 + 8 * a * b))) = 1 - ((a + b + c) ^ (3 / (2)) / (sqrt (a ^ 3 + 24 * a * b * c + b ^ 3 + c ^ 3)))
  llm_cancel_power 2
  llm_cancel_factor (1) - (((a + b + c) ^ (3 / 2) / sqrt(a ^ 3 + 24 * a * b * c + b ^ 3 + c ^ 3)) ^ 2) = (3) * (1 / (a ^ 3 + 24 * a * b * c + b ^ 3 + c ^ 3)) * (6 * a * b * c - (a * b ^ 2) - (a * c ^ 2) - (b * a ^ 2) - (b * c ^ 2) - (c * a ^ 2) - (c * b ^ 2))
  scale AM_GM_normal_right_6vars (u1 := (c * (b ^ 2))) (u2 := (c * (a ^ 2))) (u3 := (b * (c ^ 2))) (u4 := (b * (a ^ 2))) (u5 := (a * (c ^ 2))) (u6 := (a * (b ^ 2))) (k := 1) (l := 0) (left := 6 * a * b * c)
  sym_simplify 6 * a * b * c  -  6 * (c * b ^ 2 * c * a ^ 2 * b * c ^ 2 * b * a ^ 2 * a * c ^ 2 * a * b ^ 2) ^ (1 / 6) = 0
  try close

theorem P22 {a b : ℝ} (ha : a > 0) (hb : b > 0) (h : a + b < 6): 1 / sqrt (1 + a) + 1 / sqrt (1 + b) + sqrt (a * b) / sqrt (a * b + 8) ≤ 2 := by
  scale Cauchy_Schwarz_sqrt_left_2vars (u1 := 1) (u2 := 1) (v1 := (1 / sqrt ((1 + a)))) (v2 := ((1 / sqrt ((1 + b))) + (sqrt ((a * b)) / sqrt (((a * b) + 8))))) (k := 1) (l := 0) (right := 2)
  llm_cancel_power 2
  llm_simplify (sqrt 2 * sqrt((1 / sqrt(1 + a)) ^ 2 + (1 / sqrt(1 + b) + sqrt(a * b) / sqrt(a * b + 8)) ^ 2)) ^ 2 - (4) = 2 / (a + 1) + 2 * (1 / (sqrt (b + 1)) + sqrt (a) * sqrt (b) / (sqrt (a * b + 8))) ^ 2 - (4)
  scale Cauchy_Schwarz_normal_left_2vars (u1 := 1) (u2 := sqrt (b)) (v1 := (1 / sqrt ((b + 1)))) (v2 := (sqrt (a) * (1 / sqrt (((a * b) + 8))))) (k := 2) (l := (2 / (a + 1))) (right := 4)
  llm_cancel_factor (2 * (1 + sqrt b ^ 2) * ((1 / sqrt(b + 1)) ^ 2 + (sqrt a * (1 / sqrt(a * b + 8))) ^ 2) + 2 / (a + 1)) - (4) = (2) * (a) * (1 / (a + 1)) * (1 / (a * b + 8)) * (a + b - (7))
  llm_factor a + b - (7) = a + b - (7)

theorem P23 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : a / sqrt (a ^ 2 + 8 * b * c) + b / sqrt (b ^ 2 + 8 * a * c) + c / sqrt (c ^ 2 + 8 * a * b) ≤ 2 := by
  sorry

theorem P24 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : 1 / (a + 2) + 1 / (b + 2) + 1 / (c + 2) ≤ 1 / (6 * sqrt (a * b) + c) + 1 / (6 * sqrt (b * c) + a) + 1 / (6 * sqrt (c * a) + b) := by
  scale AM_GM_div_cycle_normal_right_2vars (u1 := a) (u2 := b) (u3 := a) (v1 := b) (v2 := c) (v3 := c) (i1 := 6) (i2 := 6) (i3 := 6) (j1 := c) (j2 := a) (j3 := b) (k := 1) (l := 0) (left := 1 / (a + 2) + 1 / (b + 2) + 1 / (c + 2))
  llm_simplify 1 / (a + 2) + 1 / (b + 2) + 1 / (c + 2) - (1 / (6 * (a + b) / 2 + c) + 1 / (6 * (b + c) / 2 + a) + 1 / (6 * (a + c) / 2 + b)) = 1 / (-(a) - (b) + 3) + 1 / (a + 2) + 1 / (b + 2) - (1 / (-(2 * a) + 3)) - (1 / (-(2 * b) + 3)) - (1 / (2 * a + 2 * b + 1))
  llm_simplify 1 / (-a - b + 3) + 1 / (a + 2) + 1 / (b + 2) - (1 / (2 * a + 2 * b + 1) + 1 / (-(2 * b) + 3) + 1 / (-(2 * a) + 3)) = (1 - (3 * a)) / ((-(2 * a) + 3) * (a + 2)) + (1 - (3 * b)) / ((-(2 * b) + 3) * (b + 2)) + (1 - (3 * c)) / ((-(2 * c) + 3) * (c + 2))
  sym_tangent_line 27 * a / 49 + 27 * b / 49 + 27 * c / 49 - (27 / 49) ≤ (0) - ((1 - 3 * a) / ((-(2 * a) + 3) * (a + 2)) + (1 - 3 * b) / ((-(2 * b) + 3) * (b + 2)) + (1 - 3 * c) / ((-(2 * c) + 3) * (c + 2)))
  llm_simplify 0 - (27 * a / 49 + 27 * b / 49 + 27 * c / 49 - 27 / 49) = 27 / 49 + 27 * -(a) / 49 + 27 * -(b) / 49 + 27 * -(c) / 49

theorem P25 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : 1 / (a + 2) + 1 / (b + 2) + 1 / (c + 2) ≤ 1 / (3 - 2 * c) + 1 / (3 - 2 * a) + 1 / (3 - 2 * b) := by
  sym_tangent_line 27 * a / 49 + 27 * b / 49 + 27 * c / 49 - (27 / 49) ≤ (1 / (3 - 2 * c) + 1 / (3 - 2 * a) + 1 / (3 - 2 * b)) - (1 / (a + 2) + 1 / (b + 2) + 1 / (c + 2))
  llm_simplify 0 - (27 * a / 49 + 27 * b / 49 + 27 * c / 49 - 27 / 49) = 27 / 49 + 27 * -(a) / 49 + 27 * -(b) / 49 + 27 * -(c) / 49

theorem P26 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 3) : (a / (2 * a ^ 2 + a + 1) + b / (2 * b ^ 2 + b + 1) + c / (2 * c ^ 2 + c + 1)) ≤ 3 / 4 := by
  make_homogeneous a * (a / 3 + b / 3 + c / 3) / (2 * a ^ 2 + a * (a / 3 + b / 3 + c / 3) + (a / 3 + b / 3 + c / 3) ^ 2) + b * (a / 3 + b / 3 + c / 3) / (2 * b ^ 2 + b * (a / 3 + b / 3 + c / 3) + (a / 3 + b / 3 + c / 3) ^ 2) + c * (a / 3 + b / 3 + c / 3) / (2 * c ^ 2 + c * (a / 3 + b / 3 + c / 3) + (a / 3 + b / 3 + c / 3) ^ 2) - (3 / 4) ≤ 0
  scale Jensen_dick_div_left_3vars (u := a) (v := b) (w := c) (i1 := (((a / 3) + (b / 3)) + (c / 3))) (i2 := 2) (j1 := (((a / 3) + (b / 3)) + (c / 3))) (j2 := ((((a / 3) + (b / 3)) + (c / 3)) ^ 2)) (k := 1) (l := 0) (right := 3 / 4)
  llm_simplify (a / 3 + b / 3 + c / 3) * (a + b + c) / (2 * ((a + b + c) / 3) ^ 2 + (a / 3 + b / 3 + c / 3) * (a + b + c) / 3 + (a / 3 + b / 3 + c / 3) ^ 2) - (3 / 4) = 0

theorem P27 {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h : a + b + c + d = 4) : (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≤ 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 + 1 / d ^ 2) := by
  make_homogeneous a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 - ((a / 4 + b / 4 + c / 4 + d / 4) ^ 4 / (a ^ 2)) - ((a / 4 + b / 4 + c / 4 + d / 4) ^ 4 / (b ^ 2)) - ((a / 4 + b / 4 + c / 4 + d / 4) ^ 4 / (c ^ 2)) - ((a / 4 + b / 4 + c / 4 + d / 4) ^ 4 / (d ^ 2)) ≤ 0
  llm_cancel_factor a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 - ((a / 4 + b / 4 + c / 4 + d / 4) ^ 4 / d ^ 2 + (a / 4 + b / 4 + c / 4 + d / 4) ^ 4 / c ^ 2 + (a / 4 + b / 4 + c / 4 + d / 4) ^ 4 / b ^ 2 + (a / 4 + b / 4 + c / 4 + d / 4) ^ 4 / a ^ 2) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 - ((a + b + c + d) ^ 4 * (1 / (a ^ 2) + 1 / (b ^ 2) + 1 / (c ^ 2) + 1 / (d ^ 2)) / 256)
  sym_equal_value 0 ≤ 1 / (d ^ 2) + 27 / ((d - (4)) ^ 2) - (d ^ 2) - ((d - (4)) ^ 2 / 3)

theorem P28 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 8 * (a * b * c) ^ (1 / 3) + ((a ^ 3 + b ^ 3 + c ^ 3) / 3) ^ (1 / 3) ≤ 3 * (a + b + c) := by
  scale weighted_Power_Mean_Rlt1_left_2vars (u := ((a * b) * c)) (v := ((((a ^ 3) + (b ^ 3)) + (c ^ 3)) / 3)) (i1 := 8) (i2 := 1) (r := (1 / 3)) (k := 1) (l := 0) (right := 3 * (a + b + c))
  llm_factor (8 * a * b * c + (a ^ 3 + b ^ 3 + c ^ 3) / 3) ^ (1 / 3) * 9 ^ (2 / 3) - (3 * (a + b + c)) = 3 * (a ^ 3 + b ^ 3 + c ^ 3 + 24 * a * b * c) ^ (1 / 3) - (3 * a) - (3 * b) - (3 * c)
  llm_cancel_factor (3 * (a ^ 3 + b ^ 3 + c ^ 3 + 24 * a * b * c) ^ (1 / 3)) - (3 * c + 3 * b + 3 * a) = (3) * ((a ^ 3 + b ^ 3 + c ^ 3 + 24 * a * b * c) ^ (1 / 3) - (a) - (b) - (c))
  llm_cancel_power 3
  llm_cancel_factor (a ^ 3 + b ^ 3 + c ^ 3 + 24 * a * b * c) - ((c + b + a) ^ 3) = (3) * (6 * a * b * c - (a * b ^ 2) - (a * c ^ 2) - (b * a ^ 2) - (b * c ^ 2) - (c * a ^ 2) - (c * b ^ 2))
  scale AM_GM_normal_right_2vars (u := (c * (b ^ 2))) (v := (c * (a ^ 2))) (k := 1) (l := (((b * (c ^ 2)) + (b * (a ^ 2))) + ((a * (c ^ 2)) + (a * (b ^ 2))))) (left := 6 * a * b * c)
  llm_mul_expand 6 * a * b * c - (2 * sqrt(c * b ^ 2 * c * a ^ 2) + b * c ^ 2 + b * a ^ 2 + a * c ^ 2 + a * b ^ 2) = 6 * a * b * c - (2 * sqrt (a ^ 2 * b ^ 2 * c ^ 2)) - (a * b ^ 2) - (a * c ^ 2) - (b * a ^ 2) - (b * c ^ 2)
  scale AM_GM_square_right_2vars (u := c) (v := a) (k := b) (l := ((a * (c ^ 2)) + ((a * (b ^ 2)) + (2 * sqrt ((((a ^ 2) * (b ^ 2)) * (c ^ 2))))))) (left := 6 * a * b * c)
  scale AM_GM_square_right_2vars (u := c) (v := b) (k := a) (l := ((2 * sqrt ((((a ^ 2) * (b ^ 2)) * (c ^ 2)))) + (((2 * b) * c) * a))) (left := 6 * a * b * c)
  llm_simplify 6 * a * b * c - (2 * a * c * b + 2 * sqrt(a ^ 2 * b ^ 2 * c ^ 2) + 2 * b * c * a) = 0

theorem P29 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 1 ≤ a / sqrt (a ^ 2 + 8 * b * c) + b / sqrt (b ^ 2 + 8 * a * c) + c / sqrt (c ^ 2 + 8 * a * b) := by
  scale Holder_2R_div_variant1_right_3vars (u1 := a) (u2 := b) (u3 := c) (v1 := sqrt (((a ^ 2) + ((8 * b) * c)))) (v2 := sqrt (((b ^ 2) + ((8 * a) * c)))) (v3 := sqrt (((c ^ 2) + ((8 * a) * b)))) (k := 1) (l := 0) (left := 1)
  llm_factor 1 - (sqrt((a + b + c) ^ 3 / (a * sqrt(a ^ 2 + 8 * b * c) ^ 2 + b * sqrt(b ^ 2 + 8 * a * c) ^ 2 + c * sqrt(c ^ 2 + 8 * a * b) ^ 2))) = 1 - (sqrt ((a + b + c) ^ 3 / (a ^ 3 + 24 * a * b * c + b ^ 3 + c ^ 3)))
  llm_cancel_power 2
  llm_cancel_factor (1) - ((a + b + c) ^ 3 / (a ^ 3 + 24 * a * b * c + b ^ 3 + c ^ 3)) = (3) * (1 / (a ^ 3 + 24 * a * b * c + b ^ 3 + c ^ 3)) * (6 * a * b * c - (a * b ^ 2) - (a * c ^ 2) - (b * a ^ 2) - (b * c ^ 2) - (c * a ^ 2) - (c * b ^ 2))
  scale AM_GM_square_right_2vars (u := b) (v := a) (k := c) (l := (((b * (c ^ 2)) + (b * (a ^ 2))) + ((a * (c ^ 2)) + (a * (b ^ 2))))) (left := 6 * a * b * c)
  llm_mul_expand 6 * a * b * c - (2 * c * b * a + b * c ^ 2 + b * a ^ 2 + a * c ^ 2 + a * b ^ 2) = 4 * a * b * c - (a * b ^ 2) - (a * c ^ 2) - (b * a ^ 2) - (b * c ^ 2)
  scale AM_GM_normal_right_2vars (u := (c ^ 2)) (v := (a ^ 2)) (k := b) (l := ((a * (c ^ 2)) + (a * (b ^ 2)))) (left := 4 * a * b * c)
  scale AM_GM_square_right_2vars (u := c) (v := b) (k := a) (l := ((2 * b) * sqrt (((c ^ 2) * (a ^ 2))))) (left := 4 * a * b * c)
  llm_simplify 4 * a * b * c - (2 * a * c * b + 2 * b * sqrt(c ^ 2 * a ^ 2)) = 0

theorem P30 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 27 / (2 * (a + b + c) ^ 2) ≤ 1 / (a * (b+c)) + 1 / (b * (c + a)) + 1 / (c * (a + b)) := by
  scale Holder_2R_pq_div_Peq1_right_3vars (u1 := 1) (u2 := 1) (u3 := 1) (v1 := (a * (b + c))) (v2 := (b * (c + a))) (v3 := (c * (a + b))) (w1 := 1) (w2 := 1) (w3 := 1) (q := 2) (k := 1) (l := 0) (left := 27 / (2 * (a + b + c) ^ 2))
  llm_simplify 27 / (2 * (a + b + c) ^ 2) - (27 / ((a * (b + c)) ^ (1 / 2) + (b * (c + a)) ^ (1 / 2) + (c * (a + b)) ^ (1 / 2)) ^ 2) = 27 / (2 * ((a + b + c) ^ 2)) - (27 / ((sqrt (a * b + a * c) + sqrt (a * b + b * c) + sqrt (a * c + b * c)) ^ 2))
  scale Jensen_square_div_right_3vars (u := sqrt (((a * b) + (a * c)))) (v := sqrt (((a * b) + (b * c)))) (w := sqrt (((a * c) + (b * c)))) (k := 27) (l := 0) (left := 27 / (2 * (a + b + c) ^ 2))
  llm_simplify 27 / (2 * (a + b + c) ^ 2) - (27 * (1 / sqrt(a * b + a * c) ^ 2 + 1 / sqrt(a * b + b * c) ^ 2 + 1 / sqrt(a * c + b * c) ^ 2) / 27) = 27 / (2 * ((a + b + c) ^ 2)) - (1 / (a * b + a * c)) - (1 / (a * b + b * c)) - (1 / (a * c + b * c))
  scale AM_GM_div_square_right_2vars (u := a) (v := c) (i := 1) (j := (b * c)) (k := 1) (l := ((1 / ((a * b) + (b * c))) + (1 / ((a * b) + (a * c))))) (left := 27 / (2 * (a + b + c) ^ 2))
  llm_factor 27 / (2 * (a + b + c) ^ 2) - (1 / ((a ^ 2 + c ^ 2) / 2 + b * c) + 1 / (a * b + b * c) + 1 / (a * b + a * c)) = 27 / (2 * ((a + b + c) ^ 2)) - (2 / (a ^ 2 + 2 * b * c + c ^ 2)) - (1 / ((a + c) * (b))) - (1 / ((a) * (b + c)))
  scale AM_HM_normal_right_3vars (u := (1 / (a * (b + c)))) (v := (1 / ((a + c) * b))) (w := (2 / (((a ^ 2) + ((2 * b) * c)) + (c ^ 2)))) (k := 1) (l := 0) (left := 27 / (2 * (a + b + c) ^ 2))
  llm_cancel_factor (27 / (2 * (a + b + c) ^ 2)) - (9 / (1 / (1 / (a * (b + c))) + 1 / (1 / ((a + c) * b)) + 1 / (2 / (a ^ 2 + 2 * b * c + c ^ 2)))) = (9 / 2) * (1 / (a + c)) * (1 / ((a + b + c) ^ 2)) * ((a + c - (2 * b)) ^ 2) * (-1 / (a + 4 * b + c))

theorem P31 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : (3 / 2) * (a ^ 2 + b ^ 2 + c ^ 2) ≤ (a ^ 3 + 5 * b ^ 3) / (3 * a + b) + (b ^ 3 + 5 * c ^ 3) / (3 * b + c) + (c ^ 3 + 5 * a ^ 3) / (3 * c + a) := by
  llm_mul_expand 3 / 2 * (a ^ 2 + b ^ 2 + c ^ 2) - ((a ^ 3 + 5 * b ^ 3) / (3 * a + b) + (b ^ 3 + 5 * c ^ 3) / (3 * b + c) + (c ^ 3 + 5 * a ^ 3) / (3 * c + a)) = 3 * a ^ 2 / 2 + 3 * b ^ 2 / 2 + 3 * c ^ 2 / 2 - (a ^ 3 / (3 * a + b)) - (b ^ 3 / (3 * b + c)) - (c ^ 3 / (a + 3 * c)) - (5 * b ^ 3 / (3 * a + b)) - (5 * c ^ 3 / (3 * b + c)) - (5 * a ^ 3 / (a + 3 * c))
  scale Titu_variant2_right_3vars (u1 := b) (u2 := a) (u3 := c) (v1 := ((3 * b) + c)) (v2 := ((3 * a) + b)) (v3 := (a + (3 * c))) (r := 3) (k := 1) (l := ((((5 * (a ^ 3)) / (a + (3 * c))) + ((5 * (c ^ 3)) / ((3 * b) + c))) + ((5 * (b ^ 3)) / ((3 * a) + b)))) (left := 3 * a ^ 2 / 2 + 3 * b ^ 2 / 2 + 3 * c ^ 2 / 2)
  scale Titu_variant2_right_3vars (u1 := a) (u2 := c) (u3 := b) (v1 := (a + (3 * c))) (v2 := ((3 * b) + c)) (v3 := ((3 * a) + b)) (r := 3) (k := 5) (l := (((((b ^ 2) + (a ^ 2)) + (c ^ 2)) ^ 2) / (((b * ((3 * b) + c)) + (a * ((3 * a) + b))) + (c * (a + (3 * c)))))) (left := 3 * a ^ 2 / 2 + 3 * b ^ 2 / 2 + 3 * c ^ 2 / 2)
  llm_cancel_factor (3 * a ^ 2 / 2 + 3 * b ^ 2 / 2 + 3 * c ^ 2 / 2) - (5 * ((a ^ 2 + c ^ 2 + b ^ 2) ^ 2 / (a * (a + 3 * c) + c * (3 * b + c) + b * (3 * a + b))) + (b ^ 2 + a ^ 2 + c ^ 2) ^ 2 / (b * (3 * b + c) + a * (3 * a + b) + c * (a + 3 * c))) = (1 / 2) * (1 / (a ^ 2 + 3 * a * b + 3 * a * c + b ^ 2 + 3 * b * c + c ^ 2)) * (1 / (3 * a ^ 2 + a * b + a * c + 3 * b ^ 2 + b * c + 3 * c ^ 2)) * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + a * c + b * c - (a ^ 2) - (b ^ 2) - (c ^ 2)) * (23 * a ^ 2 + 23 * b ^ 2 + 23 * c ^ 2 + 9 * a * b + 9 * a * c + 9 * b * c)
  scale Rearrange_cycle_mul_right_3vars (u := c) (v := b) (w := a) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := 1) (l := 0) (left := a * b + a * c + b * c)

theorem P32 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : 1 / 3 ≤ (1 / (a ^ 5 * (b + 2 * c) ^ 2)) + (1 / (b ^ 5 * (c + 2 * a) ^ 2)) + (1 / (c ^ 5 * (a + 2 * b) ^ 2)) := by
  make_homogeneous 1 / 3 - ((a * b * c) ^ (7 / 3) / (((2 * a + c) ^ 2) * (b ^ 5))) - ((a * b * c) ^ (7 / 3) / (((a + 2 * b) ^ 2) * (c ^ 5))) - ((a * b * c) ^ (7 / 3) / (((b + 2 * c) ^ 2) * (a ^ 5))) ≤ 0
  llm_simplify 1 / 3 - ((a * b * c) ^ (7 / 3) / ((b + 2 * c) ^ 2 * a ^ 5) + (a * b * c) ^ (7 / 3) / ((a + 2 * b) ^ 2 * c ^ 5) + (a * b * c) ^ (7 / 3) / ((2 * a + c) ^ 2 * b ^ 5)) = 1 / 3 - (1 / (((2 * a + c) ^ 2) * (b ^ 5)) + 1 / (((a + 2 * b) ^ 2) * (c ^ 5)) + 1 / (((b + 2 * c) ^ 2) * (a ^ 5)))
  scale Holder_2R_pq_div_variant1_right_3vars (u1 := 1) (u2 := 1) (u3 := 1) (v1 := ((2 * a) + c)) (v2 := (a + (2 * b))) (v3 := (b + (2 * c))) (w1 := b) (w2 := c) (w3 := a) (p := 2) (q := 5) (k := 1) (l := 0) (left := 1 / 3)
  llm_simplify 1 / 3 - (((1 / b ^ 3) ^ (1 / 3) + (1 / c ^ 3) ^ (1 / 3) + (1 / a ^ 3) ^ (1 / 3)) ^ 3 / ((2 * a + c) * b + (a + 2 * b) * c + (b + 2 * c) * a) ^ 2) = (3 * a ^ 3 * b ^ 3 * c ^ 3 - (a * b) - (a * c) - (b * c)) / (9 * (a ^ 3) * (b ^ 3) * (c ^ 3))
  llm_cancel_denom (3 * a ^ 3 * b ^ 3 * c ^ 3 - a * b - a * c - b * c) / (9 * a ^ 3 * b ^ 3 * c ^ 3) - (0) = (3 * a ^ 3 * b ^ 3 * c ^ 3 - (a * b) - (a * c) - (b * c)) / (9 * (a ^ 3) * (b ^ 3) * (c ^ 3))
  llm_simplify 3 * a ^ 3 * b ^ 3 * c ^ 3 - (b * c + a * c + a * b) = 3 - (a * b + a * c + b * c)
  scale AM_GM_normal_right_3vars (u := (a * b)) (v := (a * c)) (w := (b * c)) (k := 1) (l := 0) (left := 3)
  llm_simplify 3 - (3 * (a * b * a * c * b * c) ^ (1 / 3)) = 3 - (3 * (a * b * c) ^ (2 / 3))
  try close

theorem P33 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : 1 + sqrt (a * b) + sqrt (b * c) + sqrt (c * a) ≤ sqrt (a * b + c) + sqrt (b * c + a) + sqrt (c * a + b) := by
  make_homogeneous a + b + c + sqrt (a * b) + sqrt (a * c) + sqrt (b * c) - (sqrt (a * b + c * (a + b + c))) - (sqrt (a * c + b * (a + b + c))) - (sqrt (a * (a + b + c) + b * c)) ≤ 0
  llm_factor a + b + c + sqrt(a * b) + sqrt(a * c) + sqrt(b * c) - (sqrt(a * (a + b + c) + b * c) + sqrt(a * c + b * (a + b + c)) + sqrt(a * b + c * (a + b + c))) = a + b + c + sqrt (a * b) + sqrt (a * c) + sqrt (b * c) - (sqrt ((a + b) * (a + c))) - (sqrt ((a + b) * (b + c))) - (sqrt ((a + c) * (b + c)))
  llm_exp_expand a + b + c + sqrt(a * b) + sqrt(a * c) + sqrt(b * c) - (sqrt((a + c) * (b + c)) + sqrt((a + b) * (b + c)) + sqrt((a + b) * (a + c))) = a + b + c + sqrt (a) * sqrt (b) + sqrt (a) * sqrt (c) + sqrt (b) * sqrt (c) - (sqrt (a + b) * sqrt (a + c) + sqrt (a + b) * sqrt (b + c) + sqrt (a + c) * sqrt (b + c))
  scale Cauchy_Schwarz_sqrt_cycle_right_2vars (u1 := a) (u2 := b) (u3 := a) (u4 := b) (u5 := a) (u6 := c) (v1 := a) (v2 := c) (v3 := c) (v4 := b) (v5 := b) (v6 := c) (k := 1) (l := 0) (left := a + b + c + sqrt a * sqrt b + sqrt a * sqrt c + sqrt b * sqrt c)
  llm_simplify a + b + c + sqrt a * sqrt b + sqrt a * sqrt c + sqrt b * sqrt c - (sqrt(a * a) + sqrt(b * c) + sqrt(a * c) + sqrt(b * b) + sqrt(a * b) + sqrt(c * c)) = 0

theorem P34 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a ^ 2 + b ^ 2 + c ^ 2 = 12) : a * (b ^ 2 + c ^ 2) ^ (1 / 3) + b * (c ^ 2 + a ^ 2) ^ (1 / 3) + c * (a ^ 2 + b ^ 2) ^ (1 / 3) ≤ 12 := by
  make_homogeneous a * (b ^ 2 + c ^ 2) ^ (1 / 3) + b * (a ^ 2 + c ^ 2) ^ (1 / 3) + c * (a ^ 2 + b ^ 2) ^ (1 / 3) - (12 * (a ^ 2 / 12 + b ^ 2 / 12 + c ^ 2 / 12) ^ (5 / 6)) ≤ 0
  llm_simplify a * (b ^ 2 + c ^ 2) ^ (1 / 3) + b * (a ^ 2 + c ^ 2) ^ (1 / 3) + c * (a ^ 2 + b ^ 2) ^ (1 / 3) - (12 * (a ^ 2 / 12 + b ^ 2 / 12 + c ^ 2 / 12) ^ (5 / 6)) = a * (b ^ 2 + c ^ 2) ^ (1 / 3) + b * (a ^ 2 + c ^ 2) ^ (1 / 3) + c * (a ^ 2 + b ^ 2) ^ (1 / 3) - (2 ^ (1 / 3) * 3 ^ (1 / 6) * (a ^ 2 + b ^ 2 + c ^ 2) ^ (5 / 6))
  scale Cauchy_Schwarz_sqrt_left_3vars (u1 := a) (u2 := b) (u3 := c) (v1 := (((b ^ 2) + (c ^ 2)) ^ (1 / 3))) (v2 := (((a ^ 2) + (c ^ 2)) ^ (1 / 3))) (v3 := (((a ^ 2) + (b ^ 2)) ^ (1 / 3))) (k := 1) (l := 0) (right := 2 ^ (1 / 3) * 3 ^ (1 / 6) * (a ^ 2 + b ^ 2 + c ^ 2) ^ (5 / 6))
  scale AM_GM_square_left_2vars (u := sqrt ((((a ^ 2) + (b ^ 2)) + (c ^ 2)))) (v := sqrt (((((((b ^ 2) + (c ^ 2)) ^ (1 / 3)) ^ 2) + ((((a ^ 2) + (c ^ 2)) ^ (1 / 3)) ^ 2)) + ((((a ^ 2) + (b ^ 2)) ^ (1 / 3)) ^ 2)))) (k := 1) (l := 0) (right := 2 ^ (1 / 3) * 3 ^ (1 / 6) * (a ^ 2 + b ^ 2 + c ^ 2) ^ (5 / 6))
  llm_cancel_denom (sqrt(a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + sqrt(((b ^ 2 + c ^ 2) ^ (1 / 3)) ^ 2 + ((a ^ 2 + c ^ 2) ^ (1 / 3)) ^ 2 + ((a ^ 2 + b ^ 2) ^ (1 / 3)) ^ 2) ^ 2) / 2 - (2 ^ (1 / 3) * 3 ^ (1 / 6) * (a ^ 2 + b ^ 2 + c ^ 2) ^ (5 / 6)) = a ^ 2 / 2 + b ^ 2 / 2 + c ^ 2 / 2 + (a ^ 2 + b ^ 2) ^ (2 / 3) / 2 + (a ^ 2 + c ^ 2) ^ (2 / 3) / 2 + (b ^ 2 + c ^ 2) ^ (2 / 3) / 2 - (2 * 2 ^ (1 / 3) * 3 ^ (1 / 6) * (a ^ 2 + b ^ 2 + c ^ 2) ^ (5 / 6)) / 2
  llm_cancel_factor (a ^ 2 / 2 + b ^ 2 / 2 + c ^ 2 / 2 + (a ^ 2 + b ^ 2) ^ (2 / 3) / 2 + (a ^ 2 + c ^ 2) ^ (2 / 3) / 2 + (b ^ 2 + c ^ 2) ^ (2 / 3) / 2) - (2 * 2 ^ (1 / 3) * 3 ^ (1 / 6) * (a ^ 2 + b ^ 2 + c ^ 2) ^ (5 / 6) / 2) = (1 / 2) * (a ^ 2 + b ^ 2 + c ^ 2 + (a ^ 2 + b ^ 2) ^ (2 / 3) + (a ^ 2 + c ^ 2) ^ (2 / 3) + (b ^ 2 + c ^ 2) ^ (2 / 3) - (2 * 2 ^ (1 / 3) * 3 ^ (1 / 6) * (a ^ 2 + b ^ 2 + c ^ 2) ^ (5 / 6)))
  scale Jensen_pow_Rlt1_left_3vars (u := ((a ^ 2) + (c ^ 2))) (v := ((b ^ 2) + (c ^ 2))) (w := ((a ^ 2) + (b ^ 2))) (r := (2 / 3)) (k := 1) (l := (((a ^ 2) + (b ^ 2)) + (c ^ 2))) (right := 2 * 2 ^ (1 / 3) * 3 ^ (1 / 6) * (a ^ 2 + b ^ 2 + c ^ 2) ^ (5 / 6))
  llm_simplify 3 * ((a ^ 2 + c ^ 2 + b ^ 2 + c ^ 2 + a ^ 2 + b ^ 2) / 3) ^ (2 / 3) + a ^ 2 + b ^ 2 + c ^ 2 - (2 * 2 ^ (1 / 3) * 3 ^ (1 / 6) * (a ^ 2 + b ^ 2 + c ^ 2) ^ (5 / 6)) = 0

theorem P35 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b + b * c + c * a = 1) (h' : a * b * c ≤ 1 / (3 * (sqrt 3))) : (1 / a + 6 * b) ^ (1 / 3) + (1 / b + 6 * c) ^ (1 / 3) + (1 / c + 6 * a) ^ (1 / 3) ≤ 1 / (a * b * c) := by
  make_homogeneous (6 * a + (a * b + a * c + b * c) / (c)) ^ (1 / 3) + (6 * b + (a * b + a * c + b * c) / (a)) ^ (1 / 3) + (6 * c + (a * b + a * c + b * c) / (b)) ^ (1 / 3) - ((a * b + a * c + b * c) ^ (5 / 3) / ((a) * (b) * (c))) ≤ 0
  scale weighted_Power_Mean_Rlt1_left_3vars (u := ((6 * a) + ((((a * b) + (a * c)) + (b * c)) / c))) (v := ((6 * b) + ((((a * b) + (a * c)) + (b * c)) / a))) (w := ((6 * c) + ((((a * b) + (a * c)) + (b * c)) / b))) (i1 := 1) (i2 := 1) (i3 := 1) (r := (1 / 3)) (k := 1) (l := 0) (right := (a * b + a * c + b * c) ^ (5 / 3) / (a * b * c))
  llm_cancel_factor (6 * a + (a * b + a * c + b * c) / c + 6 * b + (a * b + a * c + b * c) / a + 6 * c + (a * b + a * c + b * c) / b) ^ (1 / 3) * 3 ^ (2 / 3) - ((a * b + a * c + b * c) ^ (5 / 3) / (a * b * c)) = 3 ^ (2 / 3) * (8 * a + 8 * b + 8 * c + a * b / (c) + a * c / (b) + b * c / (a)) ^ (1 / 3) - ((a * b + a * c + b * c) ^ (5 / 3) / ((a) * (b) * (c)))
  llm_exp_expand 3 ^ (2 / 3) * (8 * a + 8 * b + 8 * c + a * b / c + a * c / b + b * c / a) ^ (1 / 3) - ((a * b + a * c + b * c) ^ (5 / 3) / (a * b * c)) = 3 ^ (2 / 3) * (8 * a + 8 * b + 8 * c + a * b / (c) + a * c / (b) + b * c / (a)) ^ (1 / 3) - ((a * b * (a * b + a * c + b * c) ^ (2 / 3) + a * c * (a * b + a * c + b * c) ^ (2 / 3) + b * c * (a * b + a * c + b * c) ^ (2 / 3)) / ((a) * (b) * (c)))
  llm_factor 3 ^ (2 / 3) * (8 * a + 8 * b + 8 * c + a * b / c + a * c / b + b * c / a) ^ (1 / 3) - ((a * b * (a * b + a * c + b * c) ^ (2 / 3) + a * c * (a * b + a * c + b * c) ^ (2 / 3) + b * c * (a * b + a * c + b * c) ^ (2 / 3)) / (a * b * c)) = 3 ^ (2 / 3) * (8 * a + 8 * b + 8 * c + a * b / (c) + a * c / (b) + b * c / (a)) ^ (1 / 3) - ((a * b + a * c + b * c) ^ (2 / 3) / (a)) - ((a * b + a * c + b * c) ^ (2 / 3) / (b)) - ((a * b + a * c + b * c) ^ (2 / 3) / (c))
  scale AM_GM_normal_right_3vars (u := (((((a * b) + (a * c)) + (b * c)) ^ (2 / 3)) / c)) (v := (((((a * b) + (a * c)) + (b * c)) ^ (2 / 3)) / b)) (w := (((((a * b) + (a * c)) + (b * c)) ^ (2 / 3)) / a)) (k := 1) (l := 0) (left := 3 ^ (2 / 3) * (8 * a + 8 * b + 8 * c + a * b / c + a * c / b + b * c / a) ^ (1 / 3))
  llm_cancel_power 3
  llm_factor (3 ^ (2 / 3) * (8 * a + 8 * b + 8 * c + a * b / c + a * c / b + b * c / a) ^ (1 / 3)) ^ 3 - ((3 * ((a * b + a * c + b * c) ^ (2 / 3) / c * ((a * b + a * c + b * c) ^ (2 / 3) / b) * ((a * b + a * c + b * c) ^ (2 / 3) / a)) ^ (1 / 3)) ^ 3) = 72 * a + 72 * b + 72 * c + 9 * a * b / (c) + 9 * a * c / (b) + 9 * b * c / (a) - (27 * (a * b + a * c + b * c) ^ 2 / ((a) * (b) * (c)))
  llm_cancel_factor (72 * a + 72 * b + 72 * c + 9 * a * b / c + 9 * a * c / b + 9 * b * c / a) - (27 * (a * b + a * c + b * c) ^ 2 / (a * b * c)) = (18) * (1 / (a)) * (1 / (b)) * (1 / (c)) * (a * b * c ^ 2 + a * c * b ^ 2 + b * c * a ^ 2 - (a ^ 2 * b ^ 2) - (a ^ 2 * c ^ 2) - (b ^ 2 * c ^ 2))
  scale Rearrange_cycle_mul_left_3vars (u := (a * c)) (v := (b * c)) (w := (a * b)) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := 1) (l := 0) (right := b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2 + a ^ 2 * b ^ 2)

theorem P36 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h1 : a ^ 2 - a * b + b ^ 2 > 0) (h2 : b ^ 2 - b * c + c ^ 2 > 0) (h3 : c ^ 2 - c * a + a ^ 2 > 0) : sqrt (a ^ 2 - a * b + b ^ 2) + sqrt (b ^ 2 - b * c + c ^ 2) + sqrt (c ^ 2 - c * a + a ^ 2) + 9 * (a * b * c) ^ (1 / 3) ≤ 4 * (a + b + c) := by
  scale AM_GM_sqrt_cbrt_left_3vars (u := a) (v := b) (w := c) (k := 9) (l := ((sqrt ((((a ^ 2) - (a * b)) + (b ^ 2))) + sqrt ((((b ^ 2) - (b * c)) + (c ^ 2)))) + sqrt ((((c ^ 2) - (c * a)) + (a ^ 2))))) (right := 4 * (a + b + c))
  llm_factor 9 * (sqrt(a * b) + sqrt(b * c) + sqrt(c * a)) / 3 + sqrt(a ^ 2 - a * b + b ^ 2) + sqrt(b ^ 2 - b * c + c ^ 2) + sqrt(c ^ 2 - c * a + a ^ 2) - (4 * (a + b + c)) = sqrt (a ^ 2 + b ^ 2 - (a * b)) + sqrt (a ^ 2 + c ^ 2 - (a * c)) + sqrt (b ^ 2 + c ^ 2 - (b * c)) + 3 * sqrt (a * b) + 3 * sqrt (a * c) + 3 * sqrt (b * c) - (4 * a) - (4 * b) - (4 * c)
  scale weighted_Power_Mean_Rlt1_left_2vars (u := (((a ^ 2) + (b ^ 2)) - (a * b))) (v := (a * b)) (i1 := 1) (i2 := 3) (r := (1 / 2)) (k := 1) (l := ((sqrt ((((a ^ 2) + (c ^ 2)) - (a * c))) + sqrt ((((b ^ 2) + (c ^ 2)) - (b * c)))) + ((3 * sqrt ((a * c))) + (3 * sqrt ((b * c)))))) (right := 4 * c + 4 * b + 4 * a)
  llm_simplify (a ^ 2 + b ^ 2 - a * b + 3 * a * b) ^ (1 / 2) * 4 ^ (1 / 2) + sqrt(a ^ 2 + c ^ 2 - a * c) + sqrt(b ^ 2 + c ^ 2 - b * c) + 3 * sqrt(a * c) + 3 * sqrt(b * c) - (4 * c + 4 * b + 4 * a) = sqrt (a ^ 2 + c ^ 2 - (a * c)) + sqrt (b ^ 2 + c ^ 2 - (b * c)) + 3 * sqrt (a * c) + 3 * sqrt (b * c) - (2 * a) - (2 * b) - (4 * c)
  scale weighted_Power_Mean_Rlt1_left_2vars (u := (((a ^ 2) + (c ^ 2)) - (a * c))) (v := (a * c)) (i1 := 1) (i2 := 3) (r := (1 / 2)) (k := 1) (l := (sqrt ((((b ^ 2) + (c ^ 2)) - (b * c))) + (3 * sqrt ((b * c))))) (right := 4 * c + 2 * b + 2 * a)
  llm_simplify (a ^ 2 + c ^ 2 - a * c + 3 * a * c) ^ (1 / 2) * 4 ^ (1 / 2) + sqrt(b ^ 2 + c ^ 2 - b * c) + 3 * sqrt(b * c) - (4 * c + 2 * b + 2 * a) = sqrt (b ^ 2 + c ^ 2 - (b * c)) + 3 * sqrt (b * c) - (2 * b) - (2 * c)
  scale weighted_Power_Mean_Rlt1_left_2vars (u := (((b ^ 2) + (c ^ 2)) - (b * c))) (v := (b * c)) (i1 := 1) (i2 := 3) (r := (1 / 2)) (k := 1) (l := 0) (right := 2 * c + 2 * b)
  llm_simplify (b ^ 2 + c ^ 2 - b * c + 3 * b * c) ^ (1 / 2) * 4 ^ (1 / 2) - (2 * c + 2 * b) = 0

theorem P37 {a b c : ℝ}  (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a ^ 3 + b ^ 3 + c ^ 3 + a * b * c = 4) : (10 - a * b * c) ^ 2 / (a + b + c) ≤ (5 * a ^ 2 + b * c) ^ 2 / ((a + b) * (a + c)) + (5 * b ^ 2 + c * a) ^ 2 / ((b + c) * (b + a)) + (5 * c ^ 2 + a * b)^2 / ((c + a) * (c + b)) := by
  make_homogeneous (5 * a ^ 3 / 2 + 5 * b ^ 3 / 2 + 5 * c ^ 3 / 2 + 3 * a * b * c / 2) ^ 2 / (a + b + c) - ((5 * a ^ 2 + b * c) ^ 2 * (a ^ 3 / 4 + b ^ 3 / 4 + c ^ 3 / 4 + a * b * c / 4) / ((a + b) * (a + c))) - ((5 * b ^ 2 + a * c) ^ 2 * (a ^ 3 / 4 + b ^ 3 / 4 + c ^ 3 / 4 + a * b * c / 4) / ((a + b) * (b + c))) - ((5 * c ^ 2 + a * b) ^ 2 * (a ^ 3 / 4 + b ^ 3 / 4 + c ^ 3 / 4 + a * b * c / 4) / ((a + c) * (b + c))) ≤ 0
  llm_simplify (5 * a ^ 3 / 2 + 5 * b ^ 3 / 2 + 5 * c ^ 3 / 2 + 3 * a * b * c / 2) ^ 2 / (a + b + c) - ((5 * c ^ 2 + a * b) ^ 2 * (a ^ 3 / 4 + b ^ 3 / 4 + c ^ 3 / 4 + a * b * c / 4) / ((a + c) * (b + c)) + (5 * b ^ 2 + a * c) ^ 2 * (a ^ 3 / 4 + b ^ 3 / 4 + c ^ 3 / 4 + a * b * c / 4) / ((a + b) * (b + c)) + (5 * a ^ 2 + b * c) ^ 2 * (a ^ 3 / 4 + b ^ 3 / 4 + c ^ 3 / 4 + a * b * c / 4) / ((a + b) * (a + c))) = (10 - (a * b * c)) ^ 2 / (a + b + c) - ((5 * a ^ 2 + b * c) ^ 2 / ((a + b) * (a + c)) + (5 * b ^ 2 + a * c) ^ 2 / ((a + b) * (b + c)) + (5 * c ^ 2 + a * b) ^ 2 / ((a + c) * (b + c)))
  scale Titu_cycle_refactor_right_3vars (u1 := (5 * (a ^ 2))) (u2 := (5 * (b ^ 2))) (u3 := (5 * (c ^ 2))) (v1 := (((a * a) + (a * b)) + ((c * a) + (c * b)))) (v2 := (((b * a) + (b * b)) + ((c * a) + (c * b)))) (v3 := (((b * a) + (b * c)) + ((c * a) + (c * c)))) (w1 := a) (w2 := b) (w3 := c) (i := 1) (k := 1) (l := 0) (left := (10 - a * b * c) ^ 2 / (a + b + c))
  llm_simplify (10 - a * b * c) ^ 2 / (a + b + c) - ((5 * a ^ 2 * a + 5 * b ^ 2 * b + 5 * c ^ 2 * c + 3 * a * b * c) ^ 2 / ((a * a + a * b + c * a + c * b) * a ^ 2 + (b * a + b * b + c * a + c * b) * b ^ 2 + (b * a + b * c + c * a + c * c) * c ^ 2)) = (10 - (a * b * c)) ^ 2 / (a + b + c) - ((5 * a ^ 3 + 5 * b ^ 3 + 5 * c ^ 3 + 3 * a * b * c) ^ 2 / (a ^ 2 * (a ^ 2 + a * b + a * c + b * c) + b ^ 2 * (a * b + a * c + b ^ 2 + b * c) + c ^ 2 * (a * b + a * c + b * c + c ^ 2)))
  llm_factor (10 - a * b * c) ^ 2 / (a + b + c) - ((5 * a ^ 3 + 5 * b ^ 3 + 5 * c ^ 3 + 3 * a * b * c) ^ 2 / (a ^ 2 * (a ^ 2 + a * b + a * c + b * c) + b ^ 2 * (a * b + a * c + b ^ 2 + b * c) + c ^ 2 * (a * b + a * c + b * c + c ^ 2))) = -(a ^ 3 + b ^ 3 + c ^ 3 + a * b * c - (4)) * (25 * a ^ 3 + 25 * b ^ 3 + 25 * c ^ 3 + 25 * a * b * c - (a ^ 2 * b ^ 2 * c ^ 2)) / ((a + b + c) * (a ^ 3 + a * b * c + b ^ 3 + c ^ 3))
  llm_simplify -(a ^ 3 + b ^ 3 + c ^ 3 + a * b * c - 4) * (25 * a ^ 3 + 25 * b ^ 3 + 25 * c ^ 3 + 25 * a * b * c - a ^ 2 * b ^ 2 * c ^ 2) / ((a + b + c) * (a ^ 3 + a * b * c + b ^ 3 + c ^ 3)) - (0) = 0

theorem P38 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0)  (h : a + b + c = 3) : sqrt 3 ≤ sqrt (a ^ 2 + a * b + b ^ 2) + sqrt (b ^ 2 + b * c + c ^ 2) + sqrt (c ^ 2 + c * a + a ^ 2) := by
  make_homogeneous sqrt (3) * (a / 3 + b / 3 + c / 3) - (sqrt (a ^ 2 + b ^ 2 + a * b)) - (sqrt (a ^ 2 + c ^ 2 + a * c)) - (sqrt (b ^ 2 + c ^ 2 + b * c)) ≤ 0
  scale AM_GM_normal_right_2vars (u := sqrt ((((b ^ 2) + (c ^ 2)) + (b * c)))) (v := sqrt ((((a ^ 2) + (c ^ 2)) + (a * c)))) (k := 1) (l := sqrt ((((a ^ 2) + (b ^ 2)) + (a * b)))) (left := sqrt 3 * (a / 3 + b / 3 + c / 3))
  llm_frac_apart sqrt 3 * (a / 3 + b / 3 + c / 3) - (2 * sqrt(sqrt(b ^ 2 + c ^ 2 + b * c) * sqrt(a ^ 2 + c ^ 2 + a * c)) + sqrt(a ^ 2 + b ^ 2 + a * b)) = a * sqrt (3) / (3) + b * sqrt (3) / (3) + c * sqrt (3) / (3) - (sqrt (a ^ 2 + b ^ 2 + a * b)) - (2 * sqrt (sqrt (b ^ 2 + c ^ 2 + b * c) * sqrt (a ^ 2 + c ^ 2 + a * c)))
  llm_exp_expand a * sqrt 3 / 3 + b * sqrt 3 / 3 + c * sqrt 3 / 3 - (2 * sqrt(sqrt(b ^ 2 + c ^ 2 + b * c) * sqrt(a ^ 2 + c ^ 2 + a * c)) + sqrt(a ^ 2 + b ^ 2 + a * b)) = a * sqrt (3) / (3) + b * sqrt (3) / (3) + c * sqrt (3) / (3) - (sqrt (a ^ 2 + b ^ 2 + a * b)) - (2 * (a ^ 2 + c ^ 2 + a * c) ^ (1 / 4) * (b ^ 2 + c ^ 2 + b * c) ^ (1 / 4))
  scale Jensen_sqrt_right_3vars (u := (a ^ 2)) (v := (b ^ 2)) (w := (a * b)) (k := 1) (l := ((2 * ((((a ^ 2) + (c ^ 2)) + (a * c)) ^ (1 / 4))) * ((((b ^ 2) + (c ^ 2)) + (b * c)) ^ (1 / 4)))) (left := a * sqrt 3 / 3 + b * sqrt 3 / 3 + c * sqrt 3 / 3)
  llm_simplify a * sqrt 3 / 3 + b * sqrt 3 / 3 + c * sqrt 3 / 3 - ((sqrt(a ^ 2) + sqrt(b ^ 2) + sqrt(a * b)) / sqrt 3 + 2 * (a ^ 2 + c ^ 2 + a * c) ^ (1 / 4) * (b ^ 2 + c ^ 2 + b * c) ^ (1 / 4)) = a * sqrt (3) / 3 + b * sqrt (3) / 3 + c * sqrt (3) / 3 - (2 * ((a ^ 2 + c ^ 2 + a * c) * (b ^ 2 + c ^ 2 + b * c)) ^ (1 / 4)) - (sqrt (3) * (a + b + sqrt (a * b)) / 3)
  llm_frac_apart a * sqrt 3 / 3 + b * sqrt 3 / 3 + c * sqrt 3 / 3 - (sqrt 3 * (a + b + sqrt(a * b)) / 3 + 2 * ((a ^ 2 + c ^ 2 + a * c) * (b ^ 2 + c ^ 2 + b * c)) ^ (1 / 4)) = c * sqrt (3) / (3) - (2 * ((a ^ 2 + c ^ 2 + a * c) * (b ^ 2 + c ^ 2 + b * c)) ^ (1 / ((4)))) - (sqrt (3) * sqrt (a * b) / (3))
  llm_exp_expand c * sqrt 3 / 3 - (sqrt 3 * sqrt(a * b) / 3 + 2 * ((a ^ 2 + c ^ 2 + a * c) * (b ^ 2 + c ^ 2 + b * c)) ^ (1 / 4)) = c * sqrt (3) / (3) - (2 * (a ^ 2 + c ^ 2 + a * c) ^ (1 / ((4))) * (b ^ 2 + c ^ 2 + b * c) ^ (1 / ((4)))) - (sqrt (3) * sqrt (a) * sqrt (b) / (3))
  scale Holder_2R_right_2vars (u1 := (c ^ 2)) (u2 := (a ^ 2)) (u3 := (a * c)) (v1 := (c ^ 2)) (v2 := (b ^ 2)) (v3 := (b * c)) (r1 := (1 / 4)) (r2 := (1 / 4)) (k := 2) (l := (((sqrt (3) * sqrt (a)) * sqrt (b)) / 3)) (left := c * sqrt 3 / 3)
  llm_cancel_factor (c * sqrt 3 / 3) - (2 * ((c ^ 2) ^ (1 / 2) * (c ^ 2) ^ (1 / 2) + (a ^ 2) ^ (1 / 2) * (b ^ 2) ^ (1 / 2) + (a * c) ^ (1 / 2) * (b * c) ^ (1 / 2)) ^ (1 / 2) + sqrt 3 * sqrt a * sqrt b / 3) = (1 / 3) * (c * sqrt (3) - (6 * (c ^ 2 + (a ^ 2) ^ (1 / (2)) * (b ^ 2) ^ (1 / (2)) + (a * c) ^ (1 / (2)) * (b * c) ^ (1 / (2))) ^ (1 / (2))) - (sqrt (3) * sqrt (a) * sqrt (b)))
  llm_simplify c * sqrt 3 - (sqrt 3 * sqrt a * sqrt b + 6 * (c ^ 2 + (a ^ 2) ^ (1 / 2) * (b ^ 2) ^ (1 / 2) + (a * c) ^ (1 / 2) * (b * c) ^ (1 / 2)) ^ (1 / 2)) = c * sqrt (3) - (6 * sqrt (c ^ 2 + a * b + sqrt (a * c) * sqrt (b * c))) - (sqrt (3) * sqrt (a * b))
  scale Jensen_sqrt_right_3vars (u := (a * b)) (v := (c ^ 2)) (w := (sqrt ((a * c)) * sqrt ((b * c)))) (k := 6) (l := (sqrt (3) * sqrt ((a * b)))) (left := c * sqrt 3)
  llm_simplify c * sqrt 3 - (6 * ((sqrt(a * b) + sqrt(c ^ 2) + sqrt(sqrt(a * c) * sqrt(b * c))) / sqrt 3) + sqrt 3 * sqrt(a * b)) = -(c * sqrt (3)) - (3 * sqrt (3) * sqrt (a * b)) - (2 * sqrt (3) * sqrt (c * sqrt (a * b)))
  scale AM_GM_normal_right_2vars (u := (c * sqrt (3))) (v := ((2 * sqrt (3)) * sqrt ((c * sqrt ((a * b)))))) (k := 1) (l := ((3 * sqrt (3)) * sqrt ((a * b)))) (left := 0)

theorem P39 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : 3 / 2  ≤ (a * b * c) ^ 2 / (a ^ 3 * (b + c)) + (a * b * c) ^ 2 / (b ^ 3 * (c + a)) + (a * b * c) ^ 2 / (c ^ 3 * (a + b)) := by
  make_homogeneous 3 * (a * b * c) ^ (2 / 3) / 2 - (a ^ 2 * b ^ 2 / ((a + b) * (c))) - (a ^ 2 * c ^ 2 / ((a + c) * (b))) - (b ^ 2 * c ^ 2 / ((a) * (b + c))) ≤ 0
  llm_mul_expand 3 * (a * b * c) ^ (2 / 3) / 2 - (b ^ 2 * c ^ 2 / (a * (b + c)) + a ^ 2 * c ^ 2 / ((a + c) * b) + a ^ 2 * b ^ 2 / ((a + b) * c)) = 3 * a ^ (2 / (3)) * b ^ (2 / (3)) * c ^ (2 / (3)) / (2) - (b ^ 2 * c ^ 2 / (a * (b + c)) + a ^ 2 * c ^ 2 / (b * (a + c)) + a ^ 2 * b ^ 2 / (c * (a + b)))
  scale Titu_normal_right_3vars (u1 := (c * b)) (u2 := (c * a)) (u3 := (a * b)) (v1 := (a * (b + c))) (v2 := (b * (a + c))) (v3 := (c * (a + b))) (k := 1) (l := 0) (left := 3 * a ^ (2 / 3) * b ^ (2 / 3) * c ^ (2 / 3) / 2)
  llm_simplify 3 * a ^ (2 / 3) * b ^ (2 / 3) * c ^ (2 / 3) / 2 - ((c * b + c * a + a * b) ^ 2 / (a * (b + c) + b * (a + c) + c * (a + b))) = (3 * (a * b * c) ^ (2 / (3)) - (a * b + b * c + c * a)) / (2)
  llm_cancel_denom (3 * (a * b * c) ^ (2 / 3) - (a * b + b * c + c * a)) / 2 - (0) = (3 * (a * b * c) ^ (2 / (3)) - (a * b + b * c + c * a)) / (2)
  scale AM_GM_normal_right_3vars (u := (a * b)) (v := (b * c)) (w := (c * a)) (k := 1) (l := 0) (left := 3 * (a * b * c) ^ (2 / 3))
  sym_simplify 3 * (a * b * c) ^ (2 / 3)  -  3 * (a * b * b * c * c * a) ^ (1 / 3) = 0
  try close

theorem P40 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 3) : (2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) + (2 * b + c + a) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) + (2 * c + a + b) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) ≤ 8 := by
  intro_by_homogeneous a + b + c = 3
  llm_simplify (2 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) + (2 * b + c + a) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) + (2 * c + a + b) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) - (8) = (a ^ 2 + 6 * a + 9) / (3 * a ^ 2 - (6 * a) + 9) + (b ^ 2 + 6 * b + 9) / (3 * b ^ 2 - (6 * b) + 9) + (c ^ 2 + 6 * c + 9) / (3 * c ^ 2 - (6 * c) + 9) - (8)
  sym_tangent_line 4 - (4 * a / 3) - (4 * b / 3) - (4 * c / 3) ≤ (8) - ((a ^ 2 + 6 * a + 9) / (3 * a ^ 2 - 6 * a + 9) + (b ^ 2 + 6 * b + 9) / (3 * b ^ 2 - 6 * b + 9) + (c ^ 2 + 6 * c + 9) / (3 * c ^ 2 - 6 * c + 9))
  try close

theorem P41 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a + b + c) ^ 3 ≤ (a ^ 5 - a ^ 2 + 3) * (b ^ 5 - b ^ 2 + 3) * (c ^ 5 - c ^ 2 + 3) := by
  closed_by_sos

theorem P42 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = a ^ (1 / 7) + b ^ (1 / 7) + c ^ (1 / 7)) : 1 ≤ a ^ a * b ^ b * c ^ c := by
  sorry
