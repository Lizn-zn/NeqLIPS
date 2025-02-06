import Mathlib

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

/-
  The basic format of weighted Jensen √(i1 + i2 + i3) ^ 3 / √(i1 * u + i2 * v + i3 * w) ≤ (i1 / √u + i2 / √v + i3 / √w)
-/

theorem weighted_Jensen_sqrt_div_3vars (u v w i1 i2 i3 : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hi3 : i3 > 0) : sqrt (i1 + i2 + i3) ^ 3 / sqrt (i1 * u + i2 * v + i3 * w) ≤ (i1 / sqrt u + i2 / sqrt v + i3 / sqrt w) := by
  sorry

theorem weighted_Jensen_sqrt_div_left_3vars (u v w i1 i2 i3 k l right : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hi3 : i3 > 0) (hk : k > 0)
  (h : k * ((i1 / sqrt u + i2 / sqrt v + i3 / sqrt w) / sqrt (i1 + i2 + i3) ^ 3) + l ≤ right) :
  k * (1 / sqrt (i1 * u + i2 * v + i3 * w)) + l ≤ right := by
    suffices 1 / sqrt (i1 * u + i2 * v + i3 * w) ≤ (i1 / sqrt u + i2 / sqrt v + i3 / sqrt w) / sqrt (i1 + i2 + i3) ^ 3 by nlinarith
    have h := weighted_Jensen_sqrt_div_3vars u v w i1 i2 i3 hu hv hw hi1 hi2 hi3
    simp [*] at h
    rw [<- mul_le_mul_right (a := sqrt (i1 + i2 + i3) ^ 3) (b := 1 / sqrt (i1 * u + i2 * v + i3 * w)) (c := (i1 / sqrt u + i2 / sqrt v + i3 / sqrt w) / sqrt (i1 + i2 + i3) ^ 3)]
    convert h using 1
    field_simp; field_simp [*]; nlinarith
    positivity

theorem weighted_Jensen_sqrt_div_right_3vars (u v w i1 i2 i3 k l left : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hi3 : i3 > 0) (hk : k > 0)
  (h : left ≤ k * (sqrt (i1 + i2 + i3) ^ 3 / sqrt (i1 * u + i2 * v + i3 * w)) + l) :
  left ≤ k * (i1 / sqrt u + i2 / sqrt v + i3 / sqrt w) + l := by
    suffices sqrt (i1 + i2 + i3) ^ 3 / sqrt (i1 * u + i2 * v + i3 * w) ≤ (i1 / sqrt u + i2 / sqrt v + i3 / sqrt w) by nlinarith
    exact weighted_Jensen_sqrt_div_3vars u v w i1 i2 i3 hu hv hw hi1 hi2 hi3
