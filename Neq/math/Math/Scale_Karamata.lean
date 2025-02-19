import Mathlib

import Math.Scale_Cauchy_Schwarz

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

-- ========================== Karamata inequalities ==========================

/-- The Karamata for sqrt function -/
theorem Karamata_sqrt_cycle_3vars (u v w : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (h1 : u + v - w ≥ 0) (h2 : u + w - v ≥ 0) (h3 : v + w - u ≥ 0) : sqrt (u + v - w) + sqrt (u + w - v) + sqrt (v + w - u) ≤ sqrt u + sqrt v + sqrt w := by
  sorry

theorem Karamata_sqrt_cycle_left_3vars (u v w k l right : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (h1 : u + v - w ≥ 0) (h2 : u + w - v ≥ 0) (h3 : v + w - u ≥ 0) (hk : k ≥ 0) (h : k * (sqrt u + sqrt v + sqrt w) + l ≤ right) :
  k * (sqrt (u + v - w) + sqrt (u + w - v) + sqrt (v + w - u)) + l ≤ right := by
  suffices sqrt (u + v - w) + sqrt (u + w - v) + sqrt (v + w - u) ≤ sqrt u + sqrt v + sqrt w by nlinarith
  exact Karamata_sqrt_cycle_3vars u v w hu hv hw h1 h2 h3

theorem Karamata_sqrt_cycle_right_3vars (u v w k l left : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (h1 : u + v - w ≥ 0) (h2 : u + w - v ≥ 0) (h3 : v + w - u ≥ 0) (hk : k ≥ 0) (h : left ≤ k * (sqrt (u + v - w) + sqrt (u + w - v) + sqrt (v + w - u)) + l) :
  left ≤ k * (sqrt u + sqrt v + sqrt w) + l := by
  suffices sqrt (u + v - w) + sqrt (u + w - v) + sqrt (v + w - u) ≤ sqrt u + sqrt v + sqrt w by nlinarith
  exact Karamata_sqrt_cycle_3vars u v w hu hv hw h1 h2 h3

/-- The Karamata for div function -/
theorem Karamata_div_cycle_3vars (u v w : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (h1 : u + v - w > 0) (h2 : u + w - v > 0) (h3 : v + w - u > 0) : 1 / u + 1 / v + 1 / w ≤ 1 / (u + v - w) + 1 / (u + w - v) + 1 / (v + w - u) := by
  sorry

theorem Karamata_div_cycle_left_3vars (u v w k l right : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (h1 : u + v - w > 0) (h2 : u + w - v > 0) (h3 : v + w - u > 0) (hk : k ≥ 0)
  (h : k * (1 / (u + v - w) + 1 / (u + w - v) + 1 / (v + w - u)) + l ≤ right) :
  k * (1 / u + 1 / v + 1 / w) + l ≤ right := by
  suffices 1 / u + 1 / v + 1 / w ≤ 1 / (u + v - w) + 1 / (u + w - v) + 1 / (v + w - u) by nlinarith
  exact Karamata_div_cycle_3vars u v w hu hv hw h1 h2 h3

theorem Karamata_div_cycle_right_3vars (u v w k l left : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (h1 : u + v - w > 0) (h2 : u + w - v > 0) (h3 : v + w - u > 0) (hk : k ≥ 0)
  (h : left ≤ k * (1 / u + 1 / v + 1 / w) + l) :
  left ≤ k * (1 / (u + v - w) + 1 / (u + w - v) + 1 / (v + w - u)) + l := by
  suffices 1 / u + 1 / v + 1 / w ≤ 1 / (u + v - w) + 1 / (u + w - v) + 1 / (v + w - u) by nlinarith
  exact Karamata_div_cycle_3vars u v w hu hv hw h1 h2 h3

/-- The Karamata for square function -/
theorem Karamata_square_cycle_3vars (u v w : ℝ) : u ^ 2 + v ^ 2 + w ^ 2 ≤ (u + v - w) ^ 2 + (u + w - v) ^ 2 + (v + w - u) ^ 2 := by
  sorry

theorem Karamata_square_cycle_left_3vars (u v w k l right : ℝ) (hk : k ≥ 0) (h : k * ((u + v - w) ^ 2 + (u + w - v) ^ 2 + (v + w - u) ^ 2) + l ≤ right) :
  k * (u ^ 2 + v ^ 2 + w ^ 2) + l ≤ right := by
  suffices u ^ 2 + v ^ 2 + w ^ 2 ≤ (u + v - w) ^ 2 + (u + w - v) ^ 2 + (v + w - u) ^ 2 by nlinarith
  exact Karamata_square_cycle_3vars u v w

theorem Karamata_square_cycle_right_3vars (u v w k l left : ℝ) (hk : k ≥ 0) (h : left ≤ k * (u ^ 2 + v ^ 2 + w ^ 2) + l) :
  left ≤ k * ((u + v - w) ^ 2 + (u + w - v) ^ 2 + (v + w - u) ^ 2) + l := by
  suffices u ^ 2 + v ^ 2 + w ^ 2 ≤ (u + v - w) ^ 2 + (u + w - v) ^ 2 + (v + w - u) ^ 2 by nlinarith
  exact Karamata_square_cycle_3vars u v w
