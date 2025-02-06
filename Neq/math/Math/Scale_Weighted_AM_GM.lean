import Mathlib

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

/-
  The base lemma: Weighted AM-GM for 2 variables
-/
theorem weighted_AM_GM_2vars (u v i1 i2 : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) : (u ^ i1 * v ^ i2) ^ (1 / (i1 + i2)) ≤ (i1 * u + i2 * v) / (i1 + i2) := by
  sorry

/-
  Weighted AM-GM for 2 variables
-/
theorem weighted_AM_GM_normal_left_2vars (u v i1 i2 : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hk : k > 0) (h : k * ((i1 * u + i2 * v) / (i1 + i2)) ^ (i1 + i2) + l ≤ right) :
  k * (u ^ i1 * v ^ i2) + l ≤ right := by
  suffices (u ^ i1 * v ^ i2) ≤ ((i1 * u + i2 * v) / (i1 + i2)) ^ (i1 + i2) by nlinarith
  have h := weighted_AM_GM_2vars u v i1 i2 hu hv hi1 hi2
  rw [<-rpow_le_rpow_iff (z := i1 + i2)] at h
  convert h using 1
  rw [<-rpow_mul]
  field_simp [*]
  all_goals positivity

theorem weighted_AM_GM_normal_right_2vars (u v i1 i2 : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hk : k > 0) (h : left ≤ k * (i1 + i2) * (u ^ i1 * v ^ i2) ^ (1 / (i1 + i2)) + l) :
  left ≤ k * (i1 * u + i2 * v) + l := by
  suffices (i1 + i2) * (u ^ i1 * v ^ i2) ^ (1 / (i1 + i2)) ≤ i1 * u + i2 * v by nlinarith
  rw [<- mul_le_mul_right (a := 1 / (i1 + i2))]
  have h := weighted_AM_GM_2vars u v i1 i2 hu hv hi1 hi2
  convert h using 1
  field_simp [*]; ring
  field_simp [*]
  positivity

/-
  The base lemma: Weighted AM-GM for 3 variables
-/
theorem weighted_AM_GM_3vars (u v w i1 i2 i3 : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hi3 : i3 > 0) : (u ^ i1 * v ^ i2 * w ^ i3) ^ (1 / (i1 + i2 + i3)) ≤ (i1 * u + i2 * v + i3 * w) / (i1 + i2 + i3) := by
  sorry

/-
  Weighted AM-GM for 3 variables
-/
theorem weighted_AM_GM_normal_left_3vars (u v w i1 i2 i3 k l right : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hi3 : i3 > 0) (hk : k > 0) (h : k * ((i1 * u + i2 * v + i3 * w) / (i1 + i2 + i3)) ^ (i1 + i2 + i3) + l ≤ right) : k * (u ^ i1 * v ^ i2 * w ^ i3) + l ≤ right := by
  suffices (u ^ i1 * v ^ i2 * w ^ i3) ≤ ((i1 * u + i2 * v + i3 * w) / (i1 + i2 + i3)) ^ (i1 + i2 + i3) by nlinarith
  have h := weighted_AM_GM_3vars u v w i1 i2 i3 hu hv hw hi1 hi2 hi3
  rw [<-rpow_le_rpow_iff (z := i1 + i2 + i3)] at h
  convert h using 1
  rw [<-rpow_mul]
  field_simp [*]
  all_goals positivity


theorem weighted_AM_GM_normal_right_3vars (u v w i1 i2 i3 k l left : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hi3 : i3 > 0) (hk : k > 0) (h : left ≤ k * (i1 + i2 + i3) * (u ^ i1 * v ^ i2 * w ^ i3) ^ (1 / (i1 + i2 + i3)) + l) : left ≤ k * (i1 * u + i2 * v + i3 * w) + l := by
  suffices (i1 + i2 + i3) * (u ^ i1 * v ^ i2 * w ^ i3) ^ (1 / (i1 + i2 + i3)) ≤ i1 * u + i2 * v + i3 * w by nlinarith
  rw [<- mul_le_mul_right (a := 1 / (i1 + i2 + i3))]
  have h := weighted_AM_GM_3vars u v w i1 i2 i3 hu hv hw hi1 hi2 hi3
  convert h using 1
  field_simp [*]; ring
  field_simp [*]
  positivity
