import Mathlib

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

/-
  The basic form of the power mean inequality, for r > 1 case
-/
theorem power_mean_Rgt1_2vars (u v i1 i2 r : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hr : r > 1) : (i1 * u + i2 * v) / (i1 + i2) ≤ (i1 * u ^ r + i2 * v ^ r) ^ (1 / r) / (i1 + i2) ^ (1 / r) := by
  sorry

/-
  The power mean inequality for two variables with r > 1
-/
theorem weighted_Power_Mean_Rgt1_left_2vars (u v i1 i2 r k l right : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hr : r > 1) (hk : k > 0) (h : k * (i1 + i2) * (i1 * u ^ r + i2 * v ^ r) ^ (1 / r) + l ≤ right) : k * (i1 + i2) ^ (1 / r) * (i1 * u + i2 * v) + l ≤ right := by
  suffices (i1 + i2) ^ (1 / r) * (i1 * u + i2 * v) ≤ (i1 + i2) * (i1 * u ^ r + i2 * v ^ r) ^ (1 / r) by nlinarith
  have h := power_mean_Rgt1_2vars u v i1 i2 r hu hv hi1 hi2 hr
  rw [<- mul_le_mul_right (a := (1 / (i1 + i2)) * (1 / (i1 + i2) ^ (1 / r)))]
  convert h using 1
  field_simp [*]; ring_nf
  field_simp [*]; ring_nf
  all_goals positivity

theorem weighted_Power_Mean_Rgt1_right_2vars (u v i1 i2 r k l left : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hr : r > 1) (hk : k > 0) (h : left ≤ k * ((i1 * u + i2 * v) ^ r / (i1 + i2) ^ (r - 1)) + l) : left ≤ k * (i1 * u ^ r + i2 * v ^ r) + l := by
  suffices (i1 * u + i2 * v) ^ r / (i1 + i2) ^ (r - 1) ≤ i1 * u ^ r + i2 * v ^ r by nlinarith
  have h := power_mean_Rgt1_2vars u v i1 i2 r hu hv hi1 hi2 hr
  rw [<-rpow_le_rpow_iff (z := r)] at h
  rw [<- mul_le_mul_right (a := i1 + i2)] at h
  convert h using 1
  field_simp
  have hi : i1 + i2 > 0 := by positivity
  have h := rpow_add hi (r - 1) 1
  simp only [rpow_one] at h; rw [mul_comm] at h
  rw [mul_assoc]; rw [<-h]
  rw [div_rpow]
  field_simp [*];
  any_goals positivity
  rw [div_rpow]
  rw [<-rpow_mul]
  field_simp [*]
  rw [<-rpow_mul]
  field_simp [*]
  any_goals positivity


/-
  The basic form of the power mean inequality, for r < 1 case
-/
theorem power_mean_Rlt1_2vars (u v i1 i2 r : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hr : r < 1) (hr' : r > 0) : (i1 * u ^ r + i2 * v ^ r) ^ (1 / r) / (i1 + i2) ^ (1 / r) ≤ (i1 * u + i2 * v) / (i1 + i2) := by
  sorry

/-
  The power mean inequality for two variables with r < 1
-/
theorem weighted_Power_Mean_Rlt1_left_2vars (u v i1 i2 r k l right : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hr : r < 1) (hr' : r > 0) (hk : k > 0) (h : k * (i1 * u + i2 * v) ^ r * (i1 + i2) ^ (1 - r) + l ≤ right) : k * (i1 * u ^ r + i2 * v ^ r) + l ≤ right := by
  suffices (i1 * u ^ r + i2 * v ^ r) ≤ (i1 * u + i2 * v) ^ r * (i1 + i2) ^ (1 - r) by nlinarith
  have h := power_mean_Rlt1_2vars u v i1 i2 r hu hv hi1 hi2 hr hr'
  rw [<- mul_le_mul_right (a := 1 / (i1 + i2))]
  rw [<-rpow_le_rpow_iff (z := r)] at h
  convert h using 1
  rw [div_rpow]
  rw [<-rpow_mul]; field_simp [*]; rw [<-rpow_mul]; field_simp [*]
  any_goals positivity
  rw [div_rpow]
  field_simp [*];
  have hi : i1 + i2 > 0 := by positivity
  have h := rpow_add hi (1 - r) r
  rw [mul_assoc]
  rw [<-h]
  field_simp
  all_goals positivity

theorem weighted_Power_Mean_Rlt1_right_2vars (u v i1 i2 r k l left : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hr : r < 1) (hr' : r > 0) (hk : k > 0) (h : left ≤ k * (i1 + i2) * (i1 * u ^ r + i2 * v ^ r) ^ (1 / r) + l) : left ≤ k * (i1 + i2) ^ (1 / r) * (i1 * u + i2 * v) + l := by
  suffices (i1 + i2) * (i1 * u ^ r + i2 * v ^ r) ^ (1 / r) ≤ (i1 + i2) ^ (1 / r) * (i1 * u + i2 * v) by nlinarith
  have h := power_mean_Rlt1_2vars u v i1 i2 r hu hv hi1 hi2 hr hr'
  rw [<- mul_le_mul_right (a := (1 / (i1 + i2)) * (1 / (i1 + i2) ^ (1 / r)))]
  convert h using 1
  field_simp [*]; ring_nf
  field_simp [*]; ring_nf
  all_goals positivity

/-
  The basic form of the power mean inequality for 3 variables, for r > 1 case
-/
theorem power_mean_Rgt1_3vars (u v w i1 i2 i3 r : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hi3 : i3 > 0) (hr : r > 1) : (i1 * u + i2 * v + i3 * w) / (i1 + i2 + i3) ≤ (i1 * u ^ r + i2 * v ^ r + i3 * w ^ r) ^ (1 / r) / (i1 + i2 + i3) ^ (1 / r) := by
  sorry

/-
  The power mean inequality for three variables with r > 1
-/
theorem weighted_Power_Mean_Rgt1_left_3vars (u v w i1 i2 i3 r k l right : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hi3 : i3 > 0) (hr : r > 1) (hk : k > 0) (h : k * (i1 + i2 + i3) * (i1 * u ^ r + i2 * v ^ r + i3 * w ^ r) ^ (1 / r) + l ≤ right) : k * (i1 + i2 + i3) ^ (1 / r) * (i1 * u + i2 * v + i3 * w) + l ≤ right := by
  suffices (i1 + i2 + i3) ^ (1 / r) * (i1 * u + i2 * v + i3 * w) ≤ (i1 + i2 + i3) * (i1 * u ^ r + i2 * v ^ r + i3 * w ^ r) ^ (1 / r) by nlinarith
  have h := power_mean_Rgt1_3vars u v w i1 i2 i3 r hu hv hw hi1 hi2 hi3 hr
  rw [<- mul_le_mul_right (a := (1 / (i1 + i2 + i3)) * (1 / (i1 + i2 + i3) ^ (1 / r)))]
  convert h using 1
  field_simp [*]; ring_nf
  field_simp [*]; ring_nf
  all_goals positivity

theorem weighted_Power_Mean_Rgt1_right_3vars (u v w i1 i2 i3 r k l left : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hi3 : i3 > 0) (hr : r > 1) (hk : k > 0) (h : left ≤ k * ((i1 * u + i2 * v + i3 * w) ^ r / (i1 + i2 + i3) ^ (r - 1)) + l) : left ≤ k * (i1 * u ^ r + i2 * v ^ r + i3 * w ^ r) + l := by
  suffices (i1 * u + i2 * v + i3 * w) ^ r / (i1 + i2 + i3) ^ (r - 1) ≤ i1 * u ^ r + i2 * v ^ r + i3 * w ^ r by nlinarith
  have h := power_mean_Rgt1_3vars u v w i1 i2 i3 r hu hv hw hi1 hi2 hi3 hr
  rw [<-rpow_le_rpow_iff (z := r)] at h
  rw [<- mul_le_mul_right (a := i1 + i2 + i3)] at h
  convert h using 1
  field_simp
  have hi : i1 + i2 + i3 > 0 := by positivity
  have h := rpow_add hi (r - 1) 1
  simp only [rpow_one] at h; rw [mul_comm] at h
  rw [mul_assoc]; rw [<-h]
  rw [div_rpow]
  field_simp [*];
  any_goals positivity
  rw [div_rpow]
  rw [<-rpow_mul]
  field_simp [*]
  rw [<-rpow_mul]
  field_simp [*]
  any_goals positivity


/-
  The basic form of the power mean inequality for 3 variables, for r < 1 case
-/
theorem power_mean_Rlt1_3vars (u v w i1 i2 i3 r : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hi3 : i3 > 0) (hr : r < 1) (hr' : r > 0) : (i1 * u ^ r + i2 * v ^ r + i3 * w ^ r) ^ (1 / r) / (i1 + i2 + i3) ^ (1 / r) ≤ (i1 * u + i2 * v + i3 * w) / (i1 + i2 + i3) := by
  sorry

/-
  The power mean inequality for three variables with r < 1
-/
theorem weighted_Power_Mean_Rlt1_left_3vars (u v w i1 i2 i3 r k l right : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hi3 : i3 > 0) (hr : r < 1) (hr' : r > 0) (hk : k > 0) (h : k * (i1 * u + i2 * v + i3 * w) ^ r * (i1 + i2 + i3) ^ (1 - r) + l ≤ right) : k * (i1 * u ^ r + i2 * v ^ r + i3 * w ^ r) + l ≤ right := by
  suffices (i1 * u ^ r + i2 * v ^ r + i3 * w ^ r) ≤ (i1 * u + i2 * v + i3 * w) ^ r * (i1 + i2 + i3) ^ (1 - r) by nlinarith
  have h := power_mean_Rlt1_3vars u v w i1 i2 i3 r hu hv hw hi1 hi2 hi3 hr hr'
  rw [<- mul_le_mul_right (a := 1 / (i1 + i2 + i3))]
  rw [<-rpow_le_rpow_iff (z := r)] at h
  convert h using 1
  rw [div_rpow]
  rw [<-rpow_mul]; field_simp [*]; rw [<-rpow_mul]; field_simp [*]
  any_goals positivity
  rw [div_rpow]
  field_simp [*];
  have hi : i1 + i2 + i3 > 0 := by positivity
  have h := rpow_add hi (1 - r) r
  rw [mul_assoc]
  rw [<-h]
  field_simp
  all_goals positivity

theorem weighted_Power_Mean_Rlt1_right_3vars (u v w i1 i2 i3 r k l left : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hi1 : i1 > 0) (hi2 : i2 > 0) (hi3 : i3 > 0) (hr : r < 1) (hr' : r > 0) (hk : k > 0) (h : left ≤ k * (i1 + i2 + i3) * (i1 * u ^ r + i2 * v ^ r + i3 * w ^ r) ^ (1 / r) + l) : left ≤ k * (i1 + i2 + i3) ^ (1 / r) * (i1 * u + i2 * v + i3 * w) + l := by
  suffices (i1 + i2 + i3) * (i1 * u ^ r + i2 * v ^ r + i3 * w ^ r) ^ (1 / r) ≤ (i1 + i2 + i3) ^ (1 / r) * (i1 * u + i2 * v + i3 * w) by nlinarith
  have h := power_mean_Rlt1_3vars u v w i1 i2 i3 r hu hv hw hi1 hi2 hi3 hr hr'
  rw [<- mul_le_mul_right (a := (1 / (i1 + i2 + i3)) * (1 / (i1 + i2 + i3) ^ (1 / r)))]
  convert h using 1
  field_simp [*]; ring_nf
  field_simp [*]; ring_nf
  all_goals positivity
