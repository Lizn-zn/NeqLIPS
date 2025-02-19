import Mathlib

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

/-
  The basic Schur inequality for 3 variables: {\displaystyle x^{t}(x-y)(x-z)+y^{t}(y-z)(y-x)+z^{t}(z-x)(z-y)\geq 0}
-/
theorem Schur_Teq1_3vars (u v w : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) : (u ^ 3 + v ^ 3 + w ^ 3 + 3 * u * v * w ≥ u ^ 2 * v + u ^ 2 * w + v ^ 2 * u + v ^ 2 * w + w ^ 2 * u + w ^ 2 * v) := by
    sorry

theorem Schur_Teq1_left_3vars (u v w k l right : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hk : k ≥ 0)
  (h : k * (u ^ 3 + v ^ 3 + w ^ 3 + 3 * u * v * w) + l ≤ right) : k * (u ^ 2 * v + u ^ 2 * w + v ^ 2 * u + v ^ 2 * w + w ^ 2 * u + w ^ 2 * v) + l ≤ right := by
  suffices u ^ 2 * v + u ^ 2 * w + v ^ 2 * u + v ^ 2 * w + w ^ 2 * u + w ^ 2 * v ≤ u ^ 3 + v ^ 3 + w ^ 3 + 3 * u * v * w by nlinarith
  exact Schur_Teq1_3vars u v w hu hv hw

theorem Schur_Teq1_right_3vars (u v w k l left : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hk : k ≥ 0)
  (h : left ≤ k * (u ^ 2 * v + u ^ 2 * w + v ^ 2 * u + v ^ 2 * w + w ^ 2 * u + w ^ 2 * v) + l) : left ≤ k * (u ^ 3 + v ^ 3 + w ^ 3 + 3 * u * v * w) + l := by
  suffices u ^ 2 * v + u ^ 2 * w + v ^ 2 * u + v ^ 2 * w + w ^ 2 * u + w ^ 2 * v ≤ u ^ 3 + v ^ 3 + w ^ 3 + 3 * u * v * w by nlinarith
  exact Schur_Teq1_3vars u v w hu hv hw

/-- The schur for (u^2v)^(1/3), (v^2w)^(1/3), (w^2u)^(1/3) -/
theorem Schur_x2y_3vars (u v w : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) :
  (u * v * w) ^ (1 / 3) * (u * v + v * w + w * u) + (u * v * w) ^ (2 / 3) * (u + v + w) ≤ u ^ 2 * v + v ^ 2 * w + w ^ 2 * u + 3 * u * v * w := by
  sorry

theorem Schur_x2y_left_3vars (u v w k l right : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (huvw : u * v * w = 1) (hk : k ≥ 0)
  (h : k * (u ^ 2 * v + v ^ 2 * w + w ^ 2 * u + 3) + l ≤ right) :
  k * (u * v + v * w + w * u + u + v + w) + l ≤ right := by
  suffices u * v + v * w + w * u + u + v + w ≤ u ^ 2 * v + v ^ 2 * w + w ^ 2 * u + 3 by nlinarith
  have h_ := Schur_x2y_3vars u v w hu hv hw
  rw [huvw] at h_;
  norm_num at h_
  convert h_ using 1
  linarith
  simp [*]; linarith

theorem Schur_x2y_right_3vars (u v w k l left : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hk : k ≥ 0)
  (h : left ≤ k * ((u * v * w) ^ (1 / 3) * (u * v + v * w + w * u) + (u * v * w) ^ (2 / 3) * (u + v + w)) + l) :
  left ≤ k * (u ^ 2 * v + v ^ 2 * w + w ^ 2 * u + 3 * u * v * w) + l := by
  suffices (u * v * w) ^ (1 / 3) * (u * v + v * w + w * u) + (u * v * w) ^ (2 / 3) * (u + v + w) ≤ u ^ 2 * v + v ^ 2 * w + w ^ 2 * u + 3 * u * v * w by nlinarith
  exact Schur_x2y_3vars u v w hu hv hw


/-
  The basic Schur inequality for 3 variables: {\displaystyle x^{t}(x-y)(x-z)+y^{t}(y-z)(y-x)+z^{t}(z-x)(z-y)\geq 0}
-/
theorem Schur_Teq2_3vars (u v w : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) : (u ^ 4 + v ^ 4 + w ^ 4 + u ^ 2 * v * w + v ^ 2 * w * u + w ^ 2 * u * v ≥ u ^ 3 * v + u ^ 3 * w + v ^ 3 * u + v ^ 3 * w + w ^ 3 * u + w ^ 3 * v) := by
    sorry

theorem Schur_Teq2_left_3vars (u v w k l right : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hk : k ≥ 0)
  (h : k * (u ^ 4 + v ^ 4 + w ^ 4 + u ^ 2 * v * w + v ^ 2 * w * u + w ^ 2 * u * v) + l ≤ right) :
  k * (u * v ^ 3 + u * w ^ 3 + v * u ^ 3 + v * w ^ 3 + w * u ^ 3 + w * v ^ 3) + l ≤ right := by
  suffices u ^ 4 + v ^ 4 + w ^ 4 + u ^ 2 * v * w + v ^ 2 * w * u + w ^ 2 * u * v ≥ u ^ 3 * v + u ^ 3 * w + v ^ 3 * u + v ^ 3 * w + w ^ 3 * u + w ^ 3 * v by nlinarith
  exact Schur_Teq2_3vars u v w hu hv hw

theorem Schur_Teq2_fact_left_3vars (u v w k l right : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hk : k ≥ 0)
  (h : k * (u ^ 4 + v ^ 4 + w ^ 4 + u ^ 2 * v * w + v ^ 2 * w * u + w ^ 2 * u * v) + l ≤ right) :
  k * (u ^ 3 * (v + w) + v ^ 3 * (u + w) + w ^ 3 * (u + v)) + l ≤ right := by
  suffices u ^ 4 + v ^ 4 + w ^ 4 + u ^ 2 * v * w + v ^ 2 * w * u + w ^ 2 * u * v ≥ u ^ 3 * v + u ^ 3 * w + v ^ 3 * u + v ^ 3 * w + w ^ 3 * u + w ^ 3 * v by nlinarith
  exact Schur_Teq2_3vars u v w hu hv hw

theorem Schur_Teq2_right_3vars (u v w k l left : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hk : k ≥ 0)
  (h : left ≤ k * (u ^ 3 * v + u ^ 3 * w + v ^ 3 * u + v ^ 3 * w + w ^ 3 * u + w ^ 3 * v) + l) :
  left ≤ k * (u ^ 4 + v ^ 4 + w ^ 4 + u ^ 2 * v * w + v ^ 2 * w * u + w ^ 2 * u * v) + l := by
  suffices u ^ 3 * v + u ^ 3 * w + v ^ 3 * u + v ^ 3 * w + w ^ 3 * u + w ^ 3 * v ≤ u ^ 4 + v ^ 4 + w ^ 4 + u ^ 2 * v * w + v ^ 2 * w * u + w ^ 2 * u * v by nlinarith
  exact Schur_Teq2_3vars u v w hu hv hw
