import Mathlib

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

-- ========================== AM-HM inequalities ==========================

/-
  The basic format of the AM-HM inequality for 2 variables
-/
theorem AM_HM_2vars (u v : ℝ) (hu : u > 0) (hv : v > 0) : 2 / (1 / u + 1 / v) ≤ (u + v) / 2 := by
  rw [<- mul_le_mul_right (a := (1 / u + 1 / v)) (b := 2 / (1 / u + 1 / v)) (c := (u + v) / 2)];
  rw [show 2 / (1 / u + 1 / v) * (1 / u + 1 / v) = 2 by field_simp [*]]
  let f : ℕ → ℝ | 0 => sqrt (1 / u) | 1 => sqrt (1 / v) | _ => 0
  let g : ℕ → ℝ | 0 => sqrt (u) | 1 => sqrt (v) | _ => 0
  let s : Finset ℕ := {0, 1}
  have h := Finset.sum_mul_sq_le_sq_mul_sq s f g
  simp [f, s] at h
  simp [g, s] at h
  (repeat rw [sq_sqrt] at h)
  rw [<- mul_le_mul_right (a := 2) (b := 2) (c:= (u + v) / 2 * (1 / u + 1 / v))]
  convert h using 1
  field_simp; norm_num;
  simp; linarith;
  all_goals positivity

/-
  The div form of the AM-HM inequality for 2 variables
-/
theorem AM_HM_div_left_2vars (u v k l right : ℝ) (hu : u > 0) (hv : v > 0) (hk : k > 0) (h : k * (1 / u + 1 / v) / 4 + l ≤ right) : k * (1 / (u + v)) + l ≤ right := by
  suffices 1 / (u + v) ≤ (1 / u + 1 / v) / 4 by nlinarith
  have h := AM_HM_2vars (1 / u) (1 / v)
  field_simp [*] at h
  rw [<- mul_le_mul_right (a := 2) (b := 1 / (u + v)) (c := (1 / u + 1 / v) / 4)]
  convert h using 1
  norm_num; field_simp;
  field_simp; linarith;
  positivity

theorem AM_HM_div_right_2vars (u v k l left : ℝ) (hu : u > 0) (hv : v > 0) (hk : k > 0) (h : left ≤ k * (4 / (u + v)) + l) :
  left ≤ k * (1 / u + 1 / v) + l := by
  suffices 4 / (u + v) ≤ (1 / u + 1 / v) by nlinarith
  have h := AM_HM_2vars (1 / u) (1 / v)
  field_simp [*] at h
  rw [<- mul_le_mul_right (a := 1 / 2) (b := 4 / (u + v)) (c := (1 / u + 1 / v))]
  convert h using 1
  norm_num; field_simp; linarith
  field_simp; linarith;

/-
  The basic form of the AM-HM inequality for 3 variables
-/
theorem AM_HM_3vars (u v w : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) : 3 / (1 / u + 1 / v + 1 / w) ≤ (u + v + w) / 3 := by
  rw [<- mul_le_mul_right (a := (1 / u + 1 / v + 1 / w)) (b := 3 / (1 / u + 1 / v + 1 / w)) (c := (u + v + w) / 3)];
  rw [show 3 / (1 / u + 1 / v + 1 / w) * (1 / u + 1 / v + 1 / w) = 3 by field_simp [*]]
  let f : ℕ → ℝ | 0 => sqrt (1 / u) | 1 => sqrt (1 / v) | 2 => sqrt (1 / w) | _ => 0
  let g : ℕ → ℝ | 0 => sqrt (u) | 1 => sqrt (v) | 2 => sqrt (w) | _ => 0
  let s : Finset ℕ := {0, 1, 2}
  have h := Finset.sum_mul_sq_le_sq_mul_sq s f g
  simp [f, s] at h
  simp [g, s] at h
  (repeat rw [sq_sqrt] at h)
  rw [<- mul_le_mul_right (a := 3) (b := 3) (c:= (u + v + w) / 3 * (1 / u + 1 / v + 1 / w))]
  convert h using 1
  field_simp; norm_num;
  simp; linarith;
  all_goals positivity

/-
  The normal form of the AM-HM inequality for 3 variables
-/
theorem AM_HM_normal_left_3vars (u v w k l right : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hk : k > 0) (h : k * (u + v + w) / 9 + l ≤ right) : k * (1 / (1 / u + 1 / v + 1 / w)) + l ≤ right := by
  suffices 1 / (1 / u + 1 / v + 1 / w) ≤ (u + v + w) / 9 by nlinarith
  have h := AM_HM_3vars u v w
  field_simp [*] at h
  rw [<- mul_le_mul_right (a := 3) (b := 1 / (1 / u + 1 / v + 1 / w)) (c := (u + v + w) / 9)]
  convert h using 1
  norm_num; field_simp; linarith
  field_simp; linarith;
  positivity

theorem AM_HM_normal_right_3vars (u v w k l left : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hk : k > 0) (h : left ≤ k * (9 / (1 / u + 1 / v + 1 / w)) + l) : left ≤ k * (u + v + w) + l := by
  suffices 9 / (1 / u + 1 / v + 1 / w) ≤ u + v + w by nlinarith
  have h := AM_HM_3vars u v w
  field_simp [*] at h
  rw [<- mul_le_mul_right (a := 1 / 3) (b := 9 / (1 / u + 1 / v + 1 / w)) (c := u + v + w)]
  convert h using 1
  norm_num; field_simp; linarith
  field_simp; linarith;

/-
  The div form of the AM-HM inequality for 3 variables
-/
theorem AM_HM_div_left_3vars (u v w k l right : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hk : k > 0) (h : k * (1 / u + 1 / v + 1 / w) / 9 + l ≤ right) : k * (1 / (u + v + w)) + l ≤ right := by
  suffices 1 / (u + v + w) ≤ (1 / u + 1 / v + 1 / w) / 9 by nlinarith
  have h := AM_HM_3vars (1 / u) (1 / v) (1 / w)
  field_simp [*] at h
  rw [<- mul_le_mul_right (a := 3) (b := 1 / (u + v + w)) (c := (1 / u + 1 / v + 1 / w) / 9)]
  convert h using 1
  norm_num; field_simp;
  field_simp; linarith;
  positivity

theorem AM_HM_div_right_3vars (u v w k l left : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hk : k > 0) (h : left ≤ k * (9 / (u + v + w)) + l) : left ≤ k * (1 / u + 1 / v + 1 / w) + l := by
  suffices 9 / (u + v + w) ≤ (1 / u + 1 / v + 1 / w) by nlinarith
  have h := AM_HM_3vars (1 / u) (1 / v) (1 / w)
  field_simp [*] at h
  rw [<- mul_le_mul_right (a := 1 / 3) (b := 9 / (u + v + w)) (c := (1 / u + 1 / v + 1 / w))]
  convert h using 1
  norm_num; field_simp; linarith
  field_simp; linarith;
