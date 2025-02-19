import Mathlib

import Math.Scale_Cauchy_Schwarz

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

-- ========================== Titu inequalities ==========================

section Titu_3vars
/-
  The basic format Titu_3var : (u1 ^ 2 / v1 ^ 2 + u2 ^ 2 / v2 ^ 2 + u3 ^ 2 / v3 ^ 2) ≥ (u1 + u2 + u3) ^ 2 / (v1 + v2 + v3)
-/

theorem Titu_3vars (u1 u2 u3 v1 v2 v3 : ℝ) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) : (u1 + u2 + u3) ^ 2 / (v1 + v2 + v3) ≤ (u1 ^ 2 / v1 + u2 ^ 2 / v2 + u3 ^ 2 / v3) := by
  have h := Cauchy_Schwarz_3vars (u1 / sqrt v1) (u2 / sqrt v2) (u3 / sqrt v3) (sqrt v1) (sqrt v2) (sqrt v3)
  field_simp [*, sq_sqrt] at h
  rw [<- mul_le_mul_right (a := v1 + v2 + v3) (b := (u1 + u2 + u3) ^ 2 / (v1 + v2 + v3)) (c := u1 ^ 2 / v1 + u2 ^ 2 / v2 + u3 ^ 2 / v3)]
  convert h using 1
  field_simp [*]
  rw [mul_div_right_comm]
  rw [mul_right_cancel_iff_of_pos (a := (u1 ^ 2 / v1 + u2 ^ 2 / v2 + u3 ^ 2 / v3)) (b := (v1 + v2 + v3)) (c:= ((u1 ^ 2 * v2 + u2 ^ 2 * v1) * v3 + u3 ^ 2 * (v1 * v2)) / (v1 * v2 * v3))]
  field_simp [*]; ring_nf
  positivity; positivity

theorem Titu_normal_left_3vars (u1 u2 u3 v1 v2 v3 k l right : ℝ) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hk : k > 0)
  (h : k * (u1 ^ 2 / v1 + u2 ^ 2 / v2 + u3 ^ 2 / v3) + l ≤ right) :
  k * ((u1 + u2 + u3) ^ 2 / (v1 + v2 + v3)) + l ≤ right := by
    suffices (u1 + u2 + u3) ^ 2 / (v1 + v2 + v3) ≤ (u1 ^ 2 / v1 + u2 ^ 2 / v2 + u3 ^ 2 / v3) by nlinarith
    exact Titu_3vars u1 u2 u3 v1 v2 v3 hv1 hv2 hv3

theorem Titu_normal_right_3vars (u1 u2 u3 v1 v2 v3 k l left : ℝ) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hk : k > 0)
  (h : left ≤ k * ((u1 + u2 + u3) ^ 2 / (v1 + v2 + v3)) + l) :
  left ≤ k * (u1 ^ 2 / v1 + u2 ^ 2 / v2 + u3 ^ 2 / v3) + l := by
    suffices (u1 + u2 + u3) ^ 2 / (v1 + v2 + v3) ≤ (u1 ^ 2 / v1 + u2 ^ 2 / v2 + u3 ^ 2 / v3) by nlinarith
    exact Titu_3vars u1 u2 u3 v1 v2 v3 hv1 hv2 hv3

/-- (u1 + w) ^ 2 / v1 + (u2 + w) ^ 2 / v2 + (u3 + w) ^ 2 / v3 -> (u1 + u2 + u3 + 3 * w) ^ 2 / (v1 + v2 + v3) -/
theorem Titu_cycle_refactor_left_3vars (u1 u2 u3 v1 v2 v3 w k l right : ℝ) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hk : k > 0)
  (h : k * ((u1 + w) ^ 2 / v1 + (u2 + w) ^ 2 / v2 + (u3 + w) ^ 2 / v3) + l ≤ right) :
  k * ((u1 + u2 + u3 + 3 * w) ^ 2 / (v1 + v2 + v3)) + l ≤ right := by
    suffices (u1 + u2 + u3 + 3 * w) ^ 2 / (v1 + v2 + v3) ≤ ((u1 + w) ^ 2 / v1 + (u2 + w) ^ 2 / v2 + (u3 + w) ^ 2 / v3) by nlinarith
    have h_ := Titu_3vars (u1 + w) (u2 + w) (u3 + w) v1 v2 v3 hv1 hv2 hv3
    convert h_ using 1
    ring_nf

/-- (u1 + i1 * w2 * w3) ^ 2 / v1 + (u2 + i2 * w3 * w1) ^ 2 / v2 + (u3 + i3 * w1 * w2) ^ 2 / v3 -> (u1 + u2 + u3 + 3 * i1 * w2 * w3) ^ 2 / (v1 + v2 + v3) -/
theorem Titu_cycle_refactor_right_3vars (u1 u2 u3 v1 v2 v3 w1 w2 w3 k l left : ℝ) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0) (hw3 : w3 ≠ 0) (hk : k > 0)
  (h : left ≤ k * ((u1 * w1 + u2 * w2 + u3 * w3 + 3 * i * w1 * w2 * w3) ^ 2 / (v1 * w1 ^ 2 + v2 * w2 ^ 2 + v3 * w3 ^ 2)) + l) :
  left ≤ k * ((u1 + i * w2 * w3) ^ 2 / v1 + (u2 + i * w3 * w1) ^ 2 / v2 + (u3 + i * w1 * w2) ^ 2 / v3) + l := by
    suffices (u1 * w1 + u2 * w2 + u3 * w3 + 3 * i * w1 * w2 * w3) ^ 2 / (v1 * w1 ^ 2 + v2 * w2 ^ 2 + v3 * w3 ^ 2) ≤ ((u1 + i * w2 * w3) ^ 2 / v1 + (u2 + i * w3 * w1) ^ 2 / v2 + (u3 + i * w1 * w2) ^ 2 / v3) by nlinarith
    have h1 : v1 * w1 ^ 2 > 0 := by positivity
    have h2 : v2 * w2 ^ 2 > 0 := by positivity
    have h3 : v3 * w3 ^ 2 > 0 := by positivity
    have h_ := Titu_3vars (u1 * w1 + i * w1 * w2 * w3) (u2 * w2 + i * w3 * w1 * w2) (u3 * w3 + i * w1 * w2 * w3) (v1 * w1 ^ 2) (v2 * w2 ^ 2) (v3 * w3 ^ 2) h1 h2 h3
    convert h_ using 1
    field_simp [*]
    ring_nf
    field_simp [*]
    ring_nf


/-- (u1 ^ 2 * w1 / v1 + u2 ^ 2 * w2 / v2 + u3 ^ 2 * w3 / v3 -> (u1 + u2 + u3) ^ 2 / (v1 / w1 + v2 / w2 + v3 / w3) -/
theorem Titu_cycle_mul_refactor_right_3vars (u1 u2 u3 v1 v2 v3 w1 w2 w3 k l left : ℝ) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hw1 : w1 > 0) (hw2 : w2 > 0) (hw3 : w3 > 0) (hk : k > 0)
  (h : left ≤ k * ((u1 + u2 + u3) ^ 2 / (v1 / w1 + v2 / w2 + v3 / w3)) + l) :
  left ≤ k * (u1 ^ 2 * w1 / v1 + u2 ^ 2 * w2 / v2 + u3 ^ 2 * w3 / v3) + l := by
    suffices (u1 + u2 + u3) ^ 2 / (v1 / w1 + v2 / w2 + v3 / w3) ≤ (u1 ^ 2 * w1 / v1 + u2 ^ 2 * w2 / v2 + u3 ^ 2 * w3 / v3) by nlinarith
    have hv1' : v1 / w1 > 0 := by positivity
    have hv2' : v2 / w2 > 0 := by positivity
    have hv3' : v3 / w3 > 0 := by positivity
    have h_ := Titu_3vars (u1) (u2) (u3) (v1 / w1) (v2 / w2) (v3 / w3) hv1' hv2' hv3'
    convert h_ using 1
    field_simp [*]

/-- The variants of Titu inequalities: a / b -> a^2 / ab; a / b -> a^r / b^(r-1) -/
theorem Titu_variant1_right_3vars (u1 u2 u3 v1 v2 v3 k l left : ℝ) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hk : k > 0)
  (h : left ≤ k * ((u1 + u2 + u3) ^ 2 / (u1 * v1 + u2 * v2 + u3 * v3)) + l) :
  left ≤ k * (u1 / v1 + u2 / v2 + u3 / v3) + l := by
    suffices (u1 + u2 + u3) ^ 2 / (u1 * v1 + u2 * v2 + u3 * v3) ≤ (u1 / v1 + u2 / v2 + u3 / v3) by nlinarith
    sorry

theorem Titu_variant2_right_3vars (u1 u2 u3 v1 v2 v3 r k l left : ℝ) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hr : r > 0) (hk : k > 0)
  (h : left ≤ k * ((u1 ^ ((r + 1) / 2) + u2 ^ ((r + 1) / 2) + u3 ^ ((r + 1) / 2)) ^ 2 / (u1 * v1 + u2 * v2 + u3 * v3)) + l) :
  left ≤ k * (u1 ^ r / v1 + u2 ^ r / v2 + u3 ^ r / v3) + l := by
    suffices (u1 ^ ((r + 1) / 2) + u2 ^ ((r + 1) / 2) + u3 ^ ((r + 1) / 2)) ^ 2 / (u1 * v1 + u2 * v2 + u3 * v3) ≤ u1 ^ r / v1 + u2 ^ r / v2 + u3 ^ r / v3 by nlinarith
    sorry

theorem Titu_variant2_Req1_right_3vars (u1 u2 u3 v1 v2 v3 r k l left : ℝ) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hk : k > 0)
  (h : left ≤ k * ((u1 + u2 + u3) ^ 2 / (u1 * v1 + u2 * v2 + u3 * v3)) + l) :
  left ≤ k * (u1 / v1 + u2 / v2 + u3 / v3) + l := by
    have hr : (1 : ℝ) > 0 := by norm_num
    have h_ := Titu_variant2_right_3vars u1 u2 u3 v1 v2 v3 (1 : ℝ) k l left hv1 hv2 hv3 hr hk
    norm_num at h_
    apply h_
    exact h

/-- The variants of Titu inequalities: 1 / (a + bc) -> (b + c) ^ 2 / (a + bc)*(b+c)^2 --/
theorem Titu_variant3_right_3vars (u1 u2 u3 v1 v2 v3 j1 j2 j3 k l left : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hj1 : j1 > 0) (hj2 : j2 > 0) (hj3 : j3 > 0) (hk : k > 0)
  (h : left ≤ k * ((u1 + u2 + u3 + v1 + v2 + v3) ^ 2 / (((u1 * v1 + j1) * (u1 + v1) ^ 2) + ((u2 * v2 + j2) * (u2 + v2) ^ 2) + ((u3 * v3 + j3) * (u3 + v3) ^ 2))) + l) :
  left ≤ k * ((1 / (u1 * v1 + j1)) + (1 / (u2 * v2 + j2)) + (1 / (u3 * v3 + j3))) + l := by
    suffices (u1 + u2 + u3 + v1 + v2 + v3) ^ 2 / (((u1 * v1 + j1) * (u1 + v1) ^ 2) + ((u2 * v2 + j2) * (u2 + v2) ^ 2) + ((u3 * v3 + j3) * (u3 + v3) ^ 2)) ≤ ((1 / (u1 * v1 + j1)) + (1 / (u2 * v2 + j2)) + (1 / (u3 * v3 + j3))) by nlinarith
    have hv1' : (u1 * v1 + j1) * (u1 + v1) ^ 2 > 0 := by positivity
    have hv2' : (u2 * v2 + j2) * (u2 + v2) ^ 2 > 0 := by positivity
    have hv3' : (u3 * v3 + j3) * (u3 + v3) ^ 2 > 0 := by positivity
    have h_ := Titu_3vars (u1 + v1) (u2 + v2) (u3 + v3) ((u1 * v1 + j1) * (u1 + v1) ^ 2) ((u2 * v2 + j2) * (u2 + v2) ^ 2) ((u3 * v3 + j3) * (u3 + v3) ^ 2) hv1' hv2' hv3'
    convert h_ using 1
    rw[<-add_assoc]; rw[<-add_assoc]; field_simp [*]; ring_nf
    have h1 : (u1 + v1) ^ 2 / ((u1 * v1 + j1) * (u1 + v1) ^ 2) = 1 / (u1 * v1 + j1) := by
      field_simp [*]; linarith
    have h2 : (u2 + v2) ^ 2 / ((u2 * v2 + j2) * (u2 + v2) ^ 2) = 1 / (u2 * v2 + j2) := by
      field_simp [*]; linarith
    have h3 : (u3 + v3) ^ 2 / ((u3 * v3 + j3) * (u3 + v3) ^ 2) = 1 / (u3 * v3 + j3) := by
      field_simp [*]; linarith
    rw[h1, h2, h3]

end Titu_3vars

section Titu_4vars

theorem Titu_4vars (u1 u2 u3 u4 v1 v2 v3 v4 : ℝ) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hv4 : v4 > 0) : (u1 + u2 + u3 + u4) ^ 2 / (v1 + v2 + v3 + v4) ≤ (u1 ^ 2 / v1 + u2 ^ 2 / v2 + u3 ^ 2 / v3 + u4 ^ 2 / v4) := by
  sorry

theorem Titu_normal_left_4vars (u1 u2 u3 u4 v1 v2 v3 v4 k l right : ℝ) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hv4 : v4 > 0) (hk : k > 0)
  (h : k * (u1 ^ 2 / v1 + u2 ^ 2 / v2 + u3 ^ 2 / v3 + u4 ^ 2 / v4) + l ≤ right) :
  k * ((u1 + u2 + u3 + u4) ^ 2 / (v1 + v2 + v3 + v4)) + l ≤ right := by
    suffices (u1 + u2 + u3 + u4) ^ 2 / (v1 + v2 + v3 + v4) ≤ (u1 ^ 2 / v1 + u2 ^ 2 / v2 + u3 ^ 2 / v3 + u4 ^ 2 / v4) by nlinarith
    exact Titu_4vars u1 u2 u3 u4 v1 v2 v3 v4 hv1 hv2 hv3 hv4

theorem Titu_normal_right_4vars (u1 u2 u3 u4 v1 v2 v3 v4 k l left : ℝ) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hv4 : v4 > 0) (hk : k > 0)
  (h : left ≤ k * ((u1 + u2 + u3 + u4) ^ 2 / (v1 + v2 + v3 + v4)) + l) :
  left ≤ k * (u1 ^ 2 / v1 + u2 ^ 2 / v2 + u3 ^ 2 / v3 + u4 ^ 2 / v4) + l := by
    suffices (u1 + u2 + u3 + u4) ^ 2 / (v1 + v2 + v3 + v4) ≤ (u1 ^ 2 / v1 + u2 ^ 2 / v2 + u3 ^ 2 / v3 + u4 ^ 2 / v4) by nlinarith
    exact Titu_4vars u1 u2 u3 u4 v1 v2 v3 v4 hv1 hv2 hv3 hv4


/-- The variants of Titu inequalities: a / b -> a^2 / ab; a / b -> a^r / b^(r-1) -/
theorem Titu_variant1_right_4vars (u1 u2 u3 u4 v1 v2 v3 v4 k l left : ℝ) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hv4 : v4 > 0) (hk : k > 0)
  (h : left ≤ k * ((u1 + u2 + u3 + u4) ^ 2 / (u1 * v1 + u2 * v2 + u3 * v3 + u4 * v4)) + l) :
  left ≤ k * (u1 / v1 + u2 / v2 + u3 / v3 + u4 / v4) + l := by
    suffices (u1 + u2 + u3 + u4) ^ 2 / (u1 * v1 + u2 * v2 + u3 * v3 + u4 * v4) ≤ (u1 / v1 + u2 / v2 + u3 / v3 + u4 / v4) by nlinarith
    sorry

theorem Titu_variant2_right_4vars (u1 u2 u3 u4 v1 v2 v3 v4 r k l left : ℝ) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hv4 : v4 > 0) (hr : r > 0) (hk : k > 0)
  (h : left ≤ k * ((u1 ^ ((r + 1) / 2) + u2 ^ ((r + 1) / 2) + u3 ^ ((r + 1) / 2) + u4 ^ ((r + 1) / 2)) ^ 2 / (u1 * v1 + u2 * v2 + u3 * v3 + u4 * v4)) + l) :
  left ≤ k * (u1 ^ r / v1 + u2 ^ r / v2 + u3 ^ r / v3 + u4 ^ r / v4) + l := by
    suffices (u1 ^ ((r + 1) / 2) + u2 ^ ((r + 1) / 2) + u3 ^ ((r + 1) / 2) + u4 ^ ((r + 1) / 2)) ^ 2 / (u1 * v1 + u2 * v2 + u3 * v3 + u4 * v4) ≤ u1 ^ r / v1 + u2 ^ r / v2 + u3 ^ r / v3 + u4 ^ r / v4 by nlinarith
    sorry

theorem Titu_variant2_Req1_right_4vars (u1 u2 u3 u4 v1 v2 v3 v4 r k l left : ℝ) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hv4 : v4 > 0) (hk : k > 0)
  (h : left ≤ k * ((u1 + u2 + u3 + u4) ^ 2 / (u1 * v1 + u2 * v2 + u3 * v3 + u4 * v4)) + l) :
  left ≤ k * (u1 / v1 + u2 / v2 + u3 / v3 + u4 / v4) + l := by
    have hr : (1 : ℝ) > 0 := by norm_num
    have h_ := Titu_variant2_right_4vars u1 u2 u3 u4 v1 v2 v3 v4 (1 : ℝ) k l left hv1 hv2 hv3 hv4 hr hk
    norm_num at h_
    apply h_
    exact h

end Titu_4vars
