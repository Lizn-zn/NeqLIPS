import Mathlib

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

section Holder_3vars
/-
  The basic format of Holder's Inequality
-/
theorem Holder_2R_2vars (u1 u2 u3 v1 v2 v3 r1 r2 : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hr1 : r1 > 0) (hr2 : r2 > 0) :
  u1 ^ (r1 / (r1 + r2)) * v1 ^ (r2 / (r1 + r2)) + u2 ^ (r1  / (r1 + r2)) * v2 ^ (r2 / (r1 + r2)) + u3 ^ (r1 / (r1 + r2)) * v3 ^ (r2 / (r1 + r2)) ≤ (u1 + u2 + u3) ^ (r1 / (r1 + r2)) * (v1 + v2 + v3) ^ (r2 / (r1 + r2)) := by
  sorry

theorem Holder_2R_left_2vars (u1 u2 u3 v1 v2 v3 r1 r2 k l right : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hr1 : r1 > 0) (hr2 : r2 > 0) (hk : k ≥ 0) (hsum : r1 + r2 = 1)
  (h : k * (u1 + u2 + u3) ^ r1 * (v1 + v2 + v3) ^ r2 + l ≤ right) :
  k * (u1 ^ r1 * v1 ^ r2 + u2 ^ r1 * v2 ^ r2 + u3 ^ r1 * v3 ^ r2) + l ≤ right := by
    suffices u1 ^ r1 * v1 ^ r2 + u2 ^ r1 * v2 ^ r2 + u3 ^ r1 * v3 ^ r2 ≤ (u1 + u2 + u3) ^ r1 * (v1 + v2 + v3) ^ r2 by nlinarith
    have h := Holder_2R_2vars u1 u2 u3 v1 v2 v3 r1 r2 hu1 hu2 hu3 hv1 hv2 hv3 hr1 hr2
    rw [hsum] at h
    field_simp at h
    exact h

theorem Holder_2R_right_2vars (u1 u2 u3 v1 v2 v3 r1 r2 k l left : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hr1 : r1 > 0) (hr2 : r2 > 0) (hk : k ≥ 0)
  (h : left ≤ k * (u1 ^ (r1 / (r1 + r2)) * v1 ^ (r2 / (r1 + r2)) + u2 ^ (r1  / (r1 + r2)) * v2 ^ (r2 / (r1 + r2)) + u3 ^ (r1 / (r1 + r2)) * v3 ^ (r2 / (r1 + r2))) ^ (r1 + r2) + l) :
  left ≤ k * (u1 + u2 + u3) ^ r1 * (v1 + v2 + v3) ^ r2 + l := by
  suffices (u1 ^ (r1 / (r1 + r2)) * v1 ^ (r2 / (r1 + r2)) + u2 ^ (r1  / (r1 + r2)) * v2 ^ (r2 / (r1 + r2)) + u3 ^ (r1 / (r1 + r2)) * v3 ^ (r2 / (r1 + r2))) ^ (r1 + r2) ≤ (u1 + u2 + u3) ^ r1 * (v1 + v2 + v3) ^ r2 by nlinarith
  have h := Holder_2R_2vars u1 u2 u3 v1 v2 v3 r1 r2 hu1 hu2 hu3 hv1 hv2 hv3 hr1 hr2
  rw [<-rpow_le_rpow_iff (z := 1 / (r1 + r2))]
  convert h using 1
  rw [<-rpow_mul]; field_simp [*]
  positivity
  rw [mul_rpow]
  rw [<-rpow_mul]; rw [<-rpow_mul]; field_simp [*]
  all_goals positivity

theorem Holder_3R_3vars (u1 u2 v1 v2 w1 w2 r1 r2 r3 : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hw1 : w1 > 0) (hw2 : w2 > 0) (hr1 : r1 > 0) (hr2 : r2 > 0) (hr3 : r3 > 0) :
  u1 ^ (r1 / (r1 + r2 + r3)) * v1 ^ (r2 / (r1 + r2 + r3)) * w1 ^ (r3 / (r1 + r2 + r3)) + u2 ^ (r1  / (r1 + r2 + r3)) * v2 ^ (r2 / (r1 + r2 + r3)) * w2 ^ (r3 / (r1 + r2 + r3)) ≤ (u1 + u2) ^ (r1 / (r1 + r2 + r3)) * (v1 + v2) ^ (r2 / (r1 + r2 + r3)) * (w1 + w2) ^ (r3 / (r1 + r2 + r3)) := by
  sorry

theorem Holder_3R_left_3vars (u1 u2 v1 v2 w1 w2 r1 r2 r3 k l right : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hw1 : w1 > 0) (hw2 : w2 > 0) (hr1 : r1 > 0) (hr2 : r2 > 0) (hr3 : r3 > 0) (hk : k ≥ 0) (hsum : r1 + r2 + r3 = 1)
  (h : k * (u1 + u2) ^ r1 * (v1 + v2) ^ r2 * (w1 + w2) ^ r3 + l ≤ right) :
  k * (u1 ^ r1 * v1 ^ r2 * w1 ^ r3 + u2 ^ r1 * v2 ^ r2 * w2 ^ r3) + l ≤ right := by
    suffices u1 ^ r1 * v1 ^ r2 * w1 ^ r3 + u2 ^ r1 * v2 ^ r2 * w2 ^ r3 ≤ (u1 + u2) ^ r1 * (v1 + v2) ^ r2 * (w1 + w2) ^ r3 by nlinarith
    have h := Holder_3R_3vars u1 u2 v1 v2 w1 w2 r1 r2 r3 hu1 hu2 hv1 hv2 hw1 hw2 hr1 hr2 hr3
    rw [hsum] at h
    field_simp at h
    exact h

theorem Holder_3R_right_3vars (u1 u2 v1 v2 w1 w2 r1 r2 r3 k l left : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hw1 : w1 > 0) (hw2 : w2 > 0) (hr1 : r1 > 0) (hr2 : r2 > 0) (hr3 : r3 > 0) (hk : k ≥ 0)
  (h : left ≤ k * (u1 ^ (r1 / (r1 + r2 + r3)) * v1 ^ (r2 / (r1 + r2 + r3)) * w1 ^ (r3 / (r1 + r2 + r3)) + u2 ^ (r1  / (r1 + r2 + r3)) * v2 ^ (r2 / (r1 + r2 + r3)) * w2 ^ (r3 / (r1 + r2 + r3))) ^ (r1 + r2 + r3) + l) :
  left ≤ k * (u1 + u2) ^ r1 * (v1 + v2) ^ r2 * (w1 + w2) ^ r3 + l := by
  suffices (u1 ^ (r1 / (r1 + r2 + r3)) * v1 ^ (r2 / (r1 + r2 + r3)) * w1 ^ (r3 / (r1 + r2 + r3)) + u2 ^ (r1  / (r1 + r2 + r3)) * v2 ^ (r2 / (r1 + r2 + r3)) * w2 ^ (r3 / (r1 + r2 + r3))) ^ (r1 + r2 + r3) ≤ (u1 + u2) ^ r1 * (v1 + v2) ^ r2 * (w1 + w2) ^ r3 by nlinarith
  have h := Holder_3R_3vars u1 u2 v1 v2 w1 w2 r1 r2 r3 hu1 hu2 hv1 hv2 hw1 hw2 hr1 hr2 hr3
  rw [<-rpow_le_rpow_iff (z := 1 / (r1 + r2 + r3))]
  convert h using 1
  rw [<-rpow_mul];  field_simp [*]
  positivity
  rw [mul_rpow]; rw [mul_rpow]
  rw [<-rpow_mul]; rw [<-rpow_mul]; rw [<-rpow_mul]; field_simp [*]
  all_goals positivity

/-
This is a specific but general version
(u1/v1 + u2/v2 + u3/v3)^(2/3) * (u1*v1^2 + u2*v2^2 + u3*v3^2)^(1/3) ≥ (u1 + u2 + u3)
-/
theorem Holder_2R_div_variant1_right_3vars (u1 u2 u3 v1 v2 v3 k l left : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hk : k ≥ 0)
  (h : left ≤ k * sqrt ((u1 + u2 + u3) ^ 3 / (u1 * v1 ^ 2 + u2 * v2 ^ 2 + u3 * v3 ^ 2)) + l) :
  left ≤ k * (u1 / v1 + u2 / v2 + u3 / v3) + l := by
  suffices sqrt ((u1 + u2 + u3) ^ 3 / (u1 * v1 ^ 2 + u2 * v2 ^ 2 + u3 * v3 ^ 2)) ≤ (u1 / v1 + u2 / v2 + u3 / v3) by nlinarith
  rw [<-rpow_le_rpow_iff (z := 2)]
  have ht := sq_sqrt (x := (u1 + u2 + u3) ^ 3 / (u1 * v1 ^ 2 + u2 * v2 ^ 2 + u3 * v3 ^ 2))
  rw [show sqrt ((u1 + u2 + u3) ^ 3 / (u1 * v1 ^ 2 + u2 * v2 ^ 2 + u3 * v3 ^ 2)) ^ (2 : ℕ) = sqrt ((u1 + u2 + u3) ^ 3 / (u1 * v1 ^ 2 + u2 * v2 ^ 2 + u3 * v3 ^ 2)) ^ (2 : ℝ) by norm_num] at ht
  rw [ht]
  rw [<- mul_le_mul_right (a := (u1 * v1 ^ 2 + u2 * v2 ^ 2 + u3 * v3 ^ 2))]
  have hr1 : (1 : ℝ) > 0 := by norm_num
  have hr2 : (2 : ℝ) > 0 := by norm_num
  have hu1 : (u1 / v1) > 0 := by positivity
  have hu2 : (u2 / v2) > 0 := by positivity
  have hu3 : (u3 / v3) > 0 := by positivity
  have hv1 : u1 * v1 ^ 2 > 0 := by positivity
  have hv2 : u2 * v2 ^ 2 > 0 := by positivity
  have hv3 : u3 * v3 ^ 2 > 0 := by positivity
  have h := Holder_2R_2vars (u1/v1) (u2/v2) (u3/v3) (u1*v1^2) (u2*v2^2) (u3*v3^2) 2 1 hu1 hu2 hu3 hv1 hv2 hv3 hr2 hr1
  norm_num at h
  rw [<-rpow_le_rpow_iff (z := 3)] at h
  rw [mul_rpow] at h
  convert h using 1
  field_simp [*]
  have h : (u1 / v1) ^ (2 / 3) * (u1 ^ (1 / 3) * (v1 ^ 2) ^ (1 / 3)) = u1 := by
    rw [<-mul_assoc]; rw [div_rpow]; field_simp [*]; rw [<-rpow_add]; norm_num;
    rw [show v1 ^ (2 : ℕ) = v1 ^ (2 : ℝ) by norm_num]; rw [<-rpow_mul]; norm_num; all_goals positivity
  rw [h]
  have h : (u2 / v2) ^ (2 / 3) * (u2 * v2 ^ 2) ^ (1 / 3) = u2 := by
    rw [mul_rpow]; rw [<-mul_assoc]; rw [div_rpow]; field_simp [*]; rw [<-rpow_add]; norm_num;
    rw [show v2 ^ (2 : ℕ) = v2 ^ (2 : ℝ) by norm_num]; rw [<-rpow_mul]; norm_num; all_goals positivity
  rw [h]
  have h : (u3 / v3) ^ (2 / 3) * (u3 * v3 ^ 2) ^ (1 / 3) = u3 := by
    rw [mul_rpow]; rw [<-mul_assoc]; rw [div_rpow]; field_simp [*]; rw [<-rpow_add]; norm_num;
    rw [show v3 ^ (2 : ℕ) = v3 ^ (2 : ℝ) by norm_num]; rw [<-rpow_mul]; norm_num; all_goals positivity
  rw [h]
  norm_cast
  rw [mul_rpow]; rw [<-rpow_mul]; rw [<-rpow_mul];
  norm_num
  all_goals positivity

/-
This is a specific but general version
(u1/v1 + u2/v2 + u3/v3)^(2/3) * (v1^2 + v2^2 + v3^2)^(1/3) ≥ (u1^(2/3) + u2^(2/3) + u3^(2/3))
-/
theorem Holder_2R_div_variant2_right_3vars (u1 u2 u3 v1 v2 v3 k l left : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hk : k ≥ 0)
  (h : left ≤ k * sqrt ((u1 ^ (2 / 3) + u2 ^ (2 / 3) + u3 ^ (2 / 3)) ^ 3 / (v1 ^ 2 + v2 ^ 2 + v3 ^ 2)) + l) :
  left ≤ k * (u1 / v1 + u2 / v2 + u3 / v3) + l := by
  suffices sqrt ((u1 ^ (2 / 3) + u2 ^ (2 / 3) + u3 ^ (2 / 3)) ^ 3 / (v1 ^ 2 + v2 ^ 2 + v3 ^ 2)) ≤ (u1 / v1 + u2 / v2 + u3 / v3) by nlinarith
  rw [<-rpow_le_rpow_iff (z := 2)]
  have ht := sq_sqrt (x := (u1 ^ (2 / 3) + u2 ^ (2 / 3) + u3 ^ (2 / 3)) ^ 3 / (v1 ^ 2 + v2 ^ 2 + v3 ^ 2))
  rw [show sqrt ((u1 ^ (2 / 3) + u2 ^ (2 / 3) + u3 ^ (2 / 3)) ^ 3 / (v1 ^ 2 + v2 ^ 2 + v3 ^ 2)) ^ (2 : ℕ) = sqrt ((u1 ^ (2 / 3) + u2 ^ (2 / 3) + u3 ^ (2 / 3)) ^ 3 / (v1 ^ 2 + v2 ^ 2 + v3 ^ 2)) ^ (2 : ℝ) by norm_num] at ht
  rw [ht]
  rw [<- mul_le_mul_right (a := (v1 ^ 2 + v2 ^ 2 + v3 ^ 2))]
  have hr1 : (1 : ℝ) > 0 := by norm_num
  have hr2 : (2 : ℝ) > 0 := by norm_num
  have hu1 : (u1 / v1) > 0 := by positivity
  have hu2 : (u2 / v2) > 0 := by positivity
  have hu3 : (u3 / v3) > 0 := by positivity
  have hv1 : v1 ^ 2 > 0 := by positivity
  have hv2 : v2 ^ 2 > 0 := by positivity
  have hv3 : v3 ^ 2 > 0 := by positivity
  have h := Holder_2R_2vars (u1/v1) (u2/v2) (u3/v3) (v1^2) (v2^2) (v3^2) 2 1 hu1 hu2 hu3 hv1 hv2 hv3 hr2 hr1
  norm_num at h
  rw [<-rpow_le_rpow_iff (z := 3)] at h
  rw [mul_rpow] at h
  convert h using 1
  field_simp [*]
  have h : (u1 / v1) ^ (2 / 3) * ((v1 ^ 2) ^ (1 / 3)) = u1 ^ (2 / 3) := by
    rw [div_rpow]; field_simp [*];
    rw [show v1 ^ (2 : ℕ) = v1 ^ (2 : ℝ) by norm_num]; rw [<-rpow_mul]; norm_num; all_goals positivity
  rw [h]
  have h : (u2 / v2) ^ (2 / 3) * ((v2 ^ 2) ^ (1 / 3)) = u2 ^ (2 / 3) := by
    rw [div_rpow]; field_simp [*];
    rw [show v2 ^ (2 : ℕ) = v2 ^ (2 : ℝ) by norm_num]; rw [<-rpow_mul]; norm_num; all_goals positivity
  rw [h]
  have h : (u3 / v3) ^ (2 / 3) * ((v3 ^ 2) ^ (1 / 3)) = u3 ^ (2 / 3) := by
    rw [div_rpow]; field_simp [*];
    rw [show v3 ^ (2 : ℕ) = v3 ^ (2 : ℝ) by norm_num]; rw [<-rpow_mul]; norm_num; all_goals positivity
  rw [h]
  norm_cast
  rw [<-rpow_mul]; rw [<-rpow_mul];
  norm_num
  all_goals positivity

/-- This is a specific but general version (u1/(v1^p*w1^q) + u2/(v2^p*w2^q) + u3/(v3^p*w3^q))^(1/3) * (v1^(p/2)*w1 + v2^(p/2)*w2 + v3^(p/2)*w3)^(2/3) ≥ (u1*w1^q/w1^(2/3)))^(1/3) + (u2*w2^q/w2^(2/3)))^(1/3) + (u3*w3^q/w3^(2/3)))^(1/3) -/
theorem Holder_2R_pq_div_variant1_right_3vars (u1 u2 u3 v1 v2 v3 w1 w2 w3 p q k l left : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hw1 : w1 > 0) (hw2 : w2 > 0) (hw3 : w3 > 0) (hp : p > 0) (hq : q > 0) (hk : k ≥ 0)
  (h : left ≤ k * (((u1 / w1 ^ (q - 2)) ^ (1 / 3) + (u2 / w2 ^ (q - 2)) ^ (1 / 3) + (u3 / w3 ^ (q - 2)) ^ (1 / 3)) ^ 3 / (v1 ^ (p / 2) * w1 + v2 ^ (p / 2) * w2 + v3 ^ (p / 2) * w3) ^ 2) + l) :
  left ≤ k * (u1 / (v1 ^ p * w1 ^ q) + u2 / (v2 ^ p * w2 ^ q) + u3 / (v3 ^ p * w3 ^ q)) + l := by
  sorry

theorem Holder_2R_pq_div_Peq1_right_3vars (u1 u2 u3 v1 v2 v3 w1 w2 w3 q k l left : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hw1 : w1 > 0) (hw2 : w2 > 0) (hw3 : w3 > 0) (hq : q > 0) (hk : k ≥ 0)
  (h : left ≤ k * (((u1 / w1 ^ (q - 2)) ^ (1 / 3) + (u2 / w2 ^ (q - 2)) ^ (1 / 3) + (u3 / w3 ^ (q - 2)) ^ (1 / 3)) ^ 3 / (v1 ^ (1 / 2) * w1 + v2 ^ (1 / 2) * w2 + v3 ^ (1 / 2) * w3) ^ 2) + l) :
  left ≤ k * (u1 / (v1 * w1 ^ q) + u2 / (v2 * w2 ^ q) + u3 / (v3 * w3 ^ q)) + l := by
  have hp : (1 : ℝ) > 0 := by norm_num
  have h := Holder_2R_pq_div_variant1_right_3vars u1 u2 u3 v1 v2 v3 w1 w2 w3 (1 : ℝ) q k l left hu1 hu2 hu3 hv1 hv2 hv3 hw1 hw2 hw3 hp hq hk h
  norm_num at h
  exact h

theorem Holder_2R_pq_div_Qeq1_right_3vars (u1 u2 u3 v1 v2 v3 w1 w2 w3 p q k l left : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hw1 : w1 > 0) (hw2 : w2 > 0) (hw3 : w3 > 0) (hp : p > 0) (hk : k ≥ 0)
  (h : left ≤ k * (((u1 * w1) ^ (1 / 3) + (u2 * w2) ^ (1 / 3) + (u3 * w3) ^ (1 / 3)) ^ 3 / (v1 ^ (p / 2) * w1 + v2 ^ (p / 2) * w2 + v3 ^ (p / 2) * w3) ^ 2) + l) :
  left ≤ k * (u1 / (v1 ^ p * w1) + u2 / (v2 ^ p * w2) + u3 / (v3 ^ p * w3)) + l := by
  have hq : (1 : ℝ) > 0 := by norm_num
  have h_ := Holder_2R_pq_div_variant1_right_3vars u1 u2 u3 v1 v2 v3 w1 w2 w3 p (1 : ℝ) k l left hu1 hu2 hu3 hv1 hv2 hv3 hw1 hw2 hw3 hp hq hk
  norm_num at h_
  simp [rpow_neg_one] at h_
  simp [rpow_neg_one] at h
  apply h_
  exact h

theorem Holder_2R_qp_div_variant1_right_3vars (u1 u2 u3 v1 v2 v3 w1 w2 w3 p q k l left : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hw1 : w1 > 0) (hw2 : w2 > 0) (hw3 : w3 > 0) (hp : p > 0) (hq : q > 0) (hk : k ≥ 0)
  (h : left ≤ k * (((u1 / v1 ^ (p - 2)) ^ (1 / 3) + (u2 / v2 ^ (p - 2)) ^ (1 / 3) + (u3 / v3 ^ (p - 2)) ^ (1 / 3)) ^ 3 / (v1 * w1 ^ (q / 2) + v2 * w2 ^ (q / 2) + v3 * w3 ^ (q / 2)) ^ 2) + l) :
  left ≤ k * (u1 / (v1 ^ p * w1 ^ q) + u2 / (v2 ^ p * w2 ^ q) + u3 / (v3 ^ p * w3 ^ q)) + l := by
  sorry

theorem Holder_2R_qp_div_Peq1_right_3vars (u1 u2 u3 v1 v2 v3 w1 w2 w3 q k l left : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hw1 : w1 > 0) (hw2 : w2 > 0) (hw3 : w3 > 0) (hq : q > 0) (hk : k ≥ 0)
  (h : left ≤ k * (((u1 * v1) ^ (1 / 3) + (u2 * v2) ^ (1 / 3) + (u3 * v3) ^ (1 / 3)) ^ 3 / (v1 * w1 ^ (q / 2) + v2 * w2 ^ (q / 2) + v3 * w3 ^ (q / 2)) ^ 2) + l) :
  left ≤ k * (u1 / (v1 * w1 ^ q) + u2 / (v2 * w2 ^ q) + u3 / (v3 * w3 ^ q)) + l := by
  have hp : (1 : ℝ) > 0 := by norm_num
  have h_ := Holder_2R_qp_div_variant1_right_3vars u1 u2 u3 v1 v2 v3 w1 w2 w3 (1 : ℝ) q k l left hu1 hu2 hu3 hv1 hv2 hv3 hw1 hw2 hw3 hp hq hk
  norm_num at h_
  simp [rpow_neg_one] at h_
  simp [rpow_neg_one] at h
  apply h_
  exact h

theorem Holder_2R_qp_div_Qeq1_right_3vars (u1 u2 u3 v1 v2 v3 w1 w2 w3 p k l left : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hw1 : w1 > 0) (hw2 : w2 > 0) (hw3 : w3 > 0) (hp : p > 0) (hk : k ≥ 0)
  (h : left ≤ k * (((u1 / v1 ^ (p - 2)) ^ (1 / 3) + (u2 / v2 ^ (p - 2)) ^ (1 / 3) + (u3 / v3 ^ (p - 2)) ^ (1 / 3)) ^ 3 / (v1 * w1 ^ (1 / 2) + v2 * w2 ^ (1 / 2) + v3 * w3 ^ (1 / 2)) ^ 2) + l) :
  left ≤ k * (u1 / (v1 ^ p * w1) + u2 / (v2 ^ p * w2) + u3 / (v3 ^ p * w3)) + l := by
  have hq : (1 : ℝ) > 0 := by norm_num
  have h_ := Holder_2R_qp_div_variant1_right_3vars u1 u2 u3 v1 v2 v3 w1 w2 w3 p (1 : ℝ) k l left hu1 hu2 hu3 hv1 hv2 hv3 hw1 hw2 hw3 hp hq hk h
  norm_num at h_
  exact h_

end Holder_3vars

section Holder_4vars

/-
This is a specific but general version
(u1/v1 + u2/v2 + u3/v3 + u4/v4)^(3/4) * (u1*v1^3 + u2*v2^3 + u3*v3^3 + u4*v4^3)^(1/4) ≥ (u1 + u2 + u3 + u4)
-/
theorem Holder_2R_div_variant1_right_4vars (u1 u2 u3 u4 v1 v2 v3 v4 k l left : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hu4 : u4 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hv4 : v4 > 0) (hk : k ≥ 0)
  (h : left ≤ k * ((u1 + u2 + u3 + u4) ^ 4 / (u1 * v1 ^ 3 + u2 * v2 ^ 3 + u3 * v3 ^ 3 + u4 * v4 ^ 3)) ^ (1 / 3) + l) :
  left ≤ k * (u1 / v1 + u2 / v2 + u3 / v3 + u4 / v4) + l := by
  suffices ((u1 + u2 + u3 + u4) ^ 4 / (u1 * v1 ^ 3 + u2 * v2 ^ 3 + u3 * v3 ^ 3 + u4 * v4 ^ 3)) ^ (1 / 3) ≤ (u1 / v1 + u2 / v2 + u3 / v3 + u4 / v4) by nlinarith
  sorry

/-
This is a specific but general version
(u1/v1 + u2/v2 + u3/v3 + u4/v4)^(3/4) * (v1^3 + v2^3 + v3^3 + v4^3)^(1/4) ≥ (u1^(3/4) + u2^(3/4) + u3^(3/4) + u4^(3/4))
-/
theorem Holder_2R_div_variant2_right_4vars (u1 u2 u3 u4 v1 v2 v3 v4 k l left : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hu4 : u4 > 0) (hv1 : v1 > 0) (hv2 : v2 > 0) (hv3 : v3 > 0) (hv4 : v4 > 0) (hk : k ≥ 0)
  (h : left ≤ k * (((u1 ^ (3 / 4) + u2 ^ (3 / 4) + u3 ^ (3 / 4) + u4 ^ (3 / 4)) ^ 4 / (v1 ^ 3 + v2 ^ 3 + v3 ^ 3 + v4 ^ 3)) ^ (1 / 3)) + l) :
  left ≤ k * (u1 / v1 + u2 / v2 + u3 / v3 + u4 / v4) + l := by
  suffices ((u1 ^ (3 / 4) + u2 ^ (3 / 4) + u3 ^ (3 / 4) + u4 ^ (3 / 4)) ^ 4 / (v1 ^ 3 + v2 ^ 3 + v3 ^ 3 + v4 ^ 3)) ^ (1 / 3) ≤ (u1 / v1 + u2 / v2 + u3 / v3 + u4 / v4) by nlinarith
  sorry


end Holder_4vars
