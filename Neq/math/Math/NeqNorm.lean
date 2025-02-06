import Mathlib

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

/-
This lean file is created for expression normalization
-/

theorem zero_one : 0 + 1 = 1 := by simp

theorem pow_mul_zero (a : ℝ) (b : ℕ) : 0 * a ^ b = 0 := by
  field_simp

theorem inv_reduce (a : ℝ) : a ^ (-(1:ℤ)) = 1 / a := by
  norm_cast; field_simp;


/-
Handle the sqrt reduction
-/
theorem sqrt_reduce (a : ℝ) (h : a ≥ 0): sqrt a ^ 2 = a := by
  apply sq_sqrt h

theorem sqrt_reduce1 (a b : ℝ) (c : ℕ) (ha : a ≥ 0) (hb : b ≠ 0) (hc : b = c) : (a ^ (b⁻¹)) ^ c = a := by
  suffices h : (a ^ (b⁻¹)) ^ c = (a ^ (b⁻¹)) ^ b by
    subst hc
    simp_all only [ge_iff_le, ne_eq, Nat.cast_eq_zero, rpow_natCast]
    rw [← rpow_natCast, ← rpow_mul ha]
    simp_all only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, not_false_eq_true, IsUnit.inv_mul_cancel, rpow_one]
  rw [hc]
  norm_cast

theorem sqrt_reduce2 (a c : ℝ) (b : ℕ) (ha : a ≥ 0) (hb : c ≠ 0) (hc : b = c) : (a ^ b) ^ c⁻¹ = a := by
  suffices h : (a ^ b) ^ c⁻¹ = (a ^ c) ^ c⁻¹ by
    subst hc
    simp_all only [ge_iff_le, ne_eq, Nat.cast_eq_zero, rpow_natCast]
    rw [← rpow_natCast, ← rpow_mul ha]
    simp_all only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, not_false_eq_true, IsUnit.mul_inv_cancel, rpow_one]
  rw [<-hc]
  norm_cast

/-
Handle the fraction reduction
-/
theorem frac_reduce (a b : ℝ) (h : b ≥ 0) (h' : a ≤ 0) : a / b ≤ 0 := by
  have h : 1 / b ≥ 0 := by positivity
  have h : a * (1 / b) ≤ 0 := by nlinarith
  rw [show a / b = a * (1 / b) by field_simp]
  trivial

theorem frac_reduce' (a b : ℝ) (h : a ≥ 0) (h' : b ≤ 0) : a / b ≤ 0 := by
  have h : 1 / b ≤ 0 := by simp_all only [ge_iff_le, one_div, inv_nonpos]
  have h : a * (1 / b) ≤ 0 := by nlinarith
  rw [show a / b = a * (1 / b) by field_simp]
  trivial

theorem frac_reduce1 (a b c : ℝ) : a / c * b = a * b / c := by
  field_simp [*]

theorem frac_reduce2 (a b: ℝ) (h : a ≠ 0) : 1 / a ^ 2 * b = b / a ^ 2 := by
  field_simp [*]


theorem factor_reduce (a b : ℝ) (h : a ≥ 0) (h' : b ≤ 0) : a * b ≤ 0 := by
  nlinarith

theorem factor_reduce' (a b : ℝ) (h : b ≥ 0) (h' : a ≤ 0) : a * b ≤ 0 := by
  nlinarith

theorem factor_reduce_neg (a b : ℝ) (h : -a ≥ 0) (h' : -b ≤ 0) : a * b ≤ 0 := by
  nlinarith

theorem factor_reduce_neg' (a b : ℝ) (h : b ≥ 0) (h' : a ≤ 0) : a * b ≤ 0 := by
  nlinarith


/-
Rearrange
-/

theorem move_left (left right : ℝ) (h : left - right ≤ 0) : left ≤ right := by nlinarith

theorem move_right (left right : ℝ) (h : 0 ≤ right - left) : left ≤ right := by nlinarith

theorem rearrange (left right : ℝ) (h : left ≤ right) : left - right ≤ 0 := by nlinarith


/-
Variable cancalation lemmas
-/

theorem add6_sub_cancel3 (a b c d e f : ℝ) : a + b + c + d + e + f - c = a + b + d + e + f := by
  abel

theorem add6_sub_cancel4 (a b c d e f : ℝ) : a + b + c + d + e + f - d = a + b + c + e + f := by
  abel

theorem add6_sub_cancel5 (a b c d e f : ℝ) : a + b + c + d + e + f - e = a + b + c + d + f := by
  abel

/-
Variable cancalation lemmas
-/
theorem square_root_of_4 : (4 : ℝ) = 2 ^ 2:= by
  norm_num

theorem cubic_root_of_8 : (8 : ℝ) = 2 ^ 3:= by
  norm_num

theorem cubic_root_of_27 : (27 : ℝ) = 3 ^ 3 := by
  norm_num
