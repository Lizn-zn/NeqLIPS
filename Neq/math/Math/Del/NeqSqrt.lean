import Mathlib

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

theorem div_right_reduce (a b c: ℝ) (ha : b ≠ 0) : (a / b) * (b / c) = a / c := by
  field_simp

theorem div_left_reduce (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : (a / b) * (c / a) = c / b := by
  field_simp
  linarith

theorem sqrt_rw (a : ℝ) : a ^ (1 / 2) = sqrt a := by
  rw [sqrt_eq_rpow]

theorem sqrt_frac_rw (a b : ℝ) (ha : a ≥ 0) : sqrt (a / b) = sqrt (a) / sqrt b := by
  apply sqrt_div ha

theorem sqrt_mul_rewrite (a b : ℝ) (ha : a ≥ 0) : sqrt (a * b) = sqrt (a) * sqrt b := by
  apply sqrt_mul ha

theorem sqrt_div_rewrite (a b : ℝ) (ha : a ≥ 0) : sqrt (a / b) = sqrt (a) / sqrt b := by
  apply sqrt_div ha


theorem sqrt_div_right_reduce (a b c : ℝ) (ha : a / b ≥ 0) (hb : b ≠ 0) : sqrt (a / b) * sqrt (b / c) = sqrt (a / c) := by
  have h : sqrt ((a / b) * (b / c)) = sqrt (a / c) := by
    field_simp
  convert h using 1
  simp only [ha, sqrt_mul, <-mul_assoc]

theorem sqrt_div_left_reduce (a b c : ℝ) (ha : a / b ≥ 0) (hb : c / a ≥ 0) (hc : a ≠ 0) (hd : b ≠ 0) : sqrt (a / b) * sqrt (c / a) = sqrt (c / b) := by
  have h1 : a / b * c / a = c / b := by
    convert div_left_reduce a b c hc hd using 1
    ring
  have h2 : sqrt ((a / b) * (c / a)) = sqrt (c / b) := by
    rw [<-mul_div_assoc, h1]
  convert h2 using 1
  simp only [ha, hb, sqrt_mul]
