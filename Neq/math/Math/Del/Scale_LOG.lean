import Mathlib

import Math.NeqNorm
import Math.NeqTricks
import Math.Del.NeqSqrt

import Math.Scale_Cauchy_Schwarz

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

/-
https://www.lkozma.net/inequalities_cheat_sheet/ineq.pdf
-/

theorem NEQ_logarithm_1vars (u : ℝ) (ha : u > 0) : 1 / sqrt (u + 1) ≤ (2 + u) / (2 + 2 * u) := by
  sorry

theorem NEQ_logarithm_left_1vars (u k l right : ℝ) (ha : u > 0) (hk : k > 0) (h : k * ((2 + u) / (2 + 2 * u)) + l ≤ right): k * (1 / sqrt (u + 1)) + l ≤ right := by
  suffices 1 / sqrt (u + 1) ≤ (2 + u) / (2 + 2 * u) by nlinarith
  exact NEQ_logarithm_1vars u ha

theorem NEQ_logarithm_right_1vars (u k l left : ℝ) (ha : u > 0) (hk : k > 0) (h : left ≤ k * (1 / sqrt (u + 1)) + l): left ≤ k * ((2 + u) / (2 + 2 * u)) + l := by
  suffices 1 / sqrt (u + 1) ≤ (2 + u) / (2 + 2 * u) by nlinarith
  exact NEQ_logarithm_1vars u ha


theorem NEQ_logarithm_minus_left_1vars (u k l right : ℝ) (ha : u > 0) (hk : k > 0) (h : k * (1 - u / (2 + 2 * u)) + l ≤ right): k * (1 / sqrt (u + 1)) + l ≤ right := by
  suffices 1 / sqrt (u + 1) ≤ 1 - u / (2 + 2 * u) by nlinarith
  suffices 1 / sqrt (u + 1) ≤ (2 + u) / (2 + 2 * u) by convert this using 1; field_simp [*]; linarith
  exact NEQ_logarithm_1vars u ha

theorem NEQ_logarithm_minus_right_1vars (u k l left : ℝ) (ha : u > 0) (hk : k > 0) (h : left ≤ k * (u / (2 + 2 * u)) + l): left ≤ k * ((u + 1 - sqrt (u + 1)) / (u + 1)) + l := by
  suffices u / (2 + 2 * u) ≤ (u + 1 - sqrt (u + 1)) / (u + 1) by nlinarith
  suffices 1 - (u + 1 - sqrt (u + 1)) / (u + 1) ≤ 1 - u / (2 + 2 * u) by nlinarith
  suffices 1 / sqrt (u + 1) ≤ (2 + u) / (2 + 2 * u) by convert this using 1; field_simp [*]; field_simp [*]; linarith
  exact NEQ_logarithm_1vars u ha
