import Std
import Mathlib

import Math.NeqTricks
import Math.Del.NeqSqrt

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

/-
3 * (a * b * c) ^ (1 / 3) ≤ sqrt (a * b) + sqrt (b * c) + sqrt (c * a)
-/

theorem NEQ_amgm_variant1_left (u v w k l right : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hk : k ≥ 0)
  (h : k * ((sqrt (u * v) + sqrt (v * w) + sqrt (w * u)) / 3) + l ≤ right) : k * (u * v * w) ^ (1 / 3) + l ≤ right := by
  suffices (u * v * w) ^ (1 / 3) ≤ (sqrt (u * v) + sqrt (v * w) + sqrt (w * u)) / 3 by nlinarith
  sorry

theorem NEQ_cauchy_variant1_left (u v w k l right : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hk : k ≥ 0)
  (h : k * ((u * v + v * w + w * u) ^ 2) + l ≤ right) : k * (u * v * w) * (u * v + v * w + w * u) + l ≤ right := by
  suffices (u * v * w) * (u * v + v * w + w * u) ≤ (u * v + v * w + w * u) ^ 2 by nlinarith
  sorry
