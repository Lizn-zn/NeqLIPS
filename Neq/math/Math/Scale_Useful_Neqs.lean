import Mathlib
import Math.Scale_Rearrange

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

/-- some neqs from https://www.lkozma.net/inequalities_cheat_sheet/ineq.pdf
  We need this part is due to mostly scaling are homogeneous,
  so we need some non-homogeneous neqs to scale.
-/

theorem cancel_pow5_right_1vars (u i j k l left : ℝ) (hk : k > 0) (hi : i > 0) (hu : u ≥ 0) (h : left ≤ k * (i * (u ^ 3 + u ^ 2 - 1) + j)) :
  left ≤ k * (i * u ^ 5 + j) := by
  suffices i * (u ^ 3 + u ^ 2 - 1) + j ≤ i * u ^ 5 + j by nlinarith
  suffices u ^ 3 + u ^ 2 ≤ u ^ 5 + 1 by nlinarith
  suffices u ^ 3 * (u ^ 2 - 1) ≥ u ^ 2 - 1 by nlinarith
  by_cases h_ : u > 1
  have h' : (u ^ 2 - 1 > 0) := by nlinarith
  suffices u ^ 3 ≥ 1 by nlinarith
  nlinarith
  have h' : (u ^ 2 - 1 ≤ 0) := by nlinarith
  suffices u ^ 3 ≤ 1 by nlinarith
  nlinarith
