import Mathlib

open Real


set_option maxHeartbeats 0

set_option linter.unusedVariables false
-- set_option by_axiom true
#eval use_axiom

macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

theorem P1 {a b c : ℝ} : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have h := Rearrange_cycle_mul_right_3vars (u := a) (v := b) (w := c) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := 1) (l := 0) (left := a * b + b * c + c * a)
  -- scale Rearrange_cycle_mul_right_3vars (u := a) (v := b) (w := c) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := 1) (l := 0) (left := a * b + b * c + c * a)
  suppose Rearrange_cycle_mul_right_3vars (u := a) (v := b) (w := c) (i1 := 1) (j1 := 0) (i2 := 1) (j2 := 0) (k := 1) (l := 0) (left := a * b + b * c + c * a)
