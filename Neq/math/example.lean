import Math

open Real

-- open Lean Parser Parser.Tactic Elab Command Elab.Tactic Meta

macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))


theorem Example_1d2a {a b c : ℝ} : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  scale Cauchy_Schwarz_left_sqrt_3vars (u1 := a) (u2 := a) (u3 := b) (v1 := c) (v2 := b) (v3 := c) (k := 1) (l := 0) (right := a ^ 2 + b ^ 2 + c ^ 2)
  scale AM_GM_left_square_2vars (u := sqrt (a^2 + a^2 + b^2)) (v := sqrt (c^2 + b^2 + c^2)) (k := 1) (l := 0) (right := a ^ 2 + b ^ 2 + c ^ 2)
  apply move_left (left:= (sqrt (a ^ 2 + a ^ 2 + b ^ 2) ^ 2 + sqrt (c ^ 2 + b ^ 2 + c ^ 2) ^ 2) / 2 ) (right:= a ^ 2 + b ^ 2 + c ^ 2);
  vanilla_simplify ( (sqrt (a ^ 2 + a ^ 2 + b ^ 2) ^ 2 + sqrt (c ^ 2 + b ^ 2 + c ^ 2) ^ 2) / 2 ) - ( a ^ 2 + b ^ 2 + c ^ 2)  = 0
