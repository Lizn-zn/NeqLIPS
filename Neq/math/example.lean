import Math

open Real

-- open Lean Parser Parser.Tactic Elab Command Elab.Tactic Meta

macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))


theorem PExample {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : 1 / (a + 2) + 1 / (b + 2) + 1 / (c + 2) ≤ 1 / (6 * sqrt (a * b) + c) + 1 / (6 * sqrt (b * c) + a) + 1 / (6 * sqrt (c * a) + b) := by
  make_homogeneous 1 / (2 * a + 2 * b + 3 * c) + 1 / (2 * a + 3 * b + 2 * c) + 1 / (3 * a + 2 * b + 2 * c) - (1 / (a + 6 * sqrt (b * c))) - (1 / (b + 6 * sqrt (a * c))) - (1 / (c + 6 * sqrt (a * b))) ≤ 0
  scale AM_GM_div_cycle_normal_right_2vars (u1 := a) (u2 := c) (u3 := c) (v1 := b) (v2 := a) (v3 := b) (i1 := 6) (i2 := 6) (i3 := 6) (j1 := c) (j2 := b) (j3 := a) (k := 1) (l := 0) (left := 1 / (2 * a + 2 * b + 3 * c) + 1 / (2 * a + 3 * b + 2 * c) + 1 / (3 * a + 2 * b + 2 * c))
