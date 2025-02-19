import Mathlib

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

-- ========================== Vasc's inequalities ==========================

section Scale_Vasc_3vars

theorem Vasc_3vars (u v w : ℝ) (h1 : u ≥ 0) (h2 : v ≥ 0) (h3 : w ≥ 0) : (u ^ 2 + v ^ 2 + w ^ 2) ^ 2 ≥ 3 * (u ^ 3 * v + v ^ 3 * w + w ^ 3 * u) := by
  have h : 1 / 2 * (u ^ 2 - 2 * u * v + v * w - w ^ 2 + w * u) ^ 2 + 1 / 2 * (v ^ 2 - 2 * v * w + w * u - u ^ 2 + u * v) ^ 2 + 1 / 2 * (w ^ 2 - 2 * w * u + u * v - v ^ 2 + v * w) ^ 2 ≥ 0 := by positivity
  suffices (u ^ 2 + v ^ 2 + w ^ 2) ^ 2 - 3 * (u ^ 3 * v + v ^ 3 * w + w ^ 3 * u) ≥ 0 by nlinarith
  convert h using 1
  suffices (u ^ 2 + v ^ 2 + w ^ 2) ^ 2 - 3 * (u ^ 3 * v + v ^ 3 * w + w ^ 3 * u) - 1 / 2 * (u ^ 2 - 2 * u * v + v * w - w ^ 2 + w * u) ^ 2 - 1 / 2 * (v ^ 2 - 2 * v * w + w * u - u ^ 2 + u * v) ^ 2 - 1 / 2 * (w ^ 2 - 2 * w * u + u * v - v ^ 2 + v * w) ^ 2 = 0 by linarith
  ring_nf;

theorem Vasc_left_3vars (u v w k l right : ℝ) (h1 : u ≥ 0) (h2 : v ≥ 0) (h3 : w ≥ 0) (h4 : k ≥ 0)
  (h : k * (u ^ 2 + v ^ 2 + w ^ 2) ^ 2 / 3 + l ≤ right) :
  k * (u ^ 3 * v + v ^ 3 * w + w ^ 3 * u) + l ≤ right := by
  suffices (u ^ 2 + v ^ 2 + w ^ 2) ^ 2 ≥ 3 * (u ^ 3 * v + v ^ 3 * w + w ^ 3 * u) by nlinarith
  apply Vasc_3vars u v w h1 h2 h3

theorem Vasc_right_3vars (u v w k l right : ℝ) (h1 : u ≥ 0) (h2 : v ≥ 0) (h3 : w ≥ 0) (h4 : k ≥ 0)
  (h : left ≤ k * 3 * (u ^ 3 * v + v ^ 3 * w + w ^ 3 * u) + l) :
  left ≤ k * (u ^ 2 + v ^ 2 + w ^ 2) ^ 2 + l := by
  suffices (u ^ 2 + v ^ 2 + w ^ 2) ^ 2 ≥ 3 * (u ^ 3 * v + v ^ 3 * w + w ^ 3 * u) by nlinarith
  apply Vasc_3vars u v w h1 h2 h3
