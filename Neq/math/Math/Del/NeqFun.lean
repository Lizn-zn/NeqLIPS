import Mathlib
import Lean.Elab.Command
import Lean.Elab.Tactic.BuiltinTactic

open Lean Parser.Tactic Elab Command Elab.Tactic Meta

open Real

macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

theorem fun_monotone (k r : ℝ) (hk : k > 0) (hr : r ≥ 0) : MonotoneOn (fun (u : ℝ) => k * u ^ r) ({u | u ≥ 0}) := by
  intros u hu v _ huv
  have hu : u ≥ 0 := hu
  have h : u ^ r ≤ v ^ r := by apply rpow_le_rpow hu huv hr
  have h' : k * u ^ r ≤ k * v ^ r := by nlinarith
  exact h'

theorem inst_monotone (u v k r : ℝ) (hk : k > 0) (hr : r ≥ 0) (hu : u ≥ 0) (huv : u ≤ v) : k * (u ^ r) ≤ k * (v ^ r) := by
  have h : u ^ r ≤ v ^ r := by apply rpow_le_rpow hu huv hr
  have h' : k * u ^ r ≤ k * v ^ r := by nlinarith
  exact h'

-- theorem zero_one : 0 + 1 = 1 := by simp

-- theorem pow_mul_zero (a : ℝ) (b : ℕ) : 0 * a ^ b = 0 := by
--   field_simp

-- theorem pow_inv_div (a : ℝ) (b : ℤ) (ha : a ≠ 0) : a ^ (-b) = 1 / a ^ b := by
--   field_simp [ha]
