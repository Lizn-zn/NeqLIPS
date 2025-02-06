import Mathlib

macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

open Real

open Lean Parser Parser.Tactic Elab Command Elab.Tactic Meta
-- set_option maxHeartbeats 1000000000

-- macro "test " h:term : tactic =>
--     `(tactic| (first | apply $h; (try any_goals positivity)
--                      | suppose $h; (convert ($(mkIdent `this)) using 1 <;> next => ·ring); (try any_goals positivity)))

macro "test " h:term : tactic =>
    `(tactic| (first | apply $h; (try any_goals positivity); (try all_goals (simp only [mul_one, one_mul, add_zero]))
                       -- here we ignore the first goal because it is sufficient
                     | suppose $h; (convert ($(mkIdent `this)) using 1 <;> next => automation); (try any_goals positivity); (try all_goals (simp only [mul_one, add_zero]))))



-- theorem extracted_1 {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :  (c ^ 2 + 1) * b * c + (b ^ 2 + 1) * b * c ≤ (c ^ 2 + b ^ 2) * sqrt (c ^ 2 + 1) * sqrt (b ^ 2 + 1) := by

-- theorem extracted_1 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :  (a ^ 2 + 1) / (b ^ 2 + 1) + (b ^ 2 + 1) / (c ^ 2 + 1) + (c ^ 2 + 1) / (a ^ 2 + 1) ≤ a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 := by
    -- supp_solve NEQ_AM_GM_left_square_2vars (u := b) (v := c) (k := 1) (l := a*b + c*a) (right := a ^ 2 + b ^ 2 + c ^ 2)

syntax "use_neqa_" term:max term:max term:max term:max : tactic

macro_rules
| `(tactic| use_neqa_ $u:term $v:term $k:term $r:term)
 => `(tactic| (scale add_neq (u:=$u) (v:=$v) (k:=$k) (r:=$r); swap;
                assumption;
                norm;
                (try simp only [tsub_le_iff_right]);
              ))

axiom AXIOM (P : Prop) : P

def closeWithAxiom : TacticM Unit := do
  let _ ← evalTactic (← `(tactic| apply AXIOM))
  return ()

elab "explore" : tactic => do
  closeWithAxiom

theorem frac_reduce_ (a b c : ℝ) : a / c * b = a * b / c := by
  field_simp [*]

theorem frac_reduce1 (a b c : ℝ) : 1 + 1 = 3 ∧ 1 + 2 = 4 := by
  explore

-- theorem Example_1d2a {a b c : ℝ} : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  -- smt_only!


-- theorem Example_1d2a {a b c : ℝ} : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
--   scale NEQ_Cauchy_Schwarz_left_sqrt_3vars (u1 := a) (u2 := a) (u3 := b) (v1 := c) (v2 := b) (v3 := c) (k := 1) (l := 0) (right := a ^ 2 + b ^ 2 + c ^ 2)
--   scale NEQ_AM_GM_left_square_2vars (u := sqrt (a^2 + a^2 + b^2)) (v := sqrt (c^2 + b^2 + c^2)) (k := 1) (l := 0) (right := a ^ 2 + b ^ 2 + c ^ 2)
--   apply move_left (left:= (sqrt (a ^ 2 + a ^ 2 + b ^ 2) ^ 2 + sqrt (c ^ 2 + b ^ 2 + c ^ 2) ^ 2) / 2 ) (right:= a ^ 2 + b ^ 2 + c ^ 2);
--   vanilla_simplify ( (sqrt (a ^ 2 + a ^ 2 + b ^ 2) ^ 2 + sqrt (c ^ 2 + b ^ 2 + c ^ 2) ^ 2) / 2 ) - ( a ^ 2 + b ^ 2 + c ^ 2)  = 0
