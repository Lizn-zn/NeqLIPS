import Mathlib
import Lean.Elab.Command
import Lean.Elab.Tactic.BuiltinTactic

import Smt

import Math.NeqNorm

open Lean Parser Parser.Tactic Elab Command Elab.Tactic Meta
open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

/--
Define a dummy axiom to close the goal
--/
axiom AXIOM (P : Prop) : P

def closeWithAxiom : TacticM Unit := do
  let _ ← evalTactic (← `(tactic| apply AXIOM))
  return ()

elab "closed_by_axiom" : tactic => do
  closeWithAxiom

register_option by_axiom : Bool := {
  defValue := true
  group := "proof"
  descr := "use axiom to close the goal"
}

def use_axiom : MetaM Bool := do
  let opts ← getOptions
  return opts.getBool by_axiom.name by_axiom.defValue

elab "check_goal_nums " n:num : tactic => do
  let numGoals := (← getGoals).length
  guard (numGoals <= n.getNat) <|>
    throwError "expected <= {n.getNat} goals but found {numGoals}"

/-
augmented versions of some fundmental tactics: (1) suppose; (2) rewrite with positivity
-/

macro "norm_expr" : tactic =>
  `(tactic| ((try any_goals simp only [<-mul_assoc, <-add_assoc]);
              (try any_goals norm_cast); -- normalize before simp
              (try (simp only [zero_add, add_zero, mul_zero, zero_mul])); --handle zero
              (try (simp only [mul_one, one_mul, div_one, pow_mul_zero, pow_one, one_pow, rpow_one, one_rpow])); --handle one
              (try (simp only [<-sub_eq_add_neg, Int.reduceNegSucc, Int.cast_neg, Int.cast_one])); --handle negone
              (try (simp only [Int.subNatNat, Int.cast_subNatNat, Nat.cast_ofNat]));--cast_Nat
              (try (simp only [inv_reduce])); --handle inv
              (try norm_num1); --normalize after simp
              (try push_cast);
            ))

def suppose (mvarId : MVarId) (e : Expr) : MetaM (List MVarId) := do
  -- convert a -> b |- c into |- a and b |- c
  mvarId.withContext do
    -- Check that the goal is not yet assigned.
    mvarId.checkNotAssigned `suppose
    let eType ← inferType e
    let (_, _, conclusion) ← forallMetaTelescopeReducing eType
    let p ← mkFreshExprMVar conclusion MetavarKind.syntheticOpaque `admitGoal
    let (_, mvarIdNew) ← MVarId.intro1P $ ← mvarId.assert `this conclusion p
    let admitGoal := p.mvarId!
    admitGoal.withContext do
      let target ← admitGoal.getType
      let eType ← inferType e
      let (args, _, conclusion) ← forallMetaTelescopeReducing eType
      if ← isDefEq target conclusion then
        admitGoal.assign (mkAppN e args)
        let newGoals ← args.filterMapM λ mvar => do
          let mvarId := mvar.mvarId!
          if ! (← mvarId.isAssigned) && ! (← mvarId.isDelayedAssigned) then
            return some mvarId
          else
            return none
        return mvarIdNew :: newGoals.toList
      else
        throwTacticEx `Apply admitGoal m!"{e} is not applicable to goal with target {target}"
    -- return p.mvarId! :: mvarIdNew :: newGoals.toList

elab "suppose" e:term : tactic => do
  let e ← Elab.Term.elabTerm e none
  Elab.Tactic.liftMetaTactic (suppose · e)

macro "rwp_base" s:rwRuleSeq : tactic =>
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    `(tactic| (first | rewrite [$rs,*]; (try any_goals positivity); (try any_goals linarith); with_annotate_state $rbrak (try (with_reducible rfl));
                     | rewrite [add_assoc,$rs,*]; (try any_goals positivity); (try any_goals linarith); norm_expr; with_annotate_state $rbrak (try (with_reducible rfl));
                     | rewrite [mul_assoc,$rs,*]; (try any_goals positivity); (try any_goals linarith); norm_expr; with_annotate_state $rbrak (try (with_reducible rfl));))
  | _ => Macro.throwUnsupported

elab "rw_add_assoc " e:rwRuleSeq : tactic => do
  let mut success := false
  let mut s <- saveState
  for i in [1:10] do
    let u := Syntax.mkNumLit (toString i)
    try
      Tactic.evalTactic (← `(tactic| nth_rw $u:num [add_assoc]))
    catch _ =>
      restoreState s
      break
    try
      match e with
        | `(rwRuleSeq| [$rs,*]) => Tactic.evalTactic (← `(tactic| rewrite [$rs,*]))
        | _ => throwError "expected type rwRuleSeq"
      s <- saveState
      success := true
    catch _ =>
      restoreState s
  if success = true then
    Tactic.evalTactic (← `(tactic| (try any_goals positivity); (try any_goals linarith); norm_expr))
  else
    throwError m!"tactic 'rewrite' failed, did not find instance of the pattern in the target expression {e}"

elab "rw_mul_assoc " e:rwRuleSeq : tactic => do
  let mut success := false
  let mut s <- saveState
  for i in [1:10] do
    let u := Syntax.mkNumLit (toString i)
    try
      Tactic.evalTactic (← `(tactic| nth_rw $u:num [mul_assoc]))
    catch _ =>
      restoreState s
      break
    try
      match e with
        | `(rwRuleSeq| [$rs,*]) => Tactic.evalTactic (← `(tactic| rewrite [$rs,*]))
        | _ => throwError "expected type rwRuleSeq"
      s <- saveState
      success := true
    catch _ =>
      restoreState s
  if success = true then
    Tactic.evalTactic (← `(tactic| (try any_goals positivity); (try any_goals linarith); norm_expr))
  else
    throwError m!"tactic 'rewrite' failed, did not find instance of the pattern in the target expression {e}"

elab "rw_base " e:rwRuleSeq : tactic => do
  let mut success := false
  let s <- saveState
  try
    match e with
      | `(rwRuleSeq| [$rs,*]) => Tactic.evalTactic (← `(tactic| rewrite [$rs,*]))
      | _ => throwError "expected type rwRuleSeq"
    success := true
  catch _ =>
    restoreState s
  if success = true then
    Tactic.evalTactic (← `(tactic| (try any_goals positivity); (try any_goals linarith); norm_expr))
  else
    throwError m!"tactic 'rewrite' failed, did not find instance of the pattern in the target expression {e}"

macro "rwp" s:rwRuleSeq : tactic =>
  `(tactic| (first | rw_base $s | rw_add_assoc $s | rw_mul_assoc $s))


/-
Normalization tactics
-/

macro "norm_sqrt" : tactic =>
  `(tactic| (norm_expr;
              (try (repeat rwp [sqrt_reduce]));
              (try (repeat rwp [sqrt_reduce1]));
              (try (repeat rwp [sqrt_reduce2]));
            ))

macro "norm_frac" : tactic =>
  `(tactic| (norm_expr;
              (try (repeat rwp [frac_reduce]));
              (try (repeat rwp [frac_reduce1]));
              (try (repeat rwp [frac_reduce2]));
            ))


/-
automation tactics for scaling
-/

macro "auto_verify" : tactic =>
  `(tactic| first | ·(norm_cast; push_cast; norm_num;
                      (first
                       | done
                       | linarith
                       | ring_nf
                       | (field_simp (config := {decide := true}))
                       | (ring_nf; field_simp (config := {decide := true}))
                       | polyrith
                      )
                      field_simp (config := {decide := true}) [*]; linarith
                    )
                  | smt_decide!
              )

elab "automation " : tactic => do
  if !(← getBoolOption `by_axiom by_axiom.defValue) then
    Tactic.evalTactic (← `(tactic| auto_verify;))
  else
    Tactic.evalTactic (← `(tactic| closed_by_axiom;))


macro "scale " h:term : tactic =>
    `(tactic| (first | apply $h; (try any_goals positivity); norm_expr
                        -- here we ignore the first goal because it is sufficient
                     | suppose $h; (convert ($(mkIdent `this)) using 1 <;> next => automation);
                            (try any_goals positivity);
                            (try any_goals linarith);
                            check_goal_nums 1;
                            (repeat fail_if_no_progress norm_expr)))


/-
automation tactics for simplification
-/

theorem tsub_le_iff_right_p {a b : ℝ} (h : 0 ≤ a + b) :  -a ≤ b := by linarith

theorem power_k (left right k : ℝ) (h1 : right ≥ 0) (h2 : left ≥ 0) (hk : k > 0) (h : left ^ k ≤ right ^ k) : left ≤ right := by
  have h1 : 0 ≤ right := by positivity
  have h2 : 0 ≤ left := by positivity
  rw [<-rpow_le_rpow_iff h2 h1 hk];
  exact h

macro "llm_cancel_power " h:term : tactic =>
  `(tactic| (apply power_k _ _ $h; (try any_goals positivity); (try any_goals linarith);
              norm_expr;
              (repeat rwp [sqrt_reduce];);
              (repeat simp only [one_div]; rw [sqrt_reduce1]; map_tacs [skip; positivity; positivity; ·norm_num];);
              (repeat simp only [one_div]; rw [sqrt_reduce2]; map_tacs [skip; positivity; positivity; ·norm_num];);
              norm_expr;))


syntax "llm_rearrange" term:max term:max : tactic

macro_rules
| `(tactic| llm_rearrange $l:term $r:term)
 => `(tactic| apply move_left;
              scale rearrange (left := $l) (right := $r)
      )

macro "sym_simplify " h:term : tactic =>
    `(tactic| (apply move_left;
                rwp [show $h by automation];
                (try simp only [tsub_le_iff_right]);
                (try apply tsub_le_iff_right_p);
                norm_expr))

macro "llm_simplify " h:term : tactic =>
    `(tactic| (apply move_left;
                rwp [show $h by automation];
                (try simp only [tsub_le_iff_right]);
                (try apply tsub_le_iff_right_p);
                norm_expr))

macro "llm_mul_expand " h:term : tactic =>
    `(tactic| (sym_simplify $h))

macro "llm_exp_expand " h:term : tactic =>
    `(tactic| (sym_simplify $h))

macro "llm_factor " h:term : tactic =>
    `(tactic| (sym_simplify $h))

macro "llm_frac_reduce " h:term : tactic =>
    `(tactic| (sym_simplify $h))

macro "llm_frac_apart " h:term : tactic =>
    `(tactic| (sym_simplify $h))

macro "llm_frac_together " h:term : tactic =>
    `(tactic| (sym_simplify $h))

macro "llm_cancel_denom " h:term : tactic
 => `(tactic| (apply move_left;
               rwp [show $h by automation];
               (repeat (first | (apply frac_reduce; (first | assumption | positivity | ·simp[*] | linarith))
                              | (apply frac_reduce'; (first | assumption | positivity | ·simp[*] | linarith))
               ));
               first | check_goal_nums 1 | (try any_goals assumption);
               first | check_goal_nums 1 | (try any_goals positivity);
               first | check_goal_nums 1 | (try any_goals ·simp[*]);
               first | check_goal_nums 1 | (try any_goals linarith);
               check_goal_nums 1;
               try simp only [tsub_le_iff_right];
               try apply tsub_le_iff_right_p;
               norm_expr;))

macro "llm_cancel_numer " h:term : tactic
 => `(tactic| ( apply move_left;
                rwp [show $h by automation];
                (try simp only [tsub_le_iff_right]);
                (try apply tsub_le_iff_right_p);
                norm_expr))

macro "llm_cancel_factor " h:term : tactic
 => `(tactic| ( apply move_left;
                rw [show $h by automation];
                (repeat (first | (apply factor_reduce; (first | assumption | positivity | ·simp[*] | linarith))
                               | (apply factor_reduce'; (first | assumption | positivity | ·simp[*] | linarith))
                               | (apply factor_reduce_neg; (first | assumption | positivity | ·simp[*] | linarith))
                               | (apply factor_reduce_neg'; (first | assumption | positivity | ·simp[*] | linarith))
                        ));
                (try simp only [tsub_le_iff_right]);
                (try apply tsub_le_iff_right_p);
                norm_expr;))

macro "make_homogeneous " h:term : tactic
 => `(tactic| ((suffices $h by closed_by_axiom);
                (try simp only [tsub_le_iff_right]);
                (try apply tsub_le_iff_right_p);
                norm_expr;))

macro "intro_by_homogeneous" h:term : tactic
 => `(tactic| (have homo : $h := by closed_by_axiom))

theorem neq_trans {a b : ℝ} (h : a ≤ b) (h' : 0 ≤ a) : 0 ≤ b := by linarith

macro "sym_tangent_line " h:term : tactic =>
    `(tactic| (apply move_right;
               apply neq_trans (show $h by closed_by_axiom) _;
              ))


macro "sym_equal_value" h:term : tactic =>
    `(tactic| (apply move_right;
               suffices $h by closed_by_axiom;
               closed_by_axiom
              ))

macro "sym_pqr_method" h:term : tactic =>
    `(tactic| (apply move_right;
               suffices $h by closed_by_axiom;
              ))

/-
tactic of closing the goal
-/

elab "closed_by_sos" : tactic => do
  if !(← getBoolOption `by_axiom by_axiom.defValue) then
    Tactic.evalTactic (← `(tactic| sos!))
  else
    Tactic.evalTactic (← `(tactic| closed_by_axiom;))

elab "closed_by_eval" : tactic => do
  if !(← getBoolOption `by_axiom by_axiom.defValue) then
    Tactic.evalTactic (← `(tactic| smt_decide!))
  else
    Tactic.evalTactic (← `(tactic| closed_by_axiom;))

macro "close" : tactic =>
    `(tactic| ( (try (apply frac_reduce; positivity))
                (try (repeat rw [cubic_root_of_8]));
                (try (repeat rw [cubic_root_of_27]));
                (try simp only [one_div]);
                (try (repeat rwp [sqrt_reduce]));
                (try (repeat rwp [sqrt_reduce_plus]));
                (try (repeat rwp [sqrt_reduce_plus']));
                (first | done | positivity | ·simp [*] | ·nlinarith | ·ring_nf)
              ))

theorem add_apart {a b : ℝ} (h : a ≥ 0) (h' : b ≥ 0) : 0 ≤ a + b := by linarith

macro "cycle_close" h:term : tactic =>
    `(tactic| ( (have cycle : $h := by (closed_by_axiom));
                (repeat (rcases cycle with ⟨ _ , cycle ⟩));
                (try (apply add_apart));
                (try (any_goals positivity));
                (try (apply frac_reduce; positivity));
                (try (repeat rw [cubic_root_of_8]));
                (try (repeat rw [cubic_root_of_27]));
                (try simp only [one_div]);
                (try (repeat rwp [sqrt_reduce]));
                (try (repeat rwp [sqrt_reduce_plus]));
                (try (repeat rwp [sqrt_reduce_plus']));
                (first | done | positivity | ·simp [*] | ·nlinarith | ·ring_nf)
              ))
