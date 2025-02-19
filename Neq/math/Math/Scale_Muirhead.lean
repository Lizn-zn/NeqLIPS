import Mathlib

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

section Scale_Muirhead_2vars

/-- The normal form Muirhead inequality for 2 variables
    u ^ p * v ^ q + v ^ p * u ^ q ≤ u ^ (p + q) + v ^ (p + q)
    note that normal right cannot be pattern matched, and thus only onestep version supported -/
theorem Muirhead_2vars (u v p q : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : p ≥ 0) (hd : q ≥ 0): u ^ p * v ^ q + v ^ p * u ^ q ≤ u ^ (p + q) + v ^ (p + q) := by
  sorry

theorem Muirhead_normal_left_2vars (u v p q k l right : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hk : k ≥ 0)
  (hl : k * (u ^ (p + q) + v ^ (p + q)) + l ≤ right) : k * (u ^ p * v ^ q + v ^ p * u ^ q) + l ≤ right := by
  suffices u ^ p * v ^ q + v ^ p * u ^ q ≤ u ^ (p + q) + v ^ (p + q) by nlinarith
  exact Muirhead_2vars u v p q ha hb hp hq

theorem Muirhead_normal_Qeq1_left_2vars (u v p k l right : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p ≥ 0) (hk : k ≥ 0)
  (hl : k * (u ^ (p + 1) + v ^ (p + 1)) + l ≤ right) : k * (u ^ p * v + v ^ p * u) + l ≤ right := by
  suffices u ^ p * v + v ^ p * u ≤ u ^ (p + 1) + v ^ (p + 1) by nlinarith
  have hq : (1:ℝ) ≥ 0 := by positivity
  have h := Muirhead_2vars u v p (1:ℝ) ha hb hp hq
  norm_num at h
  exact h

/-- The one-step version of the Muirhead inequality, i.e., p -> p + 1 and q -> q - 1 -/
theorem Muirhead_onestep_2vars (u v p q : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p ≥ 0) (hq : q - 1 ≥ 0) : u ^ p * v ^ q + v ^ p * u ^ q ≤ u ^ (p + 1) * v ^ (q - 1) + v ^ (p + 1) * u ^ (q - 1) := by
  sorry

theorem Muirhead_onestep_left_2vars (u v p q k l right : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p ≥ 0) (hq : q - 1 ≥ 0) (hk : k ≥ 0)
  (h : k * (u ^ (p + 1) * v ^ (q - 1) + v ^ (p + 1) * u ^ (q - 1)) + l ≤ right) :
  k * (u ^ p * v ^ q + v ^ p * u ^ q) + l ≤ right := by
  suffices u ^ p * v ^ q + v ^ p * u ^ q ≤ u ^ (p + 1) * v ^ (q - 1) + v ^ (p + 1) * u ^ (q - 1) by nlinarith
  exact Muirhead_onestep_2vars u v p q ha hb hp hq

theorem Muirhead_onestep_right_2vars (u v p q k l left : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p - 1 ≥ 0) (hq : q ≥ 0) (hk : k ≥ 0)
  (h : left ≤ k * (u ^ (p - 1) * v ^ (q + 1) + v ^ (p - 1) * u ^ (q + 1)) + l) :
  left ≤ k * (u ^ p * v ^ q + v ^ p * u ^ q) + l := by
  suffices u ^ (p - 1) * v ^ (q + 1) + v ^ (p - 1) * u ^ (q + 1) ≤ u ^ p * v ^ q + v ^ p * u ^ q by nlinarith
  have hq : q + (1:ℝ) - (1:ℝ) ≥ 0 := by linarith
  have h := Muirhead_onestep_2vars u v (p - 1) (q + 1) ha hb hp hq
  norm_num at h
  exact h

theorem Muirhead_Qeq1_onestep_left_2vars (u v p k l right : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p ≥ 0) (hk : k ≥ 0)
  (h : k * (u ^ (p + 1) + v ^ (p + 1)) + l ≤ right) :
  k * (u ^ p * v + v ^ p * u) + l ≤ right := by
  suffices u ^ p * v + v ^ p * u ≤ u ^ (p + 1) + v ^ (p + 1) by nlinarith
  have hq : (1:ℝ) - (1:ℝ) ≥ 0 := by linarith
  have h := Muirhead_onestep_2vars u v p (1:ℝ) ha hb hp hq
  norm_num at h
  exact h

theorem Muirhead_Qeq1_onestep_right_2vars (u v p k l left : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p - 1 ≥ 0) (hk : k ≥ 0)
  (h : left ≤ k * (u ^ (p - 1) * v ^ 2 + v ^ (p - 1) * u ^ 2) + l) :
  left ≤ k * (u ^ p * v + v ^ p * u) + l := by
  suffices u ^ (p - 1) * v ^ 2 + v ^ (p - 1) * u ^ 2 ≤ u ^ p * v + v ^ p * u by nlinarith
  have hq : (2:ℝ) - (1:ℝ) ≥ 0 := by linarith
  have h := Muirhead_onestep_2vars u v (p - 1) (2:ℝ) ha hb hp hq
  norm_num at h
  exact h

theorem Muirhead_Qeq0_onestep_right_2vars (u v p k l left : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p - 1 ≥ 0) (hk : k ≥ 0)
  (h : left ≤ k * (u ^ (p - 1) * v + v ^ (p - 1) * u) + l) :
  left ≤ k * (u ^ p + v ^ p) + l := by
  suffices u ^ (p - 1) * v + v ^ (p - 1) * u ≤ u ^ p + v ^ p by nlinarith
  have hq : (1:ℝ) - (1:ℝ) ≥ 0 := by linarith
  have h := Muirhead_onestep_2vars u v (p - 1) (1:ℝ) ha hb hp hq
  norm_num at h
  exact h

/-- The div form Muirhead inequality for 2 variables
    note that div left cannot be pattern matched, and thus only onestep version supported -/
theorem Muirhead_div_right_2vars (u v p q k l left : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hk : k ≥ 0) (hi : i ≥ 0) (hneg : i * (u ^ p * v ^ q + v ^ p * u ^ q) + j > 0)
  (h : left ≤ k * (1 / (i * (u ^ (p + q) + v ^ (p + q)) + j)) + l) : left ≤ k * (1 / (i * (u ^ p * v ^ q + v ^ p * u ^ q) + j)) + l := by
  suffices 1 / (i * (u ^ (p + q) + v ^ (p + q)) + j) ≤ 1 / (i * (u ^ p * v ^ q + v ^ p * u ^ q) + j) by nlinarith
  suffices i * (u ^ p * v ^ q + v ^ p * u ^ q) + j ≤ i * (u ^ (p + q) + v ^ (p + q)) + j by apply one_div_le_one_div_of_le; positivity; trivial
  suffices u ^ p * v ^ q + v ^ p * u ^ q ≤ u ^ (p + q) + v ^ (p + q) by nlinarith
  exact Muirhead_2vars u v p q ha hb hp hq

theorem Muirhead_Qeq1_div_right_2vars (u v p k l left : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p ≥ 0) (hk : k ≥ 0) (hi : i ≥ 0) (hneg : i * (u ^ p * v + v ^ p * u) + j > 0)
  (h : left ≤ k * (1 / (i * (u ^ (p + 1) + v ^ (p + 1)) + j)) + l) : left ≤ k * (1 / (i * (u ^ p * v + v ^ p * u) + j)) + l := by
  have hq : (1:ℝ) ≥ 0 := by linarith
  have hneg' : i * (u ^ p * v ^ (1:ℝ) + v ^ p * u ^ (1:ℝ)) + j > 0 := by norm_num; linarith
  have h' := Muirhead_div_right_2vars u v p (1:ℝ) k l left ha hb hp hq hk hi hneg' h
  norm_num at h'; norm_num
  exact h'

theorem Muirhead_div_onestep_left_2vars (u v p q k l right : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p - 1 ≥ 0) (hq : q ≥ 0) (hk : k ≥ 0) (hi : i ≥ 0) (hneg : i * (u ^ (p - 1) * v ^ (q + 1) + v ^ (p - 1) * u ^ (q + 1)) + j > 0)
  (h : k * (1 / (i * (u ^ (p - 1) * v ^ (q + 1) + v ^ (p - 1) * u ^ (q + 1)) + j)) + l ≤ right) :
  k * (1 / (i * (u ^ p * v ^ q + v ^ p * u ^ q) + j)) + l ≤ right := by
  suffices 1 / (i * (u ^ p * v ^ q + v ^ p * u ^ q) + j) ≤ 1 / (i * (u ^ (p - 1) * v ^ (q + 1) + v ^ (p - 1) * u ^ (q + 1)) + j) by nlinarith
  suffices i * (u ^ (p - 1) * v ^ (q + 1) + v ^ (p - 1) * u ^ (q + 1)) + j ≤ i * (u ^ p * v ^ q + v ^ p * u ^ q) + j by apply one_div_le_one_div_of_le; positivity; trivial
  suffices u ^ (p - 1) * v ^ (q + 1) + v ^ (p - 1) * u ^ (q + 1) ≤ u ^ p * v ^ q + v ^ p * u ^ q by nlinarith
  have hq : q + (1:ℝ) - (1:ℝ) ≥ 0 := by linarith
  have h := Muirhead_onestep_2vars u v (p - 1) (q + 1) ha hb hp hq
  norm_num at h
  exact h

theorem Muirhead_div_onestep_right_2vars (u v p q k l left : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p ≥ 0) (hq : q - 1 ≥ 0) (hk : k ≥ 0) (hi : i ≥ 0) (hneg : i * (u ^ p * v ^ q + v ^ p * u ^ q) + j > 0)
  (h : left ≤ k * (1 / (i * (u ^ (p + 1) * v ^ (q - 1) + v ^ (p + 1) * u ^ (q - 1)) + j)) + l) :
  left ≤ k * (1 / (i * (u ^ p * v ^ q + v ^ p * u ^ q) + j)) + l := by
  suffices 1 / (i * (u ^ (p + 1) * v ^ (q - 1) + v ^ (p + 1) * u ^ (q - 1)) + j) ≤ 1 / (i * (u ^ p * v ^ q + v ^ p * u ^ q) + j) by nlinarith
  suffices i * (u ^ p * v ^ q + v ^ p * u ^ q) + j ≤ i * (u ^ (p + 1) * v ^ (q - 1) + v ^ (p + 1) * u ^ (q - 1)) + j by apply one_div_le_one_div_of_le; positivity; trivial
  suffices u ^ p * v ^ q + v ^ p * u ^ q ≤ u ^ (p + 1) * v ^ (q - 1) + v ^ (p + 1) * u ^ (q - 1) by nlinarith
  exact Muirhead_onestep_2vars u v p q ha hb hp hq

theorem Muirhead_Qeq1_div_onestep_left_2vars (u v p k l right : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p - 1 ≥ 0) (hk : k ≥ 0) (hi : i ≥ 0) (hneg : i * (u ^ (p - 1) * v ^ 2 + v ^ (p - 1) * u ^ 2) + j > 0)
  (h : k * (1 / (i * (u ^ (p - 1) * v ^ 2 + v ^ (p - 1) * u ^ 2) + j)) + l ≤ right) :
  k * (1 / (i * (u ^ p * v + v ^ p * u) + j)) + l ≤ right := by
  have hq : (1:ℝ) ≥ 0 := by linarith
  have hneg' : i * (u ^ (p - 1) * v ^ ((1:ℝ) + (1:ℝ)) + v ^ (p - 1) * u ^ ((1:ℝ) + (1:ℝ))) + j > 0 := by norm_num; linarith
  have h' := Muirhead_div_onestep_left_2vars u v p (1:ℝ) k l right ha hb hp hq hk hi hneg'
  norm_num at h'; norm_num
  apply h'
  norm_num at h
  exact h

theorem Muirhead_Qeq0_div_onestep_left_2vars (u v p k l right : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p - 1 ≥ 0) (hk : k ≥ 0) (hi : i ≥ 0) (hneg : i * (u ^ (p - 1) * v + v ^ (p - 1) * u) + j > 0)
  (h : k * (1 / (i * (u ^ (p - 1) * v + v ^ (p - 1) * u) + j)) + l ≤ right) :
  k * (1 / (i * (u ^ p + v ^ p) + j)) + l ≤ right := by
  suffices 1 / (i * (u ^ p + v ^ p) + j) ≤ 1 / (i * (u ^ (p - 1) * v + v ^ (p - 1) * u) + j) by nlinarith
  suffices i * (u ^ (p - 1) * v + v ^ (p - 1) * u) + j ≤ i * (u ^ p + v ^ p) + j by apply one_div_le_one_div_of_le; positivity; trivial
  suffices u ^ (p - 1) * v + v ^ (p - 1) * u ≤ u ^ p + v ^ p by nlinarith
  have hq : (1:ℝ) - (1:ℝ) ≥ 0 := by linarith
  have h := Muirhead_onestep_2vars u v (p - 1) (1:ℝ) ha hb hp hq
  norm_num at h
  exact h

theorem Muirhead_Qeq1_div_onestep_right_2vars (u v p q k l left : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p ≥ 0) (hq : q - 1 ≥ 0) (hk : k ≥ 0) (hi : i ≥ 0) (hneg : i * (u ^ p * v + v ^ p * u) + j > 0)
  (h : left ≤ k * (1 / (i * (u ^ (p + 1) + v ^ (p + 1)) + j)) + l) :
  left ≤ k * (1 / (i * (u ^ p * v + v ^ p * u) + j)) + l := by
  have hq : (1:ℝ) - (1:ℝ) ≥ 0 := by linarith
  have hneg' : i * (u ^ p * v ^ (1:ℝ) + v ^ p * u ^ (1:ℝ)) + j > 0 := by norm_num; linarith
  have h' := Muirhead_div_onestep_right_2vars u v p (1:ℝ) k l left ha hb hp hq hk hi hneg'
  norm_num at h'; norm_num
  apply h'
  norm_num at h
  exact h


end Scale_Muirhead_2vars


section Scale_Muirhead_3vars

/-- The basic format of the Muirhead inequality for 3 variables -/
theorem Muirhead_3vars (u v w p q r : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hr : r ≥ 0):
  u ^ p * v ^ q * w ^ r + v ^ p * w ^ q * u ^ r + w ^ p * u ^ q * v ^ r ≤ u ^ (p + r) * v ^ q + v ^ (p + r) * w ^ q + w ^ (p + r) * u ^ q := by
  sorry

/-- basic format -/
theorem Muirhead_Req0_3vars (u v w p q : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0):
  u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q ≤ u ^ (p + q) + v ^ (p + q) + w ^ (p + q) := by
  have hr : (0 : ℝ) ≥ 0 := by simp
  have h := Muirhead_3vars u w v p 0 q ha hc hb hp hr hq
  simp at h
  convert h using 1
  ring; ring

/-- The normal form (r neq 0) Muirhead inequality for 3 variables
    u ^ p * v ^ q * w ^ r + v ^ p * w ^ q * u ^ r + w ^ p * u ^ q * v ^ r ≤ u ^ (p + r) * v ^ q + v ^ (p + r) * w ^ q + w ^ (p + r) * u ^ q
    where (1) r ≠ 0; (2) r = 1; (3) q = 1, r = 1; (4) r = 0; (5) q = 1, r = 0;
    note that normal right cannot be pattern matched, and thus use onestep version instead -/
theorem Muirhead_Rneq0_left_3vars (u v w p q r k l right : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hr : r ≥ 0) (hk : k ≥ 0)
  (hl : k * (u ^ (p + r) * v ^ q + v ^ (p + r) * w ^ q + w ^ (p + r) * u ^ q) + l ≤ right) :
  k * (u ^ p * v ^ q * w ^ r + v ^ p * w ^ q * u ^ r + w ^ p * u ^ q * v ^ r) + l ≤ right := by
  suffices u ^ p * v ^ q * w ^ r + v ^ p * w ^ q * u ^ r + w ^ p * u ^ q * v ^ r ≤ u ^ (p + r) * v ^ q + v ^ (p + r) * w ^ q + w ^ (p + r) * u ^ q by nlinarith
  exact Muirhead_3vars u v w p q r ha hb hc hp hq hr

theorem Muirhead_Rneq0_div_right_3vars (u v w p q r k l left : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hr : r ≥ 0) (hi : i ≥ 0) (hk : k ≥ 0)
  (hneg : i * (u ^ p * v ^ q * w ^ r + v ^ p * w ^ q * u ^ r + w ^ p * u ^ q * v ^ r) + j > 0)
  (hl : left ≤ k * (1 / (i * (u ^ (p + r) * v ^ q + v ^ (p + r) * w ^ q + w ^ (p + r) * u ^ q) + j)) + l) :
  left ≤ k * (1 / (i * (u ^ p * v ^ q * w ^ r + v ^ p * w ^ q * u ^ r + w ^ p * u ^ q * v ^ r) + j)) + l := by
  suffices (1 / (i * (u ^ (p + r) * v ^ q + v ^ (p + r) * w ^ q + w ^ (p + r) * u ^ q) + j)) ≤ 1 / (i * (u ^ p * v ^ q * w ^ r + v ^ p * w ^ q * u ^ r + w ^ p * u ^ q * v ^ r) + j) by nlinarith
  suffices u ^ p * v ^ q * w ^ r + v ^ p * w ^ q * u ^ r + w ^ p * u ^ q * v ^ r ≤ u ^ (p + r) * v ^ q + v ^ (p + r) * w ^ q + w ^ (p + r) * u ^ q by
    apply one_div_le_one_div_of_le; exact hneg; nlinarith
  have h := Muirhead_3vars u v w p q r ha hb hc hp hq hr
  norm_num at h
  exact h

theorem Muirhead_Req1_left_3vars (u v w p q k l : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hk : k ≥ 0)
  (hl : k * (u ^ (p + 1) * v ^ q + v ^ (p + 1) * w ^ q + w ^ (p + 1) * u ^ q) + l ≤ right) :
  k * (u ^ p * v ^ q * w + v ^ p * w ^ q * u + w ^ p * u ^ q * v) + l ≤ right := by
  suffices u ^ p * v ^ q * w + v ^ p * w ^ q * u + w ^ p * u ^ q * v ≤ u ^ (p + 1) * v ^ q + v ^ (p + 1) * w ^ q + w ^ (p + 1) * u ^ q by nlinarith
  have hr : (1 : ℝ) ≥ 0 := by simp
  have h := Muirhead_3vars u v w p q 1 ha hb hc hp hq hr
  norm_num at h
  exact h

theorem Muirhead_Req1_div_right_3vars (u v w p q k l left : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hi : i ≥ 0) (hk : k ≥ 0)
  (hneg : i * (u ^ p * v ^ q * w + v ^ p * w ^ q * u + w ^ p * u ^ q * v) + j > 0)
  (hl : left ≤ k * (1 / (i * (u ^ (p + 1) * v ^ q + v ^ (p + 1) * w ^ q + w ^ (p + 1) * u ^ q) + j)) + l) :
  left ≤ k * (1 / (i * (u ^ p * v ^ q * w + v ^ p * w ^ q * u + w ^ p * u ^ q * v) + j)) + l := by
  suffices (1 / (i * (u ^ (p + 1) * v ^ q + v ^ (p + 1) * w ^ q + w ^ (p + 1) * u ^ q) + j)) ≤ 1 / (i * (u ^ p * v ^ q * w + v ^ p * w ^ q * u + w ^ p * u ^ q * v) + j) by nlinarith
  suffices u ^ p * v ^ q * w + v ^ p * w ^ q * u + w ^ p * u ^ q * v ≤ u ^ (p + 1) * v ^ q + v ^ (p + 1) * w ^ q + w ^ (p + 1) * u ^ q by
    apply one_div_le_one_div_of_le; exact hneg; nlinarith
  have hr : (1 : ℝ) ≥ 0 := by simp
  have h := Muirhead_3vars u v w p q 1 ha hb hc hp hq hr
  norm_num at h
  exact h

theorem Muirhead_QReq1_left_3vars (u v w p k l : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hk : k ≥ 0)
  (hl : k * (u ^ (p + 1) * v + v ^ (p + 1) * w + w ^ (p + 1) * u) + l ≤ right) :
  k * (u ^ p * v * w + v ^ p * w * u + w ^ p * u * v) + l ≤ right := by
  suffices u ^ p * v * w + v ^ p * w * u + w ^ p * u * v ≤ u ^ (p + 1) * v + v ^ (p + 1) * w + w ^ (p + 1) * u by nlinarith
  have hq : (1 : ℝ) ≥ 0 := by simp
  have hr : (1 : ℝ) ≥ 0 := by simp
  have h := Muirhead_3vars u v w p 1 1 ha hb hc hp hq hr
  norm_num at h
  exact h

theorem Muirhead_QReq1_div_right_3vars (u v w p q k l left : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hi : i ≥ 0) (hk : k ≥ 0)
  (hneg : i * (u ^ p * v * w + v ^ p * w * u + w ^ p * u * v) + j > 0)
  (hl : left ≤ k * (1 / (i * (u ^ (p + 1) * v + v ^ (p + 1) * w + w ^ (p + 1) * u) + j)) + l) :
  left ≤ k * (1 / (i * (u ^ p * v * w + v ^ p * w * u + w ^ p * u * v) + j)) + l := by
  suffices (1 / (i * (u ^ (p + 1) * v + v ^ (p + 1) * w + w ^ (p + 1) * u) + j)) ≤ 1 / (i * (u ^ p * v * w + v ^ p * w * u + w ^ p * u * v) + j) by nlinarith
  suffices u ^ p * v * w + v ^ p * w * u + w ^ p * u * v ≤ u ^ (p + 1) * v + v ^ (p + 1) * w + w ^ (p + 1) * u by
    apply one_div_le_one_div_of_le; exact hneg; nlinarith
  have hq : (1 : ℝ) ≥ 0 := by simp
  have hr : (1 : ℝ) ≥ 0 := by simp
  have h := Muirhead_3vars u v w p 1 1 ha hb hc hp hq hr
  norm_num at h
  exact h

theorem Muirhead_Req0_left_3vars (u v w p q k l right : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hk : k ≥ 0)
  (hl : k * (u ^ (p + q) + v ^ (p + q) + w ^ (p + q)) + l ≤ right) :
  k * (u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q) + l ≤ right := by
  suffices u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q ≤ u ^ (p + q) + v ^ (p + q) + w ^ (p + q) by nlinarith
  have h := Muirhead_Req0_3vars u v w p q ha hb hc hp hq
  simp at h
  exact h

theorem Muirhead_Req0_div_right_3vars (u v w p q k l left : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hi : i ≥ 0) (hk : k ≥ 0)
  (hneg : i * (u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q) + j > 0)
  (hl : left ≤ k * (1 / (i * (u ^ (p + q) + v ^ (p + q) + w ^ (p + q)) + j)) + l) :
  left ≤ k * (1 / (i * (u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q) + j)) + l := by
  suffices (1 / (i * (u ^ (p + q) + v ^ (p + q) + w ^ (p + q)) + j)) ≤ 1 / (i * (u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q) + j) by nlinarith
  suffices u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q ≤ u ^ (p + q) + v ^ (p + q) + w ^ (p + q) by
    apply one_div_le_one_div_of_le; exact hneg; nlinarith
  have h := Muirhead_Req0_3vars u v w p q ha hb hc hp hq
  simp at h
  exact h

theorem Muirhead_Qeq1Req0_left_3vars (u v w p k l right : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hk : k ≥ 0)
  (hl : k * (u ^ (p + 1) + v ^ (p + 1) + w ^ (p + 1)) + l ≤ right) :
  k * (u ^ p * v + v ^ p * w + w ^ p * u) + l ≤ right := by
  suffices u ^ p * v + v ^ p * w + w ^ p * u ≤ u ^ (p + 1) + v ^ (p + 1) + w ^ (p + 1) by nlinarith
  have hq : (1:ℝ) ≥ 0 := by linarith
  have h := Muirhead_Req0_3vars u v w p 1 ha hb hc hp hq
  simp at h
  exact h

theorem Muirhead_Qeq1Req0_right_3vars (u v w p k l left : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 1) (hk : k ≥ 0)
  (hl : left ≤ k * (u ^ (p - 1) * v + v ^ (p - 1) * w + w ^ (p - 1) * u) + l) :
  left ≤ k * (u ^ p + v ^ p + w ^ p) + l := by
  suffices u ^ (p - 1) * v + v ^ (p - 1) * w + w ^ (p - 1) * u ≤ u ^ p + v ^ p + w ^ p by nlinarith
  have hq : (1:ℝ) ≥ 0 := by linarith
  have hp' : p - 1 ≥ 0 := by linarith
  have h := Muirhead_Req0_3vars u v w (p - 1) 1 ha hb hc hp' hq
  simp at h
  exact h

theorem Muirhead_Qeq1Req0_split_right_3vars (u v w p k l left : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 1) (hk : k ≥ 0)
  (hl : left ≤ k * (u ^ (p - 1) * v + v ^ (p - 1) * w + w ^ (p - 1) * u + u ^ (p - 1) * w + v ^ (p - 1) * u + w ^ (p - 1) * v) / 2 + l) :
  left ≤ k * (u ^ p + v ^ p + w ^ p) + l := by
  suffices u ^ (p - 1) * v + v ^ (p - 1) * w + w ^ (p - 1) * u + u ^ (p - 1) * w + v ^ (p - 1) * u + w ^ (p - 1) * v ≤ 2 * (u ^ p + v ^ p + w ^ p) by nlinarith
  have hq : (1:ℝ) ≥ 0 := by linarith
  have hp' : p - 1 ≥ 0 := by linarith
  have h1 := Muirhead_Req0_3vars u v w (p - 1) 1 ha hb hc hp' hq
  have h2 := Muirhead_Req0_3vars u w v (p - 1) 1 ha hc hb hp' hq
  have h := add_le_add h1 h2
  convert h using 1
  field_simp; ring_nf
  field_simp; ring_nf

theorem Muirhead_Qeq1Req0_div_right_3vars (u v w p q k l left : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hi : i ≥ 0) (hk : k ≥ 0)
  (hneg : i * (u ^ p * v + v ^ p * w + w ^ p * u) + j > 0)
  (hl : left ≤ k * (1 / (i * (u ^ (p + 1) + v ^ (p + 1) + w ^ (p + 1)) + j)) + l) :
  left ≤ k * (1 / (i * (u ^ p * v + v ^ p * w + w ^ p * u) + j)) + l := by
  suffices (1 / (i * (u ^ (p + 1) + v ^ (p + 1) + w ^ (p + 1)) + j)) ≤ 1 / (i * (u ^ p * v + v ^ p * w + w ^ p * u) + j) by nlinarith
  suffices u ^ p * v + v ^ p * w + w ^ p * u ≤ u ^ (p + 1) + v ^ (p + 1) + w ^ (p + 1) by
    apply one_div_le_one_div_of_le; exact hneg; nlinarith
  have hq : (1:ℝ) ≥ 0 := by linarith
  have h := Muirhead_Req0_3vars u v w p 1 ha hb hc hp hq
  simp at h
  exact h


/-- The one step form Muirhead inequality for 3 variables -/
theorem Muirhead_Req0_onestep_3vars (u v w p q : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hq : q - 1 ≥ 0) : u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q ≤ u ^ (p + 1) * v ^ (q - 1) + v ^ (p + 1) * w ^ (q - 1) + w ^ (p + 1) * u ^ (q - 1) := by
  sorry

theorem Muirhead_Req0_onestep_left_3vars (u v w p q k l right : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hq : q - 1 ≥ 0) (hk : k ≥ 0)
  (h : k * (u ^ (p + 1) * v ^ (q - 1) + v ^ (p + 1) * w ^ (q - 1) + w ^ (p + 1) * u ^ (q - 1)) + l ≤ right) :
  k * (u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q) + l ≤ right := by
  suffices u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q ≤ u ^ (p + 1) * v ^ (q - 1) + v ^ (p + 1) * w ^ (q - 1) + w ^ (p + 1) * u ^ (q - 1) by nlinarith
  exact Muirhead_Req0_onestep_3vars u v w p q ha hb hc hp hq

theorem Muirhead_Req0_onestep_div_right_3vars (u v w p q k l left : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hq : q - 1 ≥ 0) (hi : i ≥ 0) (hk : k ≥ 0)
  (hneg : i * (u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q) + j > 0)
  (hl : left ≤ k * (1 / (i * (u ^ (p + 1) * v ^ (q - 1) + v ^ (p + 1) * w ^ (q - 1) + w ^ (p + 1) * u ^ (q - 1)) + j)) + l) :
  left ≤ k * (1 / (i * (u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q) + j)) + l := by
  suffices (1 / (i * (u ^ (p + 1) * v ^ (q - 1) + v ^ (p + 1) * w ^ (q - 1) + w ^ (p + 1) * u ^ (q - 1)) + j)) ≤ 1 / (i * (u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q) + j) by nlinarith
  suffices u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q ≤ u ^ (p + 1) * v ^ (q - 1) + v ^ (p + 1) * w ^ (q - 1) + w ^ (p + 1) * u ^ (q - 1) by
    apply one_div_le_one_div_of_le; exact hneg; nlinarith
  have h := Muirhead_Req0_onestep_3vars u v w p q ha hb hc hp hq
  norm_num at h
  exact h

theorem Muirhead_Req0_onestep_right_3vars (u v w p q k l left : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p - 1 ≥ 0) (hq : q ≥ 0) (hk : k ≥ 0)
  (h : left ≤ k * (u ^ (p - 1) * v ^ (q + 1) + v ^ (p - 1) * w ^ (q + 1) + w ^ (p - 1) * u ^ (q + 1)) + l) :
  left ≤ k * (u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q) + l := by
  suffices u ^ (p - 1) * v ^ (q + 1) + v ^ (p - 1) * w ^ (q + 1) + w ^ (p - 1) * u ^ (q + 1) ≤ u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q by nlinarith
  have hq : q + (1:ℝ) - (1:ℝ) ≥ 0 := by linarith
  have h := Muirhead_Req0_onestep_3vars u v w (p - 1) (q + 1) ha hb hc hp hq
  norm_num at h
  exact h

theorem Muirhead_Req0_onestep_div_left_3vars (u v w p q k l right : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p - 1 ≥ 0) (hq : q ≥ 0) (hi : i ≥ 0) (hk : k ≥ 0)
  (hneg : i * (u ^ (p - 1) * v ^ (q + 1) + v ^ (p - 1) * w ^ (q + 1) + w ^ (p - 1) * u ^ (q + 1)) + j > 0)
  (hl : k * (1 / (i * (u ^ (p - 1) * v ^ (q + 1) + v ^ (p - 1) * w ^ (q + 1) + w ^ (p - 1) * u ^ (q + 1)) + j)) + l ≤ right) :
  k * (1 / (i * (u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q) + j)) + l ≤ right := by
  suffices 1 / (i * (u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q) + j) ≤ (1 / (i * (u ^ (p - 1) * v ^ (q + 1) + v ^ (p - 1) * w ^ (q + 1) + w ^ (p - 1) * u ^ (q + 1)) + j)) by nlinarith
  suffices u ^ (p - 1) * v ^ (q + 1) + v ^ (p - 1) * w ^ (q + 1) + w ^ (p - 1) * u ^ (q + 1) ≤ u ^ p * v ^ q + v ^ p * w ^ q + w ^ p * u ^ q by
    apply one_div_le_one_div_of_le; exact hneg; nlinarith
  have hq : q + (1:ℝ) - (1:ℝ) ≥ 0 := by linarith
  have h := Muirhead_Req0_onestep_3vars u v w (p - 1) (q + 1) ha hb hc hp hq
  simp at h
  exact h

end Scale_Muirhead_3vars

section Scale_Muirhead_4vars
/-- The basic format of the Muirhead inequality for 4 variables
    u1 ^ p * u2 ^ q * u3 ^ r * u4 ^ s + u2 ^ p * u3 ^ q * u4 ^ r * u1 ^ s + u3 ^ p * u4 ^ q * u1 ^ r * u2 ^ s + u4 ^ p * u1 ^ q * u2 ^ r * u3 ^ s
      ≤ u1 ^ (p + s) * u2 ^ q * u3 ^ r + u2 ^ (p + s) * u3 ^ q * u4 ^ r + u3 ^ (p + s) * u4 ^ q * u1 ^ r + u4 ^ (p + s) * u1 ^ q * u2 ^ r
    where (1) s ≠ 0; (2) s = 1; (3) r = 1, s = 1; (4) q = r = s = 1;
          (5) s = 0; (6) r = 1, s = 0; (7) q = r = 1, s = 0; (8) r = s = 0; (9) q = 1, r = s = 0 -/
theorem Muirhead_4vars (u1 u2 u3 u4 p q r s: ℝ) (ha : u1 ≥ 0) (hb : u2 ≥ 0) (hc : u3 ≥ 0) (hd : u4 ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hr : r ≥ 0) (hs : s ≥ 0):
  u1 ^ p * u2 ^ q * u3 ^ r * u4 ^ s
    + u2 ^ p * u3 ^ q * u4 ^ r * u1 ^ s
    + u3 ^ p * u4 ^ q * u1 ^ r * u2 ^ s
    + u4 ^ p * u1 ^ q * u2 ^ r * u3 ^ s
  ≤ u1 ^ (p + s) * u2 ^ q * u3 ^ r
      + u2 ^ (p + s) * u3 ^ q * u4 ^ r
      + u3 ^ (p + s) * u4 ^ q * u1 ^ r
      + u4 ^ (p + s) * u1 ^ q * u2 ^ r := by
  sorry

theorem Muirhead_variant_4vars (u1 u2 u3 u4 p q r s: ℝ) (ha : u1 ≥ 0) (hb : u2 ≥ 0) (hc : u3 ≥ 0) (hd : u4 ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hr : r ≥ 0) (hs : s ≥ 0):
  u1 ^ p * u2 ^ q * u3 ^ r * u4 ^ s
    + u2 ^ p * u3 ^ q * u4 ^ r * u1 ^ s
    + u3 ^ p * u4 ^ q * u1 ^ r * u2 ^ s
    + u4 ^ p * u1 ^ q * u2 ^ r * u3 ^ s
  ≤ u1 ^ (p + r) * u2 ^ q * u4 ^ s
      + u2 ^ (p + r) * u3 ^ q * u1 ^ s
      + u3 ^ (p + r) * u4 ^ q * u2 ^ s
      + u4 ^ (p + r) * u1 ^ q * u3 ^ s := by
  sorry

theorem Muirhead_variant'_4vars (u1 u2 u3 u4 p q r s: ℝ) (ha : u1 ≥ 0) (hb : u2 ≥ 0) (hc : u3 ≥ 0) (hd : u4 ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hr : r ≥ 0) (hs : s ≥ 0):
  u1 ^ p * u2 ^ q * u3 ^ r * u4 ^ s
    + u2 ^ p * u3 ^ q * u4 ^ r * u1 ^ s
    + u3 ^ p * u4 ^ q * u1 ^ r * u2 ^ s
    + u4 ^ p * u1 ^ q * u2 ^ r * u3 ^ s
  ≤ u1 ^ (p + q) * u3 ^ r * u4 ^ s
      + u2 ^ (p + q) * u4 ^ r * u1 ^ s
      + u3 ^ (p + q) * u1 ^ r * u2 ^ s
      + u4 ^ (p + q) * u2 ^ r * u3 ^ s := by
  sorry

theorem Muirhead_Seq0_4vars (u1 u2 u3 u4 p q r : ℝ) (ha : u1 ≥ 0) (hb : u2 ≥ 0) (hc : u3 ≥ 0) (hd : u4 ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hr : r ≥ 0) :
  u1 ^ p * u2 ^ q * u3 ^ r + u2 ^ p * u3 ^ q * u4 ^ r + u3 ^ p * u4 ^ q * u1 ^ r + u4 ^ p * u1 ^ q * u2 ^ r ≤ u1 ^ (p + r) * u2 ^ q + u2 ^ (p + r) * u3 ^ q + u3 ^ (p + r) * u4 ^ q + u4 ^ (p + r) * u1 ^ q := by
  have hs : (0 : ℝ) ≥ 0 := by simp
  have h := Muirhead_variant_4vars u1 u2 u3 u4 p q r 0 ha hb hc hd hp hq hr hs
  simp at h
  exact h

theorem Muirhead_Sneq0_left_4vars (u1 u2 u3 u4 p q r s k l right : ℝ) (ha : u1 ≥ 0) (hb : u2 ≥ 0) (hc : u3 ≥ 0) (hd : u4 ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hr : r ≥ 0) (hs : s ≥ 0) (hk : k ≥ 0)
  (hl : k * (u1 ^ (p + s) * u2 ^ q * u3 ^ r + u2 ^ (p + s) * u3 ^ q * u4 ^ r + u3 ^ (p + s) * u4 ^ q * u1 ^ r + u4 ^ (p + s) * u1 ^ q * u2 ^ r) + l ≤ right) :
  k * (u1 ^ p * u2 ^ q * u3 ^ r * u4 ^ s + u2 ^ p * u3 ^ q * u4 ^ r * u1 ^ s + u3 ^ p * u4 ^ q * u1 ^ r * u2 ^ s + u4 ^ p * u1 ^ q * u2 ^ r * u3 ^ s) + l ≤ right := by
  suffices u1 ^ p * u2 ^ q * u3 ^ r * u4 ^ s + u2 ^ p * u3 ^ q * u4 ^ r * u1 ^ s + u3 ^ p * u4 ^ q * u1 ^ r * u2 ^ s + u4 ^ p * u1 ^ q * u2 ^ r * u3 ^ s ≤ u1 ^ (p + s) * u2 ^ q * u3 ^ r + u2 ^ (p + s) * u3 ^ q * u4 ^ r + u3 ^ (p + s) * u4 ^ q * u1 ^ r + u4 ^ (p + s) * u1 ^ q * u2 ^ r by nlinarith
  exact Muirhead_4vars u1 u2 u3 u4 p q r s ha hb hc hd hp hq hr hs

theorem Muirhead_Seq1_left_4vars (u1 u2 u3 u4 p q r k l right : ℝ) (ha : u1 ≥ 0) (hb : u2 ≥ 0) (hc : u3 ≥ 0) (hd : u4 ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hr : r ≥ 0) (hk : k ≥ 0)
  (hl : k * (u1 ^ (p + 1) * u2 ^ q * u3 ^ r + u2 ^ (p + 1) * u3 ^ q * u4 ^ r + u3 ^ (p + 1) * u4 ^ q * u1 ^ r + u4 ^ (p + 1) * u1 ^ q * u2 ^ r) + l ≤ right) :
  k * (u1 ^ p * u2 ^ q * u3 ^ r * u4 + u2 ^ p * u3 ^ q * u4 ^ r * u1 + u3 ^ p * u4 ^ q * u1 ^ r * u2 + u4 ^ p * u1 ^ q * u2 ^ r * u3) + l ≤ right := by
  suffices u1 ^ p * u2 ^ q * u3 ^ r * u4 + u2 ^ p * u3 ^ q * u4 ^ r * u1 + u3 ^ p * u4 ^ q * u1 ^ r * u2 + u4 ^ p * u1 ^ q * u2 ^ r * u3 ≤ u1 ^ (p + 1) * u2 ^ q * u3 ^ r + u2 ^ (p + 1) * u3 ^ q * u4 ^ r + u3 ^ (p + 1) * u4 ^ q * u1 ^ r + u4 ^ (p + 1) * u1 ^ q * u2 ^ r by nlinarith
  have hs : (1:ℝ) ≥ 0 := by linarith
  have h := Muirhead_4vars u1 u2 u3 u4 p q r 1 ha hb hc hd hp hq hr hs
  norm_num at h
  exact h

theorem Muirhead_RSeq1_left_4vars (u1 u2 u3 u4 p q k l right : ℝ) (ha : u1 ≥ 0) (hb : u2 ≥ 0) (hc : u3 ≥ 0) (hd : u4 ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hk : k ≥ 0)
  (hl : k * (u1 ^ (p + 1) * u2 ^ q * u3 + u2 ^ (p + 1) * u3 ^ q * u4 + u3 ^ (p + 1) * u4 ^ q * u1 + u4 ^ (p + 1) * u1 ^ q * u2) + l ≤ right) :
  k * (u1 ^ p * u2 ^ q * u3 * u4 + u2 ^ p * u3 ^ q * u4 * u1 + u3 ^ p * u4 ^ q * u1 * u2 + u4 ^ p * u1 ^ q * u2 * u3) + l ≤ right := by
  suffices u1 ^ p * u2 ^ q * u3 * u4 + u2 ^ p * u3 ^ q * u4 * u1 + u3 ^ p * u4 ^ q * u1 * u2 + u4 ^ p * u1 ^ q * u2 * u3 ≤ u1 ^ (p + 1) * u2 ^ q * u3 + u2 ^ (p + 1) * u3 ^ q * u4 + u3 ^ (p + 1) * u4 ^ q * u1 + u4 ^ (p + 1) * u1 ^ q * u2 by nlinarith
  have hr : (1:ℝ) ≥ 0 := by linarith
  have hs : (1:ℝ) ≥ 0 := by linarith
  have h := Muirhead_4vars u1 u2 u3 u4 p q 1 1 ha hb hc hd hp hq hr hs
  norm_num at h
  exact h

theorem Muirhead_QRSeq1_left_4vars (u1 u2 u3 u4 p k l right : ℝ) (ha : u1 ≥ 0) (hb : u2 ≥ 0) (hc : u3 ≥ 0) (hd : u4 ≥ 0) (hp : p ≥ 0) (hk : k ≥ 0)
  (hl : k * (u1 ^ (p + 1) * u2 * u3 + u2 ^ (p + 1) * u3 * u4 + u3 ^ (p + 1) * u4 * u1 + u4 ^ (p + 1) * u1 * u2) + l ≤ right) :
  k * (u1 ^ p * u2 * u3 * u4 + u2 ^ p * u3 * u4 * u1 + u3 ^ p * u4 * u1 * u2 + u4 ^ p * u1 * u2 * u3) + l ≤ right := by
  suffices u1 ^ p * u2 * u3 * u4 + u2 ^ p * u3 * u4 * u1 + u3 ^ p * u4 * u1 * u2 + u4 ^ p * u1 * u2 * u3 ≤ u1 ^ (p + 1) * u2 * u3 + u2 ^ (p + 1) * u3 * u4 + u3 ^ (p + 1) * u4 * u1 + u4 ^ (p + 1) * u1 * u2 by nlinarith
  have hq : (1:ℝ) ≥ 0 := by linarith
  have hr : (1:ℝ) ≥ 0 := by linarith
  have hs : (1:ℝ) ≥ 0 := by linarith
  have h := Muirhead_4vars u1 u2 u3 u4 p 1 1 1 ha hb hc hd hp hq hr hs
  norm_num at h
  exact h

theorem Muirhead_Seq0_left_4vars (u1 u2 u3 u4 p q r k l right : ℝ) (ha : u1 ≥ 0) (hb : u2 ≥ 0) (hc : u3 ≥ 0) (hd : u4 ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hr : r ≥ 0) (hk : k ≥ 0)
  (hl : k * (u1 ^ (p + r) * u2 ^ q + u2 ^ (p + r) * u3 ^ q + u3 ^ (p + r) * u4 ^ q + u4 ^ (p + r) * u1 ^ q) + l ≤ right) :
  k * (u1 ^ p * u2 ^ q * u3 ^ r + u2 ^ p * u3 ^ q * u4 ^ r + u3 ^ p * u4 ^ q * u1 ^ r + u4 ^ p * u1 ^ q * u2 ^ r) + l ≤ right := by
  suffices u1 ^ p * u2 ^ q * u3 ^ r + u2 ^ p * u3 ^ q * u4 ^ r + u3 ^ p * u4 ^ q * u1 ^ r + u4 ^ p * u1 ^ q * u2 ^ r ≤ u1 ^ (p + r) * u2 ^ q + u2 ^ (p + r) * u3 ^ q + u3 ^ (p + r) * u4 ^ q + u4 ^ (p + r) * u1 ^ q by nlinarith
  have h := Muirhead_Seq0_4vars u1 u2 u3 u4 p q r ha hb hc hd hp hq hr
  norm_num at h
  exact h

theorem Muirhead_Req1Seq0_left_4vars (u1 u2 u3 u4 p q k l right : ℝ) (ha : u1 ≥ 0) (hb : u2 ≥ 0) (hc : u3 ≥ 0) (hd : u4 ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hk : k ≥ 0)
  (hl : k * (u1 ^ (p + 1) * u2 ^ q + u2 ^ (p + 1) * u3 ^ q + u3 ^ (p + 1) * u4 ^ q + u4 ^ (p + 1) * u1 ^ q) + l ≤ right) :
  k * (u1 ^ p * u2 ^ q * u3 + u2 ^ p * u3 ^ q * u4 + u3 ^ p * u4 ^ q * u1 + u4 ^ p * u1 ^ q * u2) + l ≤ right := by
  suffices u1 ^ p * u2 ^ q * u3 + u2 ^ p * u3 ^ q * u4 + u3 ^ p * u4 ^ q * u1 + u4 ^ p * u1 ^ q * u2 ≤ u1 ^ (p + 1) * u2 ^ q + u2 ^ (p + 1) * u3 ^ q + u3 ^ (p + 1) * u4 ^ q + u4 ^ (p + 1) * u1 ^ q by nlinarith
  have hr : (1:ℝ) ≥ 0 := by linarith
  have hs : (0:ℝ) ≥ 0 := by simp
  have h := Muirhead_variant_4vars u1 u2 u3 u4 p q 1 0 ha hb hc hd hp hq hr hs
  simp at h
  exact h

theorem Muirhead_QReq1Seq0_left_4vars (u1 u2 u3 u4 p k l right : ℝ) (ha : u1 ≥ 0) (hb : u2 ≥ 0) (hc : u3 ≥ 0) (hd : u4 ≥ 0) (hp : p ≥ 0) (hk : k ≥ 0)
  (hl : k * (u1 ^ (p + 1) * u2 + u2 ^ (p + 1) * u3 + u3 ^ (p + 1) * u4 + u4 ^ (p + 1) * u1) + l ≤ right) :
  k * (u1 ^ p * u2 * u3 + u2 ^ p * u3 * u4 + u3 ^ p * u4 * u1 + u4 ^ p * u1 * u2) + l ≤ right := by
  suffices u1 ^ p * u2 * u3 + u2 ^ p * u3 * u4 + u3 ^ p * u4 * u1 + u4 ^ p * u1 * u2 ≤ u1 ^ (p + 1) * u2 + u2 ^ (p + 1) * u3 + u3 ^ (p + 1) * u4 + u4 ^ (p + 1) * u1 by nlinarith
  have hq : (1:ℝ) ≥ 0 := by linarith
  have hr : (1:ℝ) ≥ 0 := by simp
  have hs : (0:ℝ) ≥ 0 := by linarith
  have h := Muirhead_variant_4vars u1 u2 u3 u4 p 1 1 0 ha hb hc hd hp hq hr hs
  simp at h
  exact h

theorem Muirhead_RSeq0_left_4vars (u1 u2 u3 u4 p q k l right : ℝ) (ha : u1 ≥ 0) (hb : u2 ≥ 0) (hc : u3 ≥ 0) (hd : u4 ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hk : k ≥ 0)
  (hl : k * (u1 ^ (p + q) + u2 ^ (p + q) + u3 ^ (p + q) + u4 ^ (p + q)) + l ≤ right) :
  k * (u1 ^ p * u2 ^ q + u2 ^ p * u3 ^ q + u3 ^ p * u4 ^ q + u4 ^ p * u1 ^ q) + l ≤ right := by
  suffices u1 ^ p * u2 ^ q + u2 ^ p * u3 ^ q + u3 ^ p * u4 ^ q + u4 ^ p * u1 ^ q ≤ u1 ^ (p + q) + u2 ^ (p + q) + u3 ^ (p + q) + u4 ^ (p + q) by nlinarith
  have hr : (0:ℝ) ≥ 0 := by simp
  have hs : (0:ℝ) ≥ 0 := by simp
  have h := Muirhead_variant'_4vars u1 u2 u3 u4 p q 0 0 ha hb hc hd hp hq hr hs
  simp at h
  exact h

theorem Muirhead_Qeq1RSeq0_left_4vars (u1 u2 u3 u4 p k l right : ℝ) (ha : u1 ≥ 0) (hb : u2 ≥ 0) (hc : u3 ≥ 0) (hd : u4 ≥ 0) (hp : p ≥ 0) (hk : k ≥ 0)
  (hl : k * (u1 ^ (p + 1) + u2 ^ (p + 1) + u3 ^ (p + 1) + u4 ^ (p + 1)) + l ≤ right) :
  k * (u1 ^ p * u2 + u2 ^ p * u3 + u3 ^ p * u4 + u4 ^ p * u1) + l ≤ right := by
  suffices u1 ^ p * u2 + u2 ^ p * u3 + u3 ^ p * u4 + u4 ^ p * u1 ≤ u1 ^ (p + 1) + u2 ^ (p + 1) + u3 ^ (p + 1) + u4 ^ (p + 1) by nlinarith
  have hq : (1:ℝ) ≥ 0 := by linarith
  have hr : (0:ℝ) ≥ 0 := by simp
  have hs : (0:ℝ) ≥ 0 := by simp
  have h := Muirhead_variant'_4vars u1 u2 u3 u4 p 1 0 0 ha hb hc hd hp hq hr hs
  simp at h
  exact h

end Scale_Muirhead_4vars
