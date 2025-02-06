import Mathlib

import Math.NeqTricks
import Math.Del.NeqSqrt
import Math.Scale_AM_GM

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

-- ========================== Chebyshev's inequalities ==========================

theorem NEQ_Chebyshev1_div_cycle_3vars (u v w : ℝ) (ha : u > 0) (hb : v > 0) (hc : w > 0) : (u / v + v / w + w / u ≥ 3) := by
  have h0 : (u / v) * (v / w) * (w / u) = 1 := by field_simp [ha, hb, hc]
  have h1 := NEQ_AM_GM_3vars (u / v) (v / w) (w / u)
  simp [h0, ha, hb, hc] at h1
  apply h1
  all_goals positivity

theorem NEQ_Chebyshev1_div_cycle_normal_3vars (u v w i1 j1 i2 j2 : ℝ) (ha : i2 * u + j2 > 0) (hb : i2 * v + j2 > 0) (hc : i2 * w + j2 > 0) (hd : i1 ≥ 0) (he : i2 ≥ 0) :
      (i1 * u + j1) / (i2 * v + j2) + (i1 * v + j1) / (i2 * w + j2) + (i1 * w + j1) / (i2 * u + j2) ≥ (i1 * u + j1) / (i2 * u + j2) + (i1 * v + j1) / (i2 * v + j2) + (i1 * w + j1) / (i2 * w + j2) := by
  by_cases h : i2 = 0
  rw [h]; simp;
  have h : i2 > 0 := by positivity
  let u1 := u / (i2 * u + j2)
  let v1 := v / (i2 * v + j2)
  let w1 := w / (i2 * w + j2)
  let u2 := u / (i2 * v + j2)
  let v2 := v / (i2 * w + j2)
  let w2 := w / (i2 * u + j2)
  rw [show (i1 * u + j1) / (i2 * v + j2) = i1 * u2 + j1 / (i2 * v + j2) by unfold_let u2; field_simp [hb, hd]]
  rw [show (i1 * v + j1) / (i2 * w + j2) = i1 * v2 + j1 / (i2 * w + j2) by unfold_let v2; field_simp [hc, hd]]
  rw [show (i1 * w + j1) / (i2 * u + j2) = i1 * w2 + j1 / (i2 * u + j2) by unfold_let w2; field_simp [ha, hd]]
  rw [show (i1 * u + j1) / (i2 * u + j2) = i1 * u1 + j1 / (i2 * u + j2) by unfold_let u1; field_simp [ha, hd]]
  rw [show (i1 * v + j1) / (i2 * v + j2) = i1 * v1 + j1 / (i2 * v + j2) by unfold_let v1; field_simp [hb, hd]]
  rw [show (i1 * w + j1) / (i2 * w + j2) = i1 * w1 + j1 / (i2 * w + j2) by unfold_let w1; field_simp [hc, hd]]
  suffices i1 * u1 + i1 * v1 + i1 * w1 ≤ i1 * u2 + i1 * v2 + i1 * w2 by linarith
  suffices u1 + v1 + w1 ≤ u2 + v2 + w2 by nlinarith
  have h0 := NEQ_Chebyshev1_div_cycle_3vars (i2*u+j2) (i2*v+j2) (i2*w+j2) ha hb hc
  rw [show (i2 * u + j2) / (i2 * v + j2) = i2 * u2 - i2 * v1 + 1 by unfold_let u2 v1; field_simp [<-add_assoc, hb, hd]] at h0
  rw [show (i2 * v + j2) / (i2 * w + j2) = i2 * v2 - i2 * w1 + 1 by unfold_let v2 w1; field_simp [<-add_assoc, hc, hd]] at h0
  rw [show (i2 * w + j2) / (i2 * u + j2) = i2 * w2 - i2 * u1 + 1 by unfold_let w2 u1; field_simp [<-add_assoc, ha, hd]] at h0
  have h0 : i2 * u2 - i2 * v1 + (i2 * v2 - i2 * w1) + (i2 * w2 - i2 * u1) ≥ 0 := by linarith
  nlinarith

theorem NEQ_Chebyshev1_div_left_cycle_normal_3vars (u v w i1 j1 i2 j2 k l right : ℝ) (ha : i2 * u + j2 > 0) (hb : i2 * v + j2 > 0) (hc : i2 * w + j2 > 0) (hd : i1 ≥ 0) (he : i2 ≥ 0) (hf : k ≥ 0)
    (hj : k * ((i1 * u + j1) / (i2 * v + j2) + (i1 * v + j1) / (i2 * w + j2) + (i1 * w + j1) / (i2 * u + j2)) + l ≤ right) :
    k * ((i1 * u + j1) / (i2 * u + j2) + (i1 * v + j1) / (i2 * v + j2) + (i1 * w + j1) / (i2 * w + j2)) + l ≤ right := by
  suffices (i1 * u + j1) / (i2 * u + j2) + (i1 * v + j1) / (i2 * v + j2) + (i1 * w + j1) / (i2 * w + j2) ≤ (i1 * u + j1) / (i2 * v + j2) + (i1 * v + j1) / (i2 * w + j2) + (i1 * w + j1) / (i2 * u + j2) by nlinarith
  have h : (i1 * u + j1) / (i2 * v + j2) + (i1 * v + j1) / (i2 * w + j2) + (i1 * w + j1) / (i2 * u + j2) ≥ (i1 * u + j1) / (i2 * u + j2) + (i1 * v + j1) / (i2 * v + j2) + (i1 * w + j1) / (i2 * w + j2) := by
    apply NEQ_Chebyshev1_div_cycle_normal_3vars u v w i1 j1 i2 j2 ha hb hc hd he
  trivial

theorem NEQ_Chebyshev1_div_right_cycle_normal_3vars (u v w i1 j1 i2 j2 k l left : ℝ) (ha : i2 * u + j2 > 0) (hb : i2 * v + j2 > 0) (hc : i2 * w + j2 > 0) (hd : i1 ≥ 0) (he : i2 ≥ 0) (hf : k ≥ 0)
    (hj : left ≤ k * ((i1 * u + j1) / (i2 * u + j2) + (i1 * v + j1) / (i2 * v + j2) + (i1 * w + j1) / (i2 * w + j2)) + l) :
    left ≤ k * ((i1 * u + j1) / (i2 * v + j2) + (i1 * v + j1) / (i2 * w + j2) + (i1 * w + j1) / (i2 * u + j2)) + l := by
  suffices (i1 * u + j1) / (i2 * u + j2) + (i1 * v + j1) / (i2 * v + j2) + (i1 * w + j1) / (i2 * w + j2) ≤ (i1 * u + j1) / (i2 * v + j2) + (i1 * v + j1) / (i2 * w + j2) + (i1 * w + j1) / (i2 * u + j2) by nlinarith
  have h : (i1 * u + j1) / (i2 * v + j2) + (i1 * v + j1) / (i2 * w + j2) + (i1 * w + j1) / (i2 * u + j2) ≥ (i1 * u + j1) / (i2 * u + j2) + (i1 * v + j1) / (i2 * v + j2) + (i1 * w + j1) / (i2 * w + j2) := by
    apply NEQ_Chebyshev1_div_cycle_normal_3vars u v w i1 j1 i2 j2 ha hb hc hd he
  trivial

theorem NEQ_Chebyshev1_div_cycle_square_3vars (u v w i1 i2 i3 j1 j2 j3 : ℝ) (ha : j1 * u ^ 2 + j2 * u + j3 > 0) (hb : j1 * v ^ 2 + j2 * v + j3 > 0) (hc : j1 * w ^ 2 + j2 * w + j3 > 0) (hd : i1 ≥ 0) (he : i2 ≥ 0) (hf : j1 ≥ 0) (hg : j2 ≥ 0):
  (i1 * u ^ 2 + i2 * u + i3) / (j1 * v ^ 2 + j2 * v + j3) + (i1 * v ^ 2 + i2 * v + i3) / (j1 * w ^ 2 + j2 * w + j3) + (i1 * w ^ 2 + i2 * w + i3) / (j1 * u ^ 2 + j2 * u + j3) ≥ (i1 * u ^ 2 + i2 * u + i3) / (j1 * u ^ 2 + j2 * u + j3) + (i1 * v ^ 2 + i2 * v + i3) / (j1 * v ^ 2 + j2 * v + j3) + (i1 * w ^ 2 + i2 * w + i3) / (j1 * w ^ 2 + j2 * w + j3) := by
  sorry

theorem NEQ_Chebyshev1_div_left_cycle_square_3vars (u v w i1 i2 j1 j2 j3 j4 k l left : ℝ) (ha : i2 * u ^ 2 + j2 * u + j4 > 0) (hb : i2 * v ^ 2 + j2 * v + j4 > 0) (hc : i2 * w ^ 2 + j2 * w + j4 > 0) (hd : i1 ≥ 0) (he : j1 ≥ 0) (hf : i2 ≥ 0) (hg : j2 ≥ 0) (hh : k ≥ 0)
    (hj : k * ((i1 * u ^ 2 + j1 * u + j3) / (i2 * v ^ 2 + j2 * v + j4) + (i1 * v ^ 2 + j1 * v + j3) / (i2 * w ^ 2 + j2 * w + j4) + (i1 * w ^ 2 + j1 * w + j3) / (i2 * u ^ 2 + j2 * u + j4)) + l ≤ right) :
    k * ((i1 * u ^ 2 + j1 * u + j3) / (i2 * u ^ 2 + j2 * u + j4) + (i1 * v ^ 2 + j1 * v + j3) / (i2 * v ^ 2 + j2 * v + j4) + (i1 * w ^ 2 + j1 * w + j3) / (i2 * w ^ 2 + j2 * w + j4)) + l ≤ right := by
    suffices (i1 * u ^ 2 + j1 * u + j3) / (i2 * u ^ 2 + j2 * u + j4) + (i1 * v ^ 2 + j1 * v + j3) / (i2 * v ^ 2 + j2 * v + j4) + (i1 * w ^ 2 + j1 * w + j3) / (i2 * w ^ 2 + j2 * w + j4) ≤ (i1 * u ^ 2 + j1 * u + j3) / (i2 * v ^ 2 + j2 * v + j4) + (i1 * v ^ 2 + j1 * v + j3) / (i2 * w ^ 2 + j2 * w + j4) + (i1 * w ^ 2 + j1 * w + j3) / (i2 * u ^ 2 + j2 * u + j4) by nlinarith
    have h := NEQ_Chebyshev1_div_cycle_square_3vars u v w i1 j1 j3 i2 j2 j4 ha hb hc hd he hf hg
    trivial

theorem NEQ_Chebyshev1_div_right_cycle_square_3vars (u v w i1 i2 j1 j2 j3 j4 k l right : ℝ) (ha : i2 * u ^ 2 + j2 * u + j4 > 0) (hb : i2 * v ^ 2 + j2 * v + j4 > 0) (hc : i2 * w ^ 2 + j2 * w + j4 > 0) (hd : i1 ≥ 0) (he : j1 ≥ 0) (hf : i2 ≥ 0) (hg : j2 ≥ 0) (hh : k ≥ 0)
    (hj : left ≤ k * ((i1 * u ^ 2 + j1 * u + j3) / (i2 * u ^ 2 + j2 * u + j4) + (i1 * v ^ 2 + j1 * v + j3) / (i2 * v ^ 2 + j2 * v + j4) + (i1 * w ^ 2 + j1 * w + j3) / (i2 * w ^ 2 + j2 * w + j4)) + l) :
    left ≤ k * ((i1 * u ^ 2 + j1 * u + j3) / (i2 * v ^ 2 + j2 * v + j4) + (i1 * v ^ 2 + j1 * v + j3) / (i2 * w ^ 2 + j2 * w + j4) + (i1 * w ^ 2 + j1 * w + j3) / (i2 * u ^ 2 + j2 * u + j4)) + l := by
    suffices (i1 * u ^ 2 + j1 * u + j3) / (i2 * v ^ 2 + j2 * v + j4) + (i1 * v ^ 2 + j1 * v + j3) / (i2 * w ^ 2 + j2 * w + j4) + (i1 * w ^ 2 + j1 * w + j3) / (i2 * u ^ 2 + j2 * u + j4) ≥ (i1 * u ^ 2 + j1 * u + j3) / (i2 * u ^ 2 + j2 * u + j4) + (i1 * v ^ 2 + j1 * v + j3) / (i2 * v ^ 2 + j2 * v + j4) + (i1 * w ^ 2 + j1 * w + j3) / (i2 * w ^ 2 + j2 * w + j4) by nlinarith
    have h := NEQ_Chebyshev1_div_cycle_square_3vars u v w i1 j1 j3 i2 j2 j4 ha hb hc hd he hf hg
    trivial

theorem NEQ_Chebyshev1_div_left_cycle_normal_square_3vars (u v w i1 i2 j1 j2 j3 k l left : ℝ) (ha : i2 * u ^ 2 + j1 * u + j3 > 0) (hb : i2 * v ^ 2 + j1 * v + j3 > 0) (hc : i2 * w ^ 2 + j1 * w + j3 > 0) (he : i1 ≥ 0) (hf : i2 ≥ 0) (hg : j1 ≥ 0) (hh : k ≥ 0)
    (hj : k * ((i1 * u + j2) / (i2 * v ^ 2 + j1 * v + j3) + (i1 * v + j2) / (i2 * w ^ 2 + j1 * w + j3) + (i1 * w + j2) / (i2 * u ^ 2 + j1 * u + j3)) + l ≤ right) :
    k * ((i1 * u + j2) / (i2 * u ^ 2 + j1 * u + j3) + (i1 * v + j2) / (i2 * v ^ 2 + j1 * v + j3) + (i1 * w + j2) / (i2 * w ^ 2 + j1 * w + j3)) + l ≤ right := by
    let i0 := (0 : ℝ)
    have h : ∀ (x : ℝ), i0 * x = 0 := by simp
    suffices (i0 * u ^ 2 + i1 * u + j2) / (i2 * u ^ 2 + j1 * u + j3) + (i0 * v ^ 2 + i1 * v + j2) / (i2 * v ^ 2 + j1 * v + j3) + (i0 * w ^ 2 + i1 * w + j2) / (i2 * w ^ 2 + j1 * w + j3) ≤ (i0 * u ^ 2 + i1 * u + j2) / (i2 * v ^ 2 + j1 * v + j3) + (i0 * v ^ 2 + i1 * v + j2) / (i2 * w ^ 2 + j1 * w + j3) + (i0 * w ^ 2 + i1 * w + j2) / (i2 * u ^ 2 + j1 * u + j3) by simp [h] at this; nlinarith
    have hd : i0 ≥ 0 := by simp
    have h := NEQ_Chebyshev1_div_cycle_square_3vars u v w i0 i1 j2 i2 j1 j3 ha hb hc hd he hf hg
    trivial

theorem NEQ_Chebyshev1_div_right_cycle_normal_square_3vars (u v w i1 i2 j1 j2 j3 k l left : ℝ) (ha : i2 * u ^ 2 + j1 * u + j3 > 0) (hb : i2 * v ^ 2 + j1 * v + j3 > 0) (hc : i2 * w ^ 2 + j1 * w + j3 > 0) (he : i1 ≥ 0) (hf : i2 ≥ 0) (hg : j1 ≥ 0) (hh : k ≥ 0)
    (hj : left ≤ k * ((i1 * u + j2) / (i2 * u ^ 2 + j1 * u + j3) + (i1 * v + j2) / (i2 * v ^ 2 + j1 * v + j3) + (i1 * w + j2) / (i2 * w ^ 2 + j1 * w + j3)) + l) :
    left ≤ k * ((i1 * u + j2) / (i2 * v ^ 2 + j1 * v + j3) + (i1 * v + j2) / (i2 * w ^ 2 + j1 * w + j3) + (i1 * w + j2) / (i2 * u ^ 2 + j1 * u + j3)) + l := by
    let i0 := (0 : ℝ)
    have h : ∀ (x : ℝ), i0 * x = 0 := by simp
    suffices (i0 * u ^ 2 + i1 * u + j2) / (i2 * u ^ 2 + j1 * u + j3) + (i0 * v ^ 2 + i1 * v + j2) / (i2 * v ^ 2 + j1 * v + j3) + (i0 * w ^ 2 + i1 * w + j2) / (i2 * w ^ 2 + j1 * w + j3) ≤ (i0 * u ^ 2 + i1 * u + j2) / (i2 * v ^ 2 + j1 * v + j3) + (i0 * v ^ 2 + i1 * v + j2) / (i2 * w ^ 2 + j1 * w +
    j3) + (i0 * w ^ 2 + i1 * w + j2) / (i2 * u ^ 2 + j1 * u + j3) by simp [h] at this; nlinarith
    have hd : i0 ≥ 0 := by simp
    have h := NEQ_Chebyshev1_div_cycle_square_3vars u v w i0 i1 j2 i2 j1 j3 ha hb hc hd he hf hg
    trivial

theorem NEQ_Chebyshev2_mul_cycle_3vars (u v w : ℝ) : (u * v + v * w + w * u ≤ u ^ 2 + v ^ 2 + w ^ 2) := by
  suffices 2 * (u ^ 2 + v ^ 2 + w ^ 2) - 2 * (u * v + v * w + w * u) ≥ 0 by linarith
  have h : (u - v) ^ 2 + (v - w) ^ 2 + (w - u) ^ 2 ≥ 0 := by positivity
  convert h using 1
  nlinarith

theorem NEQ_Chebyshev2_mul_cycle_normal_3vars (u v w i1 j1 i2 j2 : ℝ) (ha : i1 ≥ 0) (hb : i2 ≥ 0) : (i1 * u + j1) * (i2 * v + j2) + (i1 * v + j1) * (i2 * w + j2) + (i1 * w + j1) * (i2 * u + j2) ≤ (i1 * u + j1) * (i2 * u + j2) + (i1 * v + j1) * (i2 * v + j2) + (i1 * w + j1) * (i2 * w + j2) := by
  by_cases h : i2 = 0
  rw [h]; simp;
  have h : i2 > 0 := by positivity
  let u1 := u * (i2 * u + j2); let v1 := v * (i2 * v + j2); let w1 := w * (i2 * w + j2)
  let u2 := u * (i2 * v + j2); let v2 := v * (i2 * w + j2); let w2 := w * (i2 * u + j2)
  rw [show (i1 * u + j1) * (i2 * v + j2) = i1 * u2 + j1 * (i2 * v + j2) by unfold_let u2; nlinarith]
  rw [show (i1 * v + j1) * (i2 * w + j2) = i1 * v2 + j1 * (i2 * w + j2) by unfold_let v2; nlinarith]
  rw [show (i1 * w + j1) * (i2 * u + j2) = i1 * w2 + j1 * (i2 * u + j2) by unfold_let w2; nlinarith]
  rw [show (i1 * u + j1) * (i2 * u + j2) = i1 * u1 + j1 * (i2 * u + j2) by unfold_let u1; nlinarith]
  rw [show (i1 * v + j1) * (i2 * v + j2) = i1 * v1 + j1 * (i2 * v + j2) by unfold_let v1; nlinarith]
  rw [show (i1 * w + j1) * (i2 * w + j2) = i1 * w1 + j1 * (i2 * w + j2) by unfold_let w1; nlinarith]
  suffices i1 * u2 + i1 * v2 + i1 * w2 ≤ i1 * u1 + i1 * v1 + i1 * w1 by nlinarith
  suffices u2 + v2 + w2 ≤ u1 + v1 + w1 by nlinarith
  have h0 := NEQ_Chebyshev2_mul_cycle_3vars (i2 * u + j2) (i2 * v + j2) (i2 * w + j2)
  rw [show (i2 * u + j2) * (i2 * v + j2) = i2 * u2 + j2 * (i2 * v + j2) by unfold_let u2; nlinarith] at h0
  rw [show (i2 * v + j2) * (i2 * w + j2) = i2 * v2 + j2 * (i2 * w + j2) by unfold_let v2; nlinarith] at h0
  rw [show (i2 * w + j2) * (i2 * u + j2) = i2 * w2 + j2 * (i2 * u + j2) by unfold_let w2; nlinarith] at h0
  rw [show (i2 * u + j2) ^ 2 = i2 * u1 + j2 * (i2 * u + j2) by unfold_let u1; nlinarith] at h0
  rw [show (i2 * v + j2) ^ 2 = i2 * v1 + j2 * (i2 * v + j2) by unfold_let v1; nlinarith] at h0
  rw [show (i2 * w + j2) ^ 2 = i2 * w1 + j2 * (i2 * w + j2) by unfold_let w1; nlinarith] at h0
  have h0 : i2 * u2 - i2 * v1 + (i2 * v2 - i2 * w1) + (i2 * w2 - i2 * u1) ≤ 0 := by linarith
  nlinarith

theorem NEQ_Chebyshev2_mul_right_cycle_normal_3vars (u v w i1 j1 i2 j2 k l left : ℝ) (ha : i1 ≥ 0) (hb : i2 ≥ 0) (hc : k ≥ 0)
    (hj : left ≤ k * ((i1 * u + j1) * (i2 * v + j2) + (i1 * v + j1) * (i2 * w + j2) + (i1 * w + j1) * (i2 * u + j2)) + l):
    left ≤ k * ((i1 * u + j1) * (i2 * u + j2) + (i1 * v + j1) * (i2 * v + j2) + (i1 * w + j1) * (i2 * w + j2)) + l := by
  suffices (i1 * u + j1) * (i2 * v + j2) + (i1 * v + j1) * (i2 * w + j2) + (i1 * w + j1) * (i2 * u + j2) ≤ (i1 * u + j1) * (i2 * u + j2) + (i1 * v + j1) * (i2 * v + j2) + (i1 * w + j1) * (i2 * w + j2) by nlinarith
  have h : (i1 * u + j1) * (i2 * v + j2) + (i1 * v + j1) * (i2 * w + j2) + (i1 * w + j1) * (i2 * u + j2) ≤ (i1 * u + j1) * (i2 * u + j2) + (i1 * v + j1) * (i2 * v + j2) + (i1 * w + j1) * (i2 * w + j2) := by
    apply NEQ_Chebyshev2_mul_cycle_normal_3vars u v w i1 j1 i2 j2 ha hb
  trivial

theorem NEQ_Chebyshev2_mul_left_cycle_normal_3vars (u v w i1 j1 i2 j2 k l right : ℝ) (ha : i1 ≥ 0) (hb : i2 ≥ 0) (hc : k ≥ 0)
    (hj : k * ((i1 * u + j1) * (i2 * u + j2) + (i1 * v + j1) * (i2 * v + j2) + (i1 * w + j1) * (i2 * w + j2)) + l ≤ right) :
    k * ((i1 * u + j1) * (i2 * v + j2) + (i1 * v + j1) * (i2 * w + j2) + (i1 * w + j1) * (i2 * u + j2)) + l ≤ right := by
  suffices (i1 * u + j1) * (i2 * v + j2) + (i1 * v + j1) * (i2 * w + j2) + (i1 * w + j1) * (i2 * u + j2) ≤ (i1 * u + j1) * (i2 * u + j2) + (i1 * v + j1) * (i2 * v + j2) + (i1 * w + j1) * (i2 * w + j2) by nlinarith
  have h : (i1 * u + j1) * (i2 * v + j2) + (i1 * v + j1) * (i2 * w + j2) + (i1 * w + j1) * (i2 * u + j2) ≤ (i1 * u + j1) * (i2 * u + j2) + (i1 * v + j1) * (i2 * v + j2) + (i1 * w + j1) * (i2 * w + j2) := by
    apply NEQ_Chebyshev2_mul_cycle_normal_3vars u v w i1 j1 i2 j2 ha hb
  trivial


theorem NEQ_Chebyshev2_mul_cycle_square_3vars (u v w i1 i2 i3 j1 j2 j3 : ℝ) (ha : i1 ≥ 0) (hb : i2 ≥ 0) (hc : j1 ≥ 0) (hd : j2 ≥ 0) (he : u ≥ 0) (hf : v ≥ 0) (hg : w ≥ 0) :
  ((i1 * u ^ 2 + i2 * u + i3) * (j1 * v ^ 2 + j2 * v + j3) + (i1 * v ^ 2 + i2 * v + i3) * (j1 * w ^ 2 + j2 * w + j3) + (i1 * w ^ 2 + i2 * w + i3) * (j1 * u ^ 2 + j2 * u + j3) ≤ (i1 * u ^ 2 + i2 * u + i3) * (j1 * u ^ 2 + j2 * u + j3) + (i1 * v ^ 2 + i2 * v + i3) * (j1 * v ^ 2 + j2 * v + j3) + (i1 * w ^ 2 + i2 * w + i3) * (j1 * w ^ 2 + j2 * w + j3)) := by
  sorry

theorem NEQ_Chebyshev2_mul_left_cycle_square_3vars (u v w i1 i2 j1 j2 j3 j4 k l right : ℝ) (ha : i1 ≥ 0) (hb : j1 ≥ 0) (hc : i2 ≥ 0) (hd : j2 ≥ 0) (he : u ≥ 0) (hf : v ≥ 0) (hg : w ≥ 0) (hh : k ≥ 0)
    (hj : k * ((i1 * u ^ 2 + j1 * u + j3) * (i2 * u ^ 2 + j2 * u + j4) + (i1 * v ^ 2 + j1 * v + j3) * (i2 * v ^ 2 + j2 * v + j4) + (i1 * w ^ 2 + j1 * w + j3) * (i2 * w ^ 2 + j2 * w + j4)) + l ≤ right) :
    k * ((i1 * u ^ 2 + j1 * u + j3) * (i2 * v ^ 2 + j2 * v + j4) + (i1 * v ^ 2 + j1 * v + j3) * (i2 * w ^ 2 + j2 * w + j4) + (i1 * w ^ 2 + j1 * w + j3) * (i2 * u ^ 2 + j2 * u + j4)) + l ≤ right := by
    suffices ((i1 * u ^ 2 + j1 * u + j3) * (i2 * v ^ 2 + j2 * v + j4) + (i1 * v ^ 2 + j1 * v + j3) * (i2 * w ^ 2 + j2 * w + j4) + (i1 * w ^ 2 + j1 * w + j3) * (i2 * u ^ 2 + j2 * u + j4) ≤ (i1 * u ^ 2 + j1 * u + j3) * (i2 * u ^ 2 + j2 * u + j4) + (i1 * v ^ 2 + j1 * v + j3) * (i2 * v ^ 2 + j2 * v + j4) + (i1 * w ^ 2 + j1 * w + j3) * (i2 * w ^ 2 + j2 * w + j4)) by nlinarith
    have h := NEQ_Chebyshev2_mul_cycle_square_3vars u v w i1 j1 j3 i2 j2 j4 ha hb hc hd he hf hg
    trivial

theorem NEQ_Chebyshev2_mul_right_cycle_square_3vars (u v w i1 i2 j1 j2 j3 j4 k l left : ℝ) (ha : i1 ≥ 0) (hb : j1 ≥ 0) (hc : i2 ≥ 0) (hd : j2 ≥ 0) (he : u ≥ 0) (hf : v ≥ 0) (hg : w ≥ 0) (hh : k ≥ 0)
    (hj : left ≤ k * ((i1 * u ^ 2 + j1 * u + j3) * (i2 * v ^ 2 + j2 * v + j4) + (i1 * v ^ 2 + j1 * v + j3) * (i2 * w ^ 2 + j2 * w + j4) + (i1 * w ^ 2 + j1 * w + j3) * (i2 * u ^ 2 + j2 * u + j4)) + l) :
    left ≤ k * ((i1 * u ^ 2 + j1 * u + j3) * (i2 * u ^ 2 + j2 * u + j4) + (i1 * v ^ 2 + j1 * v + j3) * (i2 * v ^ 2 + j2 * v + j4) + (i1 * w ^ 2 + j1 * w + j3) * (i2 * w ^ 2 + j2 * w + j4)) + l := by
    suffices ((i1 * u ^ 2 + j1 * u + j3) * (i2 * v ^ 2 + j2 * v + j4) + (i1 * v ^ 2 + j1 * v + j3) * (i2 * w ^ 2 + j2 * w + j4) + (i1 * w ^ 2 + j1 * w + j3) * (i2 * u ^ 2 + j2 * u + j4) ≤ (i1 * u ^ 2 + j1 * u + j3) * (i2 * u ^ 2 + j2 * u + j4) + (i1 * v ^ 2 + j1 * v + j3) * (i2 * v ^ 2 + j2 * v + j4) + (i1 * w ^ 2 + j1 * w + j3) * (i2 * w ^ 2 + j2 * w + j4)) by nlinarith
    have h := NEQ_Chebyshev2_mul_cycle_square_3vars u v w i1 j1 j3 i2 j2 j4 ha hb hc hd he hf hg
    trivial

theorem NEQ_Chebyshev2_mul_left_cycle_normal_square_3vars (u v w i1 i2 j1 j2 j3 k l right : ℝ) (hb : i1 ≥ 0) (hc : i2 ≥ 0) (hd : j2 ≥ 0) (he : u ≥ 0) (hf : v ≥ 0) (hg : w ≥ 0) (hh : k ≥ 0)
    (hj : k * ((i1 * u + j1) * (i2 * u ^ 2 + j2 * u + j3) + (i1 * v + j1) * (i2 * v ^ 2 + j2 * v + j3) + (i1 * w + j1) * (i2 * w ^ 2 + j2 * w + j3)) + l ≤ right) :
    k * ((i1 * u + j1) * (i2 * v ^ 2 + j2 * v + j3) + (i1 * v + j1) * (i2 * w ^ 2 + j2 * w + j3) + (i1 * w + j1) * (i2 * u ^ 2 + j2 * u + j3)) + l ≤ right := by
    let i0 := (0 : ℝ)
    have h : ∀ (x : ℝ), i0 * x = 0 := by simp
    suffices ((i0 * u ^ 2 + i1 * u + j1) * (i2 * v ^ 2 + j2 * v + j3) + (i0 * v ^ 2 + i1 * v + j1) * (i2 * w ^ 2 + j2 * w + j3) + (i0 * w ^ 2 + i1 * w + j1) * (i2 * u ^ 2 + j2 * u + j3)
        ≤ (i0 * u ^ 2 + i1 * u + j1) * (i2 * u ^ 2 + j2 * u + j3) + (i0 * v ^ 2 + i1 * v + j1) * (i2 * v ^ 2 + j2 * v + j3) + (i0 * w ^ 2 + i1 * w + j1) * (i2 * w ^ 2 + j2 * w + j3)) by simp [h] at this; nlinarith
    have ha : i0 ≥ 0 := by simp
    have h := NEQ_Chebyshev2_mul_cycle_square_3vars u v w i0 i1 j1 i2 j2 j3 ha hb hc hd he hf hg
    trivial

theorem NEQ_Chebyshev2_mul_right_cycle_normal_square_3vars (u v w i1 i2 j1 j2 j3 k l left : ℝ) (hb : i1 ≥ 0) (hc : i2 ≥ 0) (hd : j2 ≥ 0) (he : u ≥ 0) (hf : v ≥ 0) (hg : w ≥ 0) (hh : k ≥ 0)
    (hj : left ≤ k * ((i1 * u + j1) * (i2 * v ^ 2 + j2 * v + j3) + (i1 * v + j1) * (i2 * w ^ 2 + j2 * w + j3) + (i1 * w + j1) * (i2 * u ^ 2 + j2 * u + j3)) + l) :
    left ≤ k * ((i1 * u + j1) * (i2 * u ^ 2 + j2 * u + j3) + (i1 * v + j1) * (i2 * v ^ 2 + j2 * v + j3) + (i1 * w + j1) * (i2 * w ^ 2 + j2 * w + j3)) + l := by
    let i0 := (0 : ℝ)
    have h : ∀ (x : ℝ), i0 * x = 0 := by simp
    suffices ((i0 * u ^ 2 + i1 * u + j1) * (i2 * v ^ 2 + j2 * v + j3) + (i0 * v ^ 2 + i1 * v + j1) * (i2 * w ^ 2 + j2 * w + j3) + (i0 * w ^ 2 + i1 * w + j1) * (i2 * u ^ 2 + j2 * u + j3)
        ≤ (i0 * u ^ 2 + i1 * u + j1) * (i2 * u ^ 2 + j2 * u + j3) + (i0 * v ^ 2 + i1 * v + j1) * (i2 * v ^ 2 + j2 * v + j3) + (i0 * w ^ 2 + i1 * w + j1) * (i2 * w ^ 2 + j2 * w + j3)) by simp [h] at this; nlinarith
    have ha : i0 ≥ 0 := by simp
    have h := NEQ_Chebyshev2_mul_cycle_square_3vars u v w i0 i1 j1 i2 j2 j3 ha hb hc hd he hf hg
    trivial
