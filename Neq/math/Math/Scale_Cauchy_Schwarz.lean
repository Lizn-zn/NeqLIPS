import Mathlib

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

/- ========================== Cauchy Schwarz inequalities ========================== -/

theorem squared (a b : ℝ) (h1 : b ≥ 0) (h2 : a ^ 2 ≤ b ^ 2) : (a ≤ b) := by nlinarith

section Scale_Cauchy_Schwarz_2vars
/-- The base lemma: Cauchy Schwarz inequalities for 2 variables -/
theorem Cauchy_Schwarz_2vars (u₁ u₂ v₁ v₂ : ℝ) : (u₁ * v₁ + u₂ * v₂) ^ 2 ≤ (u₁ ^ 2 + u₂ ^ 2) * (v₁ ^ 2 + v₂ ^ 2) := by
  let f : ℕ → ℝ | 0 => u₁ | 1 => u₂ | _ => 0
  let g : ℕ → ℝ | 0 => v₁ | 1 => v₂ | _ => 0
  let s : Finset ℕ := {0, 1}
  have h := Finset.sum_mul_sq_le_sq_mul_sq s f g
  simp [f, s] at h
  simp [g, s] at h
  trivial


/-- The normal form of Cauchy Schwarz inequalities for 2 variables -/
theorem Cauchy_Schwarz_normal_left_2vars (u1 u2 v1 v2 k l right : ℝ) (h1 : k ≥ 0) (h2 : k * (u1 ^ 2 + u2 ^ 2) * (v1 ^ 2 + v2 ^ 2) + l ≤ right) : k * (u1 * v1 + u2 * v2) ^ 2 + l ≤ right := by
  suffices (u1 * v1 + u2 * v2) ^ 2 ≤ (u1 ^ 2 + u2 ^ 2) * (v1 ^ 2 + v2 ^ 2) by nlinarith
  have h : (u1 * v1 + u2 * v2) ^ 2 ≤ (u1 ^ 2 + u2 ^ 2) * (v1 ^ 2 + v2 ^ 2) := by apply Cauchy_Schwarz_2vars u1 u2 v1 v2
  trivial

theorem Cauchy_Schwarz_normal_right_2vars (u1 u2 v1 v2 k l left : ℝ) (h1 : k ≥ 0) (h2 : left ≤ k * (u1 * v1 + u2 * v2) ^ 2 + l) : left ≤ k * (u1 ^ 2 + u2 ^ 2) * (v1 ^ 2 + v2 ^ 2) + l := by
  apply h2.trans
  suffices (u1 * v1 + u2 * v2) ^ 2 ≤ (u1 ^ 2 + u2 ^ 2) * (v1 ^ 2 + v2 ^ 2) by nlinarith
  have h : (u1 * v1 + u2 * v2) ^ 2 ≤ (u1 ^ 2 + u2 ^ 2) * (v1 ^ 2 + v2 ^ 2) := by apply Cauchy_Schwarz_2vars u1 u2 v1 v2
  trivial

/-- The square root form of Cauchy Schwarz inequalities for 2 variables -/
theorem Cauchy_Schwarz_sqrt_left_2vars (u1 u2 v1 v2 k l right : ℝ) (h1 : k ≥ 0)
  (h2 : k * sqrt (u1 ^ 2 + u2 ^ 2) * sqrt (v1 ^ 2 + v2 ^ 2) + l ≤ right) :
  k * (u1 * v1 + u2 * v2) + l ≤ right := by
  suffices (u1 * v1 + u2 * v2) ≤ sqrt (u1 ^ 2 + u2 ^ 2) * sqrt (v1 ^ 2 + v2 ^ 2) by nlinarith
  have h : (u1 * v1 + u2 * v2) ^ 2 ≤ (u1 ^ 2 + u2 ^ 2) * (v1 ^ 2 + v2 ^ 2) := by apply Cauchy_Schwarz_2vars u1 u2 v1 v2
  apply squared
  positivity
  convert h using 1
  rw [mul_pow, sq_sqrt, sq_sqrt]
  all_goals positivity

theorem Cauchy_Schwarz_sqrt_right_2vars (u1 u2 v1 v2 k l left : ℝ) (h1 : k ≥ 0)
  (h2 : left ≤ k * (u1 * v1 + u2 * v2) + l) :
  left ≤ k * sqrt (u1 ^ 2 + u2 ^ 2) * sqrt (v1 ^ 2 + v2 ^ 2) + l := by
  apply h2.trans
  suffices (u1 * v1 + u2 * v2) ≤ sqrt (u1 ^ 2 + u2 ^ 2) * sqrt (v1 ^ 2 + v2 ^ 2) by nlinarith
  have h : (u1 * v1 + u2 * v2) ^ 2 ≤ (u1 ^ 2 + u2 ^ 2) * (v1 ^ 2 + v2 ^ 2) := by apply Cauchy_Schwarz_2vars u1 u2 v1 v2
  apply squared
  positivity
  convert h using 1
  rw [mul_pow, sq_sqrt, sq_sqrt]
  all_goals positivity

/-- Cauchy_Schwarz cycle version -/
theorem Cauchy_Schwarz_sqrt_cycle_left_2vars (u1 u2 u3 u4 u5 u6 v1 v2 v3 v4 v5 v6 k l right : ℝ) (hk : k ≥ 0)
  (h : k * (sqrt (u1 ^ 2 + u2 ^ 2) * sqrt (v1 ^ 2 + v2 ^ 2) + sqrt (u3 ^ 2 + u4 ^ 2) * sqrt (v3 ^ 2 + v4 ^ 2) + sqrt (u5 ^ 2 + u6 ^ 2) * sqrt (v5 ^ 2 + v6 ^ 2)) + l ≤ right)
  : k * (u1 * v1 + u2 * v2 + u3 * v3 + u4 * v4 + u5 * v5 + u6 * v6) + l ≤ right := by
  suffices (u1 * v1 + u2 * v2 + u3 * v3 + u4 * v4 + u5 * v5 + u6 * v6) ≤ sqrt (u1 ^ 2 + u2 ^ 2) * sqrt (v1 ^ 2 + v2 ^ 2) + sqrt (u3 ^ 2 + u4 ^ 2) * sqrt (v3 ^ 2 + v4 ^ 2) + sqrt (u5 ^ 2 + u6 ^ 2) * sqrt (v5 ^ 2 + v6 ^ 2) by nlinarith
  have h1 : (u1 * v1 + u2 * v2) ≤ sqrt (u1 ^ 2 + u2 ^ 2) * sqrt (v1 ^ 2 + v2 ^ 2) := by apply squared; positivity; rw [mul_pow]; rw [sq_sqrt]; rw [sq_sqrt]; apply Cauchy_Schwarz_2vars u1 u2 v1 v2; all_goals positivity
  have h2 : (u3 * v3 + u4 * v4) ≤ sqrt (u3 ^ 2 + u4 ^ 2) * sqrt (v3 ^ 2 + v4 ^ 2) := by apply squared; positivity; rw [mul_pow]; rw [sq_sqrt]; rw [sq_sqrt]; apply Cauchy_Schwarz_2vars u3 u4 v3 v4; all_goals positivity
  have h3 : (u5 * v5 + u6 * v6) ≤ sqrt (u5 ^ 2 + u6 ^ 2) * sqrt (v5 ^ 2 + v6 ^ 2) := by apply squared; positivity; rw [mul_pow]; rw [sq_sqrt]; rw [sq_sqrt]; apply Cauchy_Schwarz_2vars u5 u6 v5 v6; all_goals positivity
  have h := add_le_add h1 (add_le_add h2 h3)
  nlinarith

theorem Cauchy_Schwarz_sqrt_cycle_right_2vars (u1 u2 u3 u4 u5 u6 v1 v2 v3 v4 v5 v6 k l left : ℝ) (hu1: u1 ≥ 0) (hu2: u2 ≥ 0) (hu3: u3 ≥ 0) (hu4: u4 ≥ 0) (hu5: u5 ≥ 0) (hu6: u6 ≥ 0)
  (hv1 : v1 ≥ 0) (hv2 : v2 ≥ 0) (hv3 : v3 ≥ 0) (hv4 : v4 ≥ 0) (hv5 : v5 ≥ 0) (hv6 : v6 ≥ 0) (hk : k ≥ 0)
  (h : left ≤ k * (sqrt (u1 * v1) + sqrt (u2 * v2) + sqrt (u3 * v3) + sqrt (u4 * v4) + sqrt (u5 * v5) + sqrt (u6 * v6)) + l)
  : left ≤ k * (sqrt (u1 + u2) * sqrt (v1 + v2) + sqrt (u3 + u4) * sqrt (v3 + v4) + sqrt (u5 + u6) * sqrt (v5 + v6)) + l := by
  suffices k * (sqrt (u1 * v1) + sqrt (u2 * v2) + sqrt (u3 * v3) + sqrt (u4 * v4) + sqrt (u5 * v5) + sqrt (u6 * v6)) + l ≤ k * (sqrt (u1 + u2) * sqrt (v1 + v2) + sqrt (u3 + u4) * sqrt (v3 + v4) + sqrt (u5 + u6) * sqrt (v5 + v6)) + l by nlinarith
  have h1 : (sqrt (u1 * v1) + sqrt (u2 * v2)) ≤ sqrt (u1 + u2) * sqrt (v1 + v2) := by
    apply squared;
    positivity;
    rw [mul_pow]; rw [sq_sqrt]; rw [sq_sqrt];
    have h_ := Cauchy_Schwarz_2vars (sqrt u1) (sqrt u2) (sqrt v1) (sqrt v2);
    simp [sq_sqrt, *] at h_;
    convert h_ using 1;
    simp [sq_sqrt, *];
    all_goals positivity
  have h2 : (sqrt (u3 * v3) + sqrt (u4 * v4)) ≤ sqrt (u3 + u4) * sqrt (v3 + v4) := by
    apply squared;
    positivity;
    rw [mul_pow]; rw [sq_sqrt]; rw [sq_sqrt];
    have h_ := Cauchy_Schwarz_2vars (sqrt u3) (sqrt u4) (sqrt v3) (sqrt v4);
    simp [sq_sqrt, *] at h_;
    convert h_ using 1;
    simp [sq_sqrt, *];
    all_goals positivity
  have h3 : (sqrt (u5 * v5) + sqrt (u6 * v6)) ≤ sqrt (u5 + u6) * sqrt (v5 + v6) := by
    apply squared;
    positivity;
    rw [mul_pow]; rw [sq_sqrt]; rw [sq_sqrt];
    have h_ := Cauchy_Schwarz_2vars (sqrt u5) (sqrt u6) (sqrt v5) (sqrt v6);
    simp [sq_sqrt, *] at h_;
    convert h_ using 1;
    simp [sq_sqrt, *];
    all_goals positivity
  have h := add_le_add h1 (add_le_add h2 h3)
  nlinarith

end Scale_Cauchy_Schwarz_2vars

section Scale_Cauchy_Schwarz_3vars

/-- The base lemma: Cauchy Schwarz inequalities for 3 variables -/
theorem Cauchy_Schwarz_3vars (u₁ u₂ u₃ v₁ v₂ v₃ : ℝ) : (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) ^ 2 ≤ (u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2) * (v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2) := by
  let f : ℕ → ℝ | 0 => u₁ | 1 => u₂ | 2 => u₃ | _ => 0
  let g : ℕ → ℝ | 0 => v₁ | 1 => v₂ | 2 => v₃ | _ => 0
  let s : Finset ℕ := {0, 1, 2}
  have h := Finset.sum_mul_sq_le_sq_mul_sq s f g
  simp [f, s] at h
  simp [g, s] at h
  simp only [<-add_assoc] at h
  trivial

/-- The normal form of Cauchy Schwarz inequalities for 3 variables -/
theorem Cauchy_Schwarz_normal_left_3vars (u1 u2 u3 v1 v2 v3 k l right : ℝ) (h1 : k ≥ 0) (h2 : k * (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) + l ≤ right) : k * (u1 * v1 + u2 * v2 + u3 * v3) ^ 2 + l ≤ right := by
  suffices (u1 * v1 + u2 * v2 + u3 * v3) ^ 2 ≤ (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) by nlinarith
  have h : (u1 * v1 + u2 * v2 + u3 * v3) ^ 2 ≤ (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) := by apply Cauchy_Schwarz_3vars u1 u2 u3 v1 v2 v3
  trivial

theorem Cauchy_Schwarz_normal_right_3vars (u1 u2 u3 v1 v2 v3 k l left : ℝ) (h1 : k ≥ 0) (h2 : left ≤ k * (u1 * v1 + u2 * v2 + u3 * v3) ^ 2 + l) : left ≤ k * (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) + l := by
  suffices (u1 * v1 + u2 * v2 + u3 * v3) ^ 2 ≤ (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) by nlinarith
  have h : (u1 * v1 + u2 * v2 + u3 * v3) ^ 2 ≤ (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) := by apply Cauchy_Schwarz_3vars u1 u2 u3 v1 v2 v3
  trivial


/-- The square root form of Cauchy Schwarz inequalities for 3 variables -/
theorem Cauchy_Schwarz_sqrt_left_3vars (u1 u2 u3 v1 v2 v3 k l right : ℝ) (h1 : k ≥ 0) (h2 : k * sqrt (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * sqrt (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) + l ≤ right) : k * (u1 * v1 + u2 * v2 + u3 * v3) + l ≤ right := by
  suffices (u1 * v1 + u2 * v2 + u3 * v3) ≤ sqrt (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * sqrt (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) by nlinarith
  have h : (u1 * v1 + u2 * v2 + u3 * v3) ^ 2 ≤ (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) := by apply Cauchy_Schwarz_3vars u1 u2 u3 v1 v2 v3
  apply squared
  positivity
  convert h using 1
  rw [mul_pow, sq_sqrt, sq_sqrt]
  all_goals positivity

theorem Cauchy_Schwarz_sqrt_right_3vars (u1 u2 u3 v1 v2 v3 k l left : ℝ) (h1 : k ≥ 0) (h2 : left ≤ k * (u1 * v1 + u2 * v2 + u3 * v3) + l) : left ≤ k * sqrt (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * sqrt (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) + l := by
  suffices (u1 * v1 + u2 * v2 + u3 * v3) ≤ sqrt (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * sqrt (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) by nlinarith
  have h : (u1 * v1 + u2 * v2 + u3 * v3) ^ 2 ≤ (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) := by apply Cauchy_Schwarz_3vars u1 u2 u3 v1 v2 v3
  apply squared
  positivity
  convert h using 1
  rw [mul_pow, sq_sqrt, sq_sqrt]
  all_goals positivity

end Scale_Cauchy_Schwarz_3vars


-- EOC of Cauchy-Schwarz inequalities
