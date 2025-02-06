import Mathlib

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

-- ========================== AM-GM inequalities ==========================

section Scale_AM_GM_2vars

/-- The base lemma: AM-GM inequalities for 2 variables -/
theorem AM_GM_2vars (u v : ℝ) (h1 : u ≥ 0) (h2 : v ≥ 0) : 2 * sqrt (u * v) ≤ u + v := by
  suffices 0 ≤ u + v - 2 * sqrt (u * v) by nlinarith
  have h : 0 ≤ (sqrt u - sqrt v) ^ 2 := by positivity
  convert h using 1
  rw [sq]
  simp [mul_sub_left_distrib, mul_sub_right_distrib, sqrt_mul]
  have h : ∀ a b c : ℝ, a - (b - c) = a - b + c := by intros; linarith
  simp [h]
  simp [*, <-sq, sq_sqrt]
  nlinarith

/-- The normal form u + v ≥ 2√uv of AM-GM inequalities for 2 variables -/
theorem AM_GM_normal_left_2vars (u v k l right : ℝ) (h1 : k ≥ 0) (h2 : u ≥ 0) (h3 : v ≥ 0) (h4 : k * (u + v) / 2 + l ≤ right) : k * sqrt (u * v) + l ≤ right := by
  suffices 2 * sqrt (u * v) ≤ u + v by nlinarith
  have h : 2 * sqrt (u * v) ≤ u + v := by apply AM_GM_2vars u v; all_goals assumption
  trivial

theorem AM_GM_normal_right_2vars (u v k l left : ℝ) (h1 : k ≥ 0) (h2 : u ≥ 0) (h3 : v ≥ 0) (h4 : left ≤ 2 * k * sqrt (u * v) + l) : left ≤ k * (u + v) + l := by
  suffices 2 * sqrt (u * v) ≤ u + v by nlinarith
  have h : 2 * sqrt (u * v) ≤ u + v := by apply AM_GM_2vars u v; all_goals positivity
  convert h using 1

/-- The squared form u² + v² ≥ 2uv of AM-GM inequalities for 2 variables -/
theorem AM_GM_square_left_2vars (u v k l right : ℝ) (h1 : k ≥ 0) (h4 : k * (u ^ 2 + v ^ 2) / 2 + l ≤ right) : k * (u * v) + l ≤ right := by
  suffices (u - v) ^ 2 ≥ 0 by nlinarith
  positivity

theorem AM_GM_square_right_2vars (u v k l left : ℝ) (h1 : k ≥ 0) (h4 : left ≤ 2 * k * (u * v) + l) : left ≤ k * (u ^ 2 + v ^ 2) + l := by
  suffices (u - v) ^ 2 ≥ 0 by nlinarith
  positivity


/-- The div form 1 / (u + v) ≤  1/ 2√uv of AM-GM inequalities for 2 variables -/
theorem AM_GM_div_normal(u v i j : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hi : i ≥ 0) (hj : 2 * i * sqrt (u * v) + j > 0) : 1 / (i * (u + v) + j) ≤ 1 / (2 * i * sqrt (u * v) + j) := by
  suffices 2 * sqrt (u * v) ≤ (u + v) by apply one_div_le_one_div_of_le; positivity; nlinarith
  exact AM_GM_2vars u v hu hv

theorem AM_GM_div_left_2vars (u v i j k l right : ℝ) (hk : k ≥ 0) (hi : i ≥ 0) (hu : u ≥ 0) (hv : v ≥ 0) (hj : 2 * i * sqrt (u * v) + j > 0) (h : k * (1 / (2 * i * sqrt (u * v) + j)) + l ≤ right)  : k * (1 / (i * (u + v) + j)) + l ≤ right := by
  suffices (1 / (i * (u + v) + j)) ≤ (1 / (2 * i * sqrt (u * v) + j)) by nlinarith
  suffices (2 * i * sqrt (u * v) + j) ≤ i * (u + v) + j by apply one_div_le_one_div_of_le; positivity; trivial
  suffices 2 * sqrt (u * v) ≤ (u + v) by nlinarith
  exact AM_GM_2vars u v hu hv

theorem AM_GM_div_right_2vars (u v i j k l left : ℝ) (hk : k ≥ 0) (hi : i ≥ 0) (hu : u ≥ 0) (hv : v ≥ 0) (hj : i * sqrt (u * v) + j > 0) (h : left ≤ k * (1 / (i * (u + v) / 2 + j)) + l) : left ≤ k * (1 / (i * sqrt (u * v) + j)) + l := by
  suffices (1 / (i * (u + v) / 2 + j)) ≤ (1 / (i * sqrt (u * v) + j)) by nlinarith
  suffices (i * sqrt (u * v) + j) ≤ i * (u + v) / 2 + j by apply one_div_le_one_div_of_le; positivity; trivial
  suffices 2 * sqrt (u * v) ≤ (u + v) by nlinarith
  exact AM_GM_2vars u v hu hv

/-- The div squared form 1 / (u² + v²) ≤ 1 / 2uv of AM-GM inequalities for 2 variables -/
theorem AM_GM_div_square_left_2vars (u v i j k l right : ℝ) (hk : k ≥ 0) (hi : i ≥ 0) (hj : 2 * i * u * v + j > 0) (h : k * (1 / (2 * i * u * v + j)) + l ≤ right)  : k * (1 / (i * (u ^ 2 + v ^ 2) + j)) + l ≤ right := by
  suffices (1 / (i * (u ^ 2 + v ^ 2) + j)) ≤ (1 / (2 * i * u * v + j)) by nlinarith
  suffices (2 * i * u * v + j) ≤ i * (u ^ 2 + v ^ 2) + j by apply one_div_le_one_div_of_le; positivity; trivial
  suffices u * v ≤ (u ^ 2 + v ^ 2) / 2 by nlinarith
  suffices 0 ≤ (u - v) ^ 2 by nlinarith
  positivity

theorem AM_GM_div_square_right_2vars (u v i j k l left : ℝ) (hk : k ≥ 0) (hi : i ≥ 0) (hj : i * u * v + j > 0) (h : left ≤ k * (1 / (i * (u ^ 2 + v ^ 2) / 2 + j)) + l) : left ≤ k * (1 / (i * u * v + j)) + l := by
  suffices (1 / (i * (u ^ 2 + v ^ 2) / 2 + j)) ≤ (1 / (i * u * v + j)) by nlinarith
  suffices (i * u * v + j) ≤ i * (u ^ 2 + v ^ 2) / 2 + j by apply one_div_le_one_div_of_le; positivity; trivial
  suffices 0 ≤ (u ^ 2 + v ^ 2) - 2 * u * v by nlinarith
  suffices 0 ≤ (u - v) ^ 2 by nlinarith
  positivity

/-- The div cycle form 1 / (u1 + v1 / 2 + u2 + v2 / 2 + u3 + v3 / 2) ≤ 1 / (sqrt u1v1 + sqrt u2v2 + sqrt u3v3) of AM-GM inequalities for 3 variables -/
theorem AM_GM_div_cycle_normal_2vars (u1 v1 u2 v2 u3 v3 i1 j1 i2 j2 i3 j3) (hu1 : u1 ≥ 0) (hv1 : v1 ≥ 0) (hu2 : u2 ≥ 0) (hv2 : v2 ≥ 0) (hu3 : u3 ≥ 0) (hv3 : v3 ≥ 0)
    (hi1 : i1 ≥ 0) (hj1 : 2 * i1 * sqrt (u1 * v1) + j1 > 0)
    (hi2 : i2 ≥ 0) (hj2 : 2 * i2 * sqrt (u2 * v2) + j2 > 0)
    (hi3 : i3 ≥ 0) (hj3 : 2 * i3 * sqrt (u3 * v3) + j3 > 0) :
    1 / (i1 * (u1 + v1) + j1) + 1 / (i2 * (u2 + v2) + j2) + 1 / (i3 * (u3 + v3) + j3) ≤ 1 / (2 * i1 * sqrt (u1 * v1) + j1) + 1 / (2 * i2 * sqrt (u2 * v2) + j2) + 1 / (2 * i3 * sqrt (u3 * v3) + j3) := by
  have h1 : 1 / (i1 * (u1 + v1) + j1) ≤ 1 / (2 * i1 * sqrt (u1 * v1) + j1) := by exact AM_GM_div_normal u1 v1 i1 j1 hu1 hv1 hi1 hj1
  have h2 : 1 / (i2 * (u2 + v2) + j2) ≤ 1 / (2 * i2 * sqrt (u2 * v2) + j2) := by exact AM_GM_div_normal u2 v2 i2 j2 hu2 hv2 hi2 hj2
  have h3 : 1 / (i3 * (u3 + v3) + j3) ≤ 1 / (2 * i3 * sqrt (u3 * v3) + j3) := by exact AM_GM_div_normal u3 v3 i3 j3 hu3 hv3 hi3 hj3
  have h := add_le_add h1 (add_le_add h2 h3)
  nlinarith

theorem AM_GM_div_cycle_normal_left_2vars (u1 v1 u2 v2 u3 v3 i1 j1 i2 j2 i3 j3 k l right) (hk : k ≥ 0) (hu1 : u1 ≥ 0) (hv1 : v1 ≥ 0) (hu2 : u2 ≥ 0) (hv2 : v2 ≥ 0) (hu3 : u3 ≥ 0) (hv3 : v3 ≥ 0)
    (hi1 : i1 ≥ 0) (hj1 : 2 * i1 * sqrt (u1 * v1) + j1 > 0)
    (hi2 : i2 ≥ 0) (hj2 : 2 * i2 * sqrt (u2 * v2) + j2 > 0)
    (hi3 : i3 ≥ 0) (hj3 : 2 * i3 * sqrt (u3 * v3) + j3 > 0)
    (h : k * (1 / (2 * i1 * sqrt (u1 * v1) + j1) + 1 / (2 * i2 * sqrt (u2 * v2) + j2) + 1 / (2 * i3 * sqrt (u3 * v3) + j3)) + l ≤ right) :
    k * (1 / (i1 * (u1 + v1) + j1) + 1 / (i2 * (u2 + v2) + j2) + 1 / (i3 * (u3 + v3) + j3)) + l ≤ right := by
  suffices 1 / (i1 * (u1 + v1) + j1) + 1 / (i2 * (u2 + v2) + j2) + 1 / (i3 * (u3 + v3) + j3) ≤ 1 / (2 * i1 * sqrt (u1 * v1) + j1) + 1 / (2 * i2 * sqrt (u2 * v2) + j2) + 1 / (2 * i3 * sqrt (u3 * v3) + j3) by nlinarith
  apply AM_GM_div_cycle_normal_2vars u1 v1 u2 v2 u3 v3 i1 j1 i2 j2 i3 j3 hu1 hv1 hu2 hv2 hu3 hv3 hi1 hj1 hi2 hj2 hi3 hj3

theorem AM_GM_div_cycle_normal_right_2vars (u1 v1 u2 v2 u3 v3 i1 j1 i2 j2 i3 j3 k l left) (hk : k ≥ 0) (hu1 : u1 ≥ 0) (hv1 : v1 ≥ 0) (hu2 : u2 ≥ 0) (hv2 : v2 ≥ 0) (hu3 : u3 ≥ 0) (hv3 : v3 ≥ 0)
    (hi1 : i1 ≥ 0) (hj1 : i1 * sqrt (u1 * v1) + j1 > 0)
    (hi2 : i2 ≥ 0) (hj2 : i2 * sqrt (u2 * v2) + j2 > 0)
    (hi3 : i3 ≥ 0) (hj3 : i3 * sqrt (u3 * v3) + j3 > 0)
    (h : left ≤ k * (1 / (i1 * (u1 + v1) / 2 + j1) + 1 / (i2 * (u2 + v2) / 2 + j2) + 1 / (i3 * (u3 + v3) / 2 + j3)) + l) :
    left ≤ k * (1 / (i1 * sqrt (u1 * v1) + j1) + 1 / (i2 * sqrt (u2 * v2) + j2) + 1 / (i3 * sqrt (u3 * v3) + j3)) + l := by
  have hi1_ : (i1 / 2) ≥ 0 := by positivity
  have hi2_ : (i2 / 2) ≥ 0 := by positivity
  have hi3_ : (i3 / 2) ≥ 0 := by positivity
  have hj1_ : 2 * (i1 / 2) * sqrt (u1 * v1) + j1 > 0 := by linarith
  have hj2_ : 2 * (i2 / 2) * sqrt (u2 * v2) + j2 > 0 := by linarith
  have hj3_ : 2 * (i3 / 2) * sqrt (u3 * v3) + j3 > 0 := by linarith
  suffices 1 / (i1 * (u1 + v1) / 2 + j1) + 1 / (i2 * (u2 + v2) / 2 + j2) + 1 / (i3 * (u3 + v3) / 2 + j3) ≤ 1 / (i1 * sqrt (u1 * v1) + j1) + 1 / (i2 * sqrt (u2 * v2) + j2) + 1 / (i3 * sqrt (u3 * v3) + j3) by nlinarith
  have h := AM_GM_div_cycle_normal_2vars u1 v1 u2 v2 u3 v3 (i1/2) j1 (i2/2) j2 (i3/2) j3 hu1 hv1 hu2 hv2 hu3 hv3 hi1_ hj1_ hi2_ hj2_ hi3_ hj3_
  rw [show (i1 / 2 * (u1 + v1) + j1) = (i1 * (u1 + v1) / 2 + j1) by linarith] at h
  rw [show (i2 / 2 * (u2 + v2) + j2) = (i2 * (u2 + v2) / 2 + j2) by linarith] at h
  rw [show (i3 / 2 * (u3 + v3) + j3) = (i3 * (u3 + v3) / 2 + j3) by linarith] at h
  rw [show (2 * (i1 / 2) * sqrt (u1 * v1) + j1) = (i1 * sqrt (u1 * v1) + j1) by linarith] at h
  rw [show (2 * (i2 / 2) * sqrt (u2 * v2) + j2) = (i2 * sqrt (u2 * v2) + j2) by linarith] at h
  rw [show (2 * (i3 / 2) * sqrt (u3 * v3) + j3) = (i3 * sqrt (u3 * v3) + j3) by linarith] at h
  exact h

/-- The div cycle form 1 / (u1² + v1² + u2² + v2² + u3² + v3²) ≤ 1 / (2u1v1 + 2u2v2 + 2u3v3) of AM-GM inequalities for 3 variables -/
theorem AM_GM_div_cycle_square_right_2vars (u1 v1 u2 v2 u3 v3 i1 j1 i2 j2 i3 j3 k l left) (hk : k ≥ 0) (hu1 : u1 ≥ 0) (hv1 : v1 ≥ 0) (hu2 : u2 ≥ 0) (hv2 : v2 ≥ 0) (hu3 : u3 ≥ 0) (hv3 : v3 ≥ 0)
    (hi1 : i1 ≥ 0) (hj1 : i1 * u1 * v1 + j1 > 0)
    (hi2 : i2 ≥ 0) (hj2 : i2 * u2 * v2 + j2 > 0)
    (hi3 : i3 ≥ 0) (hj3 : i3 * u3 * v3 + j3 > 0)
    (h : left ≤ k * (1 / (i1 * (u1 ^ 2 + v1 ^ 2) / 2 + j1) + 1 / (i2 * (u2 ^ 2 + v2 ^ 2) / 2 + j2) + 1 / (i3 * (u3 ^ 2 + v3 ^ 2) / 2 + j3)) + l) :
    left ≤ k * (1 / (i1 * u1 * v1 + j1) + 1 / (i2 * u2 * v2 + j2) + 1 / (i3 * u3 * v3 + j3)) + l := by
  suffices 1 / (i1 * (u1 ^ 2 + v1 ^ 2) / 2 + j1) + 1 / (i2 * (u2 ^ 2 + v2 ^ 2) / 2 + j2) + 1 / (i3 * (u3 ^ 2 + v3 ^ 2) / 2 + j3) ≤ 1 / (i1 * u1 * v1 + j1) + 1 / (i2 * u2 * v2 + j2) + 1 / (i3 * u3 * v3 + j3) by nlinarith
  have hu1_ : u1 ^ 2 ≥ 0 := by positivity
  have hv1_ : v1 ^ 2 ≥ 0 := by positivity
  have hu2_ : u2 ^ 2 ≥ 0 := by positivity
  have hv2_ : v2 ^ 2 ≥ 0 := by positivity
  have hu3_ : u3 ^ 2 ≥ 0 := by positivity
  have hv3_ : v3 ^ 2 ≥ 0 := by positivity
  have hi1_ : (i1 / 2) ≥ 0 := by positivity
  have hi2_ : (i2 / 2) ≥ 0 := by positivity
  have hi3_ : (i3 / 2) ≥ 0 := by positivity
  have hj1' : i1 * u1 * v1 + j1 = 2 * (i1 / 2) * sqrt (u1 ^ 2 * v1 ^ 2) + j1 := by field_simp [*]; linarith
  have hj2' : i2 * u2 * v2 + j2 = 2 * (i2 / 2) * sqrt (u2 ^ 2 * v2 ^ 2) + j2 := by field_simp [*]; linarith
  have hj3' : i3 * u3 * v3 + j3 = 2 * (i3 / 2) * sqrt (u3 ^ 2 * v3 ^ 2) + j3 := by field_simp [*]; linarith
  rw [hj1'] at hj1
  rw [hj2'] at hj2
  rw [hj3'] at hj3
  have h := AM_GM_div_cycle_normal_2vars (u1^2) (v1^2) (u2^2) (v2^2) (u3^2) (v3^2) (i1/2) j1 (i2/2) j2 (i3/2) j3 hu1_ hv1_ hu2_ hv2_ hu3_ hv3_ hi1_ hj1 hi2_ hj2 hi3_ hj3
  rw [show (i1 / 2 * (u1 ^ 2 + v1 ^ 2) + j1) = (i1 * (u1 ^ 2 + v1 ^ 2) / 2 + j1) by linarith] at h
  rw [show (i2 / 2 * (u2 ^ 2 + v2 ^ 2) + j2) = (i2 * (u2 ^ 2 + v2 ^ 2) / 2 + j2) by linarith] at h
  rw [show (i3 / 2 * (u3 ^ 2 + v3 ^ 2) + j3) = (i3 * (u3 ^ 2 + v3 ^ 2) / 2 + j3) by linarith] at h
  rw [<-hj1', <-hj2', <-hj3'] at h
  exact h

end Scale_AM_GM_2vars

section Scale_AM_GM_3vars

/-- The base lemma: AM-GM inequalities for 3 variables -/
theorem AM_GM_3vars (u v w : ℝ) (h1 : u ≥ 0) (h2 : v ≥ 0) (h3 : w ≥ 0): 3 * (u * v * w) ^ (1 / 3) ≤ u + v + w := by
  let f : ℕ → ℝ | 0 => u | 1 => v | 2 => w | _ => 0
  let g : ℕ → ℝ | 0 => (1/3) | 1 => (1/3) | 2 => (1/3) | _ => 0
  let s : Finset ℕ := {0, 1, 2}
  have h := geom_mean_le_arith_mean_weighted s g f
  simp [f, s] at h
  simp [g, s] at h
  have ha : g 0 + g 1 + g 2 = 1 := by norm_num
  simp [g] at ha
  simp [<-add_assoc, ha] at h
  simp [h1, h2, h3] at h
  suffices (u * v * w) ^ (1 / 3) ≤ (1 / 3) * (u + v + w) by linarith
  convert h using 1
  field_simp only [*, mul_rpow]
  simp only [<-mul_assoc]
  linarith

/-- The normal form u + v + w ≥ 3∛(uvw) of AM-GM inequalities for 3 variables -/
theorem AM_GM_normal_left_3vars (u v w k l right : ℝ) (h1 : k ≥ 0) (h2 : u ≥ 0) (h3 : v ≥ 0) (h4 : w ≥ 0) (h5 : k * (u + v + w) / 3 + l ≤ right) : k * (u * v * w) ^ (1 / 3) + l ≤ right := by
  suffices 3 * (u * v * w) ^ (1 / 3) ≤ u + v + w by nlinarith
  have h : 3 * (u * v * w) ^ (1 / 3) ≤ u + v + w := by apply AM_GM_3vars u v w; all_goals assumption
  trivial

theorem AM_GM_normal_right_3vars (u v w k l left : ℝ) (h1 : k ≥ 0) (h2 : u ≥ 0) (h3 : v ≥ 0) (h4 : w ≥ 0) (h5 : left ≤ 3 * k * (u * v * w) ^ (1 / 3) + l) : left ≤ k * (u + v + w) + l := by
  suffices 3 * (u * v * w) ^ (1 / 3) ≤ u + v + w by nlinarith
  have h : 3 * (u * v * w) ^ (1 / 3) ≤ u + v + w := by apply AM_GM_3vars u v w; all_goals assumption
  trivial

/-- The cubic form u³ + v³ + w³ ≥ 3uvw of AM-GM inequalities for 3 variables -/
theorem AM_GM_cubic_left_3vars (u v w k l right : ℝ) (h1 : k ≥ 0) (h2 : u ≥ 0) (h3 : v ≥ 0) (h4 : w ≥ 0) (h5 : k * (u ^ 3 + v ^ 3 + w ^ 3) / 3 + l ≤ right) : k * (u * v * w) + l ≤ right := by
  suffices 3 * (u * v * w) ≤ (u ^ (3:ℕ) + v ^ (3:ℕ) + w ^ (3:ℕ)) by nlinarith
  have h := AM_GM_3vars (u ^ (3:ℕ)) (v ^ (3:ℕ)) (w ^ (3:ℕ)) (pow_nonneg h2 3) (pow_nonneg h3 3) (pow_nonneg h4 3)
  convert h using 1
  rw [<-mul_pow]; rw [<-mul_pow]
  rw [show (u * v * w) ^ (3:ℕ) = (u * v * w) ^ (3:ℝ) by norm_cast]
  rw [<-rpow_mul]
  simp_arith
  positivity

theorem AM_GM_cubic_right_3vars (u v w k l left : ℝ) (h1 : k ≥ 0) (h2 : u ≥ 0) (h3 : v ≥ 0) (h4 : w ≥ 0) (h5 : left ≤ 3 * k * (u * v * w) + l) : left ≤ k * (u ^ 3 + v ^ 3 + w ^ 3) + l := by
  suffices 3 * (u * v * w) ≤ (u ^ (3:ℕ) + v ^ (3:ℕ) + w ^ (3:ℕ)) by nlinarith
  have h := AM_GM_3vars (u ^ (3:ℕ)) (v ^ (3:ℕ)) (w ^ (3:ℕ)) (pow_nonneg h2 3) (pow_nonneg h3 3) (pow_nonneg h4 3)
  convert h using 1
  rw [<-mul_pow]; rw [<-mul_pow]
  rw [show (u * v * w) ^ (3:ℕ) = (u * v * w) ^ (3:ℝ) by norm_cast]
  rw [<-rpow_mul]
  simp_arith
  positivity


/-- The div normal form 1 / (u + v + w) ≤ 1 / 3∛(uvw) of AM-GM inequalities for 3 variables -/
theorem AM_GM_div_left_3vars (u v w i j k l right : ℝ) (hk : k ≥ 0) (hi : i ≥ 0) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hj : 3 * i * (u * v * w) ^ (1 / 3) + j > 0) (h : k * (1 / (3 * i * (u * v * w) ^ (1 / 3) + j)) + l ≤ right) : k * (1 / (i * (u + v + w) + j)) + l ≤ right := by
  suffices (1 / (i * (u + v + w) + j)) ≤ (1 / (3 * i * (u * v * w) ^ (1 / 3) + j)) by nlinarith
  suffices (3 * i * (u * v * w) ^ (1 / 3) + j) ≤ i * (u + v + w) + j by apply one_div_le_one_div_of_le; positivity; trivial
  suffices 3 * (u * v * w) ^ (1 / 3) ≤ u + v + w by nlinarith
  have h := AM_GM_3vars u v w hu hv hw
  exact h

theorem AM_GM_div_right_3vars (u v w i j k l left : ℝ) (hk : k ≥ 0) (hi : i ≥ 0) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hj : i * (u * v * w) ^ (1 / 3) + j > 0) (h : left ≤ k * (1 / (i * (u + v + w) / 3 + j)) + l) : left ≤ k * (1 / (i * (u * v * w) ^ (1 / 3) + j)) + l := by
  suffices (1 / (i * (u + v + w) / 3 + j)) ≤ (1 / (i * (u * v * w) ^ (1 / 3) + j)) by nlinarith
  suffices (i * (u * v * w) ^ (1 / 3) + j) ≤ i * (u + v + w) / 3 + j by apply one_div_le_one_div_of_le; positivity; trivial
  suffices 3 * (u * v * w) ^ (1 / 3) ≤ u + v + w by nlinarith
  have h := AM_GM_3vars u v w hu hv hw
  exact h


/-- The cubic div form 1 / (u³ + v³ + w³) ≤ 1 / 3uvw of AM-GM inequalities for 3 variables -/
theorem AM_GM_div_cubic_left_3vars (u v w i j k l right : ℝ) (hk : k ≥ 0) (hi : i ≥ 0) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hj : 3 * i * u * v * w + j > 0) (h : k * (1 / (3 * i * u * v * w + j)) + l ≤ right) : k * (1 / (i * (u ^ 3 + v ^ 3 + w ^ 3) + j)) + l ≤ right := by
  suffices (1 / (i * (u ^ 3 + v ^ 3 + w ^ 3) + j)) ≤ (1 / (3 * i * u * v * w + j)) by nlinarith
  suffices (3 * i * u * v * w + j) ≤ i * (u ^ 3 + v ^ 3 + w ^ 3) + j by apply one_div_le_one_div_of_le; positivity; trivial
  suffices 3 * (u * v * w) ≤ (u ^ 3 + v ^ 3 + w ^ 3) by nlinarith
  have hu1 : u ^ 3 ≥ 0 := pow_nonneg hu 3
  have hv1 : v ^ 3 ≥ 0 := pow_nonneg hv 3
  have hw1 : w ^ 3 ≥ 0 := pow_nonneg hw 3
  have h := AM_GM_3vars (u ^ 3) (v ^ 3) (w ^ 3) hu1 hv1 hw1
  convert h using 1
  rw [<-mul_pow]; rw [<-mul_pow]
  rw [show (u * v * w) ^ (3:ℕ) = (u * v * w) ^ (3:ℝ) by norm_cast]
  rw [<-rpow_mul]
  simp_arith
  positivity

theorem AM_GM_div_cubic_right_3vars (u v w i j k l left : ℝ) (hk : k ≥ 0) (hi : i ≥ 0) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hj : i * u * v * w + j > 0) (h : left ≤ k * (1 / (i * (u ^ 3 + v ^ 3 + w ^ 3) / 3 + j)) + l) : left ≤ k * (1 / (i * u * v * w + j)) + l := by
  suffices (1 / (i * (u ^ 3 + v ^ 3 + w ^ 3) / 3 + j)) ≤ (1 / (i * u * v * w + j)) by nlinarith
  suffices (i * u * v * w + j) ≤ i * (u ^ 3 + v ^ 3 + w ^ 3) / 3 + j by apply one_div_le_one_div_of_le; positivity; trivial
  suffices 3 * (u * v * w) ≤ (u ^ 3 + v ^ 3 + w ^ 3) by nlinarith
  have hu1 : u ^ 3 ≥ 0 := pow_nonneg hu 3
  have hv1 : v ^ 3 ≥ 0 := pow_nonneg hv 3
  have hw1 : w ^ 3 ≥ 0 := pow_nonneg hw 3
  have h := AM_GM_3vars (u ^ 3) (v ^ 3) (w ^ 3) hu1 hv1 hw1
  convert h using 1
  rw [<-mul_pow]; rw [<-mul_pow]
  rw [show (u * v * w) ^ (3:ℕ) = (u * v * w) ^ (3:ℝ) by norm_cast]
  rw [<-rpow_mul]
  simp_arith
  positivity

theorem AM_GM_sqrt_cbrt_3vars (u v w : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) : 3 * (u * v * w) ^ (1 / 3) ≤ sqrt (u * v) + sqrt (v * w) + sqrt (w * u) := by
  have huv : sqrt (u * v) ≥ 0 := by positivity
  have hvw : sqrt (v * w) ≥ 0 := by positivity
  have hwu : sqrt (w * u) ≥ 0 := by positivity
  have h := AM_GM_3vars (sqrt (u * v)) (sqrt (v * w)) (sqrt (w * u)) huv hvw hwu
  convert h using 1
  field_simp [*]; ring_nf; simp [sq_sqrt, *]

theorem AM_GM_sqrt_cbrt_left_3vars (u v w k l right : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hk : k ≥ 0)
  (h : k * (sqrt (u * v) + sqrt (v * w) + sqrt (w * u)) / 3 + l ≤ right) : k * (u * v * w) ^ (1 / 3) + l ≤ right := by
  suffices 3 * (u * v * w) ^ (1 / 3) ≤ sqrt (u * v) + sqrt (v * w) + sqrt (w * u) by nlinarith
  exact AM_GM_sqrt_cbrt_3vars u v w hu hv hw

theorem AM_GM_sqrt_cbrt_right_3vars (u v w k l left : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hk : k ≥ 0)
  (h : left ≤ k * (3 * (u * v * w) ^ (1 / 3)) + l) : left ≤ k * (sqrt (u * v) + sqrt (v * w) + sqrt (w * u)) + l := by
  suffices 3 * (u * v * w) ^ (1 / 3) ≤ sqrt (u * v) + sqrt (v * w) + sqrt (w * u) by nlinarith
  exact AM_GM_sqrt_cbrt_3vars u v w hu hv hw


/-- The div cycle form 1 / (u1 + v1 + w1 / 3 + u2 + v2 + w2 / 3 + u3 + v3 + w3 / 3) ≤ 1 / (cbrt u1v1w1 + cbrt u2v2w2 + cbrt u3v3w3) of AM-GM inequalities for 3 variables -/
theorem AM_GM_div_cycle_normal_3vars (u1 v1 w1 u2 v2 w2 u3 v3 w3 i1 j1 i2 j2 i3 j3) (hu1 : u1 ≥ 0) (hv1 : v1 ≥ 0) (hw1 : w1 ≥ 0) (hu2 : u2 ≥ 0) (hv2 : v2 ≥ 0) (hw2 : w2 ≥ 0) (hu3 : u3 ≥ 0) (hv3 : v3 ≥ 0) (hw3 : w3 ≥ 0)
    (hi1 : i1 ≥ 0) (hj1 : 3 * i1 * (u1 * v1 * w1) ^ (1 / 3) + j1 > 0)
    (hi2 : i2 ≥ 0) (hj2 : 3 * i2 * (u2 * v2 * w2) ^ (1 / 3) + j2 > 0)
    (hi3 : i3 ≥ 0) (hj3 : 3 * i3 * (u3 * v3 * w3) ^ (1 / 3) + j3 > 0) :
    1 / (i1 * (u1 + v1 + w1) + j1) + 1 / (i2 * (u2 + v2 + w2) + j2) + 1 / (i3 * (u3 + v3 + w3) + j3) ≤ 1 / (3 * i1 * (u1 * v1 * w1) ^ (1 / 3) + j1) + 1 / (3 * i2 * (u2 * v2 * w2) ^ (1 / 3) + j2) + 1 / (3 * i3 * (u3 * v3 * w3) ^ (1 / 3) + j3) := by
  have h1 : 1 / (i1 * (u1 + v1 + w1) + j1) ≤ 1 / (3 * i1 * (u1 * v1 * w1) ^ (1 / 3) + j1) := by
    suffices 3 * (u1 * v1 * w1) ^ (1 / 3) ≤ u1 + v1 + w1 by apply one_div_le_one_div_of_le; positivity; nlinarith
    exact AM_GM_3vars u1 v1 w1 hu1 hv1 hw1
  have h2 : 1 / (i2 * (u2 + v2 + w2) + j2) ≤ 1 / (3 * i2 * (u2 * v2 * w2) ^ (1 / 3) + j2) := by
    suffices 3 * (u2 * v2 * w2) ^ (1 / 3) ≤ u2 + v2 + w2 by apply one_div_le_one_div_of_le; positivity; nlinarith
    exact AM_GM_3vars u2 v2 w2 hu2 hv2 hw2
  have h3 : 1 / (i3 * (u3 + v3 + w3) + j3) ≤ 1 / (3 * i3 * (u3 * v3 * w3) ^ (1 / 3) + j3) := by
    suffices 3 * (u3 * v3 * w3) ^ (1 / 3) ≤ u3 + v3 + w3 by apply one_div_le_one_div_of_le; positivity; nlinarith
    exact AM_GM_3vars u3 v3 w3 hu3 hv3 hw3
  have h := add_le_add h1 (add_le_add h2 h3)
  nlinarith

theorem AM_GM_div_cycle_normal_left_3vars (u1 v1 w1 u2 v2 w2 u3 v3 w3 i1 j1 i2 j2 i3 j3 k l right) (hk : k ≥ 0) (hu1 : u1 ≥ 0) (hv1 : v1 ≥ 0) (hw1 : w1 ≥ 0) (hu2 : u2 ≥ 0) (hv2 : v2 ≥ 0) (hw2 : w2 ≥ 0) (hu3 : u3 ≥ 0) (hv3 : v3 ≥ 0) (hw3 : w3 ≥ 0)
    (hi1 : i1 ≥ 0) (hj1 : 3 * i1 * (u1 * v1 * w1) ^ (1 / 3) + j1 > 0)
    (hi2 : i2 ≥ 0) (hj2 : 3 * i2 * (u2 * v2 * w2) ^ (1 / 3) + j2 > 0)
    (hi3 : i3 ≥ 0) (hj3 : 3 * i3 * (u3 * v3 * w3) ^ (1 / 3) + j3 > 0)
    (h : k * (1 / (3 * i1 * (u1 * v1 * w1) ^ (1 / 3) + j1) + 1 / (3 * i2 * (u2 * v2 * w2) ^ (1 / 3) + j2) + 1 / (3 * i3 * (u3 * v3 * w3) ^ (1 / 3) + j3)) + l ≤ right) :
    k * (1 / (i1 * (u1 + v1 + w1) + j1) + 1 / (i2 * (u2 + v2 + w2) + j2) + 1 / (i3 * (u3 + v3 + w3) + j3)) + l ≤ right := by
  suffices 1 / (i1 * (u1 + v1 + w1) + j1) + 1 / (i2 * (u2 + v2 + w2) + j2) + 1 / (i3 * (u3 + v3 + w3) + j3) ≤ 1 / (3 * i1 * (u1 * v1 * w1) ^ (1 / 3) + j1) + 1 / (3 * i2 * (u2 * v2 * w2) ^ (1 / 3) + j2) + 1 / (3 * i3 * (u3 * v3 * w3) ^ (1 / 3) + j3) by nlinarith
  exact AM_GM_div_cycle_normal_3vars u1 v1 w1 u2 v2 w2 u3 v3 w3 i1 j1 i2 j2 i3 j3 hu1 hv1 hw1 hu2 hv2 hw2 hu3 hv3 hw3 hi1 hj1 hi2 hj2 hi3 hj3

theorem AM_GM_div_cycle_normal_right_3vars (u1 v1 w1 u2 v2 w2 u3 v3 w3 i1 j1 i2 j2 i3 j3 k l left) (hk : k ≥ 0) (hu1 : u1 ≥ 0) (hv1 : v1 ≥ 0) (hw1 : w1 ≥ 0) (hu2 : u2 ≥ 0) (hv2 : v2 ≥ 0) (hw2 : w2 ≥ 0) (hu3 : u3 ≥ 0) (hv3 : v3 ≥ 0) (hw3 : w3 ≥ 0)
    (hi1 : i1 ≥ 0) (hj1 : i1 * (u1 * v1 * w1) ^ (1 / 3) + j1 > 0)
    (hi2 : i2 ≥ 0) (hj2 : i2 * (u2 * v2 * w2) ^ (1 / 3) + j2 > 0)
    (hi3 : i3 ≥ 0) (hj3 : i3 * (u3 * v3 * w3) ^ (1 / 3) + j3 > 0)
    (h : left ≤ k * (1 / (i1 * (u1 + v1 + w1) / 3 + j1) + 1 / (i2 * (u2 + v2 + w2) / 3 + j2) + 1 / (i3 * (u3 + v3 + w3) / 3 + j3)) + l) :
    left ≤ k * (1 / (i1 * (u1 * v1 * w1) ^ (1 / 3) + j1) + 1 / (i2 * (u2 * v2 * w2) ^ (1 / 3) + j2) + 1 / (i3 * (u3 * v3 * w3) ^ (1 / 3) + j3)) + l := by
  have hi1_ : (i1 / 3) ≥ 0 := by positivity
  have hi2_ : (i2 / 3) ≥ 0 := by positivity
  have hi3_ : (i3 / 3) ≥ 0 := by positivity
  have hj1_ : 3 * (i1 / 3) * (u1 * v1 * w1) ^ (1 / 3) + j1 > 0 := by linarith
  have hj2_ : 3 * (i2 / 3) * (u2 * v2 * w2) ^ (1 / 3) + j2 > 0 := by linarith
  have hj3_ : 3 * (i3 / 3) * (u3 * v3 * w3) ^ (1 / 3) + j3 > 0 := by linarith
  suffices 1 / (i1 * (u1 + v1 + w1) / 3 + j1) + 1 / (i2 * (u2 + v2 + w2) / 3 + j2) + 1 / (i3 * (u3 + v3 + w3) / 3 + j3) ≤ 1 / (i1 * (u1 * v1 * w1) ^ (1 / 3) + j1) + 1 / (i2 * (u2 * v2 * w2) ^ (1 / 3) + j2) + 1 / (i3 * (u3 * v3 * w3) ^ (1 / 3) + j3) by nlinarith
  have h := AM_GM_div_cycle_normal_3vars u1 v1 w1 u2 v2 w2 u3 v3 w3 (i1/3) j1 (i2/3) j2 (i3/3) j3 hu1 hv1 hw1 hu2 hv2 hw2 hu3 hv3 hw3 hi1_ hj1_ hi2_ hj2_ hi3_ hj3_
  rw [show (i1 / 3 * (u1 + v1 + w1) + j1) = (i1 * (u1 + v1 + w1) / 3 + j1) by linarith] at h
  rw [show (i2 / 3 * (u2 + v2 + w2) + j2) = (i2 * (u2 + v2 + w2) / 3 + j2) by linarith] at h
  rw [show (i3 / 3 * (u3 + v3 + w3) + j3) = (i3 * (u3 + v3 + w3) / 3 + j3) by linarith] at h
  rw [show (3 * (i1 / 3) * (u1 * v1 * w1) ^ (1 / 3) + j1) = (i1 * (u1 * v1 * w1) ^ (1 / 3) + j1) by linarith] at h
  rw [show (3 * (i2 / 3) * (u2 * v2 * w2) ^ (1 / 3) + j2) = (i2 * (u2 * v2 * w2) ^ (1 / 3) + j2) by linarith] at h
  rw [show (3 * (i3 / 3) * (u3 * v3 * w3) ^ (1 / 3) + j3) = (i3 * (u3 * v3 * w3) ^ (1 / 3) + j3) by linarith] at h
  exact h

/-- The div cycle form 1 / (u1^3 + v1^3 + u2^3 + v2^3 + u3^3 + v3^3) ≤ 1 / (3u1v1w1 + 3u2v2w2 + 3u3v3w3) of AM-GM inequalities for 3 variables -/
theorem AM_GM_div_cycle_cubic_right_3vars (u1 v1 w1 u2 v2 w2 u3 v3 w3 i1 j1 i2 j2 i3 j3 k l left) (hk : k ≥ 0) (hu1 : u1 ≥ 0) (hv1 : v1 ≥ 0) (hw1 : w1 ≥ 0) (hu2 : u2 ≥ 0) (hv2 : v2 ≥ 0) (hw2 : w2 ≥ 0) (hu3 : u3 ≥ 0) (hv3 : v3 ≥ 0) (hw3 : w3 ≥ 0)
    (hi1 : i1 ≥ 0) (hj1 : i1 * u1 * v1 * w1 + j1 > 0)
    (hi2 : i2 ≥ 0) (hj2 : i2 * u2 * v2 * w2 + j2 > 0)
    (hi3 : i3 ≥ 0) (hj3 : i3 * u3 * v3 * w3 + j3 > 0)
    (h : left ≤ k * (1 / (i1 * (u1 ^ 3 + v1 ^ 3 + w1 ^ 3) / 3 + j1) + 1 / (i2 * (u2 ^ 3 + v2 ^ 3 + w2 ^ 3) / 3 + j2) + 1 / (i3 * (u3 ^ 3 + v3 ^ 3 + w3 ^ 3) / 3 + j3)) + l) :
    left ≤ k * (1 / (i1 * u1 * v1 * w1 + j1) + 1 / (i2 * u2 * v2 * w2 + j2) + 1 / (i3 * u3 * v3 * w3 + j3)) + l := by
  suffices 1 / (i1 * (u1 ^ 3 + v1 ^ 3 + w1 ^ 3) / 3 + j1) + 1 / (i2 * (u2 ^ 3 + v2 ^ 3 + w2 ^ 3) / 3 + j2) + 1 / (i3 * (u3 ^ 3 + v3 ^ 3 + w3 ^ 3) / 3 + j3) ≤ 1 / (i1 * u1 * v1 * w1 + j1) + 1 / (i2 * u2 * v2 * w2 + j2) + 1 / (i3 * u3 * v3 * w3 + j3) by nlinarith
  have h1 : 1 / (i1 * (u1 ^ 3 + v1 ^ 3 + w1 ^ 3) / 3 + j1) ≤ 1 / (i1 * u1 * v1 * w1 + j1) := by
    suffices 3 * (u1 * v1 * w1) ≤ u1 ^ 3 + v1 ^ 3 + w1 ^ 3 by apply one_div_le_one_div_of_le; positivity; nlinarith
    have h := AM_GM_3vars (u1 ^ (3:ℕ)) (v1 ^ (3:ℕ)) (w1 ^ (3:ℕ)) (pow_nonneg hu1 3) (pow_nonneg hv1 3) (pow_nonneg hw1 3)
    convert h using 1
    rw [<-mul_pow]; rw [<-mul_pow]
    rw [show (u1 * v1 * w1) ^ (3:ℕ) = (u1 * v1 * w1) ^ (3:ℝ) by norm_cast]
    rw [<-rpow_mul]
    simp_arith
    positivity
  have h2 : 1 / (i2 * (u2 ^ 3 + v2 ^ 3 + w2 ^ 3) / 3 + j2) ≤ 1 / (i2 * u2 * v2 * w2 + j2) := by
    suffices 3 * (u2 * v2 * w2) ≤ u2 ^ 3 + v2 ^ 3 + w2 ^ 3 by apply one_div_le_one_div_of_le; positivity; nlinarith
    have h := AM_GM_3vars (u2 ^ (3:ℕ)) (v2 ^ (3:ℕ)) (w2 ^ (3:ℕ)) (pow_nonneg hu2 3) (pow_nonneg hv2 3) (pow_nonneg hw2 3)
    convert h using 1
    rw [<-mul_pow]; rw [<-mul_pow]
    rw [show (u2 * v2 * w2) ^ (3:ℕ) = (u2 * v2 * w2) ^ (3:ℝ) by norm_cast]
    rw [<-rpow_mul]
    simp_arith
    positivity
  have h3 : 1 / (i3 * (u3 ^ 3 + v3 ^ 3 + w3 ^ 3) / 3 + j3) ≤ 1 / (i3 * u3 * v3 * w3 + j3) := by
    suffices 3 * (u3 * v3 * w3) ≤ u3 ^ 3 + v3 ^ 3 + w3 ^ 3 by apply one_div_le_one_div_of_le; positivity; nlinarith
    have h := AM_GM_3vars (u3 ^ (3:ℕ)) (v3 ^ (3:ℕ)) (w3 ^ (3:ℕ)) (pow_nonneg hu3 3) (pow_nonneg hv3 3) (pow_nonneg hw3 3)
    convert h using 1
    rw [<-mul_pow]; rw [<-mul_pow]
    rw [show (u3 * v3 * w3) ^ (3:ℕ) = (u3 * v3 * w3) ^ (3:ℝ) by norm_cast]
    rw [<-rpow_mul]
    simp_arith
    positivity
  have h := add_le_add h1 (add_le_add h2 h3)
  nlinarith

end Scale_AM_GM_3vars

section Scale_AM_GM_4vars

theorem AM_GM_4vars (u1 u2 u3 u4 : ℝ) (h1 : u1 ≥ 0) (h2 : u2 ≥ 0) (h3 : u3 ≥ 0) (h4 : u4 ≥ 0) : 4 * (u1 * u2 * u3 * u4) ^ (1 / 4) ≤ u1 + u2 + u3 + u4 := by
  let f : ℕ → ℝ | 0 => u1 | 1 => u2 | 2 => u3 | 3 => u4 | _ => 0
  let g : ℕ → ℝ | 0 => (1/4) | 1 => (1/4) | 2 => (1/4) | 3 => (1/4) | _ => 0
  let s : Finset ℕ := {0, 1, 2, 3}
  have h := geom_mean_le_arith_mean_weighted s g f
  simp [f, s] at h
  simp [g, s] at h
  have ha : g 0 + g 1 + g 2 + g 3 = 1 := by norm_num
  simp [g] at ha
  simp [<-add_assoc, ha] at h
  simp [h1, h2, h3] at h
  suffices (u1 * u2 * u3 * u4) ^ (1 / 4) ≤ (1 / 4) * (u1 + u2 + u3 + u4) by linarith
  simp [*] at h
  convert h using 1
  field_simp only [*, mul_rpow]
  simp only [<-mul_assoc]
  linarith

/-- The normal form u1 + u2 + u3 + u4 ≥ 4∛(u1u2u3u4) of AM-GM inequalities for 4 variables -/
theorem AM_GM_normal_left_4vars (u1 u2 u3 u4 k l right : ℝ) (h1 : k ≥ 0) (h2 : u1 ≥ 0) (h3 : u2 ≥ 0) (h4 : u3 ≥ 0) (h5 : u4 ≥ 0)
  (h : k * (u1 + u2 + u3 + u4) / 4 + l ≤ right) : k * (u1 * u2 * u3 * u4) ^ (1 / 4) + l ≤ right := by
  suffices 4 * (u1 * u2 * u3 * u4) ^ (1 / 4) ≤ u1 + u2 + u3 + u4 by nlinarith
  have h : 4 * (u1 * u2 * u3 * u4) ^ (1 / 4) ≤ u1 + u2 + u3 + u4 := by apply AM_GM_4vars u1 u2 u3 u4; all_goals assumption
  trivial

theorem AM_GM_normal_right_4vars (u1 u2 u3 u4 k l left : ℝ) (h1 : k ≥ 0) (h2 : u1 ≥ 0) (h3 : u2 ≥ 0) (h4 : u3 ≥ 0) (h5 : u4 ≥ 0)
  (h : left ≤ 4 * k * (u1 * u2 * u3 * u4) ^ (1 / 4) + l) : left ≤ k * (u1 + u2 + u3 + u4) + l := by
  suffices 4 * (u1 * u2 * u3 * u4) ^ (1 / 4) ≤ u1 + u2 + u3 + u4 by nlinarith
  have h : 4 * (u1 * u2 * u3 * u4) ^ (1 / 4) ≤ u1 + u2 + u3 + u4 := by apply AM_GM_4vars u1 u2 u3 u4; all_goals assumption
  trivial

end Scale_AM_GM_4vars


section Scale_AM_GM_6vars
/-- The base lemma: AM-GM inequalities for 6 variables -/

theorem AM_GM_6vars (u1 u2 u3 u4 u5 u6 : ℝ) (h1 : u1 ≥ 0) (h2 : u2 ≥ 0) (h3 : u3 ≥ 0) (h4 : u4 ≥ 0) (h5 : u5 ≥ 0) (h6 : u6 ≥ 0) : 6 * (u1 * u2 * u3 * u4 * u5 * u6) ^ (1 / 6) ≤ u1 + u2 + u3 + u4 + u5 + u6 := by
  let f : ℕ → ℝ | 0 => u1 | 1 => u2 | 2 => u3 | 3 => u4 | 4 => u5 | 5 => u6 | _ => 0
  let g : ℕ → ℝ | 0 => (1/6) | 1 => (1/6) | 2 => (1/6) | 3 => (1/6) | 4 => (1/6) | 5 => (1/6) | _ => 0
  let s : Finset ℕ := {0, 1, 2, 3, 4, 5}
  have h := geom_mean_le_arith_mean_weighted s g f
  simp [f, s] at h
  simp [g, s] at h
  have ha : g 0 + g 1 + g 2 + g 3 + g 4 + g 5 = 1 := by norm_num
  simp [g] at ha
  simp [<-add_assoc, ha] at h
  simp [h1, h2, h3] at h
  suffices (u1 * u2 * u3 * u4 * u5 * u6) ^ (1 / 6) ≤ (1 / 6) * (u1 + u2 + u3 + u4 + u5 + u6) by linarith
  simp [*] at h
  convert h using 1
  field_simp only [*, mul_rpow]
  simp only [<-mul_assoc]
  linarith

/-- The normal form u1 + u2 + u3 + u4 + u5 + u6 ≥ 6∛(u1u2u3u4u5u6) of AM-GM inequalities for 6 variables -/
theorem AM_GM_normal_left_6vars (u1 u2 u3 u4 u5 u6 k l right : ℝ) (h1 : k ≥ 0) (h2 : u1 ≥ 0) (h3 : u2 ≥ 0) (h4 : u3 ≥ 0) (h5 : u4 ≥ 0) (h6 : u5 ≥ 0) (h7 : u6 ≥ 0)
  (h : k * (u1 + u2 + u3 + u4 + u5 + u6) / 6 + l ≤ right) : k * (u1 * u2 * u3 * u4 * u5 * u6) ^ (1 / 6) + l ≤ right := by
  suffices 6 * (u1 * u2 * u3 * u4 * u5 * u6) ^ (1 / 6) ≤ u1 + u2 + u3 + u4 + u5 + u6 by nlinarith
  have h : 6 * (u1 * u2 * u3 * u4 * u5 * u6) ^ (1 / 6) ≤ u1 + u2 + u3 + u4 + u5 + u6 := by apply AM_GM_6vars u1 u2 u3 u4 u5 u6; all_goals assumption
  trivial

theorem AM_GM_normal_right_6vars (u1 u2 u3 u4 u5 u6 k l left : ℝ) (h1 : k ≥ 0) (h2 : u1 ≥ 0) (h3 : u2 ≥ 0) (h4 : u3 ≥ 0) (h5 : u4 ≥ 0) (h6 : u5 ≥ 0) (h7 : u6 ≥ 0)
  (h : left ≤ 6 * k * (u1 * u2 * u3 * u4 * u5 * u6) ^ (1 / 6) + l) : left ≤ k * (u1 + u2 + u3 + u4 + u5 + u6) + l := by
  suffices 6 * (u1 * u2 * u3 * u4 * u5 * u6) ^ (1 / 6) ≤ u1 + u2 + u3 + u4 + u5 + u6 by nlinarith
  have h : 6 * (u1 * u2 * u3 * u4 * u5 * u6) ^ (1 / 6) ≤ u1 + u2 + u3 + u4 + u5 + u6 := by apply AM_GM_6vars u1 u2 u3 u4 u5 u6; all_goals assumption
  trivial

end Scale_AM_GM_6vars
