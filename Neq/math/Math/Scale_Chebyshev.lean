import Mathlib

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

section Scale_Chebyshev_2vars

/-- The basic format of the cycle form Chebyshev inequality for 2 variables -/
theorem Chebyshev_cycle_2vars (u v p q : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : p ≥ 0) (hd : q ≥ 0): (u ^ p + v ^ p) * (u ^ q + v ^ q) ≤ (2 * u ^ (p + q) + 2 *  v ^ (p + q)) := by
  sorry

/-- The normal form Chebyshev inequality for 2 variables
    note that normal right cannot be pattern matched, and thus ignored -/

theorem Chebyshev_cycle_left_2vars (u v p q k l right : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hk : k ≥ 0)
  (hl : k * (2 * u ^ (p + q) + 2 * v ^ (p + q)) + l ≤ right) : k * (u ^ p + v ^ p) * (u ^ q + v ^ q) + l ≤ right := by
  suffices (u ^ p + v ^ p) * (u ^ q + v ^ q) ≤ (2 * u ^ (p + q) + 2 * v ^ (p + q)) by nlinarith
  exact Chebyshev_cycle_2vars u v p q ha hb hp hq

theorem Chebyshev_cycle_Qeq1_left_2vars (u v p k l right : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hp : p ≥ 0) (hk : k ≥ 0)
  (hl : k * (2 * u ^ (p + 1) + 2 * v ^ (p + 1)) + l ≤ right) : k * (u ^ p + v ^ p) * (u + v) + l ≤ right := by
  suffices (u ^ p + v ^ p) * (u + v) ≤ (2 * u ^ (p + 1) + 2 * v ^ (p + 1)) by nlinarith
  have hq : (1:ℝ) ≥ 0 := by positivity
  have h := Chebyshev_cycle_2vars u v p (1:ℝ) ha hb hp hq
  norm_num at h
  exact h

end Scale_Chebyshev_2vars

section Scale_Chebyshev_3vars
/-- The basic format of the cycle form Chebyshev inequality for 3 variables -/
theorem Chebyshev_cycle_3vars (u v w p q : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) : (u ^ p + v ^ p + w ^ p) * (u ^ q + v ^ q + w ^ q) ≤ (3 * u ^ (p + q) + 3 * v ^ (p + q) + 3 * w ^ (p + q)) := by
  sorry

/-- The normal form Chebyshev inequality for 3 variables
    note that normal right cannot be pattern matched, and ignored -/

theorem Chebyshev_cycle_left_3vars (u v w p q k l right : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hk : k ≥ 0)
  (hl : k * (3 * u ^ (p + q) + 3 * v ^ (p + q) + 3 * w ^ (p + q)) + l ≤ right) : k * (u ^ p + v ^ p + w ^ p) * (u ^ q + v ^ q + w ^ q) + l ≤ right := by
  suffices (u ^ p + v ^ p + w ^ p) * (u ^ q + v ^ q + w ^ q) ≤ (3 * u ^ (p + q) + 3 * v ^ (p + q) + 3 * w ^ (p + q)) by nlinarith
  exact Chebyshev_cycle_3vars u v w p q ha hb hc hp hq

theorem Chebyshev_cycle_Qeq1_left_3vars (u v w p k l right : ℝ) (ha : u ≥ 0) (hb : v ≥ 0) (hc : w ≥ 0) (hp : p ≥ 0) (hk : k ≥ 0)
  (hl : k * (3 * u ^ (p + 1) + 3 * v ^ (p + 1) + 3 * w ^ (p + 1)) + l ≤ right) : k * (u ^ p + v ^ p + w ^ p) * (u + v + w) + l ≤ right := by
  suffices (u ^ p + v ^ p + w ^ p) * (u + v + w) ≤ (3 * u ^ (p + 1) + 3 * v ^ (p + 1) + 3 * w ^ (p + 1)) by nlinarith
  have hq : (1:ℝ) ≥ 0 := by positivity
  have h := Chebyshev_cycle_3vars u v w p (1:ℝ) ha hb hc hp hq
  norm_num at h
  exact h

/-- The div form Chebyshev inequality for 3 variables
    similarly, div left cannot be pattern matched, and ignored -/
theorem Chebyshev_div_cycle_3vars (u v w p q : ℝ) (ha : u > 0) (hb : v > 0) (hc : w > 0) (hp : p ≥ 0) (hq : q ≥ 0) :
  (3 * u ^ (p - q) + 3 * v ^ (p - q) + 3 * w ^ (p - q)) ≤ (u ^ p + v ^ p + w ^ p) * (1 / u ^ q + 1 /v ^ q + 1 / w ^ q) := by
  sorry

theorem Chebyshev_div_cycle_right_3vars (u v w p q k l left : ℝ) (ha : u > 0) (hb : v > 0) (hc : w > 0) (hp : p ≥ 0) (hq : q ≥ 0) (hk : k ≥ 0)
  (hl : left ≤ k * (3 * u ^ (p - q) + 3 * v ^ (p - q) + 3 * w ^ (p - q)) + l) : left ≤ k * (u ^ p + v ^ p + w ^ p) * (1 / u ^ q + 1 /v ^ q + 1 / w ^ q) + l := by
  suffices (3 * u ^ (p - q) + 3 * v ^ (p - q) + 3 * w ^ (p - q)) ≤ (u ^ p + v ^ p + w ^ p) * (1 / u ^ q + 1 /v ^ q + 1 / w ^ q) by nlinarith
  exact Chebyshev_div_cycle_3vars u v w p q ha hb hc hp hq

theorem Chebyshev_div_cycle_Peq1_right_3vars (u v w p k l left : ℝ) (ha : u > 0) (hb : v > 0) (hc : w > 0) (hp : p ≥ 0) (hk : k ≥ 0)
  (hl : left ≤ k * (3 * u ^ (1 - p) + 3 * v ^ (1 - p) + 3 * w ^ (1 - p)) + l) : left ≤ k * (u + v + w) * (1 / u ^ p + 1 / v ^ p + 1 / w ^ p) + l := by
  suffices (3 * u ^ (1 - p) + 3 * v ^ (1 - p) + 3 * w ^ (1 - p)) ≤ (u + v + w) * (1 / u ^ p + 1 / v ^ p + 1 / w ^ p) by nlinarith
  have hq : (1:ℝ) ≥ 0 := by positivity
  have h := Chebyshev_div_cycle_3vars u v w (1:ℝ) p ha hb hc hq hp
  simp only [rpow_one] at h
  exact h

theorem Chebyshev_div_cycle_Qeq1_right_3vars (u v w p k l left : ℝ) (ha : u > 0) (hb : v > 0) (hc : w > 0) (hp : p ≥ 0) (hk : k ≥ 0)
  (hl : left ≤ k * (3 * u ^ (p - 1) + 3 * v ^ (p - 1) + 3 * w ^ (p - 1)) + l) : left ≤ k * (u ^ p + v ^ p + w ^ p) * (1 / u + 1 / v + 1 / w) + l := by
  suffices (3 * u ^ (p - 1) + 3 * v ^ (p - 1) + 3 * w ^ (p - 1)) ≤ (u ^ p + v ^ p + w ^ p) * (1 / u + 1 / v + 1 / w) by nlinarith
  have hq : (1:ℝ) ≥ 0 := by positivity
  have h := Chebyshev_div_cycle_3vars u v w p (1:ℝ) ha hb hc hp hq
  simp only [rpow_one] at h
  exact h

end Scale_Chebyshev_3vars

section Scale_Chebyshev_4vars

/-- The basic format of the cycle form Chebyshev inequality for 4 variables -/
theorem Chebyshev_cycle_4vars (u1 u2 u3 u4 p q : ℝ) (ha : u1 ≥ 0) (hb : u2 ≥ 0) (hc : u3 ≥ 0) (hd : u4 ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) : (u1 ^ p + u2 ^ p + u3 ^ p + u4 ^ p) * (u1 ^ q + u2 ^ q + u3 ^ q + u4 ^ q) ≤ (4 * u1 ^ (p + q) + 4 * u2 ^ (p + q) + 4 * u3 ^ (p + q) + 4 * u4 ^ (p + q)) := by
  sorry

/-- The normal form Chebyshev inequality for 3 variables
    note that normal right cannot be pattern matched, and ignored -/

theorem Chebyshev_cycle_left_4vars (u1 u2 u3 u4 p q k l right : ℝ) (ha : u1 ≥ 0) (hb : u2 ≥ 0) (hc : u3 ≥ 0) (hd : u4 ≥ 0) (hp : p ≥ 0) (hq : q ≥ 0) (hk : k ≥ 0)
  (hl : k * (4 * u1 ^ (p + q) + 4 * u2 ^ (p + q) + 4 * u3 ^ (p + q) + 4 * u4 ^ (p + q)) + l ≤ right) : k * (u1 ^ p + u2 ^ p + u3 ^ p + u4 ^ p) * (u1 ^ q + u2 ^ q + u3 ^ q + u4 ^ q) + l ≤ right := by
  suffices (u1 ^ p + u2 ^ p + u3 ^ p + u4 ^ p) * (u1 ^ q + u2 ^ q + u3 ^ q + u4 ^ q) ≤ (4 * u1 ^ (p + q) + 4 * u2 ^ (p + q) + 4 * u3 ^ (p + q) + 4 * u4 ^ (p + q)) by nlinarith
  exact Chebyshev_cycle_4vars u1 u2 u3 u4 p q ha hb hc hd hp hq

theorem Chebyshev_cycle_Qeq1_left_4vars (u1 u2 u3 u4 p k l right : ℝ) (ha : u1 ≥ 0) (hb : u2 ≥ 0) (hc : u3 ≥ 0) (hd : u4 ≥ 0) (hp : p ≥ 0) (hk : k ≥ 0)
  (hl : k * (4 * u1 ^ (p + 1) + 4 * u2 ^ (p + 1) + 4 * u3 ^ (p + 1) + 4 * u4 ^ (p + 1)) + l ≤ right) : k * (u1 ^ p + u2 ^ p + u3 ^ p + u4 ^ p) * (u1 + u2 + u3 + u4) + l ≤ right := by
  suffices (u1 ^ p + u2 ^ p + u3 ^ p + u4 ^ p) * (u1 + u2 + u3 + u4) ≤ (4 * u1 ^ (p + 1) + 4 * u2 ^ (p + 1) + 4 * u3 ^ (p + 1) + 4 * u4 ^ (p + 1)) by nlinarith
  have hq : (1:ℝ) ≥ 0 := by positivity
  have h := Chebyshev_cycle_4vars u1 u2 u3 u4 p (1:ℝ) ha hb hc hd hp hq
  norm_num at h
  exact h

/-- The div form Chebyshev inequality for 4 variables
    similarly, div left cannot be pattern matched, and ignored -/
theorem Chebyshev_div_cycle_4vars (u1 u2 u3 u4 p q : ℝ) (ha : u1 > 0) (hb : u2 > 0) (hc : u3 > 0) (hd : u4 > 0) (hp : p ≥ 0) (hq : q ≥ 0) :
  (4 * u1 ^ (p - q) + 4 * u2 ^ (p - q) + 4 * u3 ^ (p - q) + 4 * u4 ^ (p - q)) ≤ (u1 ^ p + u2 ^ p + u3 ^ p + u4 ^ p) * (1 / u1 ^ q + 1 / u2 ^ q + 1 / u3 ^ q + 1 / u4 ^ q) := by
  sorry

theorem Chebyshev_div_cycle_right_4vars (u1 u2 u3 u4 p q k l left : ℝ) (ha : u1 > 0) (hb : u2 > 0) (hc : u3 > 0) (hd : u4 > 0) (hp : p ≥ 0) (hq : q ≥ 0) (hk : k ≥ 0)
  (hl : left ≤ k * (4 * u1 ^ (p - q) + 4 * u2 ^ (p - q) + 4 * u3 ^ (p - q) + 4 * u4 ^ (p - q)) + l) :
  left ≤ k * (u1 ^ p + u2 ^ p + u3 ^ p + u4 ^ p) * (1 / u1 ^ q + 1 / u2 ^ q + 1 / u3 ^ q + 1 / u4 ^ q) + l := by
  suffices (4 * u1 ^ (p - q) + 4 * u2 ^ (p - q) + 4 * u3 ^ (p - q) + 4 * u4 ^ (p - q)) ≤ (u1 ^ p + u2 ^ p + u3 ^ p + u4 ^ p) * (1 / u1 ^ q + 1 / u2 ^ q + 1 / u3 ^ q + 1 / u4 ^ q) by nlinarith
  exact Chebyshev_div_cycle_4vars u1 u2 u3 u4 p q ha hb hc hd hp hq

theorem Chebyshev_div_cycle_Peq1_right_4vars (u1 u2 u3 u4 p k l left : ℝ) (ha : u1 > 0) (hb : u2 > 0) (hc : u3 > 0) (hd : u4 > 0) (hp : p ≥ 0) (hk : k ≥ 0)
  (hl : left ≤ k * (4 * u1 ^ (1 - p) + 4 * u2 ^ (1 - p) + 4 * u3 ^ (1 - p) + 4 * u4 ^ (1 - p)) + l) :
  left ≤ k * (u1 + u2 + u3 + u4) * (1 / u1 ^ p + 1 / u2 ^ p + 1 / u3 ^ p + 1 / u4 ^ p) + l := by
  suffices (4 * u1 ^ (1 - p) + 4 * u2 ^ (1 - p) + 4 * u3 ^ (1 - p) + 4 * u4 ^ (1 - p)) ≤ (u1 + u2 + u3 + u4) * (1 / u1 ^ p + 1 / u2 ^ p + 1 / u3 ^ p + 1 / u4 ^ p) by nlinarith
  have hq : (1:ℝ) ≥ 0 := by positivity
  have h := Chebyshev_div_cycle_4vars u1 u2 u3 u4 (1:ℝ) p ha hb hc hd hq hp
  simp only [rpow_one] at h
  exact h

theorem Chebyshev_div_cycle_Qeq1_right_4vars (u1 u2 u3 u4 p k l left : ℝ) (ha : u1 > 0) (hb : u2 > 0) (hc : u3 > 0) (hd : u4 > 0) (hp : p ≥ 0) (hk : k ≥ 0)
  (hl : left ≤ k * (4 * u1 ^ (p - 1) + 4 * u2 ^ (p - 1) + 4 * u3 ^ (p - 1) + 4 * u4 ^ (p - 1)) + l) :
  left ≤ k * (u1 ^ p + u2 ^ p + u3 ^ p + u4 ^ p) * (1 / u1 + 1 / u2 + 1 / u3 + 1 / u4) + l := by
  suffices (4 * u1 ^ (p - 1) + 4 * u2 ^ (p - 1) + 4 * u3 ^ (p - 1) + 4 * u4 ^ (p - 1)) ≤ (u1 ^ p + u2 ^ p + u3 ^ p + u4 ^ p) * (1 / u1 + 1 / u2 + 1 / u3 + 1 / u4) by nlinarith
  have hq : (1:ℝ) ≥ 0 := by positivity
  have h := Chebyshev_div_cycle_4vars u1 u2 u3 u4 p (1:ℝ) ha hb hc hd hp hq
  simp only [rpow_one] at h
  exact h

end Scale_Chebyshev_4vars
