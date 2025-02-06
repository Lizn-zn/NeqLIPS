import Mathlib


open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

-- apply tactics

-- rw [NEQ_reverse]
theorem reverse (a b : ℝ) : (a ≥ b) ↔ (b ≤ a) := by rw [← not_lt, not_lt]

theorem squared_plusk (left right k : ℝ) (h1 : right + k ≥ 0) (h2 : (left + k) ^ 2 ≤ (right + k) ^ 2) : (left ≤ right) := by nlinarith

theorem split (a b c d : ℝ) (h1 : a ≤ c) (h2 : b ≤ d) : a + b ≤ c + d := by nlinarith

theorem add_k (left right k : ℝ) (h1 : left + k ≤ right + k) : left ≤ right := by nlinarith

theorem sub_k (left right k : ℝ) (h1 : left - k ≤ right - k) : left ≤ right := by nlinarith

-- theorem mul_left_distrib (a b c : ℝ) : c * (a + b) = c * a + c * b := by ring

-- theorem mul_right_distrib (a b c : ℝ) : (a + b) * c = a * c + b * c := by ring

-- theorem square_expand_2vars (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring

-- theorem square_expand_3vars (a b c : ℝ) : (a + b + c) ^ 2 = a ^ 2 + 2 * a * b + 2 * a * c + b ^ 2 + 2 * b * c + c ^ 2 := by ring

-- theorem square_expand_4vars (a b c d : ℝ) : (a + b + c + d) ^ 2 = a ^ 2 + 2 * a * b + 2 * a * c + 2 * a * d + b ^ 2 + 2 * b * c + 2 * b * d + c ^ 2 + 2 * c * d + d ^ 2 := by ring

theorem frac_add_reduce (a b c d : ℝ) (ha : b ≠ 0) (hb : d ≠ 0): ((a / b) = (a * d + b * c) / (b * d)  - c / d) := by
  field_simp [*]
  linarith

theorem frac_sub_reduce (a b c d : ℝ) (ha : b ≠ 0) (hb : d ≠ 0): ((a / b) = (a * d - b * c) / (b * d)  + c / d) := by
  field_simp [*]
  linarith
