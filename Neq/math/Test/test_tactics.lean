import Math

example (a b c : ℝ) : a + b ≤ b + a + c := by
  llm_simplify a + b - (b + a + c) = -c
  extract_goal
  sorry

example (a b c : ℝ) : (a + b) ^ 2 ≤ a ^ 2 + 2 * a * b + b ^ 2 + c := by
  llm_simplify (a + b) ^ 2 - (a ^ 2 + 2 * a * b + b ^ 2 + c) = -c
  extract_goal
  sorry

example (a b c : ℝ) (h1 : a + b ≥ 0) (h2 : b * c ≥ 0) : a / b + b / c ≤ 0 := by
  llm_cancel_denom (a / b + b / c) - 0 = (a * c + b * b) / (b * c)
  extract_goal
  sorry

example (a b c : ℝ) (h1 : a ≥ 0) (h2 : b + c ≥ 0) : sqrt a ≤ sqrt (b + c) := by
  llm_cancel_power 2
  extract_goal
  sorry

example (a b c : ℝ) (h : a ≥ 0) : a * b ≤ a * c := by
  llm_cancel_factor a * b - (a * c) = a * (b - c)
  extract_goal
  sorry
