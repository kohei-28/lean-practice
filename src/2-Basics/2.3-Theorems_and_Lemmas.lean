example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt h₀
  apply lt_trans h₁
  apply lt_of_le_of_lt h₂
  apply h₃

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  apply add_le_add_left
  apply exp_le_exp.2
  apply add_le_add_left h₀

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by
    apply add_pos
    norm_num
    exact exp_pos a

  apply log_le_log h₀
  apply add_le_add_left
  apply exp_le_exp.2 h
