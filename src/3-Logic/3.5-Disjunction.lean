theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  rw [abs_of_neg]
  linarith
  apply h

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    exact neg_le_self h
  rw [abs_of_neg h]


theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    rcases le_or_gt 0 y with h' | h'
    · rw [abs_of_nonneg h']
      rcases le_or_gt 0 (x+y) with h'' | h''
      · rw [abs_of_nonneg h'']
      rw [abs_of_neg h'']
      linarith
    rw [abs_of_neg h']
    · rcases le_or_gt 0 (x+y) with h'' | h''
      · rw [abs_of_nonneg h'']
        linarith
      rw [abs_of_neg h'']
      linarith
  rw [abs_of_neg h]
  rcases le_or_gt 0 y with h' | h'
  · rw [abs_of_nonneg h']
    rcases le_or_gt 0 (x+y) with h'' | h''
    · rw [abs_of_nonneg h'']
      linarith
    rw [abs_of_neg h'']
    linarith
  rw [abs_of_neg h']
  rcases le_or_gt 0 (x+y) with h'' | h''
  · rw [abs_of_nonneg h'']
    linarith
  rw [abs_of_neg h'']
  linarith


theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro x; left; exact x
  rw [abs_of_neg h]
  intro x; right; exact x
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h'
    rcases h' with h'' | h''
    · exact h''
    linarith
  rw [abs_of_neg h]
  rintro (h' | h')
  · linarith
  linarith

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    intro h'
    constructor
    · linarith
    exact h'
  rw [abs_of_neg h]
  intro h'
  constructor
  · linarith
  linarith
  rintro ⟨h₁, h₂⟩
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    exact h₂
  rw [abs_of_neg h]
  linarith
