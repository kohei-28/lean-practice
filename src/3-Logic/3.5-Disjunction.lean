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

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl|rfl⟩
  · linarith [sq_nonneg x, sq_nonneg y]
  linarith [sq_nonneg x, sq_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h: (x - 1) = 0 ∨ (x + 1) = 0:= by
    apply eq_zero_or_eq_zero_of_mul_eq_zero
    linarith
  rcases h with h'|h'
  · left; linarith
  right; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h: (x - y) = 0 ∨ (x + y) = 0:= by
    apply eq_zero_or_eq_zero_of_mul_eq_zero
    linarith
  rcases h with h'|h'
  · left; linarith
  right; linarith
