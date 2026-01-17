example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  rcases h with ⟨h₁, h₂⟩
  constructor
  · apply h₁
  intro h'
  apply h₂
  exact Nat.dvd_antisymm h₁ h'

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · apply h₁
    intro h
    apply h₂
    exact le_of_eq (id (Eq.symm h))
  rintro ⟨h₃, h₄⟩
  constructor
  · apply h₃
  intro h'
  apply h₄
  exact le_antisymm h₃ h'

theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  pow_eq_zero h'

theorem aux1 {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : y = 0 :=
  have h' : y ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · linarith [aux h]
    linarith [aux1 h]
  rintro ⟨h₁, h₂⟩
  rw [h₁, h₂]
  norm_num

example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [Monotone]
  push_neg
  use 1, 2
  norm_num

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_ge]
  constructor
  rintro ⟨h₁,h₂⟩
  constructor
  · apply h₁
  intro h
  apply h₂
  exact le_of_eq (id (Eq.symm h))
  rintro ⟨h₁, h₂⟩
  constructor
  · apply h₁
  intro h
  apply h₂
  apply le_antisymm h₁ h


example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_ge]
  rintro ⟨h₁, h₂⟩
  rintro ⟨h₃, h₄⟩
  constructor
  · apply le_trans h₁ h₃
  intro h'
  apply h₄
  apply le_trans h' h₁
