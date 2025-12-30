theorem fnLb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnLb f a) (hgb : FnLb g b) :
    FnLb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  rcases lbf with ⟨a, lbfa⟩
  rcases lbg with ⟨b, lbgb⟩
  use a + b
  apply fnLb_add lbfa lbgb

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  rcases ubf with ⟨a, ubfa⟩
  use c*a
  intro x
  apply mul_le_mul_of_nonneg_left
  · apply ubfa
  apply h

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d, beq⟩
  rcases divac with ⟨e, ceq⟩
  rw [beq, ceq]
  use d + e; ring

example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro x
  use x/c
  dsimp;
  exact mul_div_cancel₀ x h

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  intro z
  rcases surjg z with ⟨y, gy⟩
  rcases surjf y with ⟨x, fx⟩
  dsimp
  use x
  rw [fx, gy]
