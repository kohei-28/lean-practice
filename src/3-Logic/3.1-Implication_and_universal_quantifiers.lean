theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := by rw [abs_mul]
    _ ≤ |x| * ε := by
      apply mul_le_mul
      · apply le_refl
      · linarith
      · apply abs_nonneg
      apply abs_nonneg
    _ < 1 * ε := by
      apply mul_lt_mul
      · linarith
      · apply le_refl
      · apply epos
      linarith
    _ = ε := by apply one_mul

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  · apply hfa
  apply hgb

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  dsimp
  apply mul_nonneg
  apply nnf
  apply nng

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  intro x
  dsimp
  calc
    f x * g x ≤ a * g x := by
      apply mul_le_mul_of_nonneg_right
      · apply hfa
      apply nng
    _ ≤ a * b := by
      apply mul_le_mul_of_nonneg_left
      · apply hgb
      apply nna

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  fun a b aleb ↦ mul_le_mul_of_nonneg_left (mf aleb) nnc

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  fun a b aleb ↦ mf (mg aleb)

example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  calc
    (fun x ↦ f x * g x) x = f x * g x := rfl
    _ = f (-x) * g (-x) := by rw [of, og, neg_mul_neg]

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  calc
    (fun x ↦ f x * g x) x = f x * g x := rfl
    _ = - (f (-x) * g (-x)) := by rw [ef, og, mul_neg]

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  calc
    (fun x ↦ f (g x)) x = f (g x) := rfl
    _ = f (g (-x)) := by rw [og, ef, neg_neg]

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro rs st x xr
  apply st
  apply rs
  apply xr
end

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intro x xs
  calc
    x ≤ a := by
      apply h
      apply xs
    _ ≤ b := by apply h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  intro x₁ x₂ h'
  exact (mul_right_inj' h).mp h'

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro x₁ x₂ h'
  apply injf
  apply injg
  apply h'
end
