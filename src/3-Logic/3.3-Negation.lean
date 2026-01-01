example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨a, fnlba⟩
  rcases h a with ⟨x, hx⟩
  have: a ≤ f x := fnlba x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  intro fx
  rcases fx with ⟨a, fxuba⟩
  have: (fun x ↦ x) (a + 1) ≤ a:= fxuba (a+1)
  linarith

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro blea
  have: f b ≤ f a:= by
    apply h
    apply blea
  linarith

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro mono
  have: f a ≤ f b := by
    apply mono
    apply h
  linarith

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b aleb
    simp [f]
  have h' : f 1 ≤ f 0 := le_refl _
  have: (1: ℝ) ≤ (0: ℝ):= h monof h'
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro h'
  linarith [h _ h']

example (h : ¬¬Q) : Q := by
  by_contra h'
  apply h h'


example (h : Q) : ¬¬Q := by
  by_contra h'
  apply h' h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  apply h
  use a
  intro x
  apply le_of_not_gt
  intro h''
  apply h'
  use x

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp only [Monotone] at h
  push_neg at h
  exact h
