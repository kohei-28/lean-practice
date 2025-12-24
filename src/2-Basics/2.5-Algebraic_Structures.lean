example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · apply le_inf inf_le_right inf_le_left
  apply le_inf inf_le_right inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · calc x ⊓ y ⊓ z ≤ x ⊓ y := by apply inf_le_left
      _ ≤ x := by apply inf_le_left
    apply le_inf
    · calc x ⊓ y ⊓ z ≤ x ⊓ y := by apply inf_le_left
      _ ≤ y := by apply inf_le_right
    apply inf_le_right
  apply le_inf
  · apply le_inf
    · apply inf_le_left
    calc x ⊓ (y ⊓ z) ≤ (y ⊓ z) := inf_le_right
    _ ≤ y := inf_le_left
  calc x ⊓ (y ⊓ z) ≤ (y ⊓ z) := inf_le_right
    _ ≤ z := inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · apply sup_le le_sup_right le_sup_left
  apply sup_le le_sup_right le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · apply le_sup_left
      calc y ≤ y ⊔ z := by apply le_sup_left
      _ ≤ x ⊔ (y ⊔ z) := by apply le_sup_right
    calc z ≤ y ⊔ z := by apply le_sup_right
    _ ≤ x ⊔ (y ⊔ z) := by apply le_sup_right
  apply sup_le
  · calc x ≤ x ⊔ y := by apply le_sup_left
    _ ≤ x ⊔ y ⊔ z := by apply le_sup_left
  apply sup_le
  · calc y ≤ x ⊔ y := by apply le_sup_right
    _ ≤ x ⊔ y ⊔ z := by apply le_sup_left
  apply le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  apply le_inf
  · apply le_refl
  apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    apply inf_le_left
  apply le_sup_left

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, inf_comm (a ⊔ b), absorb1, inf_comm (a ⊔ b), h, <- sup_assoc, inf_comm c, absorb2, inf_comm]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, sup_comm (a ⊓ b), absorb2, sup_comm (a ⊓ b), h, <- inf_assoc, sup_comm c, absorb1, sup_comm]

example (h : a ≤ b) : 0 ≤ b - a := by
  rw [<- sub_self a, sub_eq_add_neg, sub_eq_add_neg, add_comm, add_comm b]
  apply add_le_add_left h

example (h: 0 ≤ b - a) : a ≤ b := by
  rw [<- add_zero a, <- sub_add_cancel b a, add_comm (b - a)]
  apply add_le_add_left h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  rw [<- add_zero (a*c), <- sub_add_cancel (b*c) (a*c), add_comm (b*c - a*c)]
  apply add_le_add_left
  rw [<- sub_mul]
  apply mul_nonneg
  · rw [<- sub_self a, sub_eq_add_neg, sub_eq_add_neg, add_comm, add_comm b]
    apply add_le_add_left h
  apply h'

example (x y : X) : 0 ≤ dist x y := by
  have h: 0 ≤ dist x y + dist y x := by
    rw [<- dist_self x]
    apply dist_triangle
  linarith [dist_comm x y]
