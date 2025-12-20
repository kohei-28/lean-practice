example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · show min (min a b) c ≤ min a (min b c)
    apply le_min
    · calc
        min (min a b) c ≤ min a b := by apply min_le_left
        _≤  a := by apply min_le_left
    apply le_min
    · calc
        min (min a b) c ≤ (min a b) := by apply min_le_left
        _ ≤ b := by apply min_le_right
    apply min_le_right
  · show min a (min b c) ≤ min (min a b) c
    apply le_min
    · apply le_min
      · apply min_le_left
      calc min a (min b c) ≤ min b c := by apply min_le_right
      _ ≤ b := by apply min_le_left
    calc min a (min b c) ≤ min b c := by apply min_le_right
    _ ≤ c := by apply min_le_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_right
    apply min_le_left
  · apply add_le_add_right
    apply min_le_right


example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by ring
  rw [h]
  apply add_le_add_right
  rw [sub_eq_add_neg]
  apply le_trans
  apply aux
  rw [add_neg_cancel_right, add_neg_cancel_right]

example : |a| - |b| ≤ |a - b| := by
  have h: |a - b| = |a - b| + |b| - |b| := by ring
  rw [h, sub_eq_add_neg, sub_eq_add_neg]
  apply add_le_add_right
  have h2: |a| = |(a - b) + b| := by ring
  rw [h2]
  apply abs_add
end

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    rw [mul_comm, mul_assoc]
    apply dvd_mul_right
    apply dvd_mul_left
  rw[pow_two]
  apply dvd_mul_of_dvd_left h
end

example : Nat.gcd m n = Nat.gcd n m := by
  apply _root_.dvd_antisymm
  repeat
    apply Nat.dvd_gcd
    apply Nat.gcd_dvd_right
    apply Nat.gcd_dvd_left
end
