import MIL.Common
import Mathlib.Data.Real.Basic

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [<- mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [<- mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm]
  rw [mul_assoc]
  rw [mul_comm a]

section
variable (a b c d : ℝ)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  calc
    (a + b) * (c + d) = a * (c + d) + b * (c + d) := by
      rw [add_mul]
    _= a * c + a * d + b * c + b * d := by
      rw [mul_add, mul_add, <- add_assoc]

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  calc
    (a + b) * (a - b) = a * a - a * b + (b * a - b * b) := by
      rw[add_mul, mul_sub, mul_sub]
    _= a ^ 2 - b ^ 2 := by
      rw[<- pow_two, add_sub, <- pow_two, mul_comm, sub_add, sub_self, sub_zero]
end