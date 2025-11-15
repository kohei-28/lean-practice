import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_comm b, neg_add_cancel, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [<- zero_add b, <- neg_add_cancel a, add_assoc, h, <- add_assoc, neg_add_cancel, zero_add]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [<- zero_add a, <- neg_add_cancel b, add_assoc, add_comm b, h, add_comm c, <- add_assoc, neg_add_cancel, zero_add]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [<- add_mul, add_zero, add_zero]
  rw [add_left_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [<- add_zero (-a), <- h, neg_add_cancel_left]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [<- add_zero a, <- add_neg_cancel b, <- add_assoc, h, zero_add]

theorem neg_neg (a : R) : - -a = a := by
  have h: -a + a = 0 := by
    rw [add_comm, add_neg_cancel]
  rw [neg_eq_of_add_eq_zero h]

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg a a, add_neg_cancel]

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [<- one_add_one_eq_two, add_mul, one_mul]


section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

theorem neg_left_cancel {a b c : G} (f: a * b = a * c) : b = c := by
  rw [<- one_mul b, <- inv_mul_cancel a, mul_assoc, f, <- mul_assoc, inv_mul_cancel, one_mul]

theorem mul_one (a : G) : a * 1 = a := by
  have h: a⁻¹ * (a * 1) = a⁻¹ * a := by
    rw [<- mul_assoc, inv_mul_cancel, one_mul]
  rw [neg_left_cancel h]

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  have h: a⁻¹ * (a * a⁻¹) = a⁻¹ * 1 := by
    rw [<-mul_assoc, inv_mul_cancel, mul_one, one_mul]
  rw [neg_left_cancel h]

theorem neg_right_cancel {a b c : G} (f: b * a = c * a) : b = c := by
  rw [<- mul_one b, <- mul_inv_cancel a, <- mul_assoc, f, mul_assoc, mul_inv_cancel, mul_one]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h : (a * b)⁻¹ * (a * b) = b⁻¹ * a⁻¹ * (a * b) := by
    rw [inv_mul_cancel, <- mul_assoc, mul_assoc b⁻¹, inv_mul_cancel, mul_one, inv_mul_cancel]
  rw [neg_right_cancel h]

end MyGroup

end
