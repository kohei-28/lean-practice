import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_comm b, neg_add_cancel, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [<- zero_add b, <- neg_add_cancel a, add_assoc, h, <- add_assoc, neg_add_cancel, zero_add]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [<- zero_add a, <- neg_add_cancel b, add_assoc, add_comm b, h, add_comm c, <- add_assoc, neg_add_cancel, zero_add]
