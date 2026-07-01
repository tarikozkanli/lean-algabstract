-- RingTheorems.lean
-- Core derived theorems for rings

import Algabstract.Ring

namespace RingTheorems

variable {α : Type} (R : Ring α)

/-- If a + b = 0 then b = -a. -/
theorem eq_neg_of_add_eq_zero_right {a b : α} (h : R.add a b = R.zero) :
    b = R.neg a := by
  calc
    b = R.add R.zero b := by symm; exact R.zero_add b
    _ = R.add (R.add (R.neg a) a) b := by rw [R.neg_add a]
    _ = R.add (R.neg a) (R.add a b) := by rw [R.add_assoc]
    _ = R.add (R.neg a) R.zero := by rw [h]
    _ = R.neg a := by rw [R.add_zero]

/-- If a + b = 0 then a = -b. -/
theorem eq_neg_of_add_eq_zero_left {a b : α} (h : R.add a b = R.zero) :
    a = R.neg b := by
  have h' : R.add b a = R.zero := by rw [R.add_comm, h]
  exact eq_neg_of_add_eq_zero_right R h'

/-- Additive inverse of zero is zero. -/
theorem neg_zero : R.neg R.zero = R.zero := by
  have h : R.add R.zero (R.neg R.zero) = R.zero := R.add_neg R.zero
  have hz : R.add R.zero (R.neg R.zero) = R.neg R.zero := R.zero_add (R.neg R.zero)
  exact Eq.trans (Eq.symm hz) h

/-- Double negation. -/
theorem neg_neg (a : α) : R.neg (R.neg a) = a := by
  have h : a = R.neg (R.neg a) := eq_neg_of_add_eq_zero_left R (R.add_neg a)
  exact Eq.symm h

/-- Right additive cancellation. -/
theorem add_right_cancel {a b c : α} (h : R.add a c = R.add b c) : a = b := by
  have h1 : R.add (R.add a c) (R.neg c) = R.add (R.add b c) (R.neg c) := by
    rw [h]
  have h2 : R.add a (R.add c (R.neg c)) = R.add b (R.add c (R.neg c)) := by
    simpa [R.add_assoc] using h1
  have h3 : R.add a R.zero = R.add b R.zero := by
    simpa [R.add_neg] using h2
  simpa [R.add_zero] using h3

/-- Left additive cancellation. -/
theorem add_left_cancel {a b c : α} (h : R.add a b = R.add a c) : b = c := by
  have h' : R.add b a = R.add c a := by
    simpa [R.add_comm] using h
  exact add_right_cancel R h'

/-- a * (-b) = -(a * b). -/
theorem mul_neg (a b : α) : R.mul a (R.neg b) = R.neg (R.mul a b) := by
  have hsum : R.add (R.mul a b) (R.mul a (R.neg b)) = R.zero := by
    have hmul : R.mul a (R.add b (R.neg b)) = R.add (R.mul a b) (R.mul a (R.neg b)) :=
      R.mul_add a b (R.neg b)
    calc
      R.add (R.mul a b) (R.mul a (R.neg b)) = R.mul a (R.add b (R.neg b)) := by symm; exact hmul
      _ = R.mul a R.zero := by rw [R.add_neg]
      _ = R.zero := R.mul_zero a
  exact eq_neg_of_add_eq_zero_right R hsum

/-- (-a) * b = -(a * b). -/
theorem neg_mul (a b : α) : R.mul (R.neg a) b = R.neg (R.mul a b) := by
  have hsum : R.add (R.mul a b) (R.mul (R.neg a) b) = R.zero := by
    have hmul : R.mul (R.add a (R.neg a)) b = R.add (R.mul a b) (R.mul (R.neg a) b) :=
      R.add_mul a (R.neg a) b
    calc
      R.add (R.mul a b) (R.mul (R.neg a) b) = R.mul (R.add a (R.neg a)) b := by symm; exact hmul
      _ = R.mul R.zero b := by rw [R.add_neg]
      _ = R.zero := R.zero_mul b
  exact eq_neg_of_add_eq_zero_right R hsum

/-- (-a) * (-b) = a * b. -/
theorem neg_mul_neg (a b : α) : R.mul (R.neg a) (R.neg b) = R.mul a b := by
  calc
    R.mul (R.neg a) (R.neg b) = R.neg (R.mul a (R.neg b)) := neg_mul R a (R.neg b)
    _ = R.neg (R.neg (R.mul a b)) := by rw [mul_neg R a b]
    _ = R.mul a b := by rw [neg_neg R (R.mul a b)]

end RingTheorems
