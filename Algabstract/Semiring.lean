-- Mathematical definition:
-- A semiring (R, +, ·) is a set R with two binary operations such that:
-- 1. (R, +) is a commutative monoid with identity 0
-- 2. (R, ·) is a monoid with identity 1
-- 3. Multiplication distributes over addition on both sides
-- 4. Zero is absorbing for multiplication: 0·a = 0 and a·0 = 0
--
-- Unlike rings, semirings do NOT require additive inverses.
--
-- In the algebraic hierarchy (two operations):
-- Semiring ⊂ Ring ⊂ CommutativeRing

structure Semiring (α : Type) where
  -- Additive commutative monoid
  add : α → α → α
  add_assoc : ∀ a b c : α, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : α, add a b = add b a
  zero : α
  zero_add : ∀ a : α, add zero a = a
  add_zero : ∀ a : α, add a zero = a

  -- Multiplicative monoid
  mul : α → α → α
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)
  one : α
  one_mul : ∀ a : α, mul one a = a
  mul_one : ∀ a : α, mul a one = a

  -- Distributivity
  mul_add : ∀ a b c : α, mul a (add b c) = add (mul a b) (mul a c)
  add_mul : ∀ a b c : α, mul (add a b) c = add (mul a c) (mul b c)

  -- Zero absorption
  zero_mul : ∀ a : α, mul zero a = zero
  mul_zero : ∀ a : α, mul a zero = zero

-- Example: natural numbers form a semiring under standard addition/multiplication
def natSemiring : Semiring Nat :=
{ add := Nat.add,
  add_assoc := Nat.add_assoc,
  add_comm := Nat.add_comm,
  zero := 0,
  zero_add := Nat.zero_add,
  add_zero := Nat.add_zero,
  mul := Nat.mul,
  mul_assoc := Nat.mul_assoc,
  one := 1,
  one_mul := Nat.one_mul,
  mul_one := Nat.mul_one,
  mul_add := Nat.mul_add,
  add_mul := Nat.add_mul,
  zero_mul := Nat.zero_mul,
  mul_zero := Nat.mul_zero }

example : ∀ a b c : Nat, natSemiring.mul a (natSemiring.add b c) =
  natSemiring.add (natSemiring.mul a b) (natSemiring.mul a c) :=
  natSemiring.mul_add

example : ∀ a : Nat, natSemiring.mul natSemiring.zero a = natSemiring.zero :=
  natSemiring.zero_mul
