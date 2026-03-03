import Algabstract.Magma

-- Mathematical definition:
-- A semigroup is a set 𝑆 equipped with an associative binary operation ∗ : 𝑆 × 𝑆 → 𝑆.
-- For all a, b, c ∈ 𝑆: (a ∗ b) ∗ c = a ∗ (b ∗ c)
--
-- Explanation:
-- A semigroup extends a magma by imposing the associativity constraint on the binary operation.
-- This ensures that the result of combining multiple elements is independent of how we parenthesize.
-- Unlike monoids, semigroups do not require an identity element.
--
-- Examples:
-- - Natural numbers under addition (closed, associative)
-- - Matrix multiplication (closed, associative)
-- - String concatenation (closed, associative)

-- Uniform Unicode notation for single-operation hierarchy
infixl:70 " ∗ " => Magma.mul

structure Semigroup (α : Type) extends Magma α where
  /-- Associativity property: (a ∗ b) ∗ c = a ∗ (b ∗ c) -/
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)

-- Example: semigroup of natural numbers under addition
def natAddSemigroup : Semigroup Nat :=
{ mul := Nat.add,
  mul_assoc := Nat.add_assoc }

-- Prove associativity for natAddSemigroup
example : ∀ a b c : Nat, natAddSemigroup.mul (natAddSemigroup.mul a b) c = natAddSemigroup.mul a (natAddSemigroup.mul b c) :=
  fun a b c => Nat.add_assoc a b c

-- Proof variant using mul_assoc field
example : ∀ a b c : Nat, (a + b) + c = a + (b + c) :=
  natAddSemigroup.mul_assoc
