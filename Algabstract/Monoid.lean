-- Mathematical definition:
-- A monoid is a set 𝑀 with a binary operation ∗ : 𝑀 × 𝑀 → 𝑀 and an identity element 𝑒 ∈ 𝑀
-- such that:
-- 1. Associativity: (a ∗ b) ∗ c = a ∗ (b ∗ c) for all a, b, c ∈ 𝑀 [inherited from Semigroup]
-- 2. Left identity: 𝑒 ∗ a = a for all a ∈ 𝑀
-- 3. Right identity: a ∗ 𝑒 = a for all a ∈ 𝑀
--
-- Explanation:
-- A monoid combines the properties of a semigroup (magma with associativity) with an identity element.
-- The identity element acts as a "neutral" element - combining it with any other element doesn't change that element.
-- Monoids are fundamental in abstract algebra and have wide applications in computer science.
--
-- Key properties:
-- - Must be closed under the operation (inherited from Magma)
-- - Must be associative (inherited from Semigroup)
-- - Must have exactly one identity element (uniqueness follows from axioms)
-- - Does NOT require inverses (unlike groups)
--
-- Examples:
-- - Natural numbers under addition with identity 0
-- - Positive integers under multiplication with identity 1
-- - Lists under concatenation with identity empty list
-- - Strings under concatenation with identity empty string
--
-- In the algebraic hierarchy:
-- Magma → Semigroup (+ associativity) → Monoid (+ identity) → Group (+ inverses)
import Algabstract.Semigroup

-- Uniform Unicode notation for single-operation hierarchy
infixl:70 " ∗ " => Magma.mul

structure Monoid (α : Type) extends Semigroup α where
  /-- The identity element: combining with any element leaves it unchanged -/
  one : α
  /-- Left identity: one ∗ a = a -/
  one_mul : ∀ a : α, mul one a = a
  /-- Right identity: a ∗ one = a -/
  mul_one : ∀ a : α, mul a one = a

-- Example: monoid of natural numbers under addition
def natAddMonoid : Monoid Nat :=
{ toSemigroup := natAddSemigroup,
  one := (0 : Nat),
  one_mul := Nat.zero_add,
  mul_one := Nat.add_zero }

-- Prove associativity for natAddMonoid
example : ∀ a b c : Nat, natAddMonoid.mul (natAddMonoid.mul a b) c = natAddMonoid.mul a (natAddMonoid.mul b c) :=
  fun a b c => Nat.add_assoc a b c

-- Prove left identity for natAddMonoid: one ∗ a = a
example : ∀ a : Nat, natAddMonoid.mul natAddMonoid.one a = a :=
  fun a => Nat.zero_add a

-- Prove right identity for natAddMonoid: a ∗ one = a
example : ∀ a : Nat, natAddMonoid.mul a natAddMonoid.one = a :=
  fun a => Nat.add_zero a

-- Prove identity element property: one is the identity element
example : ∀ a : Nat, natAddMonoid.mul natAddMonoid.one a = a ∧ natAddMonoid.mul a natAddMonoid.one = a :=
  fun a => ⟨Nat.zero_add a, Nat.add_zero a⟩
