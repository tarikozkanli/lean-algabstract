import Algabstract.Semiring

-- Mathematical definition:
-- A ring (𝑅, +, ·) is a set 𝑅 with two binary operations:
-- - Addition (+): 𝑅 × 𝑅 → 𝑅
-- - Multiplication (·): 𝑅 × 𝑅 → 𝑅
-- such that:
-- 1. (𝑅, +) forms an abelian (commutative) group with identity 0
-- 2. (𝑅, ·) forms a monoid with identity 1 (associative with identity)
-- 3. Distributivity: a · (b + c) = (a · b) + (a · c) and (b + c) · a = (b · a) + (c · a)
--
-- Explanation:
-- A ring is one of the most important algebraic structures combining additive and multiplicative properties.
-- Rings generalize many familiar number systems and have deep applications in algebra, number theory, and geometry.
--
-- Key properties:
-- - Two operations with different algebraic properties
-- - Addition forms an abelian group (commutative, with inverses)
-- - Multiplication forms a monoid (no requirement for inverses or commutativity)
-- - The operations are connected by distributivity laws
--
-- Examples:
-- - Integers (ℤ) under addition and multiplication
-- - Polynomials over a field
-- - Matrices over a ring
-- - Gaussian integers: {a + bi : a, b ∈ ℤ}
--
-- Types of rings:
-- - Commutative ring: multiplication is commutative (a · b = b · a)
-- - Ring with unity: has multiplicative identity 1 (assumed above)
-- - Division ring: non-zero elements have multiplicative inverses
-- - Field: commutative division ring
--
-- In the algebraic hierarchy:
-- Single operation: Magma ⊂ Semigroup ⊂ Monoid ⊂ Group ⊂ AbelianGroup
-- Two operations: Semiring ⊂ Ring ⊂ CommutativeRing

structure Ring (α : Type) extends Semiring α where
  -- Additive inverse properties (extends Semiring with inverses)
  /-- Additive inverse: -a such that a + (-a) = 0 and (-a) + a = 0 -/
  neg : α → α
  add_neg : ∀ a : α, add a (neg a) = zero
  neg_add : ∀ a : α, add (neg a) a = zero

-- Uniform Unicode notation for additive inverse
prefix:100 "⊖" => Ring.neg

-- Example: semiring of integers ℤ (without requiring additive inverses in the structure)
def intSemiring : Semiring Int :=
{ add := Int.add,
  add_assoc := Int.add_assoc,
  add_comm := Int.add_comm,
  zero := 0,
  zero_add := Int.zero_add,
  add_zero := Int.add_zero,
  mul := Int.mul,
  mul_assoc := Int.mul_assoc,
  one := 1,
  one_mul := Int.one_mul,
  mul_one := Int.mul_one,
  mul_add := Int.mul_add,
  add_mul := Int.add_mul,
  zero_mul := Int.zero_mul,
  mul_zero := Int.mul_zero }

-- Example: ring of integers ℤ (using Int from Lean standard library)
def intRing : Ring Int :=
{ toSemiring := intSemiring,
  neg := Int.neg,
  add_neg := fun a => show a + (-a) = 0 by omega,
  neg_add := fun a => show (-a) + a = 0 by omega,
  }

-- Prove additive associativity for intRing
example : ∀ a b c : Int, intRing.add (intRing.add a b) c = intRing.add a (intRing.add b c) :=
  intRing.add_assoc

-- Prove additive commutativity for intRing
example : ∀ a b : Int, intRing.add a b = intRing.add b a :=
  intRing.add_comm

-- Prove multiplicative associativity for intRing
example : ∀ a b c : Int, intRing.mul (intRing.mul a b) c = intRing.mul a (intRing.mul b c) :=
  intRing.mul_assoc

-- Prove left distributivity for intRing
example : ∀ a b c : Int, intRing.mul a (intRing.add b c) = intRing.add (intRing.mul a b) (intRing.mul a c) :=
  intRing.mul_add

-- Prove right distributivity for intRing
example : ∀ a b c : Int, intRing.mul (intRing.add a b) c = intRing.add (intRing.mul a c) (intRing.mul b c) :=
  intRing.add_mul
