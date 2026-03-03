import Algabstract.Monoid

-- Mathematical definition:
-- A group is a set 𝐺 with a binary operation ∗ : 𝐺 × 𝐺 → 𝐺 and an identity element 𝑒 ∈ 𝐺
-- such that:
-- 1. Associativity: (a ∗ b) ∗ c = a ∗ (b ∗ c) for all a, b, c ∈ 𝐺
-- 2. Identity: 𝑒 ∗ a = a and a ∗ 𝑒 = a for all a ∈ 𝐺
-- 3. Inverses: For each a ∈ 𝐺, there exists a⁻¹ ∈ 𝐺 such that a ∗ a⁻¹ = 𝑒 and a⁻¹ ∗ a = 𝑒
--
-- Explanation:
-- A group is one of the most important algebraic structures in mathematics.
-- It extends a monoid by requiring that every element has an inverse for the group operation.
-- Groups have profound applications in physics, chemistry, cryptography, and computer science.
--
-- Key properties:
-- - Inherits closure, associativity, and identity from Monoid
-- - Every element must have a unique inverse
-- - Inverses allow us to "solve equations": if a ∗ x = b, then x = a⁻¹ ∗ b
-- - The identity element is its own inverse: e⁻¹ = e
--
-- Examples:
-- - Integers (ℤ) under addition with identity 0 and inverse -a
-- - Non-zero real numbers under multiplication with identity 1 and inverse 1/a
-- - Permutations of a set under composition with identity being no permutation
-- - Symmetries of a geometric shape
--
-- Types of groups:
-- - Abelian/Commutative: a ∗ b = b ∗ a (like integers under addition)
-- - Non-abelian: order matters (like matrix multiplication)
--
-- In the algebraic hierarchy (single operation):
-- Magma ⊂ Semigroup ⊂ Monoid ⊂ Group ⊂ AbelianGroup

-- Uniform Unicode notation for single-operation hierarchy
infixl:70 " ∗ " => Magma.mul

structure Group (α : Type) extends Monoid α where
  /-- The inverse operation: produces the inverse of an element -/
  inv : α → α
  /-- Left inverse: a⁻¹ ∗ a = one -/
  inv_mul_self : ∀ a : α, mul (inv a) a = one
  /-- Right inverse: a ∗ a⁻¹ = one -/
  mul_inv_self : ∀ a : α, mul a (inv a) = one

-- Custom notation for inverse (defined after Group structure)
notation:90 a "⁻¹" => Group.inv a

-- Example: trivial group (single element group)
-- This is the simplest group where all operations return the single element.
-- For a richer group example, one would use ℤ (integers) or other structures.
def trivialMonoid : Monoid Unit :=
{ mul := fun _ _ => (),
  mul_assoc := fun _ _ _ => rfl,
  one := (),
  one_mul := fun _ => rfl,
  mul_one := fun _ => rfl }

def trivialGroup : Group Unit :=
{ toMonoid := trivialMonoid,
  inv := fun _ => (),
  inv_mul_self := fun _ => rfl,
  mul_inv_self := fun _ => rfl }

-- Prove associativity for trivialGroup
example : ∀ a b c : Unit, trivialGroup.mul (trivialGroup.mul a b) c = trivialGroup.mul a (trivialGroup.mul b c) :=
  fun _ _ _ => rfl

-- Prove left identity for trivialGroup
example : ∀ a : Unit, trivialGroup.mul trivialGroup.one a = a :=
  fun _ => rfl

-- Prove right identity for trivialGroup
example : ∀ a : Unit, trivialGroup.mul a trivialGroup.one = a :=
  fun _ => rfl

-- Prove left inverse property
example : ∀ a : Unit, trivialGroup.mul (trivialGroup.inv a) a = trivialGroup.one :=
  trivialGroup.inv_mul_self

-- Prove right inverse property
example : ∀ a : Unit, trivialGroup.mul a (trivialGroup.inv a) = trivialGroup.one :=
  trivialGroup.mul_inv_self

-- Proof that inverse of () is ()
example : trivialGroup.inv () = () := rfl
