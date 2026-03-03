-- DivisionRing.lean
-- A division ring (skew field) is a ring where every non-zero element has a multiplicative inverse

import Algabstract.Ring

/- # Division Ring (Skew Field)

A division ring is a ring in which every non-zero element has a multiplicative inverse.
Unlike a field, multiplication need not be commutative.

**Definition:**
- A division ring (𝐷, +, ·) is a ring where:
  - ∀ a ∈ 𝐷, a ≠ 0 → ∃ a⁻¹ ∈ 𝐷, a · a⁻¹ = 1 and a⁻¹ · a = 1
  - 0 ≠ 1 (nontrivial)

**Properties inherited from Ring:**
1. (𝐷, +) is an abelian group
2. (𝐷, ·) is a monoid (not necessarily commutative)
3. Distributivity of multiplication over addition

**Additional division ring properties:**
4. Every non-zero element has a multiplicative inverse
5. Nontrivial: 0 ≠ 1

**Examples:**
- Real numbers (ℝ) - also commutative, hence a field
- Complex numbers (ℂ) - also commutative, hence a field
- Quaternions (ℍ) - non-commutative division ring
- Every field is a division ring

**Non-examples:**
- Integers (ℤ) - not every non-zero element has inverse (e.g., 2)
- Matrix rings M_n(R) for n ≥ 2 - have zero divisors

**Key properties:**
- No zero divisors (if a · b = 0, then a = 0 or b = 0)
- Cancellation laws hold
- Can solve linear equations ax = b for a ≠ 0

**Note:**
- "Division ring" and "skew field" are synonymous terms
- Every division ring that is also commutative is a field
- Finite division rings are fields (Wedderburn's theorem)

**Hierarchy Summary:**
- Single operation: Magma ⊂ Semigroup ⊂ Monoid ⊂ Group ⊂ AbelianGroup
- Two operations: Semiring ⊂ Ring ⊂ DivisionRing
- Two operations (commutative): Semiring ⊂ Ring ⊂ CommutativeRing ⊂ IntegralDomain ⊂ Field
- Note: Field = DivisionRing + Commutativity = IntegralDomain + Inverses
-/

structure DivisionRing (α : Type) extends Ring α where
  inv : α → α
  mul_inv : ∀ a : α, a ≠ zero → mul a (inv a) = one
  inv_mul : ∀ a : α, a ≠ zero → mul (inv a) a = one
  zero_ne_one : zero ≠ one

-- Note: Unicode inverse notation ⁻¹ defined in Field module to avoid duplication

-- Example: Bool forms a division ring (and actually a field since it's also commutative)
-- First define the prerequisite structures locally
def boolSemiringForDiv : Semiring Bool :=
{ add := Bool.xor,
  add_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> decide,
  add_comm := by
    intro a b
    cases a <;> cases b <;> decide,
  zero := false,
  zero_add := by
    intro a
    cases a <;> decide,
  add_zero := by
    intro a
    cases a <;> decide,
  mul := Bool.and,
  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> decide,
  one := true,
  one_mul := by
    intro a
    cases a <;> decide,
  mul_one := by
    intro a
    cases a <;> decide,
  mul_add := by
    intro a b c
    cases a <;> cases b <;> cases c <;> decide,
  add_mul := by
    intro a b c
    cases a <;> cases b <;> cases c <;> decide,
  zero_mul := by
    intro a
    cases a <;> decide,
  mul_zero := by
    intro a
    cases a <;> decide }

def boolRingForDiv : Ring Bool :=
{ toSemiring := boolSemiringForDiv,
  neg := id,
  add_neg := by
    intro a
    cases a <;> decide,
  neg_add := by
    intro a
    cases a <;> decide }

def boolDivisionRing : DivisionRing Bool :=
{ toRing := boolRingForDiv,
  inv := fun _ => true,
  mul_inv := by
    intro a h
    cases a with
    | false => cases (h rfl)
    | true => decide,
  inv_mul := by
    intro a h
    cases a with
    | false => cases (h rfl)
    | true => decide,
  zero_ne_one := by decide }

-- Demonstrate multiplicative inverse
example : boolDivisionRing.mul true (boolDivisionRing.inv true) = boolDivisionRing.one :=
  boolDivisionRing.mul_inv true (by decide)

-- Verify nontriviality
example : boolDivisionRing.zero ≠ boolDivisionRing.one := by
  intro h
  cases h
