-- IntegralDomain.lean
-- An integral domain is a commutative ring with no zero divisors

import Algabstract.CommutativeRing

/- # Integral Domain

An integral domain is a commutative ring where the product of two non-zero elements is always non-zero.

**Definition:**
- An integral domain (𝐷, +, ·) is a commutative ring where:
  - ∀ a, b ∈ 𝐷: a · b = 0 → a = 0 ∨ b = 0  (no zero divisors)
  - 0 ≠ 1  (nontrivial)

**Properties inherited from CommutativeRing:**
1. (𝐷, +) is an abelian group
2. (𝐷, ·) is a commutative monoid
3. Distributivity of multiplication over addition
4. Commutative multiplication: a · b = b · a

**Additional integral domain properties:**
5. No zero divisors: if a · b = 0, then a = 0 or b = 0
6. Nontrivial: 0 ≠ 1

**Examples:**
- Integers (ℤ)
- Gaussian integers ℤ[i]
- Polynomial rings over fields or integral domains
- Any field is an integral domain

**Non-examples:**
- ℤ/6ℤ (has zero divisors: 2 · 3 = 0)
- Matrix rings M_n(R) for n ≥ 2 (non-commutative and have zero divisors)

**Key properties:**
- Cancellation law holds: if a · b = a · c and a ≠ 0, then b = c
- Can be embedded in a field (field of fractions)
- Finite integral domains are fields

**Hierarchy Summary:**
- Single operation: Magma ⊂ Semigroup ⊂ Monoid ⊂ Group ⊂ AbelianGroup
- Two operations: Semiring ⊂ Ring ⊂ CommutativeRing ⊂ IntegralDomain ⊂ Field
-/

structure IntegralDomain (α : Type) extends CommutativeRing α where
  no_zero_divisors : ∀ a b : α, mul a b = zero → a = zero ∨ b = zero
  zero_ne_one : zero ≠ one

-- Example: integers form an integral domain
def intIntegralDomain : IntegralDomain Int :=
{ toCommutativeRing := intCommutativeRing,
  no_zero_divisors := by
    intro a b hab
    -- hab says intCommutativeRing.mul a b = 0, which is a * b = 0
    simp only [intCommutativeRing, intRing, intSemiring] at hab
    -- Now hab : a * b = 0 for native Int multiplication
    cases Classical.em (a = 0) with
    | inl h => left; exact h
    | inr ha =>
      right
      cases Classical.em (b = 0) with
      | inl h => exact h
      | inr hb =>
        -- Both a ≠ 0 and b ≠ 0, but a * b = 0 - contradiction
        exact absurd hab (Int.mul_ne_zero ha hb),
  zero_ne_one := by decide }

-- Demonstrate zero divisor property
example : intIntegralDomain.mul 3 5 = 15 := rfl

example : intIntegralDomain.mul 3 5 ≠ intIntegralDomain.zero := by decide

-- Verify nontriviality
example : intIntegralDomain.zero ≠ intIntegralDomain.one :=
  intIntegralDomain.zero_ne_one
