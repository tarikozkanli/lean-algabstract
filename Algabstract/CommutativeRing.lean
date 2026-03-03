-- CommutativeRing.lean
-- A commutative ring adds multiplicative commutativity to the Ring structure

import Algabstract.Ring

/- # Commutative Ring

A commutative ring is a Ring where multiplication is commutative.

**Definition:**
- A commutative ring (𝑅, +, ·) is a ring where:
  - ∀ a, b ∈ 𝑅: a · b = b · a  (multiplicative commutativity)
  - Plus all Ring properties

**Ring Properties Inherited:**
1. (𝑅, +) is an abelian group:
   - Closure under addition
   - Associativity of addition
   - Commutativity of addition
   - Additive identity (zero)
   - Additive inverses
2. (𝑅, ·) is a monoid:
   - Closure under multiplication
   - Associativity of multiplication
   - Multiplicative identity (one)
3. Distributivity:
   - a · (b + c) = a · b + a · c  (left distributivity)
   - (a + b) · c = a · c + b · c  (right distributivity)
4. Commutative multiplication: a · b = b · a

**Notation:**
- ⊕ denotes the additive operation
- ⊗ denotes the multiplicative operation
- 0 denotes the additive identity
- 1 denotes the multiplicative identity

**Examples:**
- (ℤ, +, ·): integers
- (ℚ, +, ·): rational numbers
- (ℝ, +, ·): real numbers
- (ℤ[x], +, ·): polynomials with integer coefficients
- 𝔽_p: finite fields with p elements

**Important Notes:**
- Most common rings are commutative
- Non-commutative rings include matrix rings M_n(R) for n ≥ 2
- Commutative rings form the natural setting for commutative algebra
- Every field is a commutative ring
- In commutative rings: ab = ba (unlike general rings)

**Relationship to Other Structures:**
- CommutativeRing ⊂ Ring
- CommutativeRing ⊃ Field (when we add multiplicative inverses for non-zero elements)
- CommutativeRing ⊃ IntegralDomain (when we add the property that ab = 0 implies a = 0 or b = 0)

**Hierarchy Summary:**
- Single operation: Magma ⊂ Semigroup ⊂ Monoid ⊂ Group ⊂ AbelianGroup
- Two operations: Semiring ⊂ Ring ⊂ CommutativeRing
-/

structure CommutativeRing (α : Type) extends Ring α where
  mul_comm : ∀ a b : α, mul a b = mul b a

-- Example: integers under standard addition and multiplication
def intCommutativeRing : CommutativeRing Int :=
{ toRing := intRing,
  mul_comm := Int.mul_comm }

-- Verify commutativity of multiplication
example : intCommutativeRing.mul 6 7 = intCommutativeRing.mul 7 6 :=
  intCommutativeRing.mul_comm 6 7

-- Demonstrate left distributivity
example : intCommutativeRing.mul 3 (intCommutativeRing.add 4 5) =
         intCommutativeRing.add (intCommutativeRing.mul 3 4) (intCommutativeRing.mul 3 5) :=
  Int.mul_add 3 4 5

-- Demonstrate right distributivity (follows from commutativity and left distributivity in commutative rings)
example : intCommutativeRing.mul (intCommutativeRing.add 2 3) 4 =
         intCommutativeRing.add (intCommutativeRing.mul 2 4) (intCommutativeRing.mul 3 4) :=
  Int.add_mul 2 3 4

-- Verify multiplicative identity
example : intCommutativeRing.mul 42 intCommutativeRing.one = 42 :=
  Int.mul_one 42

-- Combined property: commutativity of multiplication with identity
example : intCommutativeRing.mul intCommutativeRing.one 99 =
         intCommutativeRing.mul 99 intCommutativeRing.one :=
  by simp [intCommutativeRing.mul_comm]
