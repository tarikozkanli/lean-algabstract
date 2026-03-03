-- Field.lean
-- A field adds multiplicative inverses for non-zero elements to the CommutativeRing structure

import Algabstract.CommutativeRing

/- # Field

A field is a commutative ring in which every non-zero element has a multiplicative inverse.

**Definition:**
- A field (𝐹, +, ·) is a commutative ring where:
  - ∀ a ∈ 𝐹, a ≠ 0 → ∃ a⁻¹ ∈ 𝐹, a · a⁻¹ = 1 and a⁻¹ · a = 1

**Properties inherited from CommutativeRing:**
1. (𝐹, +) is an abelian group
2. (𝐹, ·) is a commutative monoid
3. Distributivity of multiplication over addition

**Additional field property:**
4. Every non-zero element has a multiplicative inverse

**Examples:**
- Rational numbers (ℚ)
- Real numbers (ℝ)
- Complex numbers (ℂ)
- Finite fields 𝔽_p (for prime p)

**Hierarchy Summary:**
- Single operation: Magma ⊂ Semigroup ⊂ Monoid ⊂ Group ⊂ AbelianGroup
- Two operations: Semiring ⊂ Ring ⊂ CommutativeRing ⊂ Field
-/

structure Field (α : Type) extends CommutativeRing α where
  inv : α → α
  mul_inv : ∀ a : α, a ≠ zero → mul a (inv a) = one
  inv_mul : ∀ a : α, a ≠ zero → mul (inv a) a = one
  zero_ne_one : zero ≠ one

-- Uniform Unicode notation for multiplicative inverse
prefix:100 "⁻¹" => Field.inv

-- Generic consequences from field axioms
example {α : Type} (F : Field α) (a : α) (h : a ≠ F.zero) :
    F.mul a (F.inv a) = F.one :=
  F.mul_inv a h

example {α : Type} (F : Field α) (a : α) (h : a ≠ F.zero) :
    F.mul (F.inv a) a = F.one :=
  F.inv_mul a h

-- Example tower on Bool (the field 𝔽₂)
def boolSemiring : Semiring Bool :=
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

def boolRing : Ring Bool :=
{ toSemiring := boolSemiring,
  neg := id,
  add_neg := by
    intro a
    cases a <;> decide,
  neg_add := by
    intro a
    cases a <;> decide }

def boolCommutativeRing : CommutativeRing Bool :=
{ toRing := boolRing,
  mul_comm := by
    intro a b
    cases a <;> cases b <;> decide }

def boolField : Field Bool :=
{ toCommutativeRing := boolCommutativeRing,
  inv := fun _ => true,
  mul_inv := by
    intro a h
    cases a with
    | false => cases (h rfl)
    | true => decide
  inv_mul := by
    intro a h
    cases a with
    | false => cases (h rfl)
    | true => decide
  zero_ne_one := by decide }

example : boolField.mul true (boolField.inv true) = boolField.one :=
  boolField.mul_inv true (by decide)
