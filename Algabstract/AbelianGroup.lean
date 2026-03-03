-- AbelianGroup.lean
-- An abelian group (commutative group) adds commutativity to the Group structure

import Algabstract.Group

/- # Abelian Group (Commutative Group)

An abelian group is a Group where the operation is commutative.

**Definition:**
- An abelian group (𝐺, ∗) is a group where:
  - ∀ a, b ∈ 𝐺: a ∗ b = b ∗ a  (commutativity)
  - Plus all Group properties: associativity, identity, and inverses

**Mathematical Notation:**
- ∗ denotes the group operation
- e denotes the identity element
- a⁻¹ denotes the inverse of a

**Properties:**
1. **Closure:** a ∗ b ∈ 𝐺
2. **Associativity:** (a ∗ b) ∗ c = a ∗ (b ∗ c)
3. **Identity:** ∃e ∈ 𝐺, ∀a ∈ 𝐺: e ∗ a = a ∗ e = a
4. **Inverses:** ∀a ∈ 𝐺, ∃a⁻¹ ∈ 𝐺: a ∗ a⁻¹ = a⁻¹ ∗ a = e
5. **Commutativity:** a ∗ b = b ∗ a

**Examples:**
- (ℤ, +): integers under addition
- (ℚ*, ·): non-zero rationals under multiplication
- (ℝ, +): real numbers under addition
- (ℝ*, ·): non-zero real numbers under multiplication
- Dihedral group D_n is a non-abelian group (counterexample)

**Important Notes:**
- Not all groups are abelian (e.g., S_n for n ≥ 3, matrix multiplication)
- Abelian groups are also called commutative groups
- Many structures in mathematics are naturally abelian groups
-/

structure AbelianGroup (α : Type) extends Group α where
  mul_comm : ∀ a b : α, mul a b = mul b a

-- In the algebraic hierarchy (single operation):
-- Magma ⊂ Semigroup ⊂ Monoid ⊂ Group ⊂ AbelianGroup

-- Example: integers under addition form a group
def intAddGroup : Group Int :=
{ toMonoid :=
    { toSemigroup :=
        { mul := Int.add,
          mul_assoc := Int.add_assoc },
      one := 0,
      one_mul := Int.zero_add,
      mul_one := Int.add_zero },
  inv := Int.neg,
  inv_mul_self := fun a => show (-a) + a = 0 by omega,
  mul_inv_self := fun a => show a + (-a) = 0 by omega }

-- Example: integers under addition form an abelian group
def intAddAbelianGroup : AbelianGroup Int :=
{ toGroup := intAddGroup,
  mul_comm := Int.add_comm }

-- Verify commutativity property for our example
example : intAddAbelianGroup.mul 5 3 = intAddAbelianGroup.mul 3 5 :=
  intAddAbelianGroup.mul_comm 5 3

-- Demonstrate identity property
example : intAddAbelianGroup.mul 42 intAddAbelianGroup.one = 42 :=
  Int.add_zero 42

-- Demonstrate inverse property
example : intAddAbelianGroup.mul 10 (intAddAbelianGroup.inv 10) = intAddAbelianGroup.one :=
  show 10 + (-10) = 0 by omega
