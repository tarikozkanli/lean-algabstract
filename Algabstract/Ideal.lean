-- Ideal.lean
-- Ideals in commutative rings

import Algabstract.CommutativeRing

/- # Ideal

An ideal is a subset of a commutative ring that is:
1. Closed under addition
2. Closed under additive inverse
3. Closed under multiplication by arbitrary ring elements

In commutative algebra, ideals are the central objects for quotient constructions,
factorization, and algebraic geometry.

**Hierarchy context:**
- Ideals are defined over `CommutativeRing`
- Special kinds include principal, prime, and maximal ideals
-/

structure Ideal (α : Type) (R : CommutativeRing α) where
  carrier : α → Prop
  zero_mem : carrier R.zero
  add_mem : ∀ {a b : α}, carrier a → carrier b → carrier (R.add a b)
  neg_mem : ∀ {a : α}, carrier a → carrier (R.neg a)
  smul_mem : ∀ (r : α) {a : α}, carrier a → carrier (R.mul r a)

def Ideal.Subset {α : Type} {R : CommutativeRing α} (I J : Ideal α R) : Prop :=
  ∀ ⦃a : α⦄, I.carrier a → J.carrier a

infix:50 " ⊆ᵢ " => Ideal.Subset

-- Top ideal: all elements belong

def topIdeal (α : Type) (R : CommutativeRing α) : Ideal α R :=
{ carrier := fun _ => True,
  zero_mem := trivial,
  add_mem := by intro _ _ _ _; trivial,
  neg_mem := by intro _ _; trivial,
  smul_mem := by intro _ _ _; trivial }

-- Helper lemma: additive inverse of zero is zero

def neg_zero_eq_zero (α : Type) (R : CommutativeRing α) : R.neg R.zero = R.zero := by
  have h1 : R.add R.zero (R.neg R.zero) = R.zero := R.add_neg R.zero
  have h2 : R.add R.zero (R.neg R.zero) = R.neg R.zero := R.zero_add (R.neg R.zero)
  exact Eq.trans (Eq.symm h2) h1

-- Zero ideal: only zero belongs

def zeroIdeal (α : Type) (R : CommutativeRing α) : Ideal α R :=
{ carrier := fun a => a = R.zero,
  zero_mem := rfl,
  add_mem := by
    intro a b ha hb
    simpa [ha, hb] using (R.zero_add R.zero),
  neg_mem := by
    intro a ha
    simpa [ha] using neg_zero_eq_zero α R,
  smul_mem := by
    intro r a ha
    simpa [ha] using (R.mul_zero r) }

-- Concrete example in Z: even integers form an ideal

def evenIntIdeal : Ideal Int intCommutativeRing :=
{ carrier := fun a => ∃ k : Int, a = 2 * k,
  zero_mem := by
    refine ⟨0, ?_⟩
    simp [intCommutativeRing, intRing, intSemiring]
  add_mem := by
    intro a b ha hb
    rcases ha with ⟨ka, hka⟩
    rcases hb with ⟨kb, hkb⟩
    refine ⟨ka + kb, ?_⟩
    simp [intCommutativeRing, intRing, intSemiring] at hka hkb ⊢
    omega,
  neg_mem := by
    intro a ha
    rcases ha with ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    calc
      intCommutativeRing.neg a = (2 * k).neg := by
        simp [hk, intCommutativeRing, intRing, intSemiring]
      _ = -(2 * k) := by
        rfl
      _ = 2 * (-k) := by omega,
  smul_mem := by
    intro r a ha
    rcases ha with ⟨k, hk⟩
    refine ⟨r * k, ?_⟩
    calc
      intCommutativeRing.mul r a = r * (2 * k) := by
        simp [hk, intCommutativeRing, intRing, intSemiring]
      _ = 2 * (r * k) := by
        simp [Int.mul_assoc, Int.mul_comm] }

-- Membership examples

example : evenIntIdeal.carrier 14 := by
  refine ⟨7, ?_⟩
  decide

example : ¬ evenIntIdeal.carrier 9 := by
  intro h
  rcases h with ⟨k, hk⟩
  omega

/- # Special Ideals -/

structure PrincipalIdeal (α : Type) (R : CommutativeRing α) extends Ideal α R where
  generator : α
  mem_iff : ∀ a : α, carrier a ↔ ∃ r : α, a = R.mul r generator

structure PrimeIdeal (α : Type) (R : CommutativeRing α) extends Ideal α R where
  proper : ¬ carrier R.one
  prime_mul : ∀ {a b : α}, carrier (R.mul a b) → carrier a ∨ carrier b

structure MaximalIdeal (α : Type) (R : CommutativeRing α) extends Ideal α R where
  proper : ¬ carrier R.one
  maximal : ∀ (J : Ideal α R), carrier R.one → (toIdeal ⊆ᵢ J) → J ⊆ᵢ toIdeal

-- In Z, the even ideal is principal: (2)
def principalEvenIntIdeal : PrincipalIdeal Int intCommutativeRing :=
{ toIdeal := evenIntIdeal,
  generator := 2,
  mem_iff := by
    intro a
    constructor
    · intro h
      rcases h with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      simpa [intCommutativeRing, intRing, intSemiring, Int.mul_comm] using hk
    · intro h
      rcases h with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      simpa [intCommutativeRing, intRing, intSemiring, Int.mul_comm] using hr }
