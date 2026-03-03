-- Mathematical definition:
-- A magma is a set 𝑀 equipped with a binary operation ∗ : 𝑀 × 𝑀 → 𝑀.
--
-- Explanation:
-- A magma is the simplest algebraic structure. It consists of a set with a single binary operation
-- that combines any two elements from the set to produce another element in the set (closure).
-- No additional properties (like associativity or commutativity) are required.
--
-- Key point: Magma is very permissive - the operation can be arbitrary.
--
-- Examples:
-- - Natural numbers under subtraction (not associative: (5-3)-1 ≠ 5-(3-1))
-- - Natural numbers under addition (happens to be associative, but magma doesn't require it)
-- - Division on positive real numbers (closed but not associative)
--
-- In the algebraic hierarchy, magma is the foundation:
-- Magma → Semigroup (add associativity) → Monoid (add identity) → Group (add inverses)

structure Magma (α : Type) where
  /-- Binary operation: combines two elements to produce another element in the set -/
  mul : α → α → α

-- Uniform Unicode notation for single-operation hierarchy
infixl:70 " ∗ " => Magma.mul

-- Example: magma of natural numbers under addition
def natAddMagma : Magma Nat :=
{ mul := Nat.add }
