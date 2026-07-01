-- HilbertBasisTheorem.lean
-- Bridge to Mathlib's Hilbert Basis Theorem

import Algabstract.NoetherianRing
import Algabstract.PolynomialRing

/- # Hilbert Basis Theorem

Classical statement:
If `R` is a Noetherian ring, then the polynomial ring `R[X]` is also Noetherian.

Mathlib already formalizes this theorem. This module provides a local bridge so
this project can reference it with a clear, dedicated entry point.
-/

namespace Algabstract

open scoped Polynomial

variable (R : Type*) [CommRing R]

/-- Hilbert Basis Theorem (Mathlib bridge): a Noetherian commutative ring has a
Noetherian polynomial ring in one variable. -/
theorem hilbert_basis_theorem [IsNoetherianRing R] :
    IsNoetherianRing (PolynomialRing R) := by
  simpa using (polynomialRing_noetherian (R := R))

end Algabstract
