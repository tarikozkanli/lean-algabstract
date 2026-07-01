-- PolynomialRing.lean
-- Polynomial ring definitions and basic results via Mathlib

import Mathlib

namespace Algabstract

/-- Univariate polynomial ring over `R`. -/
abbrev PolynomialRing (R : Type*) [Semiring R] := Polynomial R

section Basic

variable {R : Type*} [Semiring R]

/-- Coefficient at 0 of `X` is `0`. -/
theorem coeff_X_zero : (Polynomial.X : PolynomialRing R).coeff 0 = 0 := by
  simpa [PolynomialRing] using (Polynomial.coeff_X_zero : (Polynomial.X : Polynomial R).coeff 0 = 0)

/-- Coefficient at 1 of `X` is `1`. -/
theorem coeff_X_one : (Polynomial.X : PolynomialRing R).coeff 1 = 1 := by
  simpa [PolynomialRing] using (Polynomial.coeff_X_one : (Polynomial.X : Polynomial R).coeff 1 = 1)

end Basic

section Noetherian

variable (R : Type*) [CommRing R] [IsNoetherianRing R]

/-- Hilbert basis theorem specialized to the polynomial-ring alias. -/
theorem polynomialRing_noetherian : IsNoetherianRing (PolynomialRing R) := by
  infer_instance

end Noetherian

end Algabstract
