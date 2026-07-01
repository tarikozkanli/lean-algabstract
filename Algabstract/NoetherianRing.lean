-- NoetherianRing.lean
-- Noetherian ring definitions and basic results via Mathlib

import Mathlib

namespace Algabstract

/-- A commutative ring is Noetherian if it satisfies Mathlib's `IsNoetherianRing`. -/
abbrev NoetherianRing (R : Type*) [CommRing R] : Prop := IsNoetherianRing R

variable (R : Type*) [CommRing R]

/-- Convenience lemma: the alias unfolds to Mathlib's notion. -/
theorem noetherianRing_iff : NoetherianRing R ↔ IsNoetherianRing R := Iff.rfl

/-- Integers are a Noetherian ring. -/
example : NoetherianRing Int := by
  infer_instance

/-- Every field is a Noetherian ring. -/
example (K : Type*) [Field K] : NoetherianRing K := by
  infer_instance

end Algabstract
