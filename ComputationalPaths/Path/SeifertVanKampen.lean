/-
# Seifert-van Kampen Theorem

This module re-exports the Seifert-van Kampen equivalence for pushouts from the
computational paths development.

## Key Results
- `seifertVanKampenEquiv`: pi_1(Pushout) is equivalent to the amalgamated free product.

## References
- Favonia & Shulman, "The Seifert-van Kampen Theorem in HoTT"
- HoTT Book, Chapter 8.7
-/

import ComputationalPaths.Path.CompPath.PushoutPaths

namespace ComputationalPaths
namespace Path

universe u

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B}

/-- Seifert-van Kampen equivalence for pushouts. -/
noncomputable abbrev seifertVanKampenEquiv (c0 : C)
    [CompPath.Pushout.HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c0]
    [CompPath.HasPushoutSVKEncodeQuot A B C f g c0]
    [CompPath.HasPushoutSVKDecodeEncode A B C f g c0]
    [CompPath.HasPushoutSVKEncodeDecode A B C f g c0] :=
  CompPath.seifertVanKampenEquiv
    (A := A) (B := B) (C := C) (f := f) (g := g) c0

end Path
end ComputationalPaths
