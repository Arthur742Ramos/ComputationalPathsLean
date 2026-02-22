/-
# Seifert-van Kampen Theorem (computational paths)

This module re-exports the Seifert-van Kampen equivalence for pushouts in the
computational path setting.

## Key Results
- `seifertVanKampenEquiv`: PiOne(Pushout) is equivalent to the amalgamated free product.

## References
- Favonia & Shulman, "The Seifert-van Kampen Theorem in HoTT"
- HoTT Book, Chapter 8.7
-/

import ComputationalPaths.Path.CompPath.PushoutPaths

namespace ComputationalPaths
namespace Path

open CompPath

universe u

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B}

/-- Seifert-van Kampen equivalence for pushouts (Path-based PiOne). -/
noncomputable abbrev seifertVanKampenEquiv (c0 : C)
    [Pushout.HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c0]
    [HasPushoutSVKEncodeQuot A B C f g c0]
    [HasPushoutSVKDecodeEncode A B C f g c0]
    [HasPushoutSVKEncodeDecode A B C f g c0] :
    SimpleEquiv
      (PiOne (Pushout A B C f g) (Pushout.inl (f c0)))
      (AmalgamatedFreeProduct
        (PiOne A (f c0))
        (PiOne B (g c0))
        (PiOne C c0)
        (piOneFmap (A := A) (C := C) (f := f) (c₀ := c0))
        (piOneGmap (B := B) (C := C) (g := g) (c₀ := c0))) :=
  CompPath.seifertVanKampenEquiv
    (A := A) (B := B) (C := C) (f := f) (g := g) c0

end Path

private noncomputable def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

end ComputationalPaths
