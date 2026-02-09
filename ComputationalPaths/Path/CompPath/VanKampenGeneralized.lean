/-
# Generalized Seifert-Van Kampen Theorem

This module records a generalized Seifert-van Kampen equivalence for pushouts:
the fundamental group of a pushout is the amalgamated free product of the
fundamental groups of the legs, with the wedge-sum case as a corollary.

## Key Results

- `vanKampenGeneralizedEquiv`: SVK equivalence for pushouts
- `vanKampenGeneralizedEquiv_of_decodeAmalg_bijective`: encode-free variant
- `vanKampenWedgeEquiv_of_decode_bijective`: wedge-sum specialization

## References

- Favonia & Shulman, "The Seifert-van Kampen Theorem in HoTT"
- HoTT Book, Chapter 8.7
-/

import ComputationalPaths.Path.CompPath.PushoutPaths

namespace ComputationalPaths
namespace Path
namespace CompPath

open Pushout
open Wedge

universe u

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B}

/-! ## Generalized van Kampen (Pushout) -/

/-- Generalized SVK equivalence for pushouts. -/
noncomputable def vanKampenGeneralizedEquiv (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKEncodeQuot A B C f g c₀]
    [HasPushoutSVKDecodeEncode A B C f g c₀]
    [HasPushoutSVKEncodeDecode A B C f g c₀] :
    SimpleEquiv
      (π₁(Pushout A B C f g, Pushout.inl (f c₀)))
      (AmalgamatedFreeProduct
        (π₁(A, f c₀))
        (π₁(B, g c₀))
        (π₁(C, c₀))
        (piOneFmap c₀)
        (piOneGmap c₀)) :=
  seifertVanKampenEquiv (A := A) (B := B) (C := C) (f := f) (g := g) (c₀ := c₀)

/-- Generalized SVK equivalence using only Prop-level bijectivity of decode. -/
noncomputable def vanKampenGeneralizedEquiv_of_decodeAmalg_bijective (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKDecodeAmalgBijective A B C f g c₀] :
    SimpleEquiv
      (π₁(Pushout A B C f g, Pushout.inl (f c₀)))
      (AmalgamatedFreeProduct
        (π₁(A, f c₀))
        (π₁(B, g c₀))
        (π₁(C, c₀))
        (piOneFmap c₀)
        (piOneGmap c₀)) :=
  seifertVanKampenEquiv_of_decodeAmalg_bijective
    (A := A) (B := B) (C := C) (f := f) (g := g) (c₀ := c₀)

/-! ## Wedge-Sum Corollary -/

section WedgeSum

variable {A : Type u} {B : Type u}

/-- Wedge-sum specialization: pi_1 of a wedge is a free product of pi_1s. -/
noncomputable def vanKampenWedgeEquiv_of_decode_bijective (a₀ : A) (b₀ : B)
    [HasWedgeSVKDecodeBijective A B a₀ b₀] :
    SimpleEquiv
      (π₁(Wedge A B a₀ b₀, Wedge.basepoint))
      (WedgeFreeProductCode (A := A) (B := B) a₀ b₀) :=
  wedgeFundamentalGroupEquiv_of_decode_bijective (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)

end WedgeSum

/-! ## Summary -/

/-!
We package the generalized Seifert-van Kampen equivalence for pushouts and
record the wedge-sum corollary via the WedgeSVK interface.
-/

end CompPath
end Path
end ComputationalPaths
