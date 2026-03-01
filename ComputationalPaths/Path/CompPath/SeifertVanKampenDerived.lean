/-
# Derived Results from Seifert–van Kampen

This module records standard corollaries of the SVK theorem: wedge sums,
connected sums (pushouts along the circle), and surface-group specializations.

## Key Results
- `wedgePiOneEquivFreeProduct`: π₁(A ∨ B) ≃ π₁(A) * π₁(B).
- `connectedSumPiOneEquiv`: π₁(A # B) ≃ π₁(A) *_{π₁(S¹)} π₁(B).
- `surfaceGenus2PiOneEquiv`: genus-2 surface group via a torus connected sum.

## References
- HoTT Book, Chapter 8
- Favonia & Shulman, "The Seifert-van Kampen Theorem in HoTT"
-/

import ComputationalPaths.Path.CompPath.VanKampenGeneralized
import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.CompPath.Torus

namespace ComputationalPaths
namespace Path

open CompPath

universe u

/-! ## Wedge-sum corollary -/

/-- π₁ of a wedge sum is the free product (SVK wedge specialization). -/
noncomputable def wedgePiOneEquivFreeProduct {A : Type u} {B : Type u}
    (a₀ : A) (b₀ : B) [HasWedgeSVKDecodeBijective A B a₀ b₀] :
    SimpleEquiv
      (π₁(Wedge A B a₀ b₀, Wedge.basepoint))
      (WedgeFreeProductCode (A := A) (B := B) a₀ b₀) :=
  vanKampenWedgeEquiv_of_decode_bijective
    (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)

/-! ## Connected sums (pushouts along S¹) -/

/-- Connected sum as a pushout along the computational circle. -/
abbrev ConnectedSum (A : Type u) (B : Type u) (f : Circle → A) (g : Circle → B) : Type u :=
  Pushout A B Circle f g

/-- Basepoint for a connected sum, chosen from the left injection. -/
@[simp] noncomputable abbrev connectedSumBasepoint {A : Type u} {B : Type u}
    (f : Circle → A) (g : Circle → B) : ConnectedSum A B f g :=
  Pushout.inl (f circleBase)

/-- SVK equivalence for connected sums (pushouts along the circle). -/
noncomputable def connectedSumPiOneEquiv {A : Type u} {B : Type u}
    (f : Circle → A) (g : Circle → B)
    [Pushout.HasGlueNaturalLoopRwEq (A := A) (B := B) (C := Circle) (f := f) (g := g) circleBase]
    [HasPushoutSVKEncodeQuot A B Circle f g circleBase]
    [HasPushoutSVKDecodeEncode A B Circle f g circleBase]
    [HasPushoutSVKEncodeDecode A B Circle f g circleBase] :
    SimpleEquiv
      (π₁(ConnectedSum A B f g, Pushout.inl (f circleBase)))
      (AmalgamatedFreeProduct
        (π₁(A, f circleBase))
        (π₁(B, g circleBase))
        (π₁(Circle, circleBase))
        (piOneFmap (A := A) (C := Circle) (f := f) (c₀ := circleBase))
        (piOneGmap (B := B) (C := Circle) (g := g) (c₀ := circleBase))) :=
  seifertVanKampenEquiv
    (A := A) (B := B) (C := Circle) (f := f) (g := g) (c₀ := circleBase)

/-! ## Surface-group applications -/

/-- Genus-2 surface as the connected sum of two tori (pushout along a circle). -/
abbrev SurfaceGenus2 (f g : Circle → Torus) : Type u :=
  ConnectedSum Torus Torus f g

/-- The genus-2 surface group as an amalgamated free product of torus groups. -/
abbrev SurfaceGenus2Group (f g : Circle → Torus) : Type u :=
  AmalgamatedFreeProduct
    (π₁(Torus, f circleBase))
    (π₁(Torus, g circleBase))
    (π₁(Circle, circleBase))
    (piOneFmap (A := Torus) (C := Circle) (f := f) (c₀ := circleBase))
    (piOneGmap (B := Torus) (C := Circle) (g := g) (c₀ := circleBase))

/-- π₁ of a torus connected sum (genus-2 surface) via SVK. -/
noncomputable def surfaceGenus2PiOneEquiv (f g : Circle → Torus)
    [Pushout.HasGlueNaturalLoopRwEq (A := Torus) (B := Torus) (C := Circle) (f := f) (g := g) circleBase]
    [HasPushoutSVKEncodeQuot Torus Torus Circle f g circleBase]
    [HasPushoutSVKDecodeEncode Torus Torus Circle f g circleBase]
    [HasPushoutSVKEncodeDecode Torus Torus Circle f g circleBase] :
    SimpleEquiv
      (π₁(SurfaceGenus2 f g, Pushout.inl (f circleBase)))
      (SurfaceGenus2Group f g) := by
  simpa [SurfaceGenus2, SurfaceGenus2Group] using
    (connectedSumPiOneEquiv (A := Torus) (B := Torus) (f := f) (g := g))

/-! ## Summary

We package SVK corollaries for wedge sums, connected sums along the circle,
and a torus connected-sum specialization that models genus-2 surface groups.
-/

end Path
end ComputationalPaths
