/-
# π₁(Figure-Eight) ≃ F₂

This module packages the wedge-sum SVK equivalence for the figure-eight and
records its fundamental group as the free product π₁(S¹) * π₁(S¹).

## Key Results

- `FigureEightFreeGroup`: free group on two generators as π₁(S¹) * π₁(S¹)
- `figureEightPiOneEquivFreeGroup`: π₁(FigureEight) ≃ FigureEightFreeGroup

## Mathematical Background

The figure-eight is the wedge of two circles, so its fundamental group is the
free product of two copies of π₁(S¹).

## References

- HoTT Book, Chapter 8.6
- de Veras et al., "On the Calculation of Fundamental Groups..."
-/

import ComputationalPaths.Path.CompPath.FigureEight
import ComputationalPaths.Path.CompPath.PushoutPaths
import ComputationalPaths.Path.Rewrite.SimpleEquiv

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path

open CompPath

/-! ## Free group on two generators -/

/-- The free group on two generators, modeled as π₁(S¹) * π₁(S¹). -/
abbrev FigureEightFreeGroup : Type :=
  WedgeFreeProductCode (A := Circle) (B := Circle) circleBase circleBase

namespace FigureEight

/-! ## π₁ equivalence -/

/-- π₁(FigureEight) is the free group on two generators. -/
noncomputable def figureEightPiOneEquivFreeGroup
    [HasWedgeSVKDecodeBijective Circle Circle circleBase circleBase] :
    SimpleEquiv FigureEightPiOne FigureEightFreeGroup :=
  by
    simpa [FigureEightFreeGroup, FigureEight, FigureEight.base, FigureEightPiOne,
      WedgeFreeProductCode, circleBase, Wedge.basepoint, Wedge.wedgeBasepoint] using
      (wedgeFundamentalGroupEquiv_of_decode_bijective
        (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))

end FigureEight

/-! ## Summary

This module packages the figure-eight fundamental group computation:

1. `figureEightPiOneEquivFreeGroup`: π₁(S¹ ∨ S¹) ≃ π₁(S¹) * π₁(S¹)
-/

end Path
end ComputationalPaths
