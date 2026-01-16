/-
# The Figure-Eight Space (S¹ ∨ S¹)

This module formalizes the figure-eight space as the wedge sum of two circles
and records its basic loops and fundamental group elements.

## Main Results

- `FigureEight`: The figure-eight space as `Wedge Circle Circle`
- `loopA`, `loopB`: The two fundamental loops
- `loopAClass`, `loopBClass`: The corresponding π₁ classes

## Mathematical Background

The figure-eight is a canonical example of a space with non-abelian fundamental
group. The expected free product description follows from Seifert-van Kampen,
but that equivalence is not formalized here.

## References

- HoTT Book, Chapter 8.6 (The van Kampen theorem)
- de Veras et al., "On the Calculation of Fundamental Groups..."
-/

import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.HIT.Pushout
import ComputationalPaths.Path.HIT.PushoutPaths

namespace ComputationalPaths
namespace Path

universe u v w

/-! ## The Figure-Eight Space -/

/-- The figure-eight space: wedge sum of two circles sharing a common basepoint.
Topologically, this is two circles joined at a single point, forming an "8" shape. -/
def FigureEight : Type u := Wedge Circle.{u} Circle.{u} circleBase circleBase

namespace FigureEight

/-! ## Basic Structure -/

/-- The basepoint of the figure-eight (the junction where the two circles meet). -/
noncomputable def base : FigureEight := Wedge.basepoint

/-- Injection of the left circle into the figure-eight. -/
noncomputable def inlCircle (x : Circle) : FigureEight := Wedge.inl x

/-- Injection of the right circle into the figure-eight. -/
noncomputable def inrCircle (x : Circle) : FigureEight := Wedge.inr x

/-- The glue path identifying the two basepoints. -/
noncomputable def glue : Path (inlCircle circleBase) (inrCircle circleBase) :=
  Wedge.glue

/-! ## The Two Fundamental Loops

The figure-eight has two fundamental loops:
- Loop A: goes around the left circle
- Loop B: goes around the right circle (conjugated by glue)

These generate the fundamental group freely.
-/

/-- Loop A: The fundamental loop of the left circle, embedded in the figure-eight.
This is simply the left circle's loop, which is already based at the basepoint. -/
noncomputable def loopA : Path base base :=
  Pushout.inlPath circleLoop

/-- Loop B: The fundamental loop of the right circle, conjugated to be based at
the figure-eight basepoint.

Since the right circle's basepoint is identified with the left via glue,
we must conjugate: loopB = glue ⋅ circleLoop ⋅ glue⁻¹ -/
noncomputable def loopB : Path base base :=
  Path.trans
    (Wedge.glue (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))
    (Path.trans (Pushout.inrPath circleLoop)
      (Path.symm (Wedge.glue (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))))

/-! ## Loop Space and Fundamental Group -/

/-- Loop space of the figure-eight at its basepoint. -/
abbrev FigureEightLoopSpace : Type u := LoopSpace FigureEight base

/-- Fundamental group π₁(figure-eight, base). -/
abbrev FigureEightPiOne : Type u := π₁(FigureEight, base)

/-- Loop A as an element of the fundamental group. -/
noncomputable def loopAClass : FigureEightPiOne := Quot.mk _ loopA

/-- Loop B as an element of the fundamental group. -/
noncomputable def loopBClass : FigureEightPiOne := Quot.mk _ loopB

end FigureEight

/-! ## Summary

This module establishes:

1. **Figure-Eight Definition**: `FigureEight := Wedge Circle Circle`

2. **Two Generators**:
   - `loopA`: The left circle's fundamental loop
   - `loopB`: The right circle's loop (conjugated by glue)

3. **Fundamental Group Elements**:
   - `loopAClass` and `loopBClass` are the π₁ classes of the two loops.

The expected free product computation uses Seifert-van Kampen, but is not
formalized here.
-/

end Path
end ComputationalPaths
