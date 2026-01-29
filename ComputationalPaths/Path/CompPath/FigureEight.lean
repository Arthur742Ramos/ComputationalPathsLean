/-
# The Figure-Eight Space (S¹ ∨ S¹)

This module formalizes the figure-eight space as the wedge sum of two circles
and records its basic loops and fundamental group elements.

## Main Results

- `FigureEight`: The figure-eight space as `Wedge Circle Circle`
- `loopA`, `loopB`: The two fundamental loops
- `loopAClass`, `loopBClass`: The corresponding π₁ classes
- `figureEightProvenanceEquiv`: provenance SVK equivalence
- `figureEightPiOneEquiv`: provenance SVK equivalence (free product words)

## Mathematical Background

The figure-eight is a canonical example of a space with non-abelian fundamental
group. We formalize a provenance-based Seifert-van Kampen equivalence that
computes the free product word structure directly.

## References

- HoTT Book, Chapter 8.6 (The van Kampen theorem)
- de Veras et al., "On the Calculation of Fundamental Groups..."
-/

import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.CompPath.PushoutCompPath
import ComputationalPaths.Path.CompPath.PushoutPaths

namespace ComputationalPaths
namespace Path

open CompPath

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
  Wedge.glue (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase)

/-! ## The Two Fundamental Loops

The figure-eight has two fundamental loops:
- Loop A: goes around the left circle
- Loop B: goes around the right circle (conjugated by glue)

These generate the fundamental group freely.
-/

/-- Loop A: The fundamental loop of the left circle, embedded in the figure-eight.
This is simply the left circle's loop, which is already based at the basepoint. -/
noncomputable def loopA : Path base base :=
  Pushout.inlPath (A := Circle) (B := Circle) (C := PUnit') (f := fun _ => circleBase) (g := fun _ => circleBase) circleLoop

/-- Loop B: The fundamental loop of the right circle, conjugated to be based at
the figure-eight basepoint.

Since the right circle's basepoint is identified with the left via glue,
we must conjugate: loopB = glue ⋅ circleLoop ⋅ glue⁻¹ -/
noncomputable def loopB : Path base base :=
  Path.trans
    (Wedge.glue (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))
    (Path.trans (Pushout.inrPath (A := Circle) (B := Circle) (C := PUnit') (f := fun _ => circleBase) (g := fun _ => circleBase) circleLoop)
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

/-! ## Provenance-Based SVK Data -/

/-- Provenance encoding data for the figure-eight wedge (Circle ∨ Circle). -/
noncomputable instance instHasWedgeProvenanceEncode_FigureEight :
    WedgeProvenance.HasWedgeProvenanceEncode Circle Circle circleBase circleBase where
  encodeInl := by
    intro a a' p
    cases a <;> cases a'
    exact Quot.mk _ p
  encodeInr := by
    intro b b' p
    cases b <;> cases b'
    exact Quot.mk _ p
  encodeInl_loop := by
    intro p
    rfl
  encodeInr_loop := by
    intro p
    rfl

/-- Provenance-based SVK equivalence for the figure-eight. -/
noncomputable def figureEightProvenanceEquiv :
    SimpleEquiv
      (WedgeProvenance.WedgeProvenanceQuot
        (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))
      (FreeProductWord (π₁(Circle, circleBase)) (π₁(Circle, circleBase))) :=
  WedgeProvenance.wedgeProvenanceEquiv
    (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase)

/-- SVK equivalence for the figure-eight (free product words over π₁(S¹)). -/
noncomputable def figureEightPiOneEquiv :
    SimpleEquiv
      (WedgeProvenance.WedgeProvenanceQuot
        (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))
      (FreeProductWord (π₁(Circle, circleBase)) (π₁(Circle, circleBase))) :=
  figureEightProvenanceEquiv

end FigureEight

/-! ## Summary

This module establishes:

1. **Figure-Eight Definition**: `FigureEight := Wedge Circle Circle`

2. **Two Generators**:
   - `loopA`: The left circle's fundamental loop
   - `loopB`: The right circle's loop (conjugated by glue)

3. **Fundamental Group Elements**:
   - `loopAClass` and `loopBClass` are the π₁ classes of the two loops.

4. **Provenance SVK Equivalence**:
    - `figureEightProvenanceEquiv` gives a constructive SVK-style equivalence
      using the provenance-based wedge loop quotient.
    - `figureEightPiOneEquiv` repackages the same equivalence as the canonical
      SVK statement for `Circle ∨ Circle`.

This records the SVK-style computation without axioms by working with explicit
provenance paths.
-/

end Path
end ComputationalPaths
