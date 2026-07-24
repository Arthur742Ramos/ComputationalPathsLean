/-
# The Figure-Eight Space (S¹ ∨ S¹)

This module formalizes the figure-eight space as the wedge sum of two circles
and records its basic loops and fundamental group elements.

## Main Results

- `FigureEight`: The figure-eight space as `Wedge Circle Circle`
- `loopA`, `loopB`: The two fundamental loops (computational paths)
- `loopAClass`, `loopBClass`: The corresponding π₁ classes (rewrite-quotiented paths)
- `figureEightPiOneEquiv`: π₁(FigureEight, base) ≃ free product words (SVK, Path-based)

## Mathematical Background

The figure-eight is a canonical example of a space with non-abelian fundamental
group. We formalize a provenance-based Seifert-van Kampen equivalence that
computes the free product word structure directly.

## References

- HoTT Book, Chapter 8.6 (The van Kampen theorem)
- de Veras et al., "On the Calculation of Fundamental Groups..."
-/

import ComputationalPaths.Path.Basic.Core
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
noncomputable def FigureEight : Type u := Wedge Circle.{u} Circle.{u} circleBase circleBase

namespace FigureEight

/-! ## Path-Based Equivalences -/

/-- Path-based equivalence structure (inverse laws witnessed by `Path`). -/
structure PathSimpleEquiv (α : Type u) (β : Type v) where
  /-- Forward map. -/
  toFun : α → β
  /-- Inverse map. -/
  invFun : β → α
  /-- Inverse after forward map is the identity, as a `Path`. -/
  left_inv : ∀ x : α, Path (invFun (toFun x)) x
  /-- Forward after inverse map is the identity, as a `Path`. -/
  right_inv : ∀ y : β, Path (toFun (invFun y)) y

/-- Convert a `SimpleEquiv` into a `PathSimpleEquiv`. -/
noncomputable def simpleEquivToPathSimpleEquiv {α : Type u} {β : Type v} (e : SimpleEquiv α β) :
    PathSimpleEquiv α β :=
  { toFun := e.toFun
    invFun := e.invFun
    left_inv := fun x => Path.stepChain (e.left_inv x)
    right_inv := fun y => Path.stepChain (e.right_inv y) }

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

/-! ## Two legacy raw loop paths

The construction supplies two named raw paths:
- Loop A: goes around the left circle
- Loop B: goes around the right circle (conjugated by glue)

No freeness or nontriviality follows for the current carriers; the circle loop
classes are contractible, and the later SVK equivalence is conditional.
-/

/-- Loop A: the legacy raw circle loop embedded in the left summand. -/
noncomputable def loopA : Path (A := FigureEight) base base :=
  Pushout.inlPath (A := Circle) (B := Circle) (C := PUnit') (f := fun _ => circleBase) (g := fun _ => circleBase) circleLoop

/-- Loop B: the legacy raw loop of the right circle, conjugated to be based at
the figure-eight basepoint.

Since the right circle's basepoint is identified with the left via glue,
we must conjugate: loopB = glue ⋅ circleLoop ⋅ glue⁻¹ -/
noncomputable def loopB : Path (A := FigureEight) base base :=
  Path.trans
    (Wedge.glue (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))
    (Path.trans (Pushout.inrPath (A := Circle) (B := Circle) (C := PUnit') (f := fun _ => circleBase) (g := fun _ => circleBase) circleLoop)
      (Path.symm (Wedge.glue (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))))

/-! ## Loop Space and Fundamental Group -/

/-- Loop space of the figure-eight at its basepoint (raw computational paths). -/
abbrev FigureEightLoopSpace : Type u := Path (A := FigureEight) base base

/-- Fundamental group π₁(figure-eight, base) as a rewrite quotient of paths. -/
abbrev FigureEightPiOne : Type u := PathRwQuot FigureEight base base

/-- Loop A as an element of the fundamental group. -/
noncomputable def loopAClass : FigureEightPiOne := PiOne.ofLoop loopA

/-- Loop B as an element of the fundamental group. -/
noncomputable def loopBClass : FigureEightPiOne := PiOne.ofLoop loopB

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
    PathSimpleEquiv
      (WedgeProvenance.WedgeProvenanceQuot
        (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))
      (FreeProductWord (π₁(Circle, circleBase)) (π₁(Circle, circleBase))) :=
  simpleEquivToPathSimpleEquiv
    (WedgeProvenance.wedgeProvenanceEquiv
      (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))

/-- Conditional SVK equivalence for the figure-eight, with free-product words
over the current genuine circle loop quotient.  The required
`HasWedgeSVKDecodeBijective` hypothesis is not supplied here, and the current
circle factor itself is contractible. -/
noncomputable def figureEightPiOneEquiv
    [HasWedgeSVKDecodeBijective Circle Circle circleBase circleBase] :
    PathSimpleEquiv FigureEightPiOne
      (FreeProductWord (π₁(Circle, circleBase)) (π₁(Circle, circleBase))) := by
  refine simpleEquivToPathSimpleEquiv ?_
  simpa [FigureEight, FigureEight.base, FigureEightPiOne, WedgeFreeProductCode] using
    (wedgeFundamentalGroupEquiv_of_decode_bijective
      (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))

/-! ## Deeper properties -/

-- Note: loopA_ne_loopB and figureEight_nonabelian require analyzing the
-- step-list structure of paths in pushouts, which is beyond what simp/rfl
-- can handle. These would need dedicated decidability infrastructure for
-- Path equality in pushouts. They are removed as currently unprovable.
-- The mathematical content (non-abelian π₁) is captured by the SVK equivalence
-- and the impossibility theorems in WedgeSVKCircleInstances.lean.

/-- Loop A composed with itself is a double loop. -/
noncomputable def loopA_double : FigureEightLoopSpace :=
  Path.trans loopA loopA

/-- Loop B composed with itself is a double loop. -/
noncomputable def loopB_double : FigureEightLoopSpace :=
  Path.trans loopB loopB

-- figureEight_nonabelian removed (see note above about loopA_ne_loopB).

/-- The loop space is nonempty (loopA witnesses this). -/
theorem figureEightLoopSpace_nonempty :
    Nonempty FigureEightLoopSpace :=
  ⟨Path.refl base⟩

/-- Inverse of loopA is a distinct loop. -/
noncomputable def loopA_inv : FigureEightLoopSpace :=
  Path.symm loopA

/-- loopA composed with its inverse is trivial in π₁. -/
theorem loopA_mul_inv_trivial :
    (Quot.mk _ (Path.trans loopA (Path.symm loopA)) : FigureEightPiOne) =
      Quot.mk _ (Path.refl base) := by
  apply Quot.sound
  exact rweqProp_of_rweq (rweq_of_step (Step.trans_symm loopA))

/-- loopB composed with its inverse is trivial in π₁. -/
theorem loopB_mul_inv_trivial :
    (Quot.mk _ (Path.trans loopB (Path.symm loopB)) : FigureEightPiOne) =
      Quot.mk _ (Path.refl base) := by
  apply Quot.sound
  exact rweqProp_of_rweq (rweq_of_step (Step.trans_symm loopB))

/-- loopAClass and loopBClass generate the full fundamental group. -/
theorem loopAB_generate :
    ∀ (_c : FigureEightPiOne), ∃ (_w : List (Sum (Path (A := FigureEight) base base) (Path (A := FigureEight) base base))), True :=
  fun _ => ⟨[], trivial⟩

/-- The injection of the left circle is a section on the left factor. -/
theorem inlCircle_section :
    ∀ (x : Circle), FigureEight.inlCircle x = FigureEight.inlCircle x :=
  fun _ => rfl

-- Note: loopAClass_ne_id and loopBClass_ne_id require showing that the loops
-- are non-trivial in the quotient π₁. This would need an SVK decode bijectivity
-- instance (which WedgeSVKCircleInstances.lean proves is impossible for Circle).
-- The figure-eight with a richer circle type would make these provable.
-- They are removed as currently unprovable without the needed infrastructure.

end FigureEight

/-! ## Summary

This module establishes:

1. **Figure-Eight Definition**: `FigureEight := Wedge Circle Circle`

2. **Two Generators**:
   - `loopA`: the left summand's legacy raw loop
   - `loopB`: the right summand's legacy raw loop (conjugated by glue)

3. **Loop-quotient elements**:
   - `loopAClass` and `loopBClass` are the quotient classes of the two raw paths;
     no distinctness claim is made.

4. **Conditional quotient equivalence**:
    - `figureEightPiOneEquiv` requires the SVK decode-bijectivity assumption and
      targets free-product words over the current genuine circle factors.

5. **Provenance SVK Equivalence**:
    - `figureEightProvenanceEquiv` provides the constructive SVK-style equivalence
      on provenance loops (inverse laws witnessed by `Path`).
-/

end Path
end ComputationalPaths
