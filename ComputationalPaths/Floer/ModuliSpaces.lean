import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Floer.GradedPaths
import ComputationalPaths.Floer.FukayaCategoryPaths
import ComputationalPaths.Floer.PseudoHolomorphicCurves

/-!
# Floer theory paths: moduli spaces

This module encodes a minimal moduli-space interface linking Fukaya-category
morphisms to graded Floer generators with explicit computational paths.
Boundary/gluing identities are represented by `Path`, normalized by `Path.Step`,
and compared by `RwEq`.
-/

namespace ComputationalPaths
namespace Floer
namespace ModuliSpaces

open Path
open GradedPaths
open FukayaCategoryPaths
open PseudoHolomorphicCurves

universe u

/-- Domain-specific rewrite tags for moduli-space coherence moves. -/
inductive ModuliStep : Type
  | stripBoundary
  | pseudoStripBoundary
  | gluing
  | identityDegeneracy
  | dimensionDrop
  | boundaryAfterGluing

/-- Path-level interface for moduli-space data in Floer/Fukaya constructions. -/
structure ModuliSpacePathData (Obj Mor Gen : Type u) where
  fukaya : FukayaCategoryPathData Obj Mor
  graded : GradedFloerPathData Gen
  pseudo : PseudoHolomorphicPathData Gen
  chordOf : Mor → Gen
  stripBoundaryPath :
    ∀ f : Mor,
      Path (chordOf (fukaya.mu1 f)) (graded.complex.differential (chordOf f))
  pseudoCurvePath :
    ∀ f : Mor,
      Path (pseudo.strip (chordOf f)) (chordOf f)
  gluingPath :
    ∀ f g : Mor,
      Path (chordOf (fukaya.mu2 f g)) (graded.complex.continuation (chordOf g))
  identityDegeneracyPath :
    ∀ X : Obj,
      Path (chordOf (fukaya.idMor X)) graded.complex.zero
  dimensionDropPath :
    ∀ f : Mor,
      Path
        (graded.grading (chordOf (fukaya.mu1 f)))
        (Nat.pred (graded.grading (chordOf f)))

namespace ModuliSpacePathData

variable {Obj Mor Gen : Type u} (M : ModuliSpacePathData Obj Mor Gen)

/-- Boundary transport induced by gluing, under differential application. -/
noncomputable def boundaryAfterGluingPath (f g : Mor) :
    Path
      (M.graded.complex.differential (M.chordOf (M.fukaya.mu2 f g)))
      (M.graded.complex.differential (M.graded.complex.continuation (M.chordOf g))) :=
  Path.congrArg M.graded.complex.differential (M.gluingPath f g)

/-- Pseudo-holomorphic strip transport into the strip-boundary equation. -/
noncomputable def stripToBoundaryPath (f : Mor) :
    Path
      (M.pseudo.strip (M.chordOf (M.fukaya.mu1 f)))
      (M.graded.complex.differential (M.chordOf f)) :=
  Path.trans
    (M.pseudoCurvePath (M.fukaya.mu1 f))
    (M.stripBoundaryPath f)

/-- Step witness: right-unit normalization for strip-boundary paths. -/
noncomputable def stripBoundary_step (f : Mor) :
    Path.Step
      (Path.trans
        (M.stripBoundaryPath f)
        (Path.refl (M.graded.complex.differential (M.chordOf f))))
      (M.stripBoundaryPath f) :=
  Path.Step.trans_refl_right (M.stripBoundaryPath f)

noncomputable def stripBoundary_rweq (f : Mor) :
    RwEq
      (Path.trans
        (M.stripBoundaryPath f)
        (Path.refl (M.graded.complex.differential (M.chordOf f))))
      (M.stripBoundaryPath f) :=
  rweq_of_step (M.stripBoundary_step f)

/-- Step witness: right-unit normalization for pseudo strip-boundary transport. -/
noncomputable def stripToBoundary_step (f : Mor) :
    Path.Step
      (Path.trans
        (M.stripToBoundaryPath f)
        (Path.refl (M.graded.complex.differential (M.chordOf f))))
      (M.stripToBoundaryPath f) :=
  Path.Step.trans_refl_right (M.stripToBoundaryPath f)

noncomputable def stripToBoundary_rweq (f : Mor) :
    RwEq
      (Path.trans
        (M.stripToBoundaryPath f)
        (Path.refl (M.graded.complex.differential (M.chordOf f))))
      (M.stripToBoundaryPath f) :=
  rweq_of_step (M.stripToBoundary_step f)

/-- Step witness: right-unit normalization for gluing paths. -/
noncomputable def gluing_step (f g : Mor) :
    Path.Step
      (Path.trans
        (M.gluingPath f g)
        (Path.refl (M.graded.complex.continuation (M.chordOf g))))
      (M.gluingPath f g) :=
  Path.Step.trans_refl_right (M.gluingPath f g)

noncomputable def gluing_rweq (f g : Mor) :
    RwEq
      (Path.trans
        (M.gluingPath f g)
        (Path.refl (M.graded.complex.continuation (M.chordOf g))))
      (M.gluingPath f g) :=
  rweq_of_step (M.gluing_step f g)

/-- Step witness: right-unit normalization for identity-degeneracy paths. -/
noncomputable def identityDegeneracy_step (X : Obj) :
    Path.Step
      (Path.trans (M.identityDegeneracyPath X) (Path.refl M.graded.complex.zero))
      (M.identityDegeneracyPath X) :=
  Path.Step.trans_refl_right (M.identityDegeneracyPath X)

noncomputable def identityDegeneracy_rweq (X : Obj) :
    RwEq
      (Path.trans (M.identityDegeneracyPath X) (Path.refl M.graded.complex.zero))
      (M.identityDegeneracyPath X) :=
  rweq_of_step (M.identityDegeneracy_step X)

/-- Step witness: left-unit normalization for expected dimension drop. -/
noncomputable def dimensionDrop_step (f : Mor) :
    Path.Step
      (Path.trans
        (Path.refl (M.graded.grading (M.chordOf (M.fukaya.mu1 f))))
        (M.dimensionDropPath f))
      (M.dimensionDropPath f) :=
  Path.Step.trans_refl_left (M.dimensionDropPath f)

noncomputable def dimensionDrop_rweq (f : Mor) :
    RwEq
      (Path.trans
        (Path.refl (M.graded.grading (M.chordOf (M.fukaya.mu1 f))))
        (M.dimensionDropPath f))
      (M.dimensionDropPath f) :=
  rweq_of_step (M.dimensionDrop_step f)

/-- Step witness: right-unit normalization for boundary-after-gluing paths. -/
noncomputable def boundaryAfterGluing_step (f g : Mor) :
    Path.Step
      (Path.trans
        (M.boundaryAfterGluingPath f g)
        (Path.refl
          (M.graded.complex.differential (M.graded.complex.continuation (M.chordOf g)))))
      (M.boundaryAfterGluingPath f g) :=
  Path.Step.trans_refl_right (M.boundaryAfterGluingPath f g)

noncomputable def boundaryAfterGluing_rweq (f g : Mor) :
    RwEq
      (Path.trans
        (M.boundaryAfterGluingPath f g)
        (Path.refl
          (M.graded.complex.differential (M.graded.complex.continuation (M.chordOf g)))))
      (M.boundaryAfterGluingPath f g) :=
  rweq_of_step (M.boundaryAfterGluing_step f g)

noncomputable def identityDegeneracy_cancel_rweq (X : Obj) :
    RwEq
      (Path.trans (Path.symm (M.identityDegeneracyPath X)) (M.identityDegeneracyPath X))
      (Path.refl M.graded.complex.zero) :=
  rweq_cmpA_inv_left (M.identityDegeneracyPath X)

noncomputable def pseudoCurve_cancel_rweq (f : Mor) :
    RwEq
      (Path.trans (Path.symm (M.pseudoCurvePath f)) (M.pseudoCurvePath f))
      (Path.refl (M.chordOf f)) :=
  rweq_cmpA_inv_left (M.pseudoCurvePath f)

end ModuliSpacePathData

/-- Trivial model instantiating the moduli-space computational-path interface. -/
noncomputable def trivialModuliSpacePathData : ModuliSpacePathData PUnit PUnit PUnit where
  fukaya := FukayaCategoryPaths.trivialFukayaCategoryPathData
  graded := GradedPaths.trivialGradedFloerPathData
  pseudo := PseudoHolomorphicCurves.trivialPseudoHolomorphicPathData
  chordOf := fun _ => PUnit.unit
  stripBoundaryPath := fun _ => Path.refl PUnit.unit
  pseudoCurvePath := fun _ => Path.refl PUnit.unit
  gluingPath := fun _ _ => Path.refl PUnit.unit
  identityDegeneracyPath := fun _ => Path.refl PUnit.unit
  dimensionDropPath := fun _ => Path.refl 0

end ModuliSpaces
end Floer
end ComputationalPaths
