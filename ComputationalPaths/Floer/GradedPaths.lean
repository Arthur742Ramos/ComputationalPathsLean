import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Floer.FloerComplex

/-!
# Floer theory paths: graded paths

This module enriches Floer complexes with grading data and explicit
computational paths for degree behavior. Degree transport and shift
compatibility are represented with `Path`, normalized by `Path.Step`,
and compared by `RwEq`.
-/

namespace ComputationalPaths
namespace Floer
namespace GradedPaths

open Path
open FloerComplex

universe u

/-- Domain-specific rewrite tags for grading coherence moves. -/
inductive GradedStep : Type
  | differentialDegree
  | continuationDegree
  | shiftDegree
  | shiftCommutes
  | continuationShift

/-- Graded refinement of a Floer complex with explicit computational paths. -/
structure GradedFloerPathData (Gen : Type u) where
  complex : FloerComplexPathData Gen
  grading : Gen → Nat
  shift : Gen → Gen
  differentialDegreePath :
    ∀ x : Gen, Path (grading (complex.differential x)) (Nat.pred (grading x))
  continuationDegreePath :
    ∀ x : Gen, Path (grading (complex.continuation x)) (grading x)
  shiftDegreePath :
    ∀ x : Gen, Path (grading (shift x)) (grading x)
  shiftCommutesPath :
    ∀ x : Gen, Path (shift (complex.differential x)) (complex.differential (shift x))

namespace GradedFloerPathData

variable {Gen : Type u} (G : GradedFloerPathData Gen)

/-- Grading path for shifting continuation images. -/
def continuationShiftPath (x : Gen) :
    Path
      (G.grading (G.shift (G.complex.continuation x)))
      (G.grading (G.complex.continuation x)) :=
  G.shiftDegreePath (G.complex.continuation x)

/-- Step witness: right-unit normalization for differential degree behavior. -/
def differentialDegree_step (x : Gen) :
    Path.Step
      (Path.trans (G.differentialDegreePath x) (Path.refl (Nat.pred (G.grading x))))
      (G.differentialDegreePath x) :=
  Path.Step.trans_refl_right (G.differentialDegreePath x)

@[simp] theorem differentialDegree_rweq (x : Gen) :
    RwEq
      (Path.trans (G.differentialDegreePath x) (Path.refl (Nat.pred (G.grading x))))
      (G.differentialDegreePath x) :=
  rweq_of_step (G.differentialDegree_step x)

/-- Step witness: right-unit normalization for continuation degree behavior. -/
def continuationDegree_step (x : Gen) :
    Path.Step
      (Path.trans (G.continuationDegreePath x) (Path.refl (G.grading x)))
      (G.continuationDegreePath x) :=
  Path.Step.trans_refl_right (G.continuationDegreePath x)

@[simp] theorem continuationDegree_rweq (x : Gen) :
    RwEq
      (Path.trans (G.continuationDegreePath x) (Path.refl (G.grading x)))
      (G.continuationDegreePath x) :=
  rweq_of_step (G.continuationDegree_step x)

/-- Step witness: left-unit normalization for shift degree behavior. -/
def shiftDegree_step (x : Gen) :
    Path.Step
      (Path.trans (Path.refl (G.grading (G.shift x))) (G.shiftDegreePath x))
      (G.shiftDegreePath x) :=
  Path.Step.trans_refl_left (G.shiftDegreePath x)

@[simp] theorem shiftDegree_rweq (x : Gen) :
    RwEq
      (Path.trans (Path.refl (G.grading (G.shift x))) (G.shiftDegreePath x))
      (G.shiftDegreePath x) :=
  rweq_of_step (G.shiftDegree_step x)

/-- Step witness: right-unit normalization for shift/differential compatibility. -/
def shiftCommutes_step (x : Gen) :
    Path.Step
      (Path.trans (G.shiftCommutesPath x) (Path.refl (G.complex.differential (G.shift x))))
      (G.shiftCommutesPath x) :=
  Path.Step.trans_refl_right (G.shiftCommutesPath x)

@[simp] theorem shiftCommutes_rweq (x : Gen) :
    RwEq
      (Path.trans (G.shiftCommutesPath x) (Path.refl (G.complex.differential (G.shift x))))
      (G.shiftCommutesPath x) :=
  rweq_of_step (G.shiftCommutes_step x)

/-- Step witness: right-unit normalization for shifted continuation grading. -/
def continuationShift_step (x : Gen) :
    Path.Step
      (Path.trans (G.continuationShiftPath x) (Path.refl (G.grading (G.complex.continuation x))))
      (G.continuationShiftPath x) :=
  Path.Step.trans_refl_right (G.continuationShiftPath x)

@[simp] theorem continuationShift_rweq (x : Gen) :
    RwEq
      (Path.trans (G.continuationShiftPath x) (Path.refl (G.grading (G.complex.continuation x))))
      (G.continuationShiftPath x) :=
  rweq_of_step (G.continuationShift_step x)

@[simp] theorem shiftCommutes_cancel_rweq (x : Gen) :
    RwEq
      (Path.trans (Path.symm (G.shiftCommutesPath x)) (G.shiftCommutesPath x))
      (Path.refl (G.complex.differential (G.shift x))) :=
  rweq_cmpA_inv_left (G.shiftCommutesPath x)

end GradedFloerPathData

/-- Trivial model instantiating the graded Floer computational-path interface. -/
def trivialGradedFloerPathData : GradedFloerPathData PUnit where
  complex := FloerComplex.trivialFloerComplexPathData
  grading := fun _ => 0
  shift := fun _ => PUnit.unit
  differentialDegreePath := fun _ => Path.refl 0
  continuationDegreePath := fun _ => Path.refl 0
  shiftDegreePath := fun _ => Path.refl 0
  shiftCommutesPath := fun _ => Path.refl PUnit.unit

end GradedPaths
end Floer
end ComputationalPaths
