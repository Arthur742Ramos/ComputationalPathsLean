import ComputationalPaths.Path.Rewrite.RwEq
import GeometricSatake.SphericalHeckePaths

/-!
# Geometric Satake paths: weight functors

Computational-path coherence for weight functors on spherical Hecke objects.
This tracks tensor compatibility and triple-convolution reassociation with
explicit `Path` and `RwEq` witnesses.
-/

namespace ComputationalPaths
namespace GeometricSatake
namespace WeightFunctorPaths

open Path
open SphericalHeckePaths

/-- Domain-specific rewrite tags for weight-functor coherence. -/
inductive WeightFunctorStep : Type
  | tensor
  | unit
  | reassociate

/-- Weight-functor data on the spherical Hecke category. -/
structure WeightFunctorPathData where
  weight : HeckeObject → Nat
  tensorPath :
    ∀ X Y : HeckeObject,
      Path (weight (convolution X Y)) (weight X + weight Y)
  unitPath :
    Path (weight unitObj) 0

/-- Domain-specific rewrite relation induced by a weight functor. -/
inductive WeightFunctorRewrite (W : WeightFunctorPathData) : Nat → Nat → Type
  | tensor (X Y : HeckeObject) :
      WeightFunctorRewrite W (W.weight (convolution X Y)) (W.weight X + W.weight Y)
  | unit :
      WeightFunctorRewrite W (W.weight unitObj) 0
  | reassociate (X Y Z : HeckeObject) :
      WeightFunctorRewrite W
        ((W.weight X + W.weight Y) + W.weight Z)
        (W.weight X + (W.weight Y + W.weight Z))

namespace WeightFunctorRewrite

/-- Interpret a weight-functor rewrite as a computational path. -/
def toPath {W : WeightFunctorPathData} {a b : Nat}
    (r : WeightFunctorRewrite W a b) : Path a b := by
  cases r with
  | tensor X Y =>
      exact W.tensorPath X Y
  | unit =>
      exact W.unitPath
  | reassociate X Y Z =>
      exact Path.ofEqChain (Nat.add_assoc (W.weight X) (W.weight Y) (W.weight Z))

/-- Primitive right-unit normalization step for any weight rewrite path. -/
def normalizeStep {W : WeightFunctorPathData} {a b : Nat}
    (r : WeightFunctorRewrite W a b) :
    Path.Step (Path.trans r.toPath (Path.refl b)) r.toPath :=
  Path.Step.trans_refl_right r.toPath

@[simp] theorem normalize_rweq {W : WeightFunctorPathData} {a b : Nat}
    (r : WeightFunctorRewrite W a b) :
    RwEq (Path.trans r.toPath (Path.refl b)) r.toPath :=
  rweq_of_step (normalizeStep r)

@[simp] theorem cancel_rweq {W : WeightFunctorPathData} {a b : Nat}
    (r : WeightFunctorRewrite W a b) :
    RwEq (Path.trans (Path.symm r.toPath) r.toPath) (Path.refl b) :=
  rweq_cmpA_inv_left r.toPath

end WeightFunctorRewrite

namespace WeightFunctorPathData

variable (W : WeightFunctorPathData)

/-- Weight path for `((X ⋆ Y) ⋆ Z)` via two tensor-compatibility witnesses. -/
def tripleTensorLeft (X Y Z : HeckeObject) :
    Path (W.weight (convolution (convolution X Y) Z))
      ((W.weight X + W.weight Y) + W.weight Z) :=
  Path.trans (W.tensorPath (convolution X Y) Z)
    (Path.congrArg (fun n => n + W.weight Z) (W.tensorPath X Y))

/-- Weight path for `(X ⋆ (Y ⋆ Z))` via two tensor-compatibility witnesses. -/
def tripleTensorRight (X Y Z : HeckeObject) :
    Path (W.weight (convolution X (convolution Y Z)))
      (W.weight X + (W.weight Y + W.weight Z)) :=
  Path.trans (W.tensorPath X (convolution Y Z))
    (Path.congrArg (fun n => W.weight X + n) (W.tensorPath Y Z))

/-- Arithmetic reassociation path on weight sums. -/
def reassociatePath (X Y Z : HeckeObject) :
    Path ((W.weight X + W.weight Y) + W.weight Z)
      (W.weight X + (W.weight Y + W.weight Z)) :=
  WeightFunctorRewrite.toPath (WeightFunctorRewrite.reassociate (W := W) X Y Z)

/-- Weight comparison path from left-associated triple convolution to right-associated sums. -/
def leftToRightViaSatake (X Y Z : HeckeObject) :
    Path (W.weight (convolution (convolution X Y) Z))
      (W.weight X + (W.weight Y + W.weight Z)) :=
  Path.trans (tripleTensorLeft W X Y Z) (reassociatePath W X Y Z)

/-- Compare the two triple-convolution weight evaluations. -/
def rightComparison (X Y Z : HeckeObject) :
    Path (W.weight (convolution (convolution X Y) Z))
      (W.weight (convolution X (convolution Y Z))) :=
  Path.trans (leftToRightViaSatake W X Y Z) (Path.symm (tripleTensorRight W X Y Z))

@[simp] theorem tensor_rweq (X Y : HeckeObject) :
    RwEq
      (Path.trans (W.tensorPath X Y) (Path.refl (W.weight X + W.weight Y)))
      (W.tensorPath X Y) :=
  rweq_cmpA_refl_right (W.tensorPath X Y)

@[simp] theorem rightComparison_assoc_rweq (X Y Z : HeckeObject) :
    RwEq
      (Path.trans
        (Path.trans (tripleTensorLeft W X Y Z) (reassociatePath W X Y Z))
        (Path.symm (tripleTensorRight W X Y Z)))
      (Path.trans
        (tripleTensorLeft W X Y Z)
        (Path.trans (reassociatePath W X Y Z) (Path.symm (tripleTensorRight W X Y Z)))) :=
  rweq_tt (tripleTensorLeft W X Y Z) (reassociatePath W X Y Z) (Path.symm (tripleTensorRight W X Y Z))

@[simp] theorem rightComparison_cancel_rweq (X Y Z : HeckeObject) :
    RwEq
      (Path.trans (Path.symm (rightComparison W X Y Z)) (rightComparison W X Y Z))
      (Path.refl (W.weight (convolution X (convolution Y Z)))) :=
  rweq_cmpA_inv_left (rightComparison W X Y Z)

end WeightFunctorPathData

/-- Tensor compatibility path for the dominant-coweight weight functor. -/
def dominantTensorPath (X Y : HeckeObject) :
    Path ((convolution X Y).dominantCoweight)
      (X.dominantCoweight + Y.dominantCoweight) := by
  refine Path.ofEqChain ?_
  cases X
  cases Y
  simp [convolution]

/-- Unit path for the dominant-coweight weight functor. -/
def dominantUnitPath : Path unitObj.dominantCoweight 0 := by
  refine Path.ofEqChain ?_
  simp [unitObj]

/-- Canonical dominant-coweight weight functor for geometric Satake paths. -/
def dominantWeightFunctor : WeightFunctorPathData where
  weight := fun X => X.dominantCoweight
  tensorPath := fun X Y => by
    simpa using dominantTensorPath X Y
  unitPath := dominantUnitPath

@[simp] theorem dominant_tensor_rweq (X Y : HeckeObject) :
    RwEq
      (Path.trans
        (dominantWeightFunctor.tensorPath X Y)
        (Path.refl (dominantWeightFunctor.weight X + dominantWeightFunctor.weight Y)))
      (dominantWeightFunctor.tensorPath X Y) :=
  WeightFunctorPathData.tensor_rweq (W := dominantWeightFunctor) X Y

/-- Image under the dominant-weight functor of the spherical fusion normalization path. -/
def dominantOnFusionNormalizePath (X Y : HeckeObject) :
    Path
      (dominantWeightFunctor.weight (convolution (convolution X unitObj) Y))
      (dominantWeightFunctor.weight (convolution X Y)) :=
  Path.congrArg dominantWeightFunctor.weight (fusionNormalizePath X Y)

@[simp] theorem dominantOnFusionNormalize_cancel_rweq (X Y : HeckeObject) :
    RwEq
      (Path.trans
        (Path.symm (dominantOnFusionNormalizePath X Y))
        (dominantOnFusionNormalizePath X Y))
      (Path.refl (dominantWeightFunctor.weight (convolution X Y))) :=
  rweq_cmpA_inv_left (dominantOnFusionNormalizePath X Y)

@[simp] theorem dominant_rightComparison_cancel_rweq (X Y Z : HeckeObject) :
    RwEq
      (Path.trans
        (Path.symm (WeightFunctorPathData.rightComparison dominantWeightFunctor X Y Z))
        (WeightFunctorPathData.rightComparison dominantWeightFunctor X Y Z))
      (Path.refl
        (dominantWeightFunctor.weight (convolution X (convolution Y Z)))) :=
  WeightFunctorPathData.rightComparison_cancel_rweq (W := dominantWeightFunctor) X Y Z

end WeightFunctorPaths
end GeometricSatake
end ComputationalPaths
