import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Geometric Satake paths: spherical Hecke category

This module provides computational-path data for spherical Hecke categories
using explicit coweight/multiplicity objects and convolution coherence paths.
-/

namespace ComputationalPaths
namespace GeometricSatake
namespace SphericalHeckePaths

open Path

/-- Domain-specific rewrite tags for spherical Hecke coherence moves. -/
inductive SphericalHeckeStep : Type
  | leftUnit
  | rightUnit
  | associator
  | fusionNormalize

/-- A concrete object model for the spherical Hecke category. -/
structure HeckeObject where
  dominantCoweight : Nat
  multiplicity : Nat
deriving Repr, DecidableEq

/-- Monoidal unit for convolution. -/
def unitObj : HeckeObject :=
  { dominantCoweight := 0, multiplicity := 1 }

/-- Convolution on spherical Hecke objects (dominant coweight addition). -/
def convolution (X Y : HeckeObject) : HeckeObject :=
  { dominantCoweight := X.dominantCoweight + Y.dominantCoweight
    multiplicity := X.multiplicity * Y.multiplicity }

/-- Simple computational invariant for the object support size. -/
def supportRadius (X : HeckeObject) : Nat :=
  X.dominantCoweight + X.multiplicity

/-- Left unit path for spherical convolution. -/
def leftUnitPath (X : HeckeObject) : Path (convolution unitObj X) X := by
  refine Path.stepChain ?_
  cases X
  simp [unitObj, convolution]

/-- Right unit path for spherical convolution. -/
def rightUnitPath (X : HeckeObject) : Path (convolution X unitObj) X := by
  refine Path.stepChain ?_
  cases X
  simp [unitObj, convolution]

/-- Associativity path for spherical convolution. -/
def assocPath (X Y Z : HeckeObject) :
    Path (convolution (convolution X Y) Z) (convolution X (convolution Y Z)) := by
  refine Path.stepChain ?_
  cases X
  cases Y
  cases Z
  simp [convolution, Nat.add_assoc, Nat.mul_assoc]

/-- Fusion normalization path:
`((X ⋆ 1) ⋆ Y) ⟶ (X ⋆ Y)` using associativity and left-unit coherence. -/
def fusionNormalizePath (X Y : HeckeObject) :
    Path (convolution (convolution X unitObj) Y) (convolution X Y) :=
  Path.trans (assocPath X unitObj Y)
    (Path.congrArg (fun T => convolution X T) (leftUnitPath Y))

/-- `supportRadius` unfolds computationally after convolution. -/
def supportRadiusConvolutionPath (X Y : HeckeObject) :
    Path (supportRadius (convolution X Y))
      ((X.dominantCoweight + Y.dominantCoweight) + (X.multiplicity * Y.multiplicity)) :=
  Path.stepChain rfl

/-- Domain-specific rewrite relation for spherical Hecke coherence. -/
inductive SphericalHeckeRewrite : HeckeObject → HeckeObject → Type
  | leftUnit (X : HeckeObject) :
      SphericalHeckeRewrite (convolution unitObj X) X
  | rightUnit (X : HeckeObject) :
      SphericalHeckeRewrite (convolution X unitObj) X
  | associator (X Y Z : HeckeObject) :
      SphericalHeckeRewrite (convolution (convolution X Y) Z) (convolution X (convolution Y Z))
  | fusionNormalize (X Y : HeckeObject) :
      SphericalHeckeRewrite (convolution (convolution X unitObj) Y) (convolution X Y)

namespace SphericalHeckeRewrite

/-- Interpret a domain-specific spherical rewrite as a computational path. -/
def toPath {X Y : HeckeObject} : SphericalHeckeRewrite X Y → Path X Y
  | .leftUnit X => leftUnitPath X
  | .rightUnit X => rightUnitPath X
  | .associator X Y Z => assocPath X Y Z
  | .fusionNormalize X Y => fusionNormalizePath X Y

/-- Primitive right-unit normalization step for any spherical rewrite path. -/
def normalizeStep {X Y : HeckeObject} (r : SphericalHeckeRewrite X Y) :
    Path.Step (Path.trans r.toPath (Path.refl Y)) r.toPath :=
  Path.Step.trans_refl_right r.toPath

noncomputable def normalize_rweq {X Y : HeckeObject} (r : SphericalHeckeRewrite X Y) :
    RwEq (Path.trans r.toPath (Path.refl Y)) r.toPath :=
  rweq_of_step (normalizeStep r)

noncomputable def cancel_rweq {X Y : HeckeObject} (r : SphericalHeckeRewrite X Y) :
    RwEq (Path.trans (Path.symm r.toPath) r.toPath) (Path.refl Y) :=
  rweq_cmpA_inv_left r.toPath

end SphericalHeckeRewrite

/-- Spherical Hecke monoidal package with explicit computational paths. -/
structure SphericalHeckeCategoryPathData where
  unitObj : HeckeObject
  convolution : HeckeObject → HeckeObject → HeckeObject
  associatorPath :
    ∀ X Y Z : HeckeObject,
      Path (convolution (convolution X Y) Z) (convolution X (convolution Y Z))
  leftUnitPath :
    ∀ X : HeckeObject, Path (convolution unitObj X) X
  rightUnitPath :
    ∀ X : HeckeObject, Path (convolution X unitObj) X
  fusionNormalizePath :
    ∀ X Y : HeckeObject, Path (convolution (convolution X unitObj) Y) (convolution X Y)

/-- Canonical spherical Hecke category on coweight/multiplicity objects. -/
def natSphericalHeckeCategory : SphericalHeckeCategoryPathData where
  unitObj := unitObj
  convolution := convolution
  associatorPath := assocPath
  leftUnitPath := leftUnitPath
  rightUnitPath := rightUnitPath
  fusionNormalizePath := fusionNormalizePath

noncomputable def fusionNormalize_rweq (X Y : HeckeObject) :
    RwEq
      (Path.trans (natSphericalHeckeCategory.fusionNormalizePath X Y) (Path.refl (convolution X Y)))
      (natSphericalHeckeCategory.fusionNormalizePath X Y) :=
  rweq_cmpA_refl_right (natSphericalHeckeCategory.fusionNormalizePath X Y)

end SphericalHeckePaths
end GeometricSatake
end ComputationalPaths
