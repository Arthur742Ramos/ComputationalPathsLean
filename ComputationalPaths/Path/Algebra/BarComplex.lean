/-
# Bar Complexes and Resolutions for Computational Paths

This module introduces a lightweight bar complex/resolution interface
where the chain conditions are witnessed by computational `Path`s.

## Key Definitions

- `BarComplex`: chain complex data with `Path`-valued d ∘ d = 0 laws
- `BarResolution`: augmented bar complex resolving a pointed set
- `BarComplex.trivial`, `BarResolution.trivial`: basic examples

## References

- Weibel, "An Introduction to Homological Algebra", Chapter 6
- Mac Lane, "Homology", Chapter VIII
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Algebra

open HomologicalAlgebra

universe u

/-! ## Bar complex data -/

/-- A bar complex: a chain complex indexed by `Nat` with `Path`-valued d ∘ d = 0. -/
structure BarComplex where
  /-- The object in degree n. -/
  obj : Nat → PointedSet.{u}
  /-- The differential dₙ : C_{n+1} → Cₙ. -/
  d : (n : Nat) → PointedHom (obj (n + 1)) (obj n)
  /-- The chain condition, expressed as a computational `Path`. -/
  d_comp_zero :
    ∀ n,
      Path (PointedHom.comp (d n) (d (n + 1)))
        (zeroHom (obj (n + 2)) (obj n))

/-! ## Bar resolutions -/

/-- An augmented bar complex resolving a pointed set. -/
structure BarResolution (X : PointedSet.{u}) extends BarComplex.{u} where
  /-- The augmentation map ε : C₀ → X. -/
  augmentation : PointedHom (obj 0) X
  /-- The augmentation kills boundaries, witnessed by a `Path`. -/
  augmentation_zero :
    Path (PointedHom.comp augmentation (d 0))
      (zeroHom (obj 1) X)

namespace BarComplex

/-- The trivial bar complex with constant object and zero differentials. -/
def trivial (X : PointedSet.{u}) : BarComplex.{u} where
  obj := fun _ => X
  d := fun _ => zeroHom X X
  d_comp_zero := by
    intro n
    let z : PointedHom X X := zeroHom X X
    have hz : Path z z := Path.symm (Path.stepChain rfl)
    have hcomp : Path (PointedHom.comp z z) (PointedHom.comp z z) :=
      Path.congrArg (fun f => PointedHom.comp f z) hz
    have hzero : Path (PointedHom.comp z z) z := by
      apply Path.stepChain
      apply PointedHom.ext
      rfl
    simpa [z] using Path.trans hcomp hzero

end BarComplex

namespace BarResolution

/-- The trivial bar resolution with zero differentials and identity augmentation. -/
def trivial (X : PointedSet.{u}) : BarResolution X where
  obj := fun _ => X
  d := fun _ => zeroHom X X
  d_comp_zero := by
    intro n
    let z : PointedHom X X := zeroHom X X
    have hz : Path z z := Path.symm (Path.stepChain rfl)
    have hcomp : Path (PointedHom.comp z z) (PointedHom.comp z z) :=
      Path.congrArg (fun f => PointedHom.comp f z) hz
    have hzero : Path (PointedHom.comp z z) z := by
      apply Path.stepChain
      apply PointedHom.ext
      rfl
    simpa [z] using Path.trans hcomp hzero
  augmentation := PointedHom.id X
  augmentation_zero := by
    have hid : Path (PointedHom.id X) (PointedHom.id X) :=
      Path.symm (Path.stepChain rfl)
    have hcomp :
        Path (PointedHom.comp (PointedHom.id X) (zeroHom X X))
          (PointedHom.comp (PointedHom.id X) (zeroHom X X)) :=
      Path.congrArg (fun f => PointedHom.comp f (zeroHom X X)) hid
    have hzero :
        Path (PointedHom.comp (PointedHom.id X) (zeroHom X X))
          (zeroHom X X) := by
      apply Path.stepChain
      simpa using (PointedHom.id_comp (zeroHom X X))
    exact Path.trans hcomp hzero

end BarResolution

/-! ## Summary -/

/-!
We defined a `BarComplex` and `BarResolution` interface in terms of
`Path`-valued differential laws and provided trivial examples.
-/

end Algebra
end Path
end ComputationalPaths
