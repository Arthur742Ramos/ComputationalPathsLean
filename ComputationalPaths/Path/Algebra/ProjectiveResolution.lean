/-
# Projective Resolutions for Computational Paths

This module introduces a lightweight notion of projective objects and
projective resolutions in the pointed-set setting, with exactness and lifting
conditions witnessed by computational `Path`s rather than propositional
equalities.

## Key Definitions

- `PointedHomPath`: pointwise path homotopies between pointed maps.
- `PathSurjective`: surjectivity with path witnesses.
- `Projective`: the path-based lifting property.
- `PathExact`: exactness phrased with `Path` witnesses.
- `ProjectiveResolution`: a two-step projective resolution.
- `trivialResolution`: a minimal resolution for a projective object.

## References

- Weibel, "An Introduction to Homological Algebra"
- May, "A Concise Course in Algebraic Topology"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Algebra

open HomologicalAlgebra

universe u

/-! ## Path-level lifting data -/

/-- Pointwise path homotopy between pointed maps. -/
def PointedHomPath {A B : PointedSet.{u}} (f g : PointedHom A B) : Type u :=
  ∀ x : A.carrier, Path (f.toFun x) (g.toFun x)

/-- Surjectivity with path witnesses. -/
def PathSurjective {A B : PointedSet.{u}} (f : PointedHom A B) : Type u :=
  ∀ b : B.carrier, Σ a : A.carrier, Path (f.toFun a) b

/-- Projective pointed sets lift along path-surjective maps. -/
structure Projective (P : PointedSet.{u}) : Type (u + 1) where
  /-- Lifting property for pointed maps. -/
  lift :
    ∀ {A B : PointedSet.{u}} (f : PointedHom A B) (g : PointedHom P B),
      PathSurjective f → Σ h : PointedHom P A, PointedHomPath (PointedHom.comp f h) g

/-! ## Path exactness -/

/-- Path-based exactness at the middle term. -/
structure PathExact {A B C : PointedSet.{u}}
    (f : PointedHom A B) (g : PointedHom B C) : Type u where
  /-- Composition lands in the base point (as a `Path`). -/
  im_sub_ker : ∀ x : A.carrier, Path (g.toFun (f.toFun x)) C.zero
  /-- Kernel elements are hit by the previous map (as a `Path`). -/
  ker_lift : ∀ y : B.carrier, Path (g.toFun y) C.zero → Σ x : A.carrier, Path (f.toFun x) y

/-! ## The unit pointed set -/

/-- The one-point pointed set. -/
def unitPointedSet : PointedSet.{u} where
  carrier := PUnit
  zero := PUnit.unit

/-- The one-point pointed set is projective. -/
def projectiveUnit : Projective (unitPointedSet.{u}) := by
  refine ⟨?lift⟩
  intro A B f g _hsurj
  refine ⟨zeroHom unitPointedSet A, ?_⟩
  intro x
  cases x
  exact Path.stepChain (by
    have hleft :
        (PointedHom.comp f (zeroHom unitPointedSet A)).toFun PUnit.unit = B.zero := by
      simp [PointedHom.comp, zeroHom, f.map_zero]
    have hright : g.toFun PUnit.unit = B.zero := by
      simpa using g.map_zero
    exact hleft.trans hright.symm)

/-! ## Projective resolutions -/

/-- A two-step projective resolution of a pointed set. -/
structure ProjectiveResolution (A : PointedSet.{u}) : Type (u + 1) where
  /-- Degree-2 projective object. -/
  P₂ : PointedSet.{u}
  /-- Degree-1 projective object. -/
  P₁ : PointedSet.{u}
  /-- Degree-0 projective object. -/
  P₀ : PointedSet.{u}
  /-- Differential P₂ → P₁. -/
  d₂ : PointedHom P₂ P₁
  /-- Differential P₁ → P₀. -/
  d₁ : PointedHom P₁ P₀
  /-- Augmentation to the target. -/
  ε : PointedHom P₀ A
  /-- Exactness at P₁. -/
  exact₂ : PathExact d₂ d₁
  /-- Exactness at P₀. -/
  exact₁ : PathExact d₁ ε
  /-- P₂ is projective. -/
  proj₂ : Projective P₂
  /-- P₁ is projective. -/
  proj₁ : Projective P₁
  /-- P₀ is projective. -/
  proj₀ : Projective P₀

/-- The trivial resolution of a projective pointed set. -/
def trivialResolution (A : PointedSet.{u}) (hA : Projective A) :
    ProjectiveResolution A := by
  refine
    { P₂ := unitPointedSet
      P₁ := unitPointedSet
      P₀ := A
      d₂ := zeroHom unitPointedSet unitPointedSet
      d₁ := zeroHom unitPointedSet A
      ε := PointedHom.id A
      exact₂ := ?_
      exact₁ := ?_
      proj₂ := projectiveUnit
      proj₁ := projectiveUnit
      proj₀ := hA }
  · refine ⟨?_, ?_⟩
    · intro x
      cases x
      exact Path.refl A.zero
    · intro y _hy
      cases y
      refine ⟨PUnit.unit, ?_⟩
      exact Path.refl PUnit.unit
  · refine ⟨?_, ?_⟩
    · intro x
      cases x
      exact Path.refl A.zero
    · intro y hy
      refine ⟨PUnit.unit, ?_⟩
      exact Path.symm hy

end Algebra
end Path
end ComputationalPaths
