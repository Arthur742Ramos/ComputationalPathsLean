/-
# Injective Resolutions for Computational Paths

This module defines Path-valued injective objects and injective resolutions
for pointed sets. The laws and exactness conditions are witnessed by
computational paths rather than propositional equalities.

## Key Definitions

- `PathExact`: exactness with Path witnesses.
- `InjectiveObject`: Path-based lifting property for pointed sets.
- `InjectiveResolution`: two-step injective resolution with Path exactness.
- `InjectiveObject.trivial`, `InjectiveResolution.trivial`: trivial instances.

## References

- Weibel, "An Introduction to Homological Algebra"
- Mac Lane, "Homology"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Algebra

open HomologicalAlgebra

universe u

/-! ## Path-valued exactness -/

/-- Path-valued exactness for pointed homs. -/
structure PathExact {A B C : PointedSet.{u}}
    (f : PointedHom A B) (g : PointedHom B C) : Type u where
  /-- g ∘ f is zero (as a `Path`). -/
  im_sub_ker : ∀ x, Path (g.toFun (f.toFun x)) C.zero
  /-- Kernel elements lift to the image (as a `Path`). -/
  ker_sub_im : ∀ y, Path (g.toFun y) C.zero → Σ x, Path (f.toFun x) y

/-! ## Injective objects -/

/-- The one-point pointed set. -/
def unitPointed : PointedSet.{u} where
  carrier := PUnit
  zero := PUnit.unit

/-- Injective pointed set with Path-valued lifting property. -/
structure InjectiveObject (I : PointedSet.{u}) : Type (u + 1) where
  /-- Extend along injective maps with Path-commutativity. -/
  lift :
    {A B : PointedSet.{u}} →
    (f : PointedHom A B) →
    (mono : Function.Injective f.toFun) →
    (g : PointedHom A I) →
    Σ h : PointedHom B I, Path (PointedHom.comp h f) g

namespace InjectiveObject

/-- The unit pointed set is injective. -/
def trivial : InjectiveObject unitPointed where
  lift := by
    intro A B f mono g
    refine ⟨zeroHom B unitPointed, ?_⟩
    apply Path.stepChain
    apply PointedHom.ext
    funext x
    cases g.toFun x
    rfl

end InjectiveObject

/-! ## Injective resolutions -/

/-- A two-step injective resolution with Path-valued exactness. -/
structure InjectiveResolution (A : PointedSet.{u}) : Type (u + 1) where
  /-- First injective object. -/
  I0 : PointedSet.{u}
  /-- Second injective object. -/
  I1 : PointedSet.{u}
  /-- Inclusion of A into I0. -/
  ι : PointedHom A I0
  /-- Differential from I0 to I1. -/
  d0 : PointedHom I0 I1
  /-- Injectivity of the inclusion. -/
  mono : Function.Injective ι.toFun
  /-- Path-exactness at I0. -/
  exact : PathExact ι d0
  /-- Injective structure on I0. -/
  inj0 : InjectiveObject I0
  /-- Injective structure on I1. -/
  inj1 : InjectiveObject I1

namespace InjectiveResolution

/-- The trivial injective resolution of the unit pointed set. -/
def trivial : InjectiveResolution unitPointed where
  I0 := unitPointed
  I1 := unitPointed
  ι := PointedHom.id unitPointed
  d0 := zeroHom unitPointed unitPointed
  mono := by intro _ _ h; exact h
  exact := by
    refine { im_sub_ker := ?_, ker_sub_im := ?_ }
    · intro x
      exact Path.refl _
    · intro y _
      exact ⟨y, Path.refl _⟩
  inj0 := InjectiveObject.trivial
  inj1 := InjectiveObject.trivial

end InjectiveResolution

/-! ## Summary -/

/-!
We introduced Path-valued exactness, injective objects, and a two-step
injective resolution interface, along with a trivial resolution on the unit
pointed set.
-/

end Algebra
end Path
end ComputationalPaths
