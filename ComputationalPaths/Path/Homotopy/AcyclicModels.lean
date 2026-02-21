/-
# Acyclic Models and Homology

This module formalizes a retract-style acyclic models theorem for the
computational paths homology of 3-term chain complexes. We package a
Path-based notion of zero objects and retracts, then show that retracts of
acyclic models have trivial homology.

## Key Results

- `IsZero`: Path-based notion of a zero type.
- `Retract`: retracts witnessed by paths.
- `AcyclicModelsData`: acyclic models with retract coverage.
- `acyclic_models_homology_isZero`: homology vanishes under acyclic models.
- `homology_functor_isZero`: objectwise zero homology.

## References

- Eilenberg and Mac Lane, "On the Groups H(Pi,n), II"
- Weibel, "An Introduction to Homological Algebra"
-/

import ComputationalPaths.Path.Homotopy.PathHomology

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace AcyclicModels

open HomologicalAlgebra PathHomology

universe u v w

variable {C : Type u}

/-! ## Retracts and zero objects -/

/-- A type is zero if it has a chosen element and all elements are path-connected to it. -/
structure IsZero (A : Type u) where
  /-- The chosen zero element. -/
  zero : A
  /-- Every element is path-connected to zero. -/
  eq_zero : (a : A) → Path a zero

/-- A retract between types, witnessed by a section in the sense of paths. -/
structure Retract (X Y : Type u) where
  /-- Inclusion into the model. -/
  i : X → Y
  /-- Retraction back to the object. -/
  r : Y → X
  /-- The retraction is a left inverse up to paths. -/
  sectionPath : (x : X) → Path (r (i x)) x

/-- `IsZero` is stable under retracts. -/
def isZero_of_retract {X Y : Type u} (hY : IsZero Y) (h : Retract X Y) :
    IsZero X := by
  refine ⟨h.r hY.zero, ?_⟩
  intro x
  have hzero : Path (h.i x) hY.zero := hY.eq_zero (h.i x)
  have hmap : Path (h.r (h.i x)) (h.r hY.zero) :=
    Path.congrArg h.r hzero
  exact Path.trans (Path.symm (h.sectionPath x)) hmap

/-! ## Acyclic models data -/

/-- Data for a retract-style acyclic models hypothesis on a family of chain complexes. -/
structure AcyclicModelsData (F : C → ChainComplex3.{v}) where
  /-- The type of models. -/
  Model : Type w
  /-- Models as objects of the source type. -/
  modelObj : Model → C
  /-- Every object retracts onto a model at the homology level. -/
  retract :
    ∀ X : C, Σ m : Model, Retract (Homology (F X)) (Homology (F (modelObj m)))
  /-- Model values are acyclic (homology is zero). -/
  acyclic : ∀ m : Model, IsZero (Homology (F (modelObj m)))

/-! ## Acyclic models theorem -/

/-- Acyclic models theorem: retracts of acyclic models have zero homology. -/
def acyclic_models_homology_isZero {F : C → ChainComplex3.{v}}
    (data : AcyclicModelsData (F := F)) (X : C) :
    IsZero (Homology (F X)) := by
  rcases data.retract X with ⟨m, h⟩
  exact isZero_of_retract (data.acyclic m) h

/-! ## Applications to homology -/

/-- The homology family of an acyclic-models functor is zero objectwise. -/
def homology_functor_isZero {F : C → ChainComplex3.{v}}
    (data : AcyclicModelsData (F := F)) :
    ∀ X : C, IsZero (Homology (F X)) := by
  intro X
  exact acyclic_models_homology_isZero (data := data) (X := X)

/-! ## Summary

We package a retract-based acyclic models hypothesis and show that it forces
homology to vanish objectwise, yielding a zero homology family.
-/

end AcyclicModels
end Homotopy
end Path
end ComputationalPaths
