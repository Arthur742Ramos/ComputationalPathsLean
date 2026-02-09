/-
# Acyclic Models and Homology

This module formalizes a retract-style acyclic models theorem for functors into
homological complexes, and records homology-vanishing applications.

## Key Results

- `AcyclicModelsData`: acyclic models with retract coverage.
- `acyclic_models_homology_isZero`: homology vanishes under acyclic models.
- `homology_functor_isZero`: the induced homology functor is zero.

## References

- Eilenberg and Mac Lane, "On the Groups H(Pi,n), II"
- Weibel, "An Introduction to Homological Algebra"
-/

import Mathlib

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace AcyclicModels

open CategoryTheory
open CategoryTheory.Limits

universe u v w w'

variable {C : Type u} [Category C]
variable {V : Type v} [Category V] [HasZeroMorphisms V] [CategoryWithHomology V]
variable {ι : Type w} {c : ComplexShape ι}

/-! ## Retracts and zero objects -/

/-- `IsZero` is stable under retracts. -/
theorem isZero_of_retract {X Y : V} (hY : IsZero Y) (h : Retract X Y) : IsZero X := by
  refine ⟨?unique_to, ?unique_from⟩
  · intro Z
    refine ⟨⟨⟨h.i ≫ hY.to_ Z⟩, ?_⟩⟩
    intro f
    have huniq : h.r ≫ f = hY.to_ Z := hY.eq_of_src _ _
    calc
      f = (𝟙 X) ≫ f := by simp
      _ = (h.i ≫ h.r) ≫ f := by simpa
      _ = h.i ≫ (h.r ≫ f) := by simp [Category.assoc]
      _ = h.i ≫ hY.to_ Z := by simp [huniq]
  · intro Z
    refine ⟨⟨⟨hY.from_ Z ≫ h.r⟩, ?_⟩⟩
    intro f
    have huniq : f ≫ h.i = hY.from_ Z := hY.eq_of_tgt _ _
    calc
      f = f ≫ (𝟙 X) := by simp
      _ = f ≫ (h.i ≫ h.r) := by simpa
      _ = (f ≫ h.i) ≫ h.r := by simp [Category.assoc]
      _ = hY.from_ Z ≫ h.r := by simp [huniq]

/-! ## Acyclic models data -/

/-- Data for a retract-style acyclic models hypothesis on a functor. -/
structure AcyclicModelsData (F : C ⥤ HomologicalComplex V c) where
  /-- The type of models. -/
  Model : Type w'
  /-- Models as objects of the source category. -/
  modelObj : Model → C
  /-- Every object is a retract of a model. -/
  retract : ∀ X : C, Σ m : Model, Retract X (modelObj m)
  /-- Model values are acyclic homological complexes. -/
  acyclic : ∀ m : Model, (F.obj (modelObj m)).Acyclic

/-! ## Acyclic models theorem -/

/-- Acyclic models theorem: retracts of acyclic models have vanishing homology. -/
theorem acyclic_models_homology_isZero {F : C ⥤ HomologicalComplex V c}
    (data : AcyclicModelsData (F := F)) (X : C) (i : ι) :
    IsZero ((F.obj X).homology i) := by
  rcases data.retract X with ⟨m, h⟩
  have hModelZero : IsZero ((F.obj (data.modelObj m)).homology i) := by
    have hExact : (F.obj (data.modelObj m)).ExactAt i := (data.acyclic m) i
    exact HomologicalComplex.ExactAt.isZero_homology
      (K := F.obj (data.modelObj m)) (i := i) hExact
  have hRetract : Retract (F.obj X) (F.obj (data.modelObj m)) := h.map F
  have hRetractHomology :
      Retract ((F.obj X).homology i) ((F.obj (data.modelObj m)).homology i) := by
    simpa using
      (Retract.map (F := HomologicalComplex.homologyFunctor (C := V) (c := c) (i := i))
        hRetract)
  exact isZero_of_retract hModelZero hRetractHomology

/-! ## Applications to homology -/

/-- The homology functor of an acyclic-models functor is zero. -/
theorem homology_functor_isZero {F : C ⥤ HomologicalComplex V c}
    (data : AcyclicModelsData (F := F)) (i : ι) :
    IsZero (F ⋙ HomologicalComplex.homologyFunctor (C := V) (c := c) (i := i)) := by
  apply Functor.isZero
  intro X
  simpa using acyclic_models_homology_isZero (data := data) (X := X) (i := i)

/-! ## Summary

We package a retract-based acyclic models hypothesis and show that it forces
homology to vanish objectwise, yielding a zero homology functor.
-/

end AcyclicModels
end Homotopy
end Path
end ComputationalPaths
