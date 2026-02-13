 /-
# Motivic path infrastructure

This module packages motivic-homotopy-flavored path data with explicit
computational-step witnesses for A¹-invariance.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Motivic

open Path

universe u v

/-- A¹-invariance data with step-level witnesses for normalization laws. -/
structure A1PathInfrastructure (X : Type u) (A1 : Type v) where
  /-- Projection `X × A¹ → X`. -/
  proj : X × A1 → X
  /-- Section `X → X × A¹`. -/
  sec : X → X × A1
  /-- Retraction witness `proj ∘ section ~ id`. -/
  retractPath : ∀ x : X, Path (proj (sec x)) x
  /-- Section-side homotopy witness. -/
  sectionPath : ∀ p : X × A1, Path (sec (proj p)) (sec (proj p))
  /-- Retraction witness is a genuine computational step (right unit). -/
  retractStep : ∀ x : X,
    Path.Step (Path.trans (retractPath x) (Path.refl x)) (retractPath x)
  /-- Section witness is a genuine computational step (left unit). -/
  sectionStep : ∀ p : X × A1,
    Path.Step (Path.trans (Path.refl (sec (proj p))) (sectionPath p)) (sectionPath p)

namespace A1PathInfrastructure

variable {X : Type u} {A1 : Type v} (M : A1PathInfrastructure X A1)

@[simp] theorem retract_rweq (x : X) :
    RwEq (Path.trans (M.retractPath x) (Path.refl x)) (M.retractPath x) :=
  rweq_of_step (M.retractStep x)

@[simp] theorem section_rweq (p : X × A1) :
    RwEq (Path.trans (Path.refl (M.sec (M.proj p))) (M.sectionPath p)) (M.sectionPath p) :=
  rweq_of_step (M.sectionStep p)

end A1PathInfrastructure

/-- Build A¹-invariance infrastructure from path-level witnesses. -/
def mkA1PathInfrastructure
    {X : Type u} {A1 : Type v}
    (proj : X × A1 → X)
    (sec : X → X × A1)
    (retractPath : ∀ x : X, Path (proj (sec x)) x)
    (sectionPath : ∀ p : X × A1, Path (sec (proj p)) (sec (proj p))) :
    A1PathInfrastructure X A1 where
  proj := proj
  sec := sec
  retractPath := retractPath
  sectionPath := sectionPath
  retractStep := fun x => Path.Step.trans_refl_right (retractPath x)
  sectionStep := fun p => Path.Step.trans_refl_left (sectionPath p)

/-- Canonical A¹-invariance infrastructure for the identity projection/section. -/
def idA1PathInfrastructure (X : Type u) :
    A1PathInfrastructure X PUnit.{1} :=
  mkA1PathInfrastructure
    (proj := fun p => p.1)
    (sec := fun x => (x, PUnit.unit))
    (retractPath := fun x => Path.refl x)
    (sectionPath := fun _ => Path.refl _)

/-- Canonical retract normalization exposed as rewrite equivalence. -/
theorem id_retract_rweq (X : Type u) (x : X) :
    RwEq
      (Path.trans ((idA1PathInfrastructure X).retractPath x) (Path.refl x))
      ((idA1PathInfrastructure X).retractPath x) :=
  (idA1PathInfrastructure X).retract_rweq x

end Motivic
end ComputationalPaths
