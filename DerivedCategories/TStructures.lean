import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import DerivedCategories.TriangulatedPaths

/-!
# t-structure paths

This module packages t-structure style truncation and heart data with
domain-specific `Step` witnesses and derived `RwEq` normalizations.
-/

namespace ComputationalPaths
namespace DerivedCategories

open Path

universe u

/-- Domain-specific rewrite steps for t-structure coherence paths. -/
inductive TStructureStep {Obj : Type u} :
    {a b : Obj} → Path a b → Path a b → Prop where
  | trunc_ge_right_unit {a b : Obj} (p : Path a b) :
      TStructureStep (Path.trans p (Path.refl b)) p
  | trunc_ge_left_unit {a b : Obj} (p : Path a b) :
      TStructureStep (Path.trans (Path.refl a) p) p
  | trunc_le_left_unit {a b : Obj} (p : Path a b) :
      TStructureStep (Path.trans (Path.refl a) p) p
  | trunc_le_right_unit {a b : Obj} (p : Path a b) :
      TStructureStep (Path.trans p (Path.refl b)) p
  | trunc_adjunction_cancel {a b : Obj} (p : Path a b) :
      TStructureStep (Path.trans (Path.symm p) p) (Path.refl b)
  | trunc_adjunction_cancel_right {a b : Obj} (p : Path a b) :
      TStructureStep (Path.trans p (Path.symm p)) (Path.refl a)
  | trunc_assoc {a b c d : Obj}
      (p : Path a b) (q : Path b c) (r : Path c d) :
      TStructureStep
        (Path.trans (Path.trans p q) r)
        (Path.trans p (Path.trans q r))

/-- Interpret a t-structure step as a primitive `Path.Step`. -/
def TStructureStep.toStep {Obj : Type u} {a b : Obj} {p q : Path a b}
    (s : TStructureStep p q) : Path.Step p q :=
  match s with
  | .trunc_ge_right_unit p => Path.Step.trans_refl_right p
  | .trunc_ge_left_unit p => Path.Step.trans_refl_left p
  | .trunc_le_left_unit p => Path.Step.trans_refl_left p
  | .trunc_le_right_unit p => Path.Step.trans_refl_right p
  | .trunc_adjunction_cancel p => Path.Step.symm_trans p
  | .trunc_adjunction_cancel_right p => Path.Step.trans_symm p
  | .trunc_assoc p q r => Path.Step.trans_assoc p q r

/-- Lift a t-structure step to rewrite equivalence. -/
theorem rweq_of_tstructure_step {Obj : Type u} {a b : Obj}
    {p q : Path a b} (s : TStructureStep p q) : RwEq p q :=
  rweq_of_step (TStructureStep.toStep s)

@[simp] theorem tstructure_left_unit_rweq {Obj : Type u} {a b : Obj}
    (p : Path a b) :
    RwEq (Path.trans (Path.refl a) p) p :=
  rweq_of_tstructure_step (TStructureStep.trunc_ge_left_unit p)

@[simp] theorem tstructure_right_unit_rweq {Obj : Type u} {a b : Obj}
    (p : Path a b) :
    RwEq (Path.trans p (Path.refl b)) p :=
  rweq_of_tstructure_step (TStructureStep.trunc_ge_right_unit p)

@[simp] theorem tstructure_adjunction_right_rweq {Obj : Type u} {a b : Obj}
    (p : Path a b) :
    RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
  rweq_of_tstructure_step (TStructureStep.trunc_adjunction_cancel_right p)

@[simp] theorem tstructure_assoc_rweq {Obj : Type u} {a b c d : Obj}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_of_tstructure_step (TStructureStep.trunc_assoc p q r)

/-- t-Structure data over a triangulated path package. -/
structure TStructurePaths (Obj : Type u) (T : TriangulatedPaths Obj) where
  nonNeg : Obj → Prop
  nonPos : Obj → Prop
  truncGE : Obj → Obj
  truncLE : Obj → Obj
  truncGEUnit : ∀ X : Obj, Path X (truncGE X)
  truncLECounit : ∀ X : Obj, Path (truncLE X) X
  shift_nonNeg : ∀ X : Obj, nonNeg X → nonNeg (T.shiftObj X)
  shift_nonPos : ∀ X : Obj, nonPos X → nonPos (T.shiftObj X)
  truncGEStep :
    ∀ X : Obj,
      TStructureStep
        (Path.trans (truncGEUnit X) (Path.refl (truncGE X)))
        (truncGEUnit X)
  truncLEStep :
    ∀ X : Obj,
      TStructureStep
        (Path.trans (Path.refl (truncLE X)) (truncLECounit X))
        (truncLECounit X)
  adjunctionStep :
    ∀ X : Obj,
      TStructureStep
        (Path.trans (Path.symm (truncGEUnit X)) (truncGEUnit X))
        (Path.refl (truncGE X))

namespace TStructurePaths

variable {Obj : Type u} {T : TriangulatedPaths Obj} (S : TStructurePaths Obj T)

/-- Heart predicate as intersection of the two truncation halves. -/
def heart (X : Obj) : Prop :=
  S.nonNeg X ∧ S.nonPos X

theorem heart_shift_closed (X : Obj) :
    S.heart X → S.heart (T.shiftObj X) := by
  intro hX
  exact ⟨S.shift_nonNeg X hX.1, S.shift_nonPos X hX.2⟩

/-- Primitive step witness for non-negative truncation unit normalization. -/
def trunc_ge_step (X : Obj) :
    Path.Step
      (Path.trans (S.truncGEUnit X) (Path.refl (S.truncGE X)))
      (S.truncGEUnit X) :=
  TStructureStep.toStep (S.truncGEStep X)

/-- Primitive step witness for non-positive truncation counit normalization. -/
def trunc_le_step (X : Obj) :
    Path.Step
      (Path.trans (Path.refl (S.truncLE X)) (S.truncLECounit X))
      (S.truncLECounit X) :=
  TStructureStep.toStep (S.truncLEStep X)

/-- Primitive step witness for truncation adjunction cancellation. -/
def adjunction_step (X : Obj) :
    Path.Step
      (Path.trans (Path.symm (S.truncGEUnit X)) (S.truncGEUnit X))
      (Path.refl (S.truncGE X)) :=
  TStructureStep.toStep (S.adjunctionStep X)

/-- Primitive step witness for shifted truncation-unit normalization. -/
def shifted_trunc_ge_step (X : Obj) :
    Path.Step
      (Path.trans
        (T.shiftPath (S.truncGEUnit X))
        (Path.refl (T.shiftObj (S.truncGE X))))
      (T.shiftPath (S.truncGEUnit X)) :=
  T.shift_step (S.truncGEUnit X)

@[simp] theorem trunc_ge_rweq (X : Obj) :
    RwEq
      (Path.trans (S.truncGEUnit X) (Path.refl (S.truncGE X)))
      (S.truncGEUnit X) :=
  rweq_of_step (S.trunc_ge_step X)

@[simp] theorem trunc_ge_left_rweq (X : Obj) :
    RwEq
      (Path.trans (Path.refl X) (S.truncGEUnit X))
      (S.truncGEUnit X) :=
  tstructure_left_unit_rweq (S.truncGEUnit X)

@[simp] theorem trunc_le_rweq (X : Obj) :
    RwEq
      (Path.trans (Path.refl (S.truncLE X)) (S.truncLECounit X))
      (S.truncLECounit X) :=
  rweq_of_step (S.trunc_le_step X)

@[simp] theorem trunc_le_right_rweq (X : Obj) :
    RwEq
      (Path.trans (S.truncLECounit X) (Path.refl X))
      (S.truncLECounit X) :=
  tstructure_right_unit_rweq (S.truncLECounit X)

@[simp] theorem trunc_adjunction_rweq (X : Obj) :
    RwEq
      (Path.trans (Path.symm (S.truncGEUnit X)) (S.truncGEUnit X))
      (Path.refl (S.truncGE X)) :=
  rweq_of_step (S.adjunction_step X)

@[simp] theorem trunc_adjunction_right_rweq (X : Obj) :
    RwEq
      (Path.trans (S.truncGEUnit X) (Path.symm (S.truncGEUnit X)))
      (Path.refl X) :=
  tstructure_adjunction_right_rweq (S.truncGEUnit X)

@[simp] theorem shifted_trunc_ge_rweq (X : Obj) :
    RwEq
      (Path.trans
        (T.shiftPath (S.truncGEUnit X))
        (Path.refl (T.shiftObj (S.truncGE X))))
      (T.shiftPath (S.truncGEUnit X)) :=
  rweq_of_step (S.shifted_trunc_ge_step X)

/-- Coherence: double right-unit whiskering of `truncGEUnit` contracts via Step witnesses. -/
theorem trunc_ge_unit_assoc_rweq (X : Obj) :
    RwEq
      (Path.trans
        (Path.trans (S.truncGEUnit X) (Path.refl (S.truncGE X)))
        (Path.refl (S.truncGE X)))
      (S.truncGEUnit X) := by
  refine rweq_trans ?_ ?_
  exact tstructure_assoc_rweq
    (S.truncGEUnit X) (Path.refl (S.truncGE X)) (Path.refl (S.truncGE X))
  refine rweq_trans ?_ ?_
  exact rweq_trans_congr_right (S.truncGEUnit X)
    (tstructure_left_unit_rweq (Path.refl (S.truncGE X)))
  exact S.trunc_ge_rweq X

/-- Coherence: truncation adjunction cancellation survives right-unit whiskering. -/
theorem trunc_adjunction_unit_assoc_rweq (X : Obj) :
    RwEq
      (Path.trans
        (Path.trans (Path.symm (S.truncGEUnit X)) (S.truncGEUnit X))
        (Path.refl (S.truncGE X)))
      (Path.refl (S.truncGE X)) := by
  refine rweq_trans ?_ ?_
  exact tstructure_assoc_rweq
    (Path.symm (S.truncGEUnit X)) (S.truncGEUnit X) (Path.refl (S.truncGE X))
  refine rweq_trans ?_ ?_
  exact rweq_trans_congr_right (Path.symm (S.truncGEUnit X))
    (S.trunc_ge_rweq X)
  exact S.trunc_adjunction_rweq X

end TStructurePaths

/-- Trivial t-structure package over any triangulated path data. -/
def trivialTStructurePaths (Obj : Type u) (T : TriangulatedPaths Obj) :
    TStructurePaths Obj T where
  nonNeg := fun _ => True
  nonPos := fun _ => True
  truncGE := id
  truncLE := id
  truncGEUnit := fun X => Path.refl X
  truncLECounit := fun X => Path.refl X
  shift_nonNeg := fun _ _ => trivial
  shift_nonPos := fun _ _ => trivial
  truncGEStep := fun X => TStructureStep.trunc_ge_right_unit (Path.refl X)
  truncLEStep := fun X => TStructureStep.trunc_le_left_unit (Path.refl X)
  adjunctionStep := fun X => TStructureStep.trunc_adjunction_cancel (Path.refl X)

end DerivedCategories
end ComputationalPaths
