import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Triangulated structure paths

This module packages triangulated-category style coherence data with
domain-specific rewrite steps and derived `RwEq` witnesses.
-/

namespace ComputationalPaths
namespace DerivedCategories

open Path

universe u

/-- Domain-specific rewrite steps for triangulated coherence paths. -/
inductive TriangulatedStep {Obj : Type u} :
    {a b : Obj} → Path a b → Path a b → Prop where
  | shift_right_unit {a b : Obj} (p : Path a b) :
      TriangulatedStep (Path.trans p (Path.refl b)) p
  | connect_left_unit {a b : Obj} (p : Path a b) :
      TriangulatedStep (Path.trans (Path.refl a) p) p
  | cone_cancel {a b : Obj} (p : Path a b) :
      TriangulatedStep (Path.trans (Path.symm p) p) (Path.refl b)
  | cone_cancel_right {a b : Obj} (p : Path a b) :
      TriangulatedStep (Path.trans p (Path.symm p)) (Path.refl a)
  | triangle_assoc {a b c d : Obj}
      (p : Path a b) (q : Path b c) (r : Path c d) :
      TriangulatedStep
        (Path.trans (Path.trans p q) r)
        (Path.trans p (Path.trans q r))
  | rotation_symm_trans {a b c : Obj}
      (p : Path a b) (q : Path b c) :
      TriangulatedStep
        (Path.symm (Path.trans p q))
        (Path.trans (Path.symm q) (Path.symm p))

/-- Interpret a triangulated step as a primitive `Path.Step`. -/
def TriangulatedStep.toStep {Obj : Type u} {a b : Obj} {p q : Path a b}
    (s : TriangulatedStep p q) : Path.Step p q :=
  match s with
  | .shift_right_unit p => Path.Step.trans_refl_right p
  | .connect_left_unit p => Path.Step.trans_refl_left p
  | .cone_cancel p => Path.Step.symm_trans p
  | .cone_cancel_right p => Path.Step.trans_symm p
  | .triangle_assoc p q r => Path.Step.trans_assoc p q r
  | .rotation_symm_trans p q => Path.Step.symm_trans_congr p q

/-- Lift a triangulated step to rewrite equivalence. -/
theorem rweq_of_triangulated_step {Obj : Type u} {a b : Obj}
    {p q : Path a b} (s : TriangulatedStep p q) : RwEq p q :=
  rweq_of_step (TriangulatedStep.toStep s)

/-- Triangulated-category style data tracked with computational paths. -/
structure TriangulatedPaths (Obj : Type u) where
  shiftObj : Obj → Obj
  shiftPath : ∀ {X Y : Obj}, Path X Y → Path (shiftObj X) (shiftObj Y)
  distinguished : Obj → Obj → Obj → Prop
  connect :
    ∀ {X Y Z : Obj},
      distinguished X Y Z → Path X Y → Path Y Z → Path Z (shiftObj X)
  shiftStep :
    ∀ {X Y : Obj} (p : Path X Y),
      TriangulatedStep
        (Path.trans (shiftPath p) (Path.refl (shiftObj Y)))
        (shiftPath p)
  connectStep :
    ∀ {X Y Z : Obj} (h : distinguished X Y Z) (f : Path X Y) (g : Path Y Z),
      TriangulatedStep
        (Path.trans (Path.refl Z) (connect h f g))
        (connect h f g)
  rotationPath :
    ∀ {X Y Z : Obj} (_h : distinguished X Y Z) (_f : Path X Y) (_g : Path Y Z),
      Path (shiftObj X) (shiftObj X)
  rotationStep :
    ∀ {X Y Z : Obj} (h : distinguished X Y Z) (f : Path X Y) (g : Path Y Z),
      TriangulatedStep
        (Path.trans (rotationPath h f g) (Path.refl (shiftObj X)))
        (rotationPath h f g)
  coneStep :
    ∀ {X Y : Obj} (p : Path X Y),
      TriangulatedStep
        (Path.trans (Path.symm p) p)
        (Path.refl Y)

namespace TriangulatedPaths

variable {Obj : Type u} (T : TriangulatedPaths Obj)

/-- Primitive step witness for shift coherence. -/
def shift_step {X Y : Obj} (p : Path X Y) :
    Path.Step
      (Path.trans (T.shiftPath p) (Path.refl (T.shiftObj Y)))
      (T.shiftPath p) :=
  TriangulatedStep.toStep (T.shiftStep p)

/-- Primitive step witness for connecting morphism coherence. -/
def connect_step {X Y Z : Obj}
    (h : T.distinguished X Y Z) (f : Path X Y) (g : Path Y Z) :
    Path.Step
      (Path.trans (Path.refl Z) (T.connect h f g))
      (T.connect h f g) :=
  TriangulatedStep.toStep (T.connectStep h f g)

/-- Primitive step witness for triangle rotation coherence. -/
def rotation_step {X Y Z : Obj}
    (h : T.distinguished X Y Z) (f : Path X Y) (g : Path Y Z) :
    Path.Step
      (Path.trans (T.rotationPath h f g) (Path.refl (T.shiftObj X)))
      (T.rotationPath h f g) :=
  TriangulatedStep.toStep (T.rotationStep h f g)

/-- Primitive step witness for cone cancellation coherence. -/
def cone_step {X Y : Obj} (p : Path X Y) :
    Path.Step
      (Path.trans (Path.symm p) p)
      (Path.refl Y) :=
  TriangulatedStep.toStep (T.coneStep p)

/-- Primitive step witness for right-cancellation in cone-style composites. -/
def cone_right_step {X Y : Obj} (p : Path X Y) :
    Path.Step
      (Path.trans p (Path.symm p))
      (Path.refl X) :=
  TriangulatedStep.toStep (TriangulatedStep.cone_cancel_right p)

/-- Primitive step witness for associativity in triangulated composites. -/
def assoc_step {W X Y Z : Obj}
    (p : Path W X) (q : Path X Y) (r : Path Y Z) :
    Path.Step
      (Path.trans (Path.trans p q) r)
      (Path.trans p (Path.trans q r)) :=
  TriangulatedStep.toStep (TriangulatedStep.triangle_assoc p q r)

/-- Primitive step witness for symmetry over composition. -/
def symm_trans_step {X Y Z : Obj}
    (p : Path X Y) (q : Path Y Z) :
    Path.Step
      (Path.symm (Path.trans p q))
      (Path.trans (Path.symm q) (Path.symm p)) :=
  TriangulatedStep.toStep (TriangulatedStep.rotation_symm_trans p q)

@[simp] theorem shift_rweq {X Y : Obj} (p : Path X Y) :
    RwEq
      (Path.trans (T.shiftPath p) (Path.refl (T.shiftObj Y)))
      (T.shiftPath p) :=
  rweq_of_step (T.shift_step p)

@[simp] theorem connect_rweq {X Y Z : Obj}
    (h : T.distinguished X Y Z) (f : Path X Y) (g : Path Y Z) :
    RwEq
      (Path.trans (Path.refl Z) (T.connect h f g))
      (T.connect h f g) :=
  rweq_of_step (T.connect_step h f g)

@[simp] theorem rotation_rweq {X Y Z : Obj}
    (h : T.distinguished X Y Z) (f : Path X Y) (g : Path Y Z) :
    RwEq
      (Path.trans (T.rotationPath h f g) (Path.refl (T.shiftObj X)))
      (T.rotationPath h f g) :=
  rweq_of_step (T.rotation_step h f g)

@[simp] theorem cone_rweq {X Y : Obj} (p : Path X Y) :
    RwEq
      (Path.trans (Path.symm p) p)
      (Path.refl Y) :=
  rweq_of_step (T.cone_step p)

@[simp] theorem cone_right_rweq {X Y : Obj} (p : Path X Y) :
    RwEq
      (Path.trans p (Path.symm p))
      (Path.refl X) :=
  rweq_of_step (T.cone_right_step p)

@[simp] theorem assoc_rweq {W X Y Z : Obj}
    (p : Path W X) (q : Path X Y) (r : Path Y Z) :
    RwEq
      (Path.trans (Path.trans p q) r)
      (Path.trans p (Path.trans q r)) :=
  rweq_of_step (T.assoc_step p q r)

@[simp] theorem symm_trans_rweq {X Y Z : Obj}
    (p : Path X Y) (q : Path Y Z) :
    RwEq
      (Path.symm (Path.trans p q))
      (Path.trans (Path.symm q) (Path.symm p)) :=
  rweq_of_step (T.symm_trans_step p q)

/-- Coherence: connect-unit normalizations are stable under right whiskering by `refl`. -/
theorem connect_unit_assoc_rweq {X Y Z : Obj}
    (h : T.distinguished X Y Z) (f : Path X Y) (g : Path Y Z) :
    RwEq
      (Path.trans
        (Path.trans (Path.refl Z) (T.connect h f g))
        (Path.refl (T.shiftObj X)))
      (T.connect h f g) := by
  refine rweq_trans ?_ ?_
  exact T.assoc_rweq (Path.refl Z) (T.connect h f g) (Path.refl (T.shiftObj X))
  refine rweq_trans ?_ ?_
  exact rweq_trans_congr_right (Path.refl Z)
    (rweq_cmpA_refl_right (T.connect h f g))
  exact T.connect_rweq h f g

/-- Coherence: cone cancellation remains stable after appending a right unit. -/
theorem cone_unit_assoc_rweq {X Y : Obj} (p : Path X Y) :
    RwEq
      (Path.trans (Path.trans (Path.symm p) p) (Path.refl Y))
      (Path.refl Y) := by
  refine rweq_trans ?_ ?_
  exact T.assoc_rweq (Path.symm p) p (Path.refl Y)
  refine rweq_trans ?_ ?_
  exact rweq_trans_congr_right (Path.symm p) (rweq_cmpA_refl_right p)
  exact T.cone_rweq p

end TriangulatedPaths

/-- Trivial triangulated-path package with canonical unit/cancellation steps. -/
def trivialTriangulatedPaths (Obj : Type u) : TriangulatedPaths Obj where
  shiftObj := id
  shiftPath := fun {_ _} p => p
  distinguished := fun _ _ _ => True
  connect := fun _ f g => Path.symm (Path.trans f g)
  shiftStep := fun p => TriangulatedStep.shift_right_unit p
  connectStep := fun _ f g => TriangulatedStep.connect_left_unit (Path.symm (Path.trans f g))
  rotationPath := fun _ _ _ => Path.refl _
  rotationStep := fun _ _ _ => TriangulatedStep.shift_right_unit (Path.refl _)
  coneStep := fun p => TriangulatedStep.cone_cancel p

end DerivedCategories
end ComputationalPaths
