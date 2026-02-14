/-
# Step-based Kan extension path infrastructure

This module packages left and right pointwise Kan extension actions as
path-preserving constructions. The preservation laws are witnessed by explicit
`Step` constructors from the computational-path rewrite system.
-/

import ComputationalPaths.Path.KanExtension
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Kan

open Path

universe u v

section Left

variable {A B : Type u}
variable (J : PathCategoryFunctor A B)
variable (X : PathFunctor.{u, v} (A := A))

abbrev LeftKanObj (b : B) : Type (max u v) :=
  pointwiseLeftKanObj J X b

abbrev leftMap {b b' : B} (q : Path b b') :
    LeftKanObj (J := J) (X := X) b → LeftKanObj (J := J) (X := X) b' :=
  pointwiseLeftKanMap (F := J) (G := X) (b := b) (b' := b') q

theorem leftMap_id_step {b : B}
    (a : A) (p : Path (J.obj a) b) (x : X.obj a) :
    Path.Step ((leftMap (J := J) (X := X) (q := Path.refl b) ⟨a, ⟨p, x⟩⟩).2.1) p := by
  simpa [leftMap, pointwiseLeftKanMap] using (Path.Step.trans_refl_right p)

theorem leftMap_comp_step {b c d : B}
    (q : Path b c) (r : Path c d)
    (a : A) (p : Path (J.obj a) b) (x : X.obj a) :
    Path.Step
      ((leftMap (J := J) (X := X) (q := r)
        (leftMap (J := J) (X := X) (q := q) ⟨a, ⟨p, x⟩⟩)).2.1)
      ((leftMap (J := J) (X := X) (q := Path.trans q r) ⟨a, ⟨p, x⟩⟩).2.1) := by
  simpa [leftMap, pointwiseLeftKanMap] using (Path.Step.trans_assoc p q r)

theorem leftMap_id_rweq {b : B}
    (a : A) (p : Path (J.obj a) b) (x : X.obj a) :
    RwEq ((leftMap (J := J) (X := X) (q := Path.refl b) ⟨a, ⟨p, x⟩⟩).2.1) p :=
  rweq_of_step (leftMap_id_step (J := J) (X := X) (b := b) a p x)

theorem leftMap_comp_rweq {b c d : B}
    (q : Path b c) (r : Path c d)
    (a : A) (p : Path (J.obj a) b) (x : X.obj a) :
    RwEq
      ((leftMap (J := J) (X := X) (q := r)
        (leftMap (J := J) (X := X) (q := q) ⟨a, ⟨p, x⟩⟩)).2.1)
      ((leftMap (J := J) (X := X) (q := Path.trans q r) ⟨a, ⟨p, x⟩⟩).2.1) :=
  rweq_of_step (leftMap_comp_step (J := J) (X := X) q r a p x)

/-- Left Kan extension action equipped with explicit `Step` witnesses. -/
structure LeftKanPathPreserving where
  map_id_step :
    ∀ {b : B} (a : A) (p : Path (J.obj a) b) (x : X.obj a),
      Path.Step ((leftMap (J := J) (X := X) (q := Path.refl b) ⟨a, ⟨p, x⟩⟩).2.1) p
  map_comp_step :
    ∀ {b c d : B} (q : Path b c) (r : Path c d)
      (a : A) (p : Path (J.obj a) b) (x : X.obj a),
      Path.Step
        ((leftMap (J := J) (X := X) (q := r)
          (leftMap (J := J) (X := X) (q := q) ⟨a, ⟨p, x⟩⟩)).2.1)
        ((leftMap (J := J) (X := X) (q := Path.trans q r) ⟨a, ⟨p, x⟩⟩).2.1)
  map_id_rweq :
    ∀ {b : B} (a : A) (p : Path (J.obj a) b) (x : X.obj a),
      RwEq ((leftMap (J := J) (X := X) (q := Path.refl b) ⟨a, ⟨p, x⟩⟩).2.1) p
  map_comp_rweq :
    ∀ {b c d : B} (q : Path b c) (r : Path c d)
      (a : A) (p : Path (J.obj a) b) (x : X.obj a),
      RwEq
        ((leftMap (J := J) (X := X) (q := r)
          (leftMap (J := J) (X := X) (q := q) ⟨a, ⟨p, x⟩⟩)).2.1)
        ((leftMap (J := J) (X := X) (q := Path.trans q r) ⟨a, ⟨p, x⟩⟩).2.1)

def leftKanPathPreserving : LeftKanPathPreserving (J := J) (X := X) where
  map_id_step := by
    intro b a p x
    exact leftMap_id_step (J := J) (X := X) (b := b) a p x
  map_comp_step := by
    intro b c d q r a p x
    exact leftMap_comp_step (J := J) (X := X) q r a p x
  map_id_rweq := by
    intro b a p x
    exact leftMap_id_rweq (J := J) (X := X) (b := b) a p x
  map_comp_rweq := by
    intro b c d q r a p x
    exact leftMap_comp_rweq (J := J) (X := X) q r a p x

end Left

section Right

variable {A B : Type u}
variable (J : PathCategoryFunctor A B)
variable (X : PathFunctor.{u, v} (A := A))

abbrev RightKanObj (b : B) : Type (max u v) :=
  pointwiseRightKanObj J X b

abbrev rightMap {b b' : B} (q : Path b b') :
    RightKanObj (J := J) (X := X) b → RightKanObj (J := J) (X := X) b' :=
  pointwiseRightKanMap (F := J) (G := X) (b := b) (b' := b') q

theorem rightMap_id_arg_step {b : B} {a : A}
    (p : Path b (J.obj a)) :
    Path.Step (Path.trans (Path.refl b) p) p :=
  Path.Step.trans_refl_left p

theorem rightMap_comp_arg_step {b c d : B}
    (q : Path b c) (r : Path c d) {a : A}
    (p : Path d (J.obj a)) :
    Path.Step (Path.trans (Path.trans q r) p) (Path.trans q (Path.trans r p)) :=
  Path.Step.trans_assoc q r p

theorem rightMap_id_arg_rweq {b : B} {a : A}
    (p : Path b (J.obj a)) :
    RwEq (Path.trans (Path.refl b) p) p :=
  rweq_of_step (rightMap_id_arg_step (J := J) (a := a) p)

theorem rightMap_comp_arg_rweq {b c d : B}
    (q : Path b c) (r : Path c d) {a : A}
    (p : Path d (J.obj a)) :
    RwEq (Path.trans (Path.trans q r) p) (Path.trans q (Path.trans r p)) :=
  rweq_of_step (rightMap_comp_arg_step (J := J) q r (a := a) p)

/-- Right Kan extension action equipped with explicit `Step` witnesses. -/
structure RightKanPathPreserving where
  map_id_arg_step :
    ∀ {b : B} {a : A} (p : Path b (J.obj a)),
      Path.Step (Path.trans (Path.refl b) p) p
  map_comp_arg_step :
    ∀ {b c d : B} (q : Path b c) (r : Path c d)
      {a : A} (p : Path d (J.obj a)),
      Path.Step (Path.trans (Path.trans q r) p) (Path.trans q (Path.trans r p))
  map_id_arg_rweq :
    ∀ {b : B} {a : A} (p : Path b (J.obj a)),
      RwEq (Path.trans (Path.refl b) p) p
  map_comp_arg_rweq :
    ∀ {b c d : B} (q : Path b c) (r : Path c d)
      {a : A} (p : Path d (J.obj a)),
      RwEq (Path.trans (Path.trans q r) p) (Path.trans q (Path.trans r p))

def rightKanPathPreserving : RightKanPathPreserving (J := J) where
  map_id_arg_step := by
    intro b a p
    exact Path.Step.trans_refl_left p
  map_comp_arg_step := by
    intro b c d q r a p
    exact Path.Step.trans_assoc q r p
  map_id_arg_rweq := by
    intro b a p
    exact rightMap_id_arg_rweq (J := J) (a := a) p
  map_comp_arg_rweq := by
    intro b c d q r a p
    exact rightMap_comp_arg_rweq (J := J) q r (a := a) p

end Right

end Kan
end ComputationalPaths
