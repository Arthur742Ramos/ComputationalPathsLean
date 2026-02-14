import ComputationalPaths.Path.Homotopy.BordismTheory
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Bordism category paths

This module packages bordism-category style coherence data in the computational
path setting.  The unit/associativity laws are carried by explicit `Path.Step`
witnesses and then lifted to `RwEq`.
-/

namespace ComputationalPaths
namespace Cobordism

open Path
open Path.Homotopy
open Homotopy.BordismTheory

universe u

/-- A bordism-category skeleton where morphisms are computational paths. -/
structure BordismPathCategory where
  Obj : Type u
  id : (X : Obj) → Path X X
  comp : {X Y Z : Obj} → Path X Y → Path Y Z → Path X Z
  id_left : ∀ {X Y : Obj} (f : Path X Y), RwEq (comp (id X) f) f
  id_right : ∀ {X Y : Obj} (f : Path X Y), RwEq (comp f (id Y)) f
  assoc :
    ∀ {W X Y Z : Obj} (f : Path W X) (g : Path X Y) (h : Path Y Z),
      RwEq (comp (comp f g) h) (comp f (comp g h))

/-- Objects in degree `n` for bordism-path categories. -/
abbrev BordismObj (n : Nat) : Type (u + 1) := BordismClass.{u} n

/-- Identity bordism path. -/
def bordismId {n : Nat} (X : BordismObj n) : Path X X :=
  Path.refl X

/-- Composition of bordism paths. -/
def bordismComp {n : Nat} {X Y Z : BordismObj n}
    (p : Path X Y) (q : Path Y Z) : Path X Z :=
  Path.trans p q

/-- Left unit as a primitive rewrite step. -/
theorem bordism_id_left_step {n : Nat} {X Y : BordismObj n}
    (p : Path X Y) :
    Path.Step (bordismComp (bordismId X) p) p := by
  simpa [bordismComp, bordismId] using Path.Step.trans_refl_left p

/-- Right unit as a primitive rewrite step. -/
theorem bordism_id_right_step {n : Nat} {X Y : BordismObj n}
    (p : Path X Y) :
    Path.Step (bordismComp p (bordismId Y)) p := by
  simpa [bordismComp, bordismId] using Path.Step.trans_refl_right p

/-- Associativity as a primitive rewrite step. -/
theorem bordism_assoc_step {n : Nat}
    {W X Y Z : BordismObj n}
    (f : Path W X) (g : Path X Y) (h : Path Y Z) :
    Path.Step (bordismComp (bordismComp f g) h) (bordismComp f (bordismComp g h)) := by
  simpa [bordismComp] using Path.Step.trans_assoc f g h

/-- Cancellation `p⁻¹ · p` as a primitive rewrite step. -/
theorem bordism_cancel_step {n : Nat} {X Y : BordismObj n}
    (p : Path X Y) :
    Path.Step (bordismComp (Path.symm p) p) (bordismId Y) := by
  simpa [bordismComp, bordismId] using Path.Step.symm_trans p

/-- Left unit as rewrite equivalence. -/
theorem bordism_id_left_rweq {n : Nat} {X Y : BordismObj n}
    (p : Path X Y) :
    RwEq (bordismComp (bordismId X) p) p :=
  rweq_of_step (bordism_id_left_step (p := p))

/-- Right unit as rewrite equivalence. -/
theorem bordism_id_right_rweq {n : Nat} {X Y : BordismObj n}
    (p : Path X Y) :
    RwEq (bordismComp p (bordismId Y)) p :=
  rweq_of_step (bordism_id_right_step (p := p))

/-- Associativity as rewrite equivalence. -/
theorem bordism_assoc_rweq {n : Nat}
    {W X Y Z : BordismObj n}
    (f : Path W X) (g : Path X Y) (h : Path Y Z) :
    RwEq (bordismComp (bordismComp f g) h) (bordismComp f (bordismComp g h)) :=
  rweq_of_step (bordism_assoc_step f g h)

/-- Inverse cancellation as rewrite equivalence. -/
theorem bordism_cancel_rweq {n : Nat} {X Y : BordismObj n}
    (p : Path X Y) :
    RwEq (bordismComp (Path.symm p) p) (bordismId Y) :=
  rweq_of_step (bordism_cancel_step (p := p))

/-- Canonical bordism category with morphisms as computational paths. -/
def bordismPathCategory (n : Nat) : BordismPathCategory where
  Obj := BordismObj n
  id := bordismId
  comp := fun f g => bordismComp f g
  id_left := fun f => bordism_id_left_rweq (p := f)
  id_right := fun f => bordism_id_right_rweq (p := f)
  assoc := fun f g h => bordism_assoc_rweq f g h

end Cobordism
end ComputationalPaths
