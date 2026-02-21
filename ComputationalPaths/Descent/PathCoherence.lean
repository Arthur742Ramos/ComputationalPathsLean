/- 
# Descent path coherence via computational paths

This module packages effective descent data and faithfully flat descent in a
path-preserving form. Coherence is expressed with `RwEq` so descent
compatibilities normalize by explicit rewriting.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Descent
namespace PathCoherence

open Path

universe u v w

/-- A map that preserves computational paths and rewrite equivalence. -/
structure PathPreservingMap (A : Type u) (B : Type v) where
  toFun : A → B
  mapPath : {a a' : A} → Path a a' → Path (toFun a) (toFun a')
  map_rweq :
    {a a' : A} → {p q : Path a a'} →
    RwEq p q → RwEq (mapPath p) (mapPath q)
  map_refl :
    (a : A) → RwEq (mapPath (Path.refl a)) (Path.refl (toFun a))
  map_trans :
    {a b c : A} → (p : Path a b) → (q : Path b c) →
    RwEq (mapPath (Path.trans p q))
         (Path.trans (mapPath p) (mapPath q))

/-- Effective descent data with path-valued transitions and gluing coherence. -/
structure EffectiveDescentData (Idx : Type u) (Obj : Type v) where
  localObj : Idx → Obj
  transition : {i j : Idx} → Path i j → Path (localObj i) (localObj j)
  transition_refl :
    (i : Idx) → RwEq (transition (Path.refl i)) (Path.refl (localObj i))
  transition_trans :
    {i j k : Idx} → (p : Path i j) → (q : Path j k) →
    RwEq (transition (Path.trans p q))
         (Path.trans (transition p) (transition q))
  glued : Obj
  glue : (i : Idx) → Path glued (localObj i)
  glue_compat :
    {i j : Idx} → (p : Path i j) →
    RwEq (Path.trans (glue i) (transition p)) (glue j)

namespace EffectiveDescentData

variable {Idx : Type u} {Obj : Type v} (D : EffectiveDescentData Idx Obj)

/-- Left-unit coherence for transition composition. -/
noncomputable def transition_left_unit {i j : Idx} (p : Path i j) :
    RwEq (Path.trans (D.transition (Path.refl i)) (D.transition p))
         (D.transition p) := by
  exact rweq_trans
    (rweq_trans_congr_left (D.transition p) (D.transition_refl i))
    (rweq_cmpA_refl_left (D.transition p))

/-- Right-unit coherence for transition composition. -/
noncomputable def transition_right_unit {i j : Idx} (p : Path i j) :
    RwEq (Path.trans (D.transition p) (D.transition (Path.refl j)))
         (D.transition p) := by
  exact rweq_trans
    (rweq_trans_congr_right (D.transition p) (D.transition_refl j))
    (rweq_cmpA_refl_right (D.transition p))

/-- Associativity coherence for transition composition. -/
noncomputable def transition_assoc {i j k l : Idx}
    (p : Path i j) (q : Path j k) (r : Path k l) :
    RwEq
      (Path.trans (Path.trans (D.transition p) (D.transition q)) (D.transition r))
      (Path.trans (D.transition p) (Path.trans (D.transition q) (D.transition r))) :=
  rweq_of_step (Step.trans_assoc (D.transition p) (D.transition q) (D.transition r))

end EffectiveDescentData

namespace PathPreservingMap

variable {A : Type u} {B : Type v} {Idx : Type w}

/-- Push effective descent data forward along a path-preserving map. -/
def mapEffectiveDescent (F : PathPreservingMap A B)
    (D : EffectiveDescentData Idx A) :
    EffectiveDescentData Idx B where
  localObj := fun i => F.toFun (D.localObj i)
  transition := fun {i j} p => F.mapPath (D.transition p)
  transition_refl := by
    intro i
    exact rweq_trans
      (F.map_rweq (D.transition_refl i))
      (F.map_refl (D.localObj i))
  transition_trans := by
    intro i j k p q
    exact rweq_trans
      (F.map_rweq (D.transition_trans p q))
      (F.map_trans (D.transition p) (D.transition q))
  glued := F.toFun D.glued
  glue := fun i => F.mapPath (D.glue i)
  glue_compat := by
    intro i j p
    exact rweq_trans
      (rweq_symm (F.map_trans (D.glue i) (D.transition p)))
      (F.map_rweq (D.glue_compat p))

/-- The mapped descent datum still satisfies gluing coherence. -/
noncomputable def mapEffectiveDescent_glue_compat
    (F : PathPreservingMap A B) (D : EffectiveDescentData Idx A)
    {i j : Idx} (p : Path i j) :
    RwEq
      (Path.trans ((mapEffectiveDescent F D).glue i)
                  ((mapEffectiveDescent F D).transition p))
      ((mapEffectiveDescent F D).glue j) :=
  (mapEffectiveDescent F D).glue_compat p

end PathPreservingMap

/-- Faithfully flat descent map with path reflection of rewrite-equivalence. -/
structure FaithfullyFlatDescent (A : Type u) (B : Type v)
    extends PathPreservingMap A B where
  witness : B → A
  section_path : (b : B) → Path (toFun (witness b)) b
  faithful :
    {a a' : A} → (p q : Path a a') →
    RwEq (mapPath p) (mapPath q) → RwEq p q

namespace FaithfullyFlatDescent

variable {A : Type u} {B : Type v} {Idx : Type w}

/-- Effective descent data induced by a faithfully flat path-preserving map. -/
def mapEffectiveDescent (ff : FaithfullyFlatDescent A B)
    (D : EffectiveDescentData Idx A) :
    EffectiveDescentData Idx B :=
  PathPreservingMap.mapEffectiveDescent ff.toPathPreservingMap D

/-- Faithfulness reflects rewrite-equivalent descent transitions. -/
noncomputable def reflect_transition_rweq (ff : FaithfullyFlatDescent A B)
    (D : EffectiveDescentData Idx A) {i j : Idx}
    (p q : Path i j) :
    RwEq (ff.mapPath (D.transition p)) (ff.mapPath (D.transition q)) →
      RwEq (D.transition p) (D.transition q) :=
  ff.faithful (D.transition p) (D.transition q)

/-- Section paths contract with their inverses by rewrite normalization. -/
noncomputable def section_path_cancel (ff : FaithfullyFlatDescent A B) (b : B) :
    RwEq (Path.trans (ff.section_path b) (Path.symm (ff.section_path b)))
         (Path.refl (ff.toFun (ff.witness b))) :=
  rweq_cmpA_inv_right (ff.section_path b)

end FaithfullyFlatDescent

end PathCoherence
end Descent
end ComputationalPaths
