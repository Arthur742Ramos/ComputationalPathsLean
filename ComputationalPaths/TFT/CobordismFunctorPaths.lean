import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Topological field theory paths: cobordism functors

This module provides a compact cobordism-category interface and functors
between such categories, with explicit Step-based path chains for
functoriality coherence.
-/

namespace ComputationalPaths
namespace TFT
namespace CobordismFunctorPaths

open Path

universe u₁ v₁ u₂ v₂

/-- A lightweight cobordism category for TFT path infrastructure. -/
structure CobordismCategory where
  Obj : Type u₁
  Hom : Obj → Obj → Type v₁
  id : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  assoc : {W X Y Z : Obj} → (f : Hom W X) → (g : Hom X Y) → (h : Hom Y Z) →
    Path (comp (comp f g) h) (comp f (comp g h))
  left_id : {X Y : Obj} → (f : Hom X Y) → Path (comp (id X) f) f
  right_id : {X Y : Obj} → (f : Hom X Y) → Path (comp f (id Y)) f

/-- Cobordism functor data with path-level preservation of identities and gluing. -/
structure CobordismFunctor (C : CobordismCategory.{u₁, v₁})
    (D : CobordismCategory.{u₂, v₂}) where
  objMap : C.Obj → D.Obj
  morMap : {X Y : C.Obj} → C.Hom X Y → D.Hom (objMap X) (objMap Y)
  map_id : (X : C.Obj) → Path (morMap (C.id X)) (D.id (objMap X))
  map_comp : {X Y Z : C.Obj} → (f : C.Hom X Y) → (g : C.Hom Y Z) →
    Path (morMap (C.comp f g)) (D.comp (morMap f) (morMap g))

namespace CobordismFunctor

variable {C : CobordismCategory.{u₁, v₁}} {D : CobordismCategory.{u₂, v₂}}
variable (F : CobordismFunctor C D)

/-- Step witness: right-unit normalization for mapped identities. -/
def mapId_step (X : C.Obj) :
    Path.Step
      (Path.trans (F.map_id X) (Path.refl (D.id (F.objMap X))))
      (F.map_id X) :=
  Path.Step.trans_refl_right (F.map_id X)

noncomputable def mapId_rweq (X : C.Obj) :
    RwEq
      (Path.trans (F.map_id X) (Path.refl (D.id (F.objMap X))))
      (F.map_id X) :=
  rweq_of_step (F.mapId_step X)

/-- Middle leg in the functorial gluing coherence chain. -/
def mapCompMiddle {W X Y Z : C.Obj}
    (f : C.Hom W X) (g : C.Hom X Y) (h : C.Hom Y Z) :
    Path
      (D.comp (F.morMap (C.comp f g)) (F.morMap h))
      (D.comp (D.comp (F.morMap f) (F.morMap g)) (F.morMap h)) :=
  Path.congrArg (fun t => D.comp t (F.morMap h)) (F.map_comp f g)

/-- Final leg in the functorial gluing coherence chain. -/
def mapCompLast {W X Y Z : C.Obj}
    (f : C.Hom W X) (g : C.Hom X Y) (h : C.Hom Y Z) :
    Path
      (D.comp (D.comp (F.morMap f) (F.morMap g)) (F.morMap h))
      (D.comp (F.morMap f) (D.comp (F.morMap g) (F.morMap h))) :=
  D.assoc (F.morMap f) (F.morMap g) (F.morMap h)

/-- Left-associated threefold coherence chain for mapped composition. -/
def mapCompChainLeft {W X Y Z : C.Obj}
    (f : C.Hom W X) (g : C.Hom X Y) (h : C.Hom Y Z) :
    Path
      (F.morMap (C.comp (C.comp f g) h))
      (D.comp (F.morMap f) (D.comp (F.morMap g) (F.morMap h))) :=
  Path.trans
    (Path.trans (F.map_comp (C.comp f g) h) (F.mapCompMiddle f g h))
    (F.mapCompLast f g h)

/-- Right-associated threefold coherence chain for mapped composition. -/
def mapCompChainRight {W X Y Z : C.Obj}
    (f : C.Hom W X) (g : C.Hom X Y) (h : C.Hom Y Z) :
    Path
      (F.morMap (C.comp (C.comp f g) h))
      (D.comp (F.morMap f) (D.comp (F.morMap g) (F.morMap h))) :=
  Path.trans
    (F.map_comp (C.comp f g) h)
    (Path.trans (F.mapCompMiddle f g h) (F.mapCompLast f g h))

/-- Associativity of the coherence chain as a primitive Step witness. -/
theorem mapComp_assoc_step {W X Y Z : C.Obj}
    (f : C.Hom W X) (g : C.Hom X Y) (h : C.Hom Y Z) :
    Path.Step (F.mapCompChainLeft f g h) (F.mapCompChainRight f g h) := by
  simpa [mapCompChainLeft, mapCompChainRight] using
    (Path.Step.trans_assoc
      (F.map_comp (C.comp f g) h)
      (F.mapCompMiddle f g h)
      (F.mapCompLast f g h))

/-- Rewrite-equivalence form of functorial coherence associativity. -/
noncomputable def mapComp_assoc_rweq {W X Y Z : C.Obj}
    (f : C.Hom W X) (g : C.Hom X Y) (h : C.Hom Y Z) :
    RwEq (F.mapCompChainLeft f g h) (F.mapCompChainRight f g h) :=
  rweq_of_step (F.mapComp_assoc_step f g h)

noncomputable def mapComp_cancel_rweq {W X Y Z : C.Obj}
    (f : C.Hom W X) (g : C.Hom X Y) (h : C.Hom Y Z) :
    RwEq
      (Path.trans (Path.symm (F.mapCompChainRight f g h)) (F.mapCompChainRight f g h))
      (Path.refl (D.comp (F.morMap f) (D.comp (F.morMap g) (F.morMap h)))) :=
  rweq_cmpA_inv_left (F.mapCompChainRight f g h)

end CobordismFunctor

end CobordismFunctorPaths
end TFT
end ComputationalPaths
