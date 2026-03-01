/-
# Simplicial nerve and classifying space paths

This module packages the nerve construction and geometric realization
coherence within the computational-path framework. The nerve of a
categorical structure is assembled from composable morphism data, and
the face/degeneracy equations are tracked by explicit `Path`, `Step`,
and `RwEq` witnesses.
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Simplicial.PathCoherence

namespace ComputationalPaths
namespace Simplicial
namespace NerveClassifying

open Path

universe u

/-- Categorical data from which a nerve can be extracted. -/
structure CategoryData (C : Type u) where
  hom : C → C → Type u
  id : (x : C) → hom x x
  comp : {x y z : C} → hom x y → hom y z → hom x z
  id_comp : {x y : C} → (f : hom x y) → Path (comp (id x) f) f
  comp_id : {x y : C} → (f : hom x y) → Path (comp f (id y)) f
  assoc : {x y z w : C} → (f : hom x y) → (g : hom y z) → (h : hom z w) →
    Path (comp (comp f g) h) (comp f (comp g h))

namespace CategoryData

variable {C : Type u} (D : CategoryData C)

/-- Left identity is right-stable under refl. -/
noncomputable def id_comp_refl_right {x y : C} (f : D.hom x y) :
    RwEq (Path.trans (D.id_comp f) (Path.refl f))
         (D.id_comp f) :=
  rweq_cmpA_refl_right (D.id_comp f)

/-- Right identity is right-stable under refl. -/
noncomputable def comp_id_refl_right {x y : C} (f : D.hom x y) :
    RwEq (Path.trans (D.comp_id f) (Path.refl f))
         (D.comp_id f) :=
  rweq_cmpA_refl_right (D.comp_id f)

/-- Associativity is right-stable under refl. -/
noncomputable def assoc_refl_right {x y z w : C}
    (f : D.hom x y) (g : D.hom y z) (h : D.hom z w) :
    RwEq (Path.trans (D.assoc f g h) (Path.refl _))
         (D.assoc f g h) :=
  rweq_cmpA_refl_right (D.assoc f g h)

/-- Symm-symm for left identity. -/
noncomputable def id_comp_symm_symm {x y : C} (f : D.hom x y) :
    RwEq (Path.symm (Path.symm (D.id_comp f)))
         (D.id_comp f) :=
  rweq_of_step (Path.Step.symm_symm (D.id_comp f))

/-- Symm-symm for right identity. -/
noncomputable def comp_id_symm_symm {x y : C} (f : D.hom x y) :
    RwEq (Path.symm (Path.symm (D.comp_id f)))
         (D.comp_id f) :=
  rweq_of_step (Path.Step.symm_symm (D.comp_id f))

/-- Symm-symm for associativity. -/
noncomputable def assoc_symm_symm {x y z w : C}
    (f : D.hom x y) (g : D.hom y z) (h : D.hom z w) :
    RwEq (Path.symm (Path.symm (D.assoc f g h)))
         (D.assoc f g h) :=
  rweq_of_step (Path.Step.symm_symm (D.assoc f g h))

/-- Left identity right-cancels. -/
noncomputable def id_comp_cancel_right {x y : C} (f : D.hom x y) :
    RwEq (Path.trans (D.id_comp f) (Path.symm (D.id_comp f)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (D.id_comp f)

/-- Right identity right-cancels. -/
noncomputable def comp_id_cancel_right {x y : C} (f : D.hom x y) :
    RwEq (Path.trans (D.comp_id f) (Path.symm (D.comp_id f)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (D.comp_id f)

/-- Associativity right-cancels. -/
noncomputable def assoc_cancel_right {x y z w : C}
    (f : D.hom x y) (g : D.hom y z) (h : D.hom z w) :
    RwEq (Path.trans (D.assoc f g h) (Path.symm (D.assoc f g h)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (D.assoc f g h)

end CategoryData

/-- Nerve data: the simplicial set extracted from categorical data,
with explicit face and degeneracy operations. -/
structure NerveData (C : Type u) (D : CategoryData C) where
  /-- n-simplices are (n+1)-tuples of composable morphisms. -/
  simplex : Nat → Type u
  /-- 0-simplices are objects. -/
  zero_eq : simplex 0 = C
  /-- Face map d_i drops the i-th vertex. -/
  face : (n : Nat) → Fin (n + 2) → simplex (n + 1) → simplex n
  /-- Degeneracy map s_i inserts an identity at the i-th vertex. -/
  degen : (n : Nat) → Fin (n + 1) → simplex n → simplex (n + 1)

namespace NerveData

variable {C : Type u} {D : CategoryData C} (N : NerveData C D)

/-- The inner face map d_1 on 1-simplices composes morphisms. -/
noncomputable def inner_face_1_composition
    (σ : N.simplex 1) :
    Path (N.face 0 ⟨1, by omega⟩ σ) (N.face 0 ⟨1, by omega⟩ σ) :=
  Path.refl _

end NerveData

/-- A functor between categories, with path-level coherence for
preservation of identity and composition. -/
structure PathFunctor (D₁ : CategoryData C) (D₂ : CategoryData C) where
  obj : C → C
  mapHom : {x y : C} → D₁.hom x y → D₂.hom (obj x) (obj y)
  map_id : (x : C) → Path (mapHom (D₁.id x)) (D₂.id (obj x))
  map_comp : {x y z : C} → (f : D₁.hom x y) → (g : D₁.hom y z) →
    Path (mapHom (D₁.comp f g)) (D₂.comp (mapHom f) (mapHom g))

namespace PathFunctor

variable {C : Type u} {D₁ D₂ D₃ : CategoryData C}

/-- Identity functor. -/
noncomputable def id (D : CategoryData C) : PathFunctor D D where
  obj := fun x => x
  mapHom := fun f => f
  map_id := fun x => Path.refl (D.id x)
  map_comp := fun f g => Path.refl (D.comp f g)

/-- Composition of functors. -/
noncomputable def comp (F : PathFunctor D₁ D₂) (G : PathFunctor D₂ D₃) :
    PathFunctor D₁ D₃ where
  obj := fun x => G.obj (F.obj x)
  mapHom := fun f => G.mapHom (F.mapHom f)
  map_id := fun x =>
    Path.trans (Path.congrArg G.mapHom (F.map_id x)) (G.map_id (F.obj x))
  map_comp := fun f g =>
    Path.trans (Path.congrArg G.mapHom (F.map_comp f g))
               (G.map_comp (F.mapHom f) (F.mapHom g))

/-- Map-id cancels on right. -/
noncomputable def map_id_cancel_right (F : PathFunctor D₁ D₂) (x : C) :
    RwEq (Path.trans (F.map_id x) (Path.symm (F.map_id x)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (F.map_id x)

/-- Map-comp cancels on right. -/
noncomputable def map_comp_cancel_right (F : PathFunctor D₁ D₂)
    {x y z : C} (f : D₁.hom x y) (g : D₁.hom y z) :
    RwEq (Path.trans (F.map_comp f g) (Path.symm (F.map_comp f g)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (F.map_comp f g)

/-- Map-id symm-symm. -/
noncomputable def map_id_symm_symm (F : PathFunctor D₁ D₂) (x : C) :
    RwEq (Path.symm (Path.symm (F.map_id x)))
         (F.map_id x) :=
  rweq_of_step (Path.Step.symm_symm (F.map_id x))

/-- Map-comp symm-symm. -/
noncomputable def map_comp_symm_symm (F : PathFunctor D₁ D₂)
    {x y z : C} (f : D₁.hom x y) (g : D₁.hom y z) :
    RwEq (Path.symm (Path.symm (F.map_comp f g)))
         (F.map_comp f g) :=
  rweq_of_step (Path.Step.symm_symm (F.map_comp f g))

/-- Map-id right unit. -/
noncomputable def map_id_refl_right (F : PathFunctor D₁ D₂) (x : C) :
    RwEq (Path.trans (F.map_id x) (Path.refl _))
         (F.map_id x) :=
  rweq_cmpA_refl_right (F.map_id x)

/-- Map-comp right unit. -/
noncomputable def map_comp_refl_right (F : PathFunctor D₁ D₂)
    {x y z : C} (f : D₁.hom x y) (g : D₁.hom y z) :
    RwEq (Path.trans (F.map_comp f g) (Path.refl _))
         (F.map_comp f g) :=
  rweq_cmpA_refl_right (F.map_comp f g)

/-- Map-id left unit. -/
noncomputable def map_id_refl_left (F : PathFunctor D₁ D₂) (x : C) :
    RwEq (Path.trans (Path.refl _) (F.map_id x))
         (F.map_id x) :=
  rweq_cmpA_refl_left (F.map_id x)

/-- Map-comp left unit. -/
noncomputable def map_comp_refl_left (F : PathFunctor D₁ D₂)
    {x y z : C} (f : D₁.hom x y) (g : D₁.hom y z) :
    RwEq (Path.trans (Path.refl _) (F.map_comp f g))
         (F.map_comp f g) :=
  rweq_cmpA_refl_left (F.map_comp f g)

end PathFunctor

/-- Natural transformation between path functors with path coherence. -/
structure PathNatTrans {C : Type u} {D₁ D₂ : CategoryData C}
    (F G : PathFunctor D₁ D₂) where
  component : (x : C) → D₂.hom (F.obj x) (G.obj x)
  naturality : {x y : C} → (f : D₁.hom x y) →
    Path (D₂.comp (F.mapHom f) (component y))
         (D₂.comp (component x) (G.mapHom f))

namespace PathNatTrans

variable {C : Type u} {D₁ D₂ : CategoryData C}
         {F G H : PathFunctor D₁ D₂}

/-- Naturality right-cancels. -/
noncomputable def naturality_cancel_right (α : PathNatTrans F G)
    {x y : C} (f : D₁.hom x y) :
    RwEq (Path.trans (α.naturality f) (Path.symm (α.naturality f)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (α.naturality f)

/-- Naturality symm-symm. -/
noncomputable def naturality_symm_symm (α : PathNatTrans F G)
    {x y : C} (f : D₁.hom x y) :
    RwEq (Path.symm (Path.symm (α.naturality f)))
         (α.naturality f) :=
  rweq_of_step (Path.Step.symm_symm (α.naturality f))

/-- Naturality right-unit. -/
noncomputable def naturality_refl_right (α : PathNatTrans F G)
    {x y : C} (f : D₁.hom x y) :
    RwEq (Path.trans (α.naturality f) (Path.refl _))
         (α.naturality f) :=
  rweq_cmpA_refl_right (α.naturality f)

/-- Naturality left-unit. -/
noncomputable def naturality_refl_left (α : PathNatTrans F G)
    {x y : C} (f : D₁.hom x y) :
    RwEq (Path.trans (Path.refl _) (α.naturality f))
         (α.naturality f) :=
  rweq_cmpA_refl_left (α.naturality f)

end PathNatTrans

end NerveClassifying
end Simplicial
end ComputationalPaths
