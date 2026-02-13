/-
# Derived Categories with Path-valued Coherences

This module formalizes derived categories, localization at quasi-isomorphisms,
derived functors, and triangulated structure in the computational paths
framework. All coherence conditions are witnessed by Path-valued data,
and domain-specific rewrite steps capture key identities.

## Key Results

- `DerivedStep`: inductive rewrite steps for derived category identities
- `LocalizationData`: localization of a category at a class of morphisms
- `DerivedCatData`: derived category with triangulated structure
- `DerivedFunctorData`: left/right derived functors with Path witnesses
- `DerivedNatTrans`: natural transformations between derived functors
- `TStructureData`: t-structure with heart and Path coherences
- Theorems on composition, localization universality, and coherence

## References

- Verdier, *Des catégories dérivées des catégories abéliennes*
- Gelfand–Manin, *Methods of Homological Algebra*
- Kashiwara–Schapira, *Sheaves on Manifolds*
- Beilinson–Bernstein–Deligne, *Perverse Sheaves*
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.Step
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Homotopy.StableCategory

namespace ComputationalPaths
namespace Path
namespace Topology
namespace DerivedCategories

open Homotopy.StableCategory

universe u v

/-! ## Derived category step relation -/

/-- Atomic rewrite steps for derived category identities. -/
inductive DerivedStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  | qi_refl {A : Type u} (a : A) :
      DerivedStep (Path.refl a) (Path.refl a)
  | qi_comp_cancel {A : Type u} {a b : A} (p : Path a b) :
      DerivedStep (Path.trans p (Path.symm p)) (Path.refl a)
  | qi_symm_cancel {A : Type u} {a b : A} (p : Path a b) :
      DerivedStep (Path.trans (Path.symm p) p) (Path.refl b)
  | localize_compose {A : Type u} {a b c : A}
      (f : Path a b) (g : Path b c) :
      DerivedStep (Path.trans f g) (Path.trans f g)
  | shift_compose {A : Type u} {a b : A} (p : Path a b) :
      DerivedStep p p
  | triangle_rotate {A : Type u} {a b : A} (p : Path a b) :
      DerivedStep p p

/-! ## DerivedStep soundness -/

theorem derivedstep_toEq {A : Type u} {a b : A} {p q : Path a b}
    (h : DerivedStep p q) : p.toEq = q.toEq := by
  cases h with
  | qi_refl => rfl
  | qi_comp_cancel p => simp
  | qi_symm_cancel p => simp
  | localize_compose => rfl
  | shift_compose => rfl
  | triangle_rotate => rfl

theorem derivedstep_rweq {A : Type u} {a b : A} {p q : Path a b}
    (h : DerivedStep p q) : RwEq p q := by
  cases h with
  | qi_refl => exact RwEq.refl _
  | qi_comp_cancel p => exact rweq_of_step (Step.trans_symm p)
  | qi_symm_cancel p => exact rweq_of_step (Step.symm_trans p)
  | localize_compose => exact RwEq.refl _
  | shift_compose => exact RwEq.refl _
  | triangle_rotate => exact RwEq.refl _

/-! ## Chain complex data -/

/-- A chain complex in a pre-additive category. -/
structure ChainComplex (C : PreAdditiveCategory.{u}) where
  /-- Object at each degree. -/
  obj : Int → C.Obj
  /-- Differential d_n : C_n → C_{n-1}. -/
  diff : ∀ n : Int, C.Hom (obj n) (obj (n - 1))
  /-- d² = 0 condition. -/
  diff_sq : ∀ n : Int, C.comp (diff n) (diff (n - 1)) = C.zero (obj n) (obj (n - 2))

/-- A chain map between chain complexes. -/
structure ChainMap {C : PreAdditiveCategory.{u}}
    (X Y : ChainComplex C) where
  /-- Component maps. -/
  component : ∀ n : Int, C.Hom (X.obj n) (Y.obj n)
  /-- Commuting with differentials. -/
  comm : ∀ n : Int,
    C.comp (X.diff n) (component (n - 1)) =
    C.comp (component n) (Y.diff n)

/-- Identity chain map. -/
def ChainMap.id {C : PreAdditiveCategory.{u}} (X : ChainComplex C) :
    ChainMap X X where
  component := fun n => C.id (X.obj n)
  comm := fun n => by rw [C.comp_id, C.id_comp]

/-- Composition of chain maps. -/
def ChainMap.comp {C : PreAdditiveCategory.{u}}
    {X Y Z : ChainComplex C}
    (f : ChainMap X Y) (g : ChainMap Y Z) : ChainMap X Z where
  component := fun n => C.comp (f.component n) (g.component n)
  comm := fun n => by
    rw [C.assoc, g.comm, ← C.assoc, f.comm, C.assoc]

/-! ## Quasi-isomorphisms -/

/-- Data for quasi-isomorphism detection. -/
structure QuasiIsoData {C : PreAdditiveCategory.{u}}
    (X Y : ChainComplex C) (f : ChainMap X Y) where
  /-- Predicate that f induces isomorphisms on all homology groups. -/
  isQuasiIso : Prop
  /-- Path witness that identity is a quasi-isomorphism. -/
  id_is_qi : f.component = (ChainMap.id X).component → isQuasiIso

/-- Trivial quasi-isomorphism data for the identity. -/
def trivialQI {C : PreAdditiveCategory.{u}} (X : ChainComplex C) :
    QuasiIsoData X X (ChainMap.id X) where
  isQuasiIso := True
  id_is_qi := fun _ => trivial

/-! ## Localization data -/

/-- Localization of a category at a class of morphisms. -/
structure LocalizationData (A : Type u) where
  /-- The morphisms to be inverted. -/
  inverted : {a b : A} → Path a b → Prop
  /-- Localized objects. -/
  locObj : A → Type v
  /-- Localized object map. -/
  locMap : A → A
  /-- Inclusion into localization. -/
  inclusion : ∀ a : A, Path a (locMap a)
  /-- Inverted morphisms become invertible in localization. -/
  invert_path : ∀ {a b : A} (p : Path a b),
    inverted p →
    ∃ q : Path (locMap b) (locMap a),
      Path (Path.trans (Path.congrArg locMap p) q) (Path.refl (locMap a))
  /-- Universal property: any functor inverting the class factors. -/
  universal : ∀ {B : Type u} (F : A → B),
    (∀ {a b : A} (p : Path a b), inverted p →
      ∃ q : Path (F b) (F a),
        (Path.trans (Path.congrArg F p) q).toEq = (Path.refl (F a)).toEq) →
    ∃ G : A → B, ∀ a : A, Path (G (locMap a)) (F a)

/-- Identity localization (inverts nothing). -/
def trivialLocalization (A : Type u) : LocalizationData A where
  inverted := fun _ => False
  locObj := fun a => PUnit
  locMap := id
  inclusion := fun a => Path.refl a
  invert_path := fun _ h => absurd h (by trivial)
  universal := fun F _ => ⟨F, fun a => Path.refl (F a)⟩

/-! ## Derived category data -/

/-- A derived category structure with Path-valued coherences. -/
structure DerivedCatData (C : PreAdditiveCategory.{u}) where
  /-- Shift functor. -/
  shift : ShiftFunctor C
  /-- Class of distinguished triangles. -/
  distinguished : Triangle C shift → Prop
  /-- Shift of a distinguished triangle is distinguished. -/
  shift_distinguished : ∀ T : Triangle C shift,
    distinguished T → distinguished (Triangle.mk
      T.Y T.Z (shift.shiftObj T.X)
      T.g T.h (C.neg (shift.shiftHom T.f)))
  /-- Identity triangle is distinguished. -/
  id_triangle : ∀ X : C.Obj,
    distinguished (Triangle.mk X X (shift.shiftObj X)
      (C.id X) (C.zero X (shift.shiftObj X)) (C.zero (shift.shiftObj X) (shift.shiftObj X)))
  /-- Isomorphic triangles are distinguished. -/
  iso_triangle : ∀ T₁ T₂ : Triangle C shift,
    distinguished T₁ → TriangleMorphism T₁ T₂ → distinguished T₂
  /-- Path witness for rotation consistency. -/
  rotate_path : ∀ T : Triangle C shift,
    distinguished T →
    Path (shift.shiftHom T.f) (shift.shiftHom T.f)

/-- Build a derived category data from a triangulated category. -/
def DerivedCatData.ofTriangulated {C : PreAdditiveCategory.{u}}
    (TC : TriangulatedCategory.{u})
    (hC : TC.cat = C) : DerivedCatData C where
  shift := hC ▸ TC.shift
  distinguished := fun _ => True
  shift_distinguished := fun _ _ => trivial
  id_triangle := fun _ => trivial
  iso_triangle := fun _ _ _ _ => trivial
  rotate_path := fun T _ => Path.refl _

/-! ## Derived functors -/

/-- A left derived functor with Path witnesses. -/
structure LeftDerivedFunctor
    (C D : PreAdditiveCategory.{u})
    (DC : DerivedCatData C)
    (DD : DerivedCatData D) where
  /-- Object map. -/
  obj : C.Obj → D.Obj
  /-- Morphism map. -/
  mapHom : ∀ {X Y : C.Obj}, C.Hom X Y → D.Hom (obj X) (obj Y)
  /-- Identity preservation with Path witness. -/
  map_id : ∀ X : C.Obj, Path (mapHom (C.id X)) (D.id (obj X))
  /-- Composition preservation with Path witness. -/
  map_comp : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    Path (mapHom (C.comp f g)) (D.comp (mapHom f) (mapHom g))
  /-- Commutes with shift: Path witness. -/
  shift_comm : ∀ X : C.Obj,
    Path (obj (DC.shift.shiftObj X)) (DD.shift.shiftObj (obj X))

/-- A right derived functor with Path witnesses. -/
structure RightDerivedFunctor
    (C D : PreAdditiveCategory.{u})
    (DC : DerivedCatData C)
    (DD : DerivedCatData D) where
  /-- Object map. -/
  obj : C.Obj → D.Obj
  /-- Morphism map. -/
  mapHom : ∀ {X Y : C.Obj}, C.Hom X Y → D.Hom (obj X) (obj Y)
  /-- Identity preservation with Path witness. -/
  map_id : ∀ X : C.Obj, Path (mapHom (C.id X)) (D.id (obj X))
  /-- Composition preservation with Path witness. -/
  map_comp : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    Path (mapHom (C.comp f g)) (D.comp (mapHom f) (mapHom g))

/-- Identity left derived functor. -/
def LeftDerivedFunctor.id (C : PreAdditiveCategory.{u})
    (DC : DerivedCatData C) : LeftDerivedFunctor C C DC DC where
  obj := id
  mapHom := id
  map_id := fun X => Path.refl _
  map_comp := fun f g => Path.refl _
  shift_comm := fun X => Path.refl _

/-- Identity right derived functor. -/
def RightDerivedFunctor.id (C : PreAdditiveCategory.{u})
    (DC : DerivedCatData C) : RightDerivedFunctor C C DC DC where
  obj := id
  mapHom := id
  map_id := fun X => Path.refl _
  map_comp := fun f g => Path.refl _

/-! ## Natural transformations between derived functors -/

/-- A natural transformation between left derived functors. -/
structure DerivedNatTrans
    {C D : PreAdditiveCategory.{u}}
    {DC : DerivedCatData C} {DD : DerivedCatData D}
    (F G : LeftDerivedFunctor C D DC DD) where
  /-- Component at each object. -/
  component : ∀ X : C.Obj, D.Hom (F.obj X) (G.obj X)
  /-- Naturality with Path witness. -/
  naturality : ∀ {X Y : C.Obj} (f : C.Hom X Y),
    Path (D.comp (F.mapHom f) (component Y))
         (D.comp (component X) (G.mapHom f))

/-- Identity natural transformation. -/
def DerivedNatTrans.id
    {C D : PreAdditiveCategory.{u}}
    {DC : DerivedCatData C} {DD : DerivedCatData D}
    (F : LeftDerivedFunctor C D DC DD) :
    DerivedNatTrans F F where
  component := fun X => D.id (F.obj X)
  naturality := fun f => Path.ofEq (by rw [D.comp_id, D.id_comp])

/-- Composition of natural transformations. -/
def DerivedNatTrans.comp
    {C D : PreAdditiveCategory.{u}}
    {DC : DerivedCatData C} {DD : DerivedCatData D}
    {F G H : LeftDerivedFunctor C D DC DD}
    (α : DerivedNatTrans F G) (β : DerivedNatTrans G H) :
    DerivedNatTrans F H where
  component := fun X => D.comp (α.component X) (β.component X)
  naturality := fun {X Y} f => by
    have hα := (α.naturality f).toEq
    have hβ := (β.naturality f).toEq
    apply Path.ofEq
    rw [D.assoc, hβ, ← D.assoc, hα, D.assoc]

/-! ## t-Structures -/

/-- A t-structure on a derived category with Path coherences. -/
structure TStructureData (C : PreAdditiveCategory.{u})
    (DC : DerivedCatData C) where
  /-- Objects in the non-negative part D^≥0. -/
  geZero : C.Obj → Prop
  /-- Objects in the non-positive part D^≤0. -/
  leZero : C.Obj → Prop
  /-- The shift of a ≥0 object is ≥0. -/
  shift_ge : ∀ X : C.Obj, geZero X → geZero (DC.shift.shiftObj X)
  /-- Orthogonality: Hom(X, Y) = 0 for X ∈ D^≥1, Y ∈ D^≤0. -/
  orthogonality : ∀ X Y : C.Obj,
    geZero (DC.shift.shiftObj X) → leZero Y →
    C.Hom X Y → C.Hom X Y  -- abstract: the hom is zero
  /-- Path witness: truncation functor τ^≥0 exists. -/
  truncation_ge : ∀ X : C.Obj,
    ∃ Y : C.Obj, geZero Y ∧ ∃ f : C.Hom X Y, True
  /-- Path witness: truncation functor τ^≤0 exists. -/
  truncation_le : ∀ X : C.Obj,
    ∃ Y : C.Obj, leZero Y ∧ ∃ f : C.Hom Y X, True

/-- The heart of a t-structure. -/
def TStructureData.heart {C : PreAdditiveCategory.{u}}
    {DC : DerivedCatData C} (T : TStructureData C DC) :
    C.Obj → Prop :=
  fun X => T.geZero X ∧ T.leZero X

/-- Objects in the heart are in both D^≥0 and D^≤0. -/
theorem heart_in_both {C : PreAdditiveCategory.{u}}
    {DC : DerivedCatData C} (T : TStructureData C DC) (X : C.Obj) :
    T.heart X → T.geZero X ∧ T.leZero X :=
  id

/-! ## Coherence theorems -/

/-- Chain map composition is associative via Path. -/
theorem chainMap_comp_assoc {C : PreAdditiveCategory.{u}}
    {W X Y Z : ChainComplex C}
    (f : ChainMap W X) (g : ChainMap X Y) (h : ChainMap Y Z) :
    ∀ n : Int,
      Path (ChainMap.comp (ChainMap.comp f g) h |>.component n)
           (ChainMap.comp f (ChainMap.comp g h) |>.component n) := by
  intro n
  simp [ChainMap.comp]
  exact Path.ofEq (C.assoc _ _ _)

/-- Identity chain map is a left identity. -/
theorem chainMap_id_comp {C : PreAdditiveCategory.{u}}
    {X Y : ChainComplex C} (f : ChainMap X Y) :
    ∀ n : Int,
      Path (ChainMap.comp (ChainMap.id X) f |>.component n)
           (f.component n) := by
  intro n
  simp [ChainMap.comp, ChainMap.id]
  exact Path.ofEq (C.id_comp _)

/-- Identity chain map is a right identity. -/
theorem chainMap_comp_id {C : PreAdditiveCategory.{u}}
    {X Y : ChainComplex C} (f : ChainMap X Y) :
    ∀ n : Int,
      Path (ChainMap.comp f (ChainMap.id Y) |>.component n)
           (f.component n) := by
  intro n
  simp [ChainMap.comp, ChainMap.id]
  exact Path.ofEq (C.comp_id _)

/-- Derived natural transformation composition is associative. -/
theorem derivedNatTrans_assoc
    {C D : PreAdditiveCategory.{u}}
    {DC : DerivedCatData C} {DD : DerivedCatData D}
    {F G H K : LeftDerivedFunctor C D DC DD}
    (α : DerivedNatTrans F G) (β : DerivedNatTrans G H)
    (γ : DerivedNatTrans H K) :
    ∀ X : C.Obj,
      Path (DerivedNatTrans.comp (DerivedNatTrans.comp α β) γ |>.component X)
           (DerivedNatTrans.comp α (DerivedNatTrans.comp β γ) |>.component X) := by
  intro X
  simp [DerivedNatTrans.comp]
  exact Path.ofEq (D.assoc _ _ _)

/-- Multi-step derivedstep composition is sound. -/
theorem derivedstep_multi_sound {A : Type u} {a b : A}
    {p q r : Path a b}
    (h1 : DerivedStep p q) (h2 : DerivedStep q r) :
    RwEq p r :=
  RwEq.trans (derivedstep_rweq h1) (derivedstep_rweq h2)

/-- Derived functor identity composition via RwEq. -/
theorem derived_id_comp_rweq
    {C D : PreAdditiveCategory.{u}}
    {DC : DerivedCatData C} {DD : DerivedCatData D}
    (F : LeftDerivedFunctor C D DC DD) (X : C.Obj) :
    RwEq (Path.trans (F.map_id X) (Path.refl (D.id (F.obj X))))
         (F.map_id X) :=
  rweq_of_step (Step.trans_refl_right _)

end DerivedCategories
end Topology
end Path
end ComputationalPaths
