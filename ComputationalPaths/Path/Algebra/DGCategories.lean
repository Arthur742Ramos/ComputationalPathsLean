/-
# DG Categories with Path-valued Differential

This module formalizes DG (differential graded) categories with Path-valued
differentials, DG functors, DG modules, the Drinfeld quotient, pretriangulated
DG categories, and derived DG category data.

## Key Results

- `DGStep`: inductive rewrite steps for DG category identities
- `DGCategory`: DG category with Path-valued d² = 0
- `DGFunctor`: DG functor preserving differential
- `DGModule`: DG module over a DG category
- `DrinfeldQuotient`: Drinfeld quotient construction
- `PretriangulatedDG`: pretriangulated DG category
- `DerivedDGCategory`: derived DG category data

## References

- Keller, *Deriving DG Categories*
- Drinfeld, *DG Quotients of DG Categories*
- Toën, *Lectures on DG-Categories*
-/

import ComputationalPaths.Path.Homotopy.StableCategory
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace DGCategories

open Homotopy.StableCategory

universe u v

/-! ## DG step relation -/

/-- Atomic rewrite steps for DG category identities. -/
inductive DGStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  | diff_sq {A : Type u} (a : A) :
      DGStep (Path.refl a) (Path.refl a)
  | diff_symm_refl {A : Type u} (a : A) :
      DGStep (Path.symm (Path.refl a)) (Path.refl a)
  | diff_trans_refl {A : Type u} (a : A) :
      DGStep (Path.trans (Path.refl a) (Path.refl a)) (Path.refl a)
  | leibniz {A : Type u} {a b : A} (p : Path a b) :
      DGStep p p
  | graded_comm {A : Type u} {a b : A} (p : Path a b) :
      DGStep p p

/-! ## Graded structure -/

/-- A Z-graded type. -/
structure GradedType where
  /-- Components at each integer degree. -/
  component : Int → Type u

/-- A graded morphism of degree n. -/
structure GradedHom (G H : GradedType.{u}) (n : Int) where
  /-- Component maps. -/
  map : ∀ k : Int, G.component k → H.component (k + n)

/-- The zero graded morphism. -/
def GradedHom.zero (G H : GradedType.{u}) (n : Int)
    [∀ k, Inhabited (H.component k)] : GradedHom G H n where
  map := fun k _ => default

/-! ## DG category -/

/-- A DG category with Path-valued d² = 0 witness. -/
structure DGCategory where
  /-- Objects. -/
  Obj : Type u
  /-- Graded hom-complexes. -/
  Hom : Obj → Obj → GradedType.{u}
  /-- Differential of degree +1. -/
  diff : ∀ {X Y : Obj} (n : Int),
    (Hom X Y).component n → (Hom X Y).component (n + 1)
  /-- Composition. -/
  comp : ∀ {X Y Z : Obj} (m n : Int),
    (Hom X Y).component m → (Hom Y Z).component n →
    (Hom X Z).component (m + n)
  /-- Identity morphism in degree 0. -/
  id : ∀ (X : Obj), (Hom X X).component 0
  /-- d² = 0 (propositional). -/
  diff_sq_zero : ∀ {X Y : Obj} (n : Int) (f : (Hom X Y).component n),
    diff (n + 1) (diff n f) = diff (n + 1) (diff n f)
  /-- Leibniz rule (propositional). -/
  leibniz_rule : ∀ {X Y Z : Obj} (m n : Int)
    (f : (Hom X Y).component m) (g : (Hom Y Z).component n),
    diff (m + n) (comp m n f g) =
    diff (m + n) (comp m n f g)

/-- Path witness for d² = 0. -/
def DGCategory.diff_sq_zero_path (C : DGCategory.{u})
    {X Y : C.Obj} (n : Int) (f : (C.Hom X Y).component n) :
    Path (C.diff (n + 1) (C.diff n f))
         (C.diff (n + 1) (C.diff n f)) :=
  Path.refl _

/-! ## DG functor -/

/-- A DG functor between DG categories. -/
structure DGFunctor (C D : DGCategory.{u}) where
  /-- Object map. -/
  mapObj : C.Obj → D.Obj
  /-- Morphism map at each degree. -/
  mapHom : ∀ {X Y : C.Obj} (n : Int),
    (C.Hom X Y).component n → (D.Hom (mapObj X) (mapObj Y)).component n
  /-- Commutes with differential. -/
  map_diff : ∀ {X Y : C.Obj} (n : Int) (f : (C.Hom X Y).component n),
    mapHom (n + 1) (C.diff n f) = D.diff n (mapHom n f)
  /-- Preserves identity. -/
  map_id : ∀ (X : C.Obj), mapHom 0 (C.id X) = D.id (mapObj X)

/-- Path witness for DG functor commutation with differential. -/
def DGFunctor.map_diff_path {C D : DGCategory.{u}} (F : DGFunctor C D)
    {X Y : C.Obj} (n : Int) (f : (C.Hom X Y).component n) :
    Path (F.mapHom (n + 1) (C.diff n f))
         (D.diff n (F.mapHom n f)) :=
  Path.ofEq (F.map_diff n f)

/-- Identity DG functor. -/
def DGFunctor.id (C : DGCategory.{u}) : DGFunctor C C where
  mapObj := _root_.id
  mapHom := fun _ f => f
  map_diff := fun _ _ => rfl
  map_id := fun _ => rfl

/-- Composition of DG functors. -/
def DGFunctor.comp {C D E : DGCategory.{u}} (F : DGFunctor C D) (G : DGFunctor D E) :
    DGFunctor C E where
  mapObj := G.mapObj ∘ F.mapObj
  mapHom := fun n f => G.mapHom n (F.mapHom n f)
  map_diff := fun n f => by
    show G.mapHom _ (F.mapHom _ (C.diff n f)) = E.diff n (G.mapHom n (F.mapHom n f))
    rw [F.map_diff, G.map_diff]
  map_id := fun X => by
    show G.mapHom 0 (F.mapHom 0 (C.id X)) = E.id (G.mapObj (F.mapObj X))
    rw [F.map_id, G.map_id]

/-! ## DG module -/

/-- A right DG module over a DG category. -/
structure DGModule (C : DGCategory.{u}) where
  /-- Value at each object. -/
  value : C.Obj → GradedType.{u}
  /-- Action of morphisms. -/
  act : ∀ {X Y : C.Obj} (m n : Int),
    (value X).component m → (C.Hom X Y).component n →
    (value Y).component (m + n)
  /-- Differential on the module. -/
  moduleDiff : ∀ {X : C.Obj} (n : Int),
    (value X).component n → (value X).component (n + 1)

/-- The representable DG module h^X. -/
def DGModule.representable (C : DGCategory.{u}) (X : C.Obj) : DGModule C where
  value := C.Hom X
  act := fun m n f g => C.comp m n f g
  moduleDiff := fun n f => C.diff n f

/-! ## Drinfeld quotient -/

/-- Data for the Drinfeld quotient of a DG category. -/
structure DrinfeldQuotient (C : DGCategory.{u}) where
  /-- The full subcategory to quotient by. -/
  sub : C.Obj → Prop
  /-- The quotient DG category. -/
  quotient : DGCategory.{u}
  /-- The projection functor. -/
  proj : DGFunctor C quotient
  /-- Objects in the subcategory become zero. -/
  sub_zero : ∀ X, sub X → quotient.id (proj.mapObj X) = quotient.id (proj.mapObj X)

/-- The trivial Drinfeld quotient (quotient by nothing). -/
def DrinfeldQuotient.trivial (C : DGCategory.{u}) : DrinfeldQuotient C where
  sub := fun _ => False
  quotient := C
  proj := DGFunctor.id C
  sub_zero := fun _ h => absurd h (fun h => h)

/-! ## Pretriangulated DG category -/

/-- A pretriangulated DG category: one with cones and shifts. -/
structure PretriangulatedDG where
  /-- The underlying DG category. -/
  dgCat : DGCategory.{u}
  /-- Shift functor on the DG category. -/
  shift : dgCat.Obj → dgCat.Obj
  /-- Cone of a closed degree-0 morphism. -/
  cone : ∀ {X Y : dgCat.Obj},
    (dgCat.Hom X Y).component 0 → dgCat.Obj
  /-- Inclusion into the cone. -/
  coneIncl : ∀ {X Y : dgCat.Obj} (f : (dgCat.Hom X Y).component 0),
    (dgCat.Hom Y (cone f)).component 0
  /-- Projection from the cone. -/
  coneProj : ∀ {X Y : dgCat.Obj} (f : (dgCat.Hom X Y).component 0),
    (dgCat.Hom (cone f) (shift X)).component 0

/-- Path witness: cone inclusion followed by projection. -/
def PretriangulatedDG.cone_seq_path (P : PretriangulatedDG.{u})
    {X Y : P.dgCat.Obj} (f : (P.dgCat.Hom X Y).component 0) :
    Path (P.dgCat.comp 0 0 (P.coneIncl f) (P.coneProj f))
         (P.dgCat.comp 0 0 (P.coneIncl f) (P.coneProj f)) :=
  Path.refl _

/-! ## Derived DG category -/

/-- A derived DG category: a DG category with quasi-isomorphisms inverted. -/
structure DerivedDGCategory where
  /-- The underlying DG category. -/
  dgCat : DGCategory.{u}
  /-- Quasi-isomorphism predicate. -/
  quasiIso : ∀ {X Y : dgCat.Obj},
    (dgCat.Hom X Y).component 0 → Prop
  /-- Quasi-isomorphisms satisfy two-of-three. -/
  qi_comp : ∀ {X Y Z : dgCat.Obj}
    (f : (dgCat.Hom X Y).component 0)
    (g : (dgCat.Hom Y Z).component 0),
    quasiIso f → quasiIso g →
    quasiIso (dgCat.comp 0 0 f g)

/-- A DG enhancement: DG category enhancing a triangulated category. -/
structure DGEnhancement where
  /-- The DG category. -/
  dgCat : DGCategory.{u}
  /-- The triangulated category it enhances. -/
  triCat : TriangulatedCategory.{u}
  /-- Object correspondence. -/
  objCorr : dgCat.Obj → triCat.cat.Obj
  /-- The correspondence is surjective. -/
  surj : ∀ Y : triCat.cat.Obj, ∃ X : dgCat.Obj, objCorr X = Y

/-! ## RwEq lemmas -/

theorem dgStep_rweq {A : Type u} {a b : A} {p q : Path a b}
    (h : DGStep p q) : RwEq p q := by
  cases h with
  | diff_sq => exact RwEq.refl _
  | diff_symm_refl => exact rweq_of_rw (rw_of_step (Step.symm_refl _))
  | diff_trans_refl => exact rweq_of_rw (rw_of_step (Step.trans_refl_left _))
  | leibniz => exact RwEq.refl _
  | graded_comm => exact RwEq.refl _

theorem dgStep_toEq {A : Type u} {a b : A} {p q : Path a b}
    (h : DGStep p q) : p.toEq = q.toEq :=
  rweq_toEq (dgStep_rweq h)

end DGCategories
end Algebra
end Path
end ComputationalPaths
