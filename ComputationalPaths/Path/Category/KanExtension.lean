/-
# Kan Extensions in the Path Category

Derived lemmas for Kan extensions of path functors, including identity and
composition constructions and adjunction-style universal properties.
-/

import ComputationalPaths.Path.KanExtension
import ComputationalPaths.Path.YonedaLemma

namespace ComputationalPaths
namespace Path

universe u v

/-! ## Path-category functors -/

namespace PathCategoryFunctor

variable {A B C : Type u}

/-- Identity path-category functor. -/
noncomputable def id (A : Type u) : PathCategoryFunctor A A where
  obj := fun a => a
  map := fun {a b} p => p
  map_id := by intro a; rfl
  map_comp := by intro a b c p q; rfl

/-- Composition of path-category functors. -/
noncomputable def comp (F : PathCategoryFunctor A B) (G : PathCategoryFunctor B C) :
    PathCategoryFunctor A C where
  obj := fun a => G.obj (F.obj a)
  map := fun {a b} p => G.map (F.map p)
  map_id := by
    intro a
    simp only [F.map_id]
    exact G.map_id (F.obj a)
  map_comp := by
    intro a b c p q
    simp only [F.map_comp]
    exact G.map_comp (F.map p) (F.map q)

end PathCategoryFunctor

/-! ## Natural transformations -/

namespace PathNatTrans

variable {A : Type u}

/-- Vertical composition of natural transformations. -/
noncomputable def vcomp {F G H : PathFunctor.{u, v} (A := A)}
    (η : PathNatTrans F G) (θ : PathNatTrans G H) :
    PathNatTrans F H where
  app := fun a x => θ.app a (η.app a x)
  naturality := by
    intro a b p x
    calc
      H.map p (θ.app a (η.app a x)) =
          θ.app b (G.map p (η.app a x)) :=
        θ.naturality (p := p) (x := η.app a x)
      _ = θ.app b (η.app b (F.map p x)) := by
        rw [η.naturality (p := p) (x := x)]

/-- Whisker a natural transformation by precomposition. -/
noncomputable def precompose {A B : Type u} (F : PathCategoryFunctor A B)
    {G H : PathFunctor.{u, v} (A := B)} (η : PathNatTrans G H) :
    PathNatTrans (PathFunctor.precompose F G) (PathFunctor.precompose F H) where
  app := fun a x => η.app (F.obj a) x
  naturality := by
    intro a b p x
    simpa using η.naturality (p := F.map p) (x := x)

end PathNatTrans

/-! ## Precomposition equivalences -/

variable {A B C : Type u}

/-- Repackage natural transformations against precomposition by the identity functor. -/
noncomputable def precomposeIdEquiv (G M : PathFunctor.{u, v} (A := A)) :
    SimpleEquiv (PathNatTrans G M)
      (PathNatTrans G (PathFunctor.precompose (PathCategoryFunctor.id A) M)) where
  toFun := fun η =>
    { app := η.app
      naturality := by intro a b p x; simpa using η.naturality (p := p) (x := x) }
  invFun := fun η =>
    { app := η.app
      naturality := by intro a b p x; simpa using η.naturality (p := p) (x := x) }
  left_inv := by intro η; apply PathNatTrans.ext; intro a; rfl
  right_inv := by intro η; apply PathNatTrans.ext; intro a; rfl

/-- Repackage natural transformations with domain precomposed by the identity functor. -/
noncomputable def precomposeIdEquivDom (G M : PathFunctor.{u, v} (A := A)) :
    SimpleEquiv (PathNatTrans M G)
      (PathNatTrans (PathFunctor.precompose (PathCategoryFunctor.id A) M) G) where
  toFun := fun η =>
    { app := η.app
      naturality := by intro a b p x; simpa using η.naturality (p := p) (x := x) }
  invFun := fun η =>
    { app := η.app
      naturality := by intro a b p x; simpa using η.naturality (p := p) (x := x) }
  left_inv := by intro η; apply PathNatTrans.ext; intro a; rfl
  right_inv := by intro η; apply PathNatTrans.ext; intro a; rfl

/-! ## Kan extension lemmas -/

section KanLemmas

variable {A B C : Type u}
variable {F : PathCategoryFunctor A B}
variable {H : PathCategoryFunctor B C}
variable {G : PathFunctor.{u, v} (A := A)}

/-- Universal property of a left Kan extension as an adjunction. -/
abbrev leftKanAdjunction (L : LeftKanExtension F G)
    (M : PathFunctor.{u, v} (A := B)) :
    SimpleEquiv (PathNatTrans L.lan M)
      (PathNatTrans G (PathFunctor.precompose F M)) :=
  L.universal M

/-- Universal property of a right Kan extension as an adjunction. -/
abbrev rightKanAdjunction (R : RightKanExtension F G)
    (M : PathFunctor.{u, v} (A := B)) :
    SimpleEquiv (PathNatTrans M R.ran)
      (PathNatTrans (PathFunctor.precompose F M) G) :=
  R.universal M

/-- Abbreviation for the pointwise left Kan extension functor. -/
noncomputable abbrev pointwiseLeftKanExtension (F : PathCategoryFunctor A B)
    (G : PathFunctor.{u, v} (A := A)) :
    PathFunctor (A := B) :=
  pointwiseLeftKan F G

/-- Abbreviation for the pointwise right Kan extension functor. -/
noncomputable abbrev pointwiseRightKanExtension (F : PathCategoryFunctor A B)
    (G : PathFunctor.{u, v} (A := A)) :
    PathFunctor (A := B) :=
  pointwiseRightKan F G

/-- The identity functor admits a left Kan extension given by itself. -/
noncomputable def leftKanExtension_id (G : PathFunctor.{u, v} (A := A)) :
    LeftKanExtension (PathCategoryFunctor.id A) G where
  lan := G
  unit :=
    { app := fun _ x => x
      naturality := by intro a b p x; rfl }
  universal := fun M => precomposeIdEquiv (G := G) (M := M)

/-- The identity functor admits a right Kan extension given by itself. -/
noncomputable def rightKanExtension_id (G : PathFunctor.{u, v} (A := A)) :
    RightKanExtension (PathCategoryFunctor.id A) G where
  ran := G
  counit :=
    { app := fun _ x => x
      naturality := by intro a b p x; rfl }
  universal := fun M => precomposeIdEquivDom (G := G) (M := M)

end KanLemmas

/-! ## Basic theorem statements -/

section BasicTheorems

variable {A B C : Type u}

theorem pathCategoryFunctor_id_obj (A : Type u) (a : A) :
    (PathCategoryFunctor.id A).obj a = a := by
  rfl

theorem pathCategoryFunctor_id_map (A : Type u) {a b : A} (p : Path a b) :
    (PathCategoryFunctor.id A).map p = p := by
  rfl

theorem pathCategoryFunctor_comp_obj (F : PathCategoryFunctor A B)
    (G : PathCategoryFunctor B C) (a : A) :
    (PathCategoryFunctor.comp F G).obj a = G.obj (F.obj a) := by
  rfl

theorem pathCategoryFunctor_comp_map (F : PathCategoryFunctor A B)
    (G : PathCategoryFunctor B C) {a b : A} (p : Path a b) :
    (PathCategoryFunctor.comp F G).map p = G.map (F.map p) := by
  rfl

theorem pathNatTrans_vcomp_app {X : Type u}
    {F G H : PathFunctor.{u, v} (A := X)}
    (η : PathNatTrans F G) (θ : PathNatTrans G H) (x : X) (u : F.obj x) :
    (PathNatTrans.vcomp η θ).app x u = θ.app x (η.app x u) := by
  rfl

theorem pathNatTrans_precompose_app {X Y : Type u}
    (F : PathCategoryFunctor X Y)
    {G H : PathFunctor.{u, v} (A := Y)}
    (η : PathNatTrans G H) (x : X) (u : G.obj (F.obj x)) :
    (PathNatTrans.precompose F η).app x u = η.app (F.obj x) u := by
  rfl

theorem precomposeIdEquiv_toFun_app (G M : PathFunctor.{u, v} (A := A))
    (η : PathNatTrans G M) (a : A) (x : G.obj a) :
    ((precomposeIdEquiv (G := G) (M := M)).toFun η).app a x = η.app a x := by
  rfl

theorem precomposeIdEquivDom_toFun_app (G M : PathFunctor.{u, v} (A := A))
    (η : PathNatTrans M G) (a : A) (x : M.obj a) :
    ((precomposeIdEquivDom (G := G) (M := M)).toFun η).app a x = η.app a x := by
  rfl

theorem leftKanAdjunction_eq_universal
    (F : PathCategoryFunctor A B) (G : PathFunctor.{u, v} (A := A))
    (L : LeftKanExtension F G) (M : PathFunctor.{u, v} (A := B)) :
    leftKanAdjunction (F := F) (G := G) L M = L.universal M := by
  rfl

theorem rightKanAdjunction_eq_universal
    (F : PathCategoryFunctor A B) (G : PathFunctor.{u, v} (A := A))
    (R : RightKanExtension F G) (M : PathFunctor.{u, v} (A := B)) :
    rightKanAdjunction (F := F) (G := G) R M = R.universal M := by
  rfl

theorem pointwiseLeftKanExtension_eq (F : PathCategoryFunctor A B)
    (G : PathFunctor.{u, v} (A := A)) :
    pointwiseLeftKanExtension (F := F) (G := G) = pointwiseLeftKan F G := by
  rfl

theorem pointwiseRightKanExtension_eq (F : PathCategoryFunctor A B)
    (G : PathFunctor.{u, v} (A := A)) :
    pointwiseRightKanExtension (F := F) (G := G) = pointwiseRightKan F G := by
  rfl

theorem leftKanExtension_id_lan (G : PathFunctor.{u, v} (A := A)) :
    (leftKanExtension_id (A := A) G).lan = G := by
  rfl

theorem rightKanExtension_id_ran (G : PathFunctor.{u, v} (A := A)) :
    (rightKanExtension_id (A := A) G).ran = G := by
  rfl

end BasicTheorems

/-! ## Summary -/

/-!
We constructed identity and composition Kan extensions, along with adjunction
formulas and pointwise abbreviations for path-category functors.
-/

end Path
end ComputationalPaths
