/-
# Natural Transformations for Fundamental Groupoid Functors

This module defines natural transformations between fundamental groupoid
functors, together with vertical and horizontal composition. We then package
these operations into the functor category structure.

## Key Results

- `FundamentalGroupoidNatTrans`: natural transformations between functors.
- `FundamentalGroupoidNatTrans.vcomp`: vertical composition.
- `FundamentalGroupoidNatTrans.hcomp`: horizontal composition.
- `fundamentalGroupoidFunctorCategory`: category structure on functors.

## References

- Mac Lane, "Categories for the Working Mathematician"
- Brown, "Topology and Groupoids"
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroupoidFunctor

namespace ComputationalPaths
namespace Path

universe u

/-! ## Natural transformations -/

/-- Natural transformations between fundamental groupoid functors. -/
structure FundamentalGroupoidNatTrans {A : Type u} {B : Type u}
    (F G : FundamentalGroupoidFunctor A B) where
  /-- Component morphism at each object. -/
  app : ∀ a, FundamentalGroupoid.Hom B (F.obj a) (G.obj a)
  /-- Naturality with respect to paths. -/
  naturality : ∀ {a b : A} (p : FundamentalGroupoid.Hom A a b),
      FundamentalGroupoid.comp' B (app a) (G.map p) =
        FundamentalGroupoid.comp' B (F.map p) (app b)

namespace FundamentalGroupoidNatTrans

variable {A B C : Type u}

/-- Extensionality for natural transformations. -/
@[ext] theorem ext {F G : FundamentalGroupoidFunctor A B}
    {η θ : FundamentalGroupoidNatTrans F G}
    (h : ∀ a, η.app a = θ.app a) : η = θ := by
  cases η with
  | mk appη natη =>
    cases θ with
    | mk appθ natθ =>
      have h_app : appη = appθ := funext h
      subst h_app
      have h_nat : @natη = @natθ := by
        funext a b p
        apply Subsingleton.elim
      cases h_nat
      rfl

/-- Identity natural transformation. -/
def id (F : FundamentalGroupoidFunctor A B) :
    FundamentalGroupoidNatTrans F F where
  app := fun a => FundamentalGroupoid.id' B (F.obj a)
  naturality := by
    intro a b p
    calc
      FundamentalGroupoid.comp' B (FundamentalGroupoid.id' B (F.obj a)) (F.map p)
          = F.map p :=
            FundamentalGroupoid.id_comp' (A := B) (p := F.map p)
      _ = FundamentalGroupoid.comp' B (F.map p) (FundamentalGroupoid.id' B (F.obj b)) := by
            symm
            exact FundamentalGroupoid.comp_id' (A := B) (p := F.map p)

/-- Vertical composition of natural transformations. -/
def vcomp {F G H : FundamentalGroupoidFunctor A B}
    (η : FundamentalGroupoidNatTrans F G)
    (θ : FundamentalGroupoidNatTrans G H) :
    FundamentalGroupoidNatTrans F H where
  app := fun a => FundamentalGroupoid.comp' B (η.app a) (θ.app a)
  naturality := by
    intro a b p
    calc
      FundamentalGroupoid.comp' B
          (FundamentalGroupoid.comp' B (η.app a) (θ.app a)) (H.map p)
          =
          FundamentalGroupoid.comp' B (η.app a)
            (FundamentalGroupoid.comp' B (θ.app a) (H.map p)) := by
            exact FundamentalGroupoid.comp_assoc' (A := B)
              (p := η.app a) (q := θ.app a) (r := H.map p)
      _ = FundamentalGroupoid.comp' B (η.app a)
            (FundamentalGroupoid.comp' B (G.map p) (θ.app b)) := by
            rw [θ.naturality]
      _ = FundamentalGroupoid.comp' B
            (FundamentalGroupoid.comp' B (η.app a) (G.map p)) (θ.app b) := by
            symm
            exact FundamentalGroupoid.comp_assoc' (A := B)
              (p := η.app a) (q := G.map p) (r := θ.app b)
      _ = FundamentalGroupoid.comp' B
            (FundamentalGroupoid.comp' B (F.map p) (η.app b)) (θ.app b) := by
            rw [η.naturality]
      _ = FundamentalGroupoid.comp' B (F.map p)
            (FundamentalGroupoid.comp' B (η.app b) (θ.app b)) := by
            exact FundamentalGroupoid.comp_assoc' (A := B)
              (p := F.map p) (q := η.app b) (r := θ.app b)

/-- Vertical composition is associative. -/
@[simp] theorem vcomp_assoc {F G H I : FundamentalGroupoidFunctor A B}
    (η : FundamentalGroupoidNatTrans F G)
    (θ : FundamentalGroupoidNatTrans G H)
    (ι : FundamentalGroupoidNatTrans H I) :
    vcomp (vcomp η θ) ι = vcomp η (vcomp θ ι) := by
  ext a
  exact FundamentalGroupoid.comp_assoc' (A := B)
    (p := η.app a) (q := θ.app a) (r := ι.app a)

/-- Right identity for vertical composition. -/
@[simp] theorem vcomp_id {F G : FundamentalGroupoidFunctor A B}
    (η : FundamentalGroupoidNatTrans F G) :
    vcomp η (id G) = η := by
  ext a
  exact FundamentalGroupoid.comp_id' (A := B) (p := η.app a)

/-- Left identity for vertical composition. -/
@[simp] theorem id_vcomp {F G : FundamentalGroupoidFunctor A B}
    (η : FundamentalGroupoidNatTrans F G) :
    vcomp (id F) η = η := by
  ext a
  exact FundamentalGroupoid.id_comp' (A := B) (p := η.app a)

/-- Horizontal composition of natural transformations. -/
def hcomp {F G : FundamentalGroupoidFunctor A B}
    {H K : FundamentalGroupoidFunctor B C}
    (η : FundamentalGroupoidNatTrans F G)
    (θ : FundamentalGroupoidNatTrans H K) :
    FundamentalGroupoidNatTrans
      (FundamentalGroupoidFunctor.comp F H)
      (FundamentalGroupoidFunctor.comp G K) where
  app := fun a =>
    FundamentalGroupoid.comp' C (H.map (η.app a)) (θ.app (G.obj a))
  naturality := by
    intro a b p
    calc
      FundamentalGroupoid.comp' C
          (FundamentalGroupoid.comp' C (H.map (η.app a)) (θ.app (G.obj a)))
          (K.map (G.map p))
          =
          FundamentalGroupoid.comp' C (H.map (η.app a))
            (FundamentalGroupoid.comp' C (θ.app (G.obj a)) (K.map (G.map p))) := by
            exact FundamentalGroupoid.comp_assoc' (A := C)
              (p := H.map (η.app a)) (q := θ.app (G.obj a)) (r := K.map (G.map p))
      _ = FundamentalGroupoid.comp' C (H.map (η.app a))
            (FundamentalGroupoid.comp' C (H.map (G.map p)) (θ.app (G.obj b))) := by
            rw [θ.naturality (p := G.map p)]
      _ = FundamentalGroupoid.comp' C
            (FundamentalGroupoid.comp' C (H.map (η.app a)) (H.map (G.map p)))
            (θ.app (G.obj b)) := by
            symm
            exact FundamentalGroupoid.comp_assoc' (A := C)
              (p := H.map (η.app a)) (q := H.map (G.map p)) (r := θ.app (G.obj b))
      _ = FundamentalGroupoid.comp' C
            (H.map (FundamentalGroupoid.comp' B (η.app a) (G.map p)))
            (θ.app (G.obj b)) := by
            rw [← H.map_comp (p := η.app a) (q := G.map p)]
      _ = FundamentalGroupoid.comp' C
            (H.map (FundamentalGroupoid.comp' B (F.map p) (η.app b)))
            (θ.app (G.obj b)) := by
            rw [η.naturality (p := p)]
      _ = FundamentalGroupoid.comp' C
            (FundamentalGroupoid.comp' C (H.map (F.map p)) (H.map (η.app b)))
            (θ.app (G.obj b)) := by
            rw [H.map_comp (p := F.map p) (q := η.app b)]
      _ = FundamentalGroupoid.comp' C (H.map (F.map p))
            (FundamentalGroupoid.comp' C (H.map (η.app b)) (θ.app (G.obj b))) := by
            exact FundamentalGroupoid.comp_assoc' (A := C)
              (p := H.map (F.map p)) (q := H.map (η.app b)) (r := θ.app (G.obj b))

end FundamentalGroupoidNatTrans

/-! ## Functor category structure -/

/-- Category structure on fundamental groupoid functors with natural transformations. -/
structure FundamentalGroupoidFunctorCategory (A : Type u) (B : Type u) where
  /-- Identity natural transformation. -/
  id :
    ∀ (F : FundamentalGroupoidFunctor A B),
      FundamentalGroupoidNatTrans F F
  /-- Composition of natural transformations. -/
  comp :
    ∀ {F G H : FundamentalGroupoidFunctor A B},
      FundamentalGroupoidNatTrans F G →
      FundamentalGroupoidNatTrans G H →
      FundamentalGroupoidNatTrans F H
  /-- Associativity of composition. -/
  comp_assoc :
    ∀ {F G H I : FundamentalGroupoidFunctor A B}
      (η : FundamentalGroupoidNatTrans F G)
      (θ : FundamentalGroupoidNatTrans G H)
      (ι : FundamentalGroupoidNatTrans H I),
      comp (comp η θ) ι = comp η (comp θ ι)
  /-- Left identity law. -/
  id_comp :
    ∀ {F G : FundamentalGroupoidFunctor A B}
      (η : FundamentalGroupoidNatTrans F G),
      comp (id F) η = η
  /-- Right identity law. -/
  comp_id :
    ∀ {F G : FundamentalGroupoidFunctor A B}
      (η : FundamentalGroupoidNatTrans F G),
      comp η (id G) = η

/-- The functor category of fundamental groupoid functors. -/
def fundamentalGroupoidFunctorCategory (A : Type u) (B : Type u) :
    FundamentalGroupoidFunctorCategory A B where
  id := FundamentalGroupoidNatTrans.id
  comp := fun η θ => FundamentalGroupoidNatTrans.vcomp η θ
  comp_assoc := by
    intro F G H I η θ ι
    exact FundamentalGroupoidNatTrans.vcomp_assoc (η := η) (θ := θ) (ι := ι)
  id_comp := by
    intro F G η
    exact FundamentalGroupoidNatTrans.id_vcomp (η := η)
  comp_id := by
    intro F G η
    exact FundamentalGroupoidNatTrans.vcomp_id (η := η)

private def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

/-! ## Summary -/

/-!
We introduced natural transformations between fundamental groupoid functors,
defined vertical and horizontal composition, and packaged the resulting
functor category structure.
-/

end Path
end ComputationalPaths
