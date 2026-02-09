/-
# Yoneda Lemma for the Path Category

This module presents a lightweight Yoneda lemma for the path category whose
morphisms are rewrite-quotiented paths. We define representable functors on
`PathRwQuot`, describe natural transformations, and show the Yoneda embedding
is fully faithful.

## Key Results

- `representable`: covariant representable functor Hom(a, -)
- `yoneda`: Yoneda lemma as an equivalence between natural transformations and elements
- `yonedaEmbeddingFullyFaithful`: full faithfulness of the Yoneda embedding

## References

- Mac Lane, "Categories for the Working Mathematician"
- Leinster, "Higher Operads, Higher Categories"
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroupoid
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path

universe u v

/-! ## Functors and natural transformations on the path category -/

/-- Functor from the path category on `A` to types. -/
structure PathFunctor (A : Type u) where
  /-- Object assignment. -/
  obj : A → Type v
  /-- Action on morphisms. -/
  map : {a b : A} → FundamentalGroupoid.Hom A a b → obj a → obj b
  /-- Identity preservation. -/
  map_id : ∀ a (x : obj a), map (FundamentalGroupoid.id' A a) x = x
  /-- Composition preservation. -/
  map_comp :
    ∀ {a b c : A} (p : FundamentalGroupoid.Hom A a b)
      (q : FundamentalGroupoid.Hom A b c) (x : obj a),
      map (FundamentalGroupoid.comp' A p q) x = map q (map p x)

/-- Natural transformations between path functors. -/
structure PathNatTrans {A : Type u} (F G : PathFunctor (A := A)) where
  /-- Component map at each object. -/
  app : ∀ a, F.obj a → G.obj a
  /-- Naturality with respect to paths. -/
  naturality :
    ∀ {a b : A} (p : FundamentalGroupoid.Hom A a b) (x : F.obj a),
      G.map p (app a x) = app b (F.map p x)

namespace PathNatTrans

/-- Extensionality for natural transformations. -/
@[ext] theorem ext {A : Type u} {F G : PathFunctor (A := A)}
    {η θ : PathNatTrans F G} (h : ∀ a, η.app a = θ.app a) : η = θ := by
  cases η with
  | mk appη natη =>
    cases θ with
    | mk appθ natθ =>
      have h_app : appη = appθ := funext h
      subst h_app
      have h_nat : @natη = @natθ := by
        funext a b p x
        apply Subsingleton.elim
      cases h_nat
      rfl

end PathNatTrans

/-! ## Representable functors -/

/-- Representable functor Hom(a, -) on the path category. -/
def representable (A : Type u) (a : A) : PathFunctor (A := A) where
  obj := fun b => FundamentalGroupoid.Hom A a b
  map := fun {b c} p q => FundamentalGroupoid.comp' A q p
  map_id := by
    intro b q
    exact FundamentalGroupoid.comp_id' (A := A) (p := q)
  map_comp := by
    intro b c d p q r
    exact (FundamentalGroupoid.comp_assoc' (A := A) (p := r) (q := p) (r := q)).symm

/-! ## Yoneda lemma -/

/-- Yoneda lemma for the path category. -/
def yoneda {A : Type u} (F : PathFunctor (A := A)) (a : A) :
    SimpleEquiv (PathNatTrans (representable A a) F) (F.obj a) where
  toFun := fun η => η.app a (FundamentalGroupoid.id' A a)
  invFun := fun x =>
    { app := fun b q => F.map q x
      naturality := by
        intro b c p q
        exact (F.map_comp (p := q) (q := p) (x := x)).symm }
  left_inv := by
    intro η
    apply PathNatTrans.ext
    intro b
    funext q
    have h := η.naturality (p := q) (x := FundamentalGroupoid.id' A a)
    simpa [representable, FundamentalGroupoid.id_comp'] using h
  right_inv := by
    intro x
    exact F.map_id a x

/-! ## Yoneda embedding -/

/-- Yoneda embedding on objects. -/
def yonedaEmbedding (A : Type u) : A → PathFunctor (A := A) :=
  fun a => representable A a

/-- Yoneda embedding on morphisms (precomposition). -/
def yonedaEmbeddingMap {A : Type u} {a b : A}
    (p : FundamentalGroupoid.Hom A b a) :
    PathNatTrans (yonedaEmbedding A a) (yonedaEmbedding A b) :=
  (yoneda (A := A) (F := representable A b) a).invFun p

/-- Yoneda hom-set equivalence (full faithfulness). -/
def yonedaEmbeddingFullyFaithful (A : Type u) :
    ∀ a b,
      SimpleEquiv
        (PathNatTrans (yonedaEmbedding A a) (yonedaEmbedding A b))
        (FundamentalGroupoid.Hom A b a) :=
  fun a b => yoneda (A := A) (F := representable A b) a

/-! ## Summary -/

/-!
We defined the representable functors on the path category, proved the Yoneda
lemma as a simple equivalence, and recorded the full faithfulness of the
Yoneda embedding on `PathRwQuot` morphisms.
-/

end Path
end ComputationalPaths
