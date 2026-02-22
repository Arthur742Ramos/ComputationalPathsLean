/-
# Yoneda Lemma for the Path Category

This module presents a lightweight Yoneda lemma for the path category whose
morphisms are computational paths. We define representable functors on `Path`,
describe natural transformations, and show the Yoneda embedding is fully faithful.

## Key Results

- `representable`: covariant representable functor `Path a _`
- `yoneda`: Yoneda lemma as an equivalence between natural transformations and elements
- `yonedaEmbeddingFullyFaithful`: full faithfulness of the Yoneda embedding

## References

- Mac Lane, "Categories for the Working Mathematician"
- Leinster, "Higher Operads, Higher Categories"
-/

import ComputationalPaths.Path.Basic
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
  map : {a b : A} → Path a b → obj a → obj b
  /-- Identity preservation. -/
  map_id : ∀ a (x : obj a), Path (map (Path.refl a) x) x
  /-- Composition preservation. -/
  map_comp :
    ∀ {a b c : A} (p : Path a b)
      (q : Path b c) (x : obj a),
      Path (map (Path.trans p q) x) (map q (map p x))

/-- Natural transformations between path functors. -/
structure PathNatTrans {A : Type u} (F G : PathFunctor (A := A)) where
  /-- Component map at each object. -/
  app : ∀ a, F.obj a → G.obj a
  /-- Naturality with respect to paths. -/
  naturality :
    ∀ {a b : A} (p : Path a b) (x : F.obj a),
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
noncomputable def representable (A : Type u) (a : A) : PathFunctor (A := A) where
  obj := fun b => Path a b
  map := fun {b c} p q => Path.trans q p
  map_id := by
    intro b q
    exact Path.stepChain (Path.trans_refl_right q)
  map_comp := by
    intro b c d p q r
    exact Path.stepChain (Path.trans_assoc r p q).symm

/-! ## Yoneda lemma -/

/-- Yoneda lemma for the path category. -/
noncomputable def yoneda {A : Type u} (F : PathFunctor (A := A)) (a : A) :
    SimpleEquiv (PathNatTrans (representable A a) F) (F.obj a) where
  toFun := fun η => η.app a (Path.refl a)
  invFun := fun x =>
    { app := fun b q => F.map q x
      naturality := by
        intro b c p q
        exact (F.map_comp (p := q) (q := p) (x := x)).toEq.symm }
  left_inv := by
    intro η
    apply PathNatTrans.ext
    intro b
    funext q
    have h := η.naturality (p := q) (x := Path.refl a)
    simpa [representable, Path.trans_refl_left] using h
  right_inv := by
    intro x
    exact (F.map_id a x).toEq

/-- Naturality of a representable natural transformation at the identity witness. -/
noncomputable def yonedaNaturalityPath {A : Type u} {F : PathFunctor (A := A)} {a b : A}
    (η : PathNatTrans (representable A a) F) (p : Path a b) :
    Path (F.map p (η.app a (Path.refl a))) (η.app b p) := by
  refine Path.stepChain ?_
  have h := η.naturality (p := p) (x := Path.refl a)
  simpa [representable, Path.trans_refl_left] using h

/-- Compose two representable legs and evaluate via Yoneda naturality. -/
noncomputable def yonedaNaturalityComposePath {A : Type u} {F : PathFunctor (A := A)}
    {a b c : A} (η : PathNatTrans (representable A a) F)
    (p : Path a b) (q : Path b c) :
    Path (F.map q (F.map p (η.app a (Path.refl a))))
         (η.app c (Path.trans p q)) := by
  exact Path.trans
    (Path.symm (F.map_comp (p := p) (q := q) (x := η.app a (Path.refl a))))
    (yonedaNaturalityPath (η := η) (p := Path.trans p q))

/-! ## Yoneda embedding -/

/-- Yoneda embedding on objects. -/
noncomputable def yonedaEmbedding (A : Type u) : A → PathFunctor (A := A) :=
  fun a => representable A a

/-- Yoneda embedding on morphisms (precomposition). -/
noncomputable def yonedaEmbeddingMap {A : Type u} {a b : A}
    (p : Path b a) :
    PathNatTrans (yonedaEmbedding A a) (yonedaEmbedding A b) :=
  (yoneda (A := A) (F := representable A b) a).invFun p

/-- Yoneda hom-set equivalence (full faithfulness). -/
noncomputable def yonedaEmbeddingFullyFaithful (A : Type u) :
    ∀ a b,
      SimpleEquiv
        (PathNatTrans (yonedaEmbedding A a) (yonedaEmbedding A b))
        (Path b a) :=
  fun a b => yoneda (A := A) (F := representable A b) a

/-! ## Deeper properties of the Yoneda embedding -/

/-- The Yoneda embedding preserves identity: yonedaEmbeddingMap (refl a) is the identity nat trans. -/
theorem yonedaEmbeddingMap_refl (A : Type u) (a : A) :
    ∀ b (q : Path a b),
      (yonedaEmbeddingMap (Path.refl a)).app b q = q := by
  intro b q
  simp [yonedaEmbeddingMap, yoneda, representable]

/-- PathFunctor identity law: map of refl acts as the identity up to a path. -/
noncomputable def pathFunctor_map_id_path {A : Type u} (F : PathFunctor (A := A)) (a : A) (x : F.obj a) :
    Path (F.map (Path.refl a) x) x :=
  F.map_id a x

/-- Naturality of yoneda: the equivalence is natural in the functor argument. -/
theorem yoneda_natural_functor {A : Type u} {F G : PathFunctor (A := A)}
    (η : PathNatTrans F G) (a : A) (θ : PathNatTrans (representable A a) F) :
    η.app a ((yoneda F a).toFun θ) = (yoneda G a).toFun
      { app := fun b q => η.app b (θ.app b q)
        naturality := by intro a' b' p x; rw [η.naturality p (θ.app a' x), θ.naturality p x] } := by
  simp [yoneda]


/-- Composition of natural transformations between path functors. -/
noncomputable def PathNatTrans.comp {A : Type u} {F G H : PathFunctor (A := A)}
    (η : PathNatTrans G H) (θ : PathNatTrans F G) : PathNatTrans F H where
  app := fun a x => η.app a (θ.app a x)
  naturality := by
    intro a b p x
    rw [η.naturality p (θ.app a x), θ.naturality p x]


/-- Identity natural transformation. -/
noncomputable def PathNatTrans.id {A : Type u} (F : PathFunctor (A := A)) : PathNatTrans F F where
  app := fun _ x => x
  naturality := by intros; rfl




/-- Representable functors preserve path composition up to a path. -/
noncomputable def representable_map_comp {A : Type u} (a : A) {b c d : A}
    (p : Path b c) (q : Path c d) (r : Path a b) :
    Path ((representable A a).map q ((representable A a).map p r))
         ((representable A a).map (Path.trans p q) r) :=
  (representable A a).map_comp p q r |>.symm

/-! ## Summary -/

/-!
We defined the representable functors on the path category, proved the Yoneda
lemma as a simple equivalence, and recorded the full faithfulness of the
Yoneda embedding on computational paths.
-/

end Path
end ComputationalPaths
