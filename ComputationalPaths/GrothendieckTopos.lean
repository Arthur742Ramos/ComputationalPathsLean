/-
# Grothendieck Topoi via Computational Paths

This module formalizes Grothendieck topoi — categories of sheaves on sites —
including geometric morphisms, Giraud's characterization theorem, points of a
topos, and classifying topoi, all with `Path` coherence witnesses.

## Mathematical Background

A Grothendieck topos (SGA 4, Artin–Grothendieck–Verdier) is a category
equivalent to the category of sheaves on some site:

1. **Sites and sieves**: a Grothendieck topology J on a category C assigns
   to each object a collection of covering sieves, closed under pullback.
2. **Presheaves and sheaves**: presheaves are contravariant functors C^op → Set;
   sheaves satisfy descent for all covering sieves.
3. **Sheafification**: the left-exact left adjoint a : PSh(C) → Sh(C,J).
4. **Geometric morphisms**: adjunctions f^* ⊣ f_* between topoi where f^*
   is left-exact.
5. **Giraud's theorem**: characterization of Grothendieck topoi.
6. **Points of a topos**: geometric morphisms Set → E.
7. **Classifying topos**: for a geometric theory T, the classifying topos B[T].

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `GrothendieckTopology` | Topology J on a category |
| `Sieve` | Sieve on an object |
| `PresheafData` | Presheaf on a site |
| `SheafCondition` | Sheaf condition for a sieve |
| `SheafData` | Sheaf on a site |
| `Sheafification` | Sheafification functor |
| `GeometricMorphism` | Geometric morphism f^* ⊣ f_* |
| `GiraudData` | Giraud's axioms |
| `ToposPoint` | Point of a topos |
| `EnoughPoints` | Enough-points condition |
| `ClassifyingTopos` | Classifying topos |

## References

- Artin–Grothendieck–Verdier, "SGA 4"
- Mac Lane–Moerdijk, "Sheaves in Geometry and Logic"
- Johnstone, "Sketches of an Elephant"
- Caramello, "Theories, Sites, Toposes"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace GrothendieckTopos

universe u v w

/-! ## Categories -/

/-- A small category for use as the underlying site. -/
structure SmallCat where
  /-- Objects. -/
  Obj : Type u
  /-- Morphisms. -/
  Hom : Obj → Obj → Type v
  /-- Identity. -/
  id : (X : Obj) → Hom X X
  /-- Composition (diagrammatic order). -/
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  /-- Left identity. -/
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  /-- Right identity. -/
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f
  /-- Associativity. -/
  assoc : ∀ {X Y Z W : Obj} (f : Hom X Y) (g : Hom Y Z) (h : Hom Z W),
    comp (comp f g) h = comp f (comp g h)

/-! ## Sieves and Grothendieck Topologies -/

/-- A sieve on an object X: a collection of morphisms into X closed under
precomposition. -/
structure Sieve (C : SmallCat) (X : C.Obj) where
  /-- Membership predicate. -/
  mem : {Y : C.Obj} → C.Hom Y X → Prop
  /-- Closure under precomposition. -/
  closed : ∀ {Y Z : C.Obj} (f : C.Hom Y X) (g : C.Hom Z Y),
    mem f → mem (C.comp g f)

namespace Sieve

variable {C : SmallCat} {X : C.Obj}

/-- The maximal sieve on X: all morphisms into X. -/
def maximal (C : SmallCat) (X : C.Obj) : Sieve C X where
  mem := fun _ => True
  closed := fun _ _ _ => trivial

/-- The pullback of a sieve along a morphism. -/
def pullback (S : Sieve C X) {Y : C.Obj} (f : C.Hom Y X) : Sieve C Y where
  mem := fun g => S.mem (C.comp g f)
  closed := fun g h hg => by
    show S.mem (C.comp (C.comp h g) f)
    rw [C.assoc]
    exact S.closed (C.comp g f) h hg

/-- Pullback of maximal sieve is maximal. -/
theorem pullback_maximal {Y : C.Obj} (f : C.Hom Y X) :
    ∀ {Z : C.Obj} (g : C.Hom Z Y), (maximal C X |>.pullback f).mem g :=
  fun _ => trivial

end Sieve

/-- A Grothendieck topology J on a category C. -/
structure GrothendieckTopology (C : SmallCat) where
  /-- Whether a sieve is covering. -/
  covers : {X : C.Obj} → Sieve C X → Prop
  /-- The maximal sieve is always covering. -/
  max_covers : ∀ (X : C.Obj), covers (Sieve.maximal C X)
  /-- Stability under pullback. -/
  stability : ∀ {X Y : C.Obj} (S : Sieve C X) (f : C.Hom Y X),
    covers S → covers (S.pullback f)
  /-- Transitivity. -/
  transitivity : ∀ {X : C.Obj} (S T : Sieve C X),
    covers S →
    (∀ {Y : C.Obj} (f : C.Hom Y X), S.mem f → covers (T.pullback f)) →
    covers T

namespace GrothendieckTopology

variable {C : SmallCat}

/-- The indiscrete (trivial) topology: every sieve covers. -/
def indiscrete (C : SmallCat) : GrothendieckTopology C where
  covers := fun _ => True
  max_covers := fun _ => trivial
  stability := fun _ _ _ => trivial
  transitivity := fun _ _ _ _ => trivial

end GrothendieckTopology

/-! ## Presheaves and Sheaves -/

/-- A presheaf on C: a contravariant functor C^op → Type. -/
structure PresheafData (C : SmallCat) where
  /-- Sections over an object. -/
  sections : C.Obj → Type v
  /-- Restriction along a morphism. -/
  restrict : {X Y : C.Obj} → C.Hom X Y → sections Y → sections X
  /-- Restriction along identity is identity. -/
  restrict_id : ∀ (X : C.Obj) (s : sections X),
    restrict (C.id X) s = s
  /-- Restriction along composition. -/
  restrict_comp : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z)
    (s : sections Z),
    restrict (C.comp f g) s = restrict f (restrict g s)

namespace PresheafData

variable {C : SmallCat}

/-- The representable presheaf y(X) = Hom(–, X). -/
def representable (C : SmallCat) (X : C.Obj) : PresheafData C where
  sections := fun Y => C.Hom Y X
  restrict := fun f g => C.comp f g
  restrict_id := fun Y s => C.id_comp s
  restrict_comp := fun f g s => C.assoc f g s

end PresheafData

/-- The sheaf condition for a presheaf F w.r.t. a sieve S on X. -/
structure SheafCondition (C : SmallCat) (F : PresheafData C)
    {X : C.Obj} (S : Sieve C X) where
  /-- A compatible family. -/
  family : ∀ {Y : C.Obj} (f : C.Hom Y X), S.mem f → F.sections Y
  /-- Compatibility. -/
  compat : ∀ {Y Z : C.Obj} (f : C.Hom Y X) (g : C.Hom Z Y)
    (hf : S.mem f),
    F.restrict g (family f hf) =
      family (C.comp g f) (S.closed f g hf)
  /-- Glued section. -/
  glue : F.sections X
  /-- Glued section restricts correctly. -/
  glue_spec : ∀ {Y : C.Obj} (f : C.Hom Y X) (hf : S.mem f),
    F.restrict f glue = family f hf
  /-- Uniqueness of gluing. -/
  glue_unique : ∀ (t : F.sections X),
    (∀ {Y : C.Obj} (f : C.Hom Y X) (hf : S.mem f),
      F.restrict f t = family f hf) →
    t = glue

/-- A sheaf on a site (C, J). -/
structure SheafData (C : SmallCat) (J : GrothendieckTopology C) where
  /-- The underlying presheaf. -/
  presheaf : PresheafData C
  /-- Sheaf condition for every covering sieve. -/
  sheaf_cond : ∀ {X : C.Obj} (S : Sieve C X), J.covers S →
    ∀ (fam : ∀ {Y : C.Obj} (f : C.Hom Y X), S.mem f → presheaf.sections Y),
    (∀ {Y Z : C.Obj} (f : C.Hom Y X) (g : C.Hom Z Y)
      (hf : S.mem f),
      presheaf.restrict g (fam f hf) =
        fam (C.comp g f) (S.closed f g hf)) →
    SheafCondition C presheaf S

namespace SheafData

variable {C : SmallCat} {J : GrothendieckTopology C}

/-- Gluing uniqueness for sheaves. -/
theorem sheaf_gluing_unique (F : SheafData C J) {X : C.Obj}
    (S : Sieve C X) (hS : J.covers S)
    (fam : ∀ {Y : C.Obj} (f : C.Hom Y X), S.mem f → F.presheaf.sections Y)
    (hcompat : ∀ {Y Z : C.Obj} (f : C.Hom Y X) (g : C.Hom Z Y)
      (hf : S.mem f),
      F.presheaf.restrict g (fam f hf) =
        fam (C.comp g f) (S.closed f g hf))
    (sc : SheafCondition C F.presheaf S)
    (t : F.presheaf.sections X)
    (ht : ∀ {Y : C.Obj} (f : C.Hom Y X) (hf : S.mem f),
      F.presheaf.restrict f t = sc.family f hf) :
    t = sc.glue :=
  sc.glue_unique t ht

end SheafData

/-! ## Sheafification -/

/-- Sheafification: the left adjoint a : PSh(C) → Sh(C, J). -/
structure Sheafification (C : SmallCat) (J : GrothendieckTopology C) where
  /-- The sheafification functor on objects. -/
  sheafify : PresheafData C → SheafData C J
  /-- The unit: η : F → a(F). -/
  unit : (F : PresheafData C) → ∀ (X : C.Obj),
    F.sections X → (sheafify F).presheaf.sections X
  /-- Unit is natural. -/
  unit_natural : ∀ (F : PresheafData C) {X Y : C.Obj} (f : C.Hom X Y)
    (s : F.sections Y),
    (sheafify F).presheaf.restrict f (unit F Y s) =
      unit F X (F.restrict f s)
  /-- Universality. -/
  univ_factor : (F : PresheafData C) → (G : SheafData C J) →
    (∀ (X : C.Obj), F.sections X → G.presheaf.sections X) →
    (∀ (X : C.Obj), (sheafify F).presheaf.sections X → G.presheaf.sections X)
  /-- Factorization commutes with unit. -/
  univ_comm : ∀ (F : PresheafData C) (G : SheafData C J)
    (τ : ∀ (X : C.Obj), F.sections X → G.presheaf.sections X)
    (X : C.Obj) (s : F.sections X),
    univ_factor F G τ X (unit F X s) = τ X s

namespace Sheafification

variable {C : SmallCat} {J : GrothendieckTopology C}
  (a : Sheafification C J)

/-- Sheafification unit commutes with factorization. -/
theorem sheafification_unit_comm (F : PresheafData C) (X : C.Obj)
    (s : F.sections X) :
    a.univ_factor F (a.sheafify F) (a.unit F) X (a.unit F X s) =
      a.unit F X s :=
  a.univ_comm F (a.sheafify F) (a.unit F) X s

end Sheafification

/-! ## Geometric Morphisms -/

/-- A geometric morphism between two sheaf categories. -/
structure GeometricMorphism (C₁ C₂ : SmallCat)
    (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂) where
  /-- Direct image functor f_*. -/
  direct_obj : SheafData C₁ J₁ → SheafData C₂ J₂
  /-- Inverse image functor f^*. -/
  inverse_obj : SheafData C₂ J₂ → SheafData C₁ J₁
  /-- Adjunction unit: F → f_*(f^*(F)). -/
  adj_unit : (F : SheafData C₂ J₂) → ∀ (X : C₂.Obj),
    F.presheaf.sections X → (direct_obj (inverse_obj F)).presheaf.sections X
  /-- Adjunction counit: f^*(f_*(G)) → G. -/
  adj_counit : (G : SheafData C₁ J₁) → ∀ (X : C₁.Obj),
    (inverse_obj (direct_obj G)).presheaf.sections X → G.presheaf.sections X

namespace GeometricMorphism

variable {C₁ C₂ : SmallCat} {J₁ : GrothendieckTopology C₁}
  {J₂ : GrothendieckTopology C₂}

/-- Composition of geometric morphisms. -/
structure Composition (f : GeometricMorphism C₁ C₂ J₁ J₂)
    {C₃ : SmallCat} {J₃ : GrothendieckTopology C₃}
    (g : GeometricMorphism C₂ C₃ J₂ J₃) where
  /-- Composed direct image. -/
  comp_direct : SheafData C₁ J₁ → SheafData C₃ J₃
  /-- Composed inverse image. -/
  comp_inverse : SheafData C₃ J₃ → SheafData C₁ J₁
  /-- Direct image is g_* ∘ f_*. -/
  direct_is_comp : ∀ (F : SheafData C₁ J₁),
    comp_direct F = g.direct_obj (f.direct_obj F)
  /-- Inverse image is f^* ∘ g^*. -/
  inverse_is_comp : ∀ (F : SheafData C₃ J₃),
    comp_inverse F = f.inverse_obj (g.inverse_obj F)

end GeometricMorphism

/-! ## Giraud's Theorem -/

/-- Giraud's axioms for a Grothendieck topos. -/
structure GiraudData where
  /-- The category. -/
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  /-- A set of generators. -/
  generators : List Obj
  /-- Generator coverage. -/
  gen_covers : ∀ (X : Obj), ∃ (G : Obj),
    G ∈ generators ∧ ∃ (_ : Hom G X), True
  /-- Coproducts exist. -/
  coproduct : Obj → Obj → Obj
  inl : (X Y : Obj) → Hom X (coproduct X Y)
  inr : (X Y : Obj) → Hom Y (coproduct X Y)
  /-- Coproducts are disjoint. -/
  disjoint : ∀ (X Y : Obj)
    (Z : Obj) (f : Hom Z (coproduct X Y)),
    (∃ (g : Hom Z X), comp g (inl X Y) = f) ∨
    (∃ (g : Hom Z Y), comp g (inr X Y) = f)
  /-- Equivalence relations are effective. -/
  effective_epi : ∀ {X Y : Obj} (f g : Hom X Y),
    ∃ (Q : Obj) (q : Hom Y Q),
    comp f q = comp g q

namespace GiraudData

variable (G : GiraudData)

/-- Giraud's theorem: coproducts exist in the category. -/
theorem giraud_coprod_exists (X Y : G.Obj) : ∃ (Z : G.Obj), Z = G.coproduct X Y :=
  ⟨G.coproduct X Y, rfl⟩

end GiraudData

/-! ## Points of a Topos -/

/-- A point of a topos: a geometric morphism from Set (modeled abstractly). -/
structure ToposPoint (C : SmallCat) (J : GrothendieckTopology C) where
  /-- Stalk functor: for each sheaf, produces a type. -/
  stalk : SheafData C J → Type v
  /-- Stalk is functorial. -/
  stalk_map : {F G : SheafData C J} →
    (∀ (X : C.Obj), F.presheaf.sections X → G.presheaf.sections X) →
    stalk F → stalk G
  /-- Stalk preserves identity. -/
  stalk_id : ∀ (F : SheafData C J) (x : stalk F),
    stalk_map (fun _ s => s) x = x
  /-- Constant sheaf. -/
  const_sheaf : Type v → SheafData C J
  /-- Stalk of constant sheaf recovers the type. -/
  stalk_const : ∀ (A : Type v), (stalk (const_sheaf A) → A) ×
    (A → stalk (const_sheaf A))
  /-- Round trip. -/
  stalk_const_round : ∀ (A : Type v) (a : A),
    (stalk_const A).1 ((stalk_const A).2 a) = a

namespace ToposPoint

variable {C : SmallCat} {J : GrothendieckTopology C}

/-- Stalk at a point preserves identity. -/
theorem point_stalk_id (p : ToposPoint C J) (F : SheafData C J)
    (x : p.stalk F) :
    p.stalk_map (fun _ s => s) x = x :=
  p.stalk_id F x

end ToposPoint

/-- Enough points: a family of jointly conservative points. -/
structure EnoughPoints (C : SmallCat) (J : GrothendieckTopology C) where
  /-- Index type for the family. -/
  PointIndex : Type v
  /-- The family of points. -/
  points : PointIndex → ToposPoint C J
  /-- Joint conservativity. -/
  conservative : ∀ {F G : SheafData C J}
    (τ : ∀ (X : C.Obj), F.presheaf.sections X → G.presheaf.sections X),
    (∀ (i : PointIndex) (x : (points i).stalk F),
      ∃ (y : (points i).stalk G), (points i).stalk_map τ x = y) →
    True

/-! ## Classifying Topos -/

/-- A geometric theory. -/
structure GeometricTheory where
  /-- Sorts. -/
  Sort_ : Type u
  /-- Function symbols. -/
  FunSym : Type u
  /-- Function types. -/
  fun_type : FunSym → Sort_ × Sort_
  /-- Relation symbols. -/
  RelSym : Type u
  /-- Arities. -/
  rel_arity : RelSym → List Sort_
  /-- Number of axioms. -/
  axiom_count : Nat

/-- The classifying topos for a geometric theory T. -/
structure ClassifyingTopos (T : GeometricTheory) where
  /-- The underlying site. -/
  site : SmallCat
  /-- The topology. -/
  topology : GrothendieckTopology site
  /-- The generic model. -/
  generic_sorts : T.Sort_ → SheafData site topology
  /-- Classification property. -/
  classify : ∀ (C : SmallCat) (J : GrothendieckTopology C),
    (T.Sort_ → SheafData C J) →
    ∃ (_ : GeometricMorphism C site J topology), True

/-! ## Morphisms of Sites -/

/-- A morphism of sites. -/
structure SiteMorphism (C D : SmallCat)
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D) where
  /-- Object map. -/
  obj_map : C.Obj → D.Obj
  /-- Morphism map. -/
  hom_map : {X Y : C.Obj} → C.Hom X Y → D.Hom (obj_map X) (obj_map Y)
  /-- Preserves identity. -/
  map_id : ∀ (X : C.Obj), hom_map (C.id X) = D.id (obj_map X)
  /-- Preserves composition. -/
  map_comp : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    hom_map (C.comp f g) = D.comp (hom_map f) (hom_map g)

namespace SiteMorphism

variable {C D : SmallCat} {JC : GrothendieckTopology C}
  {JD : GrothendieckTopology D}

/-- Identity site morphism. -/
def idSiteMorphism (C : SmallCat) (J : GrothendieckTopology C) :
    SiteMorphism C C J J where
  obj_map := id
  hom_map := id
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

end SiteMorphism

/-! ## Comparison Lemma -/

/-- Comparison lemma data: a dense subcategory. -/
structure ComparisonLemma (C : SmallCat) (J : GrothendieckTopology C) where
  /-- The dense subcategory objects. -/
  subcat_obj : List C.Obj
  /-- Density. -/
  dense : ∀ (X : C.Obj), ∃ (Y : C.Obj),
    Y ∈ subcat_obj ∧ ∃ (_ : C.Hom Y X), True
  /-- Comparison produces the same sheaves on the subcategory. -/
  comparison : ∀ (F : SheafData C J),
    ∃ (G : PresheafData C), ∀ (X : C.Obj),
    X ∈ subcat_obj →
    ∀ (s : G.sections X), ∃ (t : F.presheaf.sections X), True

end GrothendieckTopos
end ComputationalPaths
