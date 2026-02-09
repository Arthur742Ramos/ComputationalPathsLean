/-
# Limits and Colimits in the Path Category

This module formalizes limits and colimits in the path category whose objects
are types and whose morphisms are path algebra homomorphisms. We define binary
products and equalizers as limits, and binary coproducts and coequalizers as
colimits, together with their universal properties.

## Key Results
- `Product`, `productConeEquiv`: products and their universal property.
- `Equalizer`, `equalizerForkEquiv`: equalizers and their universal property.
- `Coproduct`, `coproductCoconeEquiv`: coproducts and their universal property.
- `Coequalizer`, `coequalizerCoconeEquiv`: coequalizers and their universal property.

## References
- Mac Lane, "Categories for the Working Mathematician"
- HoTT Book, Chapter 2
-/

import ComputationalPaths.Path.PathAlgebraHomomorphism

namespace ComputationalPaths
namespace Path
namespace LimitsColimits

universe u v w

/-! ## Morphisms in the path category -/

/-- Morphisms in the path category (path algebra homomorphisms). -/
abbrev Hom (A : Type u) (B : Type v) : Type (max u v) :=
  PathAlgebraHom A B

namespace PathAlgebraHom

/-- Extensionality for path algebra homomorphisms. -/
@[ext] theorem ext {A : Type u} {B : Type v} {f g : PathAlgebraHom A B}
    (h : forall x, f x = g x) : f = g := by
  cases f with
  | mk ffun =>
      cases g with
      | mk gfun =>
          have hfun : ffun = gfun := funext h
          cases hfun
          rfl

end PathAlgebraHom

/-! ## Products (limits) -/

section Products

variable {A : Type u} {B : Type v}

/-- Binary product object in the path category. -/
def Product (A : Type u) (B : Type v) : Type (max u v) :=
  A × B

/-- First projection from the product. -/
def productFst (A : Type u) (B : Type v) : Hom (Product A B) A where
  toFun := Prod.fst

/-- Second projection from the product. -/
def productSnd (A : Type u) (B : Type v) : Hom (Product A B) B where
  toFun := Prod.snd

/-- Pairing map into the product. -/
def productPair {X : Type w} (f : Hom X A) (g : Hom X B) : Hom X (Product A B) where
  toFun := fun x => (f x, g x)

/-- Pairing followed by the first projection recovers the first component. -/
@[simp] theorem productFst_pair {X : Type w} (f : Hom X A) (g : Hom X B) :
    PathAlgebraHom.comp (productPair f g) (productFst A B) = f := by
  apply PathAlgebraHom.ext
  intro x
  rfl

/-- Pairing followed by the second projection recovers the second component. -/
@[simp] theorem productSnd_pair {X : Type w} (f : Hom X A) (g : Hom X B) :
    PathAlgebraHom.comp (productPair f g) (productSnd A B) = g := by
  apply PathAlgebraHom.ext
  intro x
  rfl

/-- A cone over the product diagram with vertex `X`. -/
abbrev ProductCone (X : Type w) (A : Type u) (B : Type v) : Type (max u v w) :=
  Hom X A × Hom X B

/-- Extract the product cone from a map into the product. -/
def productConeMap {X : Type w} (h : Hom X (Product A B)) : ProductCone X A B :=
  (⟨fun x => (h x).1⟩, ⟨fun x => (h x).2⟩)

/-- Build the product map from a product cone. -/
def productConeInv {X : Type w} (c : ProductCone X A B) : Hom X (Product A B) :=
  productPair c.1 c.2

/-- Universal property: maps into the product are equivalent to product cones. -/
def productConeEquiv {X : Type w} :
    SimpleEquiv (Hom X (Product A B)) (ProductCone X A B) where
  toFun := productConeMap (A := A) (B := B)
  invFun := productConeInv (A := A) (B := B)
  left_inv := by
    intro h
    cases h with
    | mk hfun =>
      apply PathAlgebraHom.ext
      intro x
      cases hfun x with
      | mk a b => rfl
  right_inv := by
    intro c
    cases c with
    | mk f g =>
        cases f
        cases g
        rfl

end Products

/-! ## Equalizers (limits) -/

section Equalizers

variable {A : Type u} {B : Type v}

/-- Equalizer of two morphisms in the path category. -/
def Equalizer (f g : Hom A B) : Type (max u v) :=
  Sigma fun a : A => Path (f a) (g a)

/-- The canonical inclusion into the equalizer. -/
def equalizerInclusion (f g : Hom A B) : Hom (Equalizer f g) A where
  toFun := fun x => x.1

/-- The equalizer inclusion satisfies the equalizing path. -/
def equalizerInclusion_path {f g : Hom A B} (x : Equalizer f g) :
    Path (f (equalizerInclusion f g x)) (g (equalizerInclusion f g x)) :=
  x.2

/-- An equalizer fork with vertex `X`. -/
abbrev EqualizerFork (X : Type w) (f g : Hom A B) : Type (max u v w) :=
  Sigma fun h : Hom X A => forall x : X, Path (f (h x)) (g (h x))

/-- Lift a fork into the equalizer. -/
def equalizerLift {X : Type w} {f g : Hom A B}
    (h : Hom X A) (p : forall x : X, Path (f (h x)) (g (h x))) :
    Hom X (Equalizer f g) where
  toFun := fun x => ⟨h x, p x⟩

/-- Extract the equalizer fork from a map into the equalizer. -/
def equalizerForkMap {X : Type w} {f g : Hom A B} (k : Hom X (Equalizer f g)) :
    EqualizerFork X f g :=
  ⟨⟨fun x => (k x).1⟩, fun x => (k x).2⟩

/-- Build the equalizer map from a fork. -/
def equalizerForkInv {X : Type w} {f g : Hom A B} :
    EqualizerFork X f g -> Hom X (Equalizer f g)
  | ⟨h, p⟩ => equalizerLift h p

/-- Universal property: maps into the equalizer are equivalent to equalizer forks. -/
def equalizerForkEquiv {X : Type w} {f g : Hom A B} :
    SimpleEquiv (Hom X (Equalizer f g)) (EqualizerFork X f g) where
  toFun := equalizerForkMap (f := f) (g := g)
  invFun := equalizerForkInv (f := f) (g := g)
  left_inv := by
    intro k
    cases k with
    | mk kfun =>
      apply PathAlgebraHom.ext
      intro x
      cases kfun x with
      | mk a p => rfl
  right_inv := by
    intro c
    cases c with
    | mk h p =>
        cases h
        rfl

end Equalizers

/-! ## Coproducts (colimits) -/

section Coproducts

variable {A : Type u} {B : Type v}

/-- Binary coproduct object in the path category. -/
def Coproduct (A : Type u) (B : Type v) : Type (max u v) :=
  Sum A B

/-- Left injection into the coproduct. -/
def coproductInl (A : Type u) (B : Type v) : Hom A (Coproduct A B) where
  toFun := Sum.inl

/-- Right injection into the coproduct. -/
def coproductInr (A : Type u) (B : Type v) : Hom B (Coproduct A B) where
  toFun := Sum.inr

/-- Recursor out of the coproduct. -/
def coproductRec {X : Type w} (f : Hom A X) (g : Hom B X) :
    Hom (Coproduct A B) X where
  toFun := fun
    | Sum.inl a => f a
    | Sum.inr b => g b

/-- Recursor followed by left injection recovers the left map. -/
@[simp] theorem coproductInl_rec {X : Type w} (f : Hom A X) (g : Hom B X) :
    PathAlgebraHom.comp (coproductInl A B) (coproductRec f g) = f := by
  apply PathAlgebraHom.ext
  intro a
  rfl

/-- Recursor followed by right injection recovers the right map. -/
@[simp] theorem coproductInr_rec {X : Type w} (f : Hom A X) (g : Hom B X) :
    PathAlgebraHom.comp (coproductInr A B) (coproductRec f g) = g := by
  apply PathAlgebraHom.ext
  intro b
  rfl

/-- A cocone over the coproduct diagram with vertex `X`. -/
abbrev CoproductCocone (X : Type w) (A : Type u) (B : Type v) : Type (max u v w) :=
  Hom A X × Hom B X

/-- Extract the coproduct cocone from a map out of the coproduct. -/
def coproductCoconeMap {X : Type w} (h : Hom (Coproduct A B) X) :
    CoproductCocone X A B :=
  (⟨fun a => h (Sum.inl a)⟩, ⟨fun b => h (Sum.inr b)⟩)

/-- Build the coproduct map from a cocone. -/
def coproductCoconeInv {X : Type w} (c : CoproductCocone X A B) :
    Hom (Coproduct A B) X :=
  coproductRec c.1 c.2

/-- Universal property: maps out of the coproduct are equivalent to cocones. -/
def coproductCoconeEquiv {X : Type w} :
    SimpleEquiv (Hom (Coproduct A B) X) (CoproductCocone X A B) where
  toFun := coproductCoconeMap (A := A) (B := B)
  invFun := coproductCoconeInv (A := A) (B := B)
  left_inv := by
    intro h
    apply PathAlgebraHom.ext
    intro x
    cases x with
    | inl a => rfl
    | inr b => rfl
  right_inv := by
    intro c
    cases c with
    | mk f g =>
        cases f
        cases g
        rfl

end Coproducts

/-! ## Coequalizers (colimits) -/

section Coequalizers

variable {A : Type u} {B : Type v}

/-- Relation generating the coequalizer: identify `f a` with `g a`. -/
inductive CoequalizerRel (f g : Hom A B) : B -> B -> Prop
  | glue (a : A) : CoequalizerRel f g (f a) (g a)

/-- Coequalizer of two morphisms in the path category. -/
def Coequalizer (f g : Hom A B) : Type v :=
  Quot (CoequalizerRel f g)

/-- The canonical map into the coequalizer. -/
def coequalizerMk (f g : Hom A B) : Hom B (Coequalizer f g) where
  toFun := fun b => Quot.mk (CoequalizerRel f g) b

/-- The coequalizer map identifies `f a` and `g a`. -/
@[simp] theorem coequalizerMk_glue (f g : Hom A B) (a : A) :
    coequalizerMk f g (f a) = coequalizerMk f g (g a) := by
  apply Quot.sound
  exact CoequalizerRel.glue (f := f) (g := g) a

/-- A cocone over the coequalizer diagram with vertex `X`. -/
abbrev CoequalizerCocone (X : Type w) (f g : Hom A B) : Type (max v w) :=
  { h : Hom B X // forall a : A, h (f a) = h (g a) }

/-- Descend a cocone to the coequalizer. -/
def coequalizerDesc {X : Type w} {f g : Hom A B} (c : CoequalizerCocone X f g) :
    Hom (Coequalizer f g) X where
  toFun :=
    Quot.lift
      (fun b => c.1 b)
      (fun _ _ h => by
        cases h with
        | glue a => exact c.2 a)

/-- Evaluate the coequalizer descent on a representative. -/
@[simp] theorem coequalizerDesc_mk {X : Type w} {f g : Hom A B}
    (c : CoequalizerCocone X f g) (b : B) :
    coequalizerDesc c (Quot.mk (CoequalizerRel f g) b) = c.1 b := rfl

/-- Build a coequalizer cocone from a map out of the coequalizer. -/
def coequalizerCoconeMap {X : Type w} {f g : Hom A B} (h : Hom (Coequalizer f g) X) :
    CoequalizerCocone X f g :=
  ⟨
    ⟨fun b => h (Quot.mk (CoequalizerRel f g) b)⟩,
    by
      intro a
      have hrel : Quot.mk (CoequalizerRel f g) (f a) =
          Quot.mk (CoequalizerRel f g) (g a) :=
        Quot.sound (CoequalizerRel.glue (f := f) (g := g) a)
      simpa using _root_.congrArg h.toFun hrel
  ⟩

/-- Build the coequalizer map from a cocone. -/
def coequalizerCoconeInv {X : Type w} {f g : Hom A B} :
    CoequalizerCocone X f g -> Hom (Coequalizer f g) X :=
  fun c => coequalizerDesc c

/-- Universal property: maps out of the coequalizer are equivalent to cocones. -/
def coequalizerCoconeEquiv {X : Type w} {f g : Hom A B} :
    SimpleEquiv (Hom (Coequalizer f g) X) (CoequalizerCocone X f g) where
  toFun := coequalizerCoconeMap (f := f) (g := g)
  invFun := coequalizerCoconeInv (f := f) (g := g)
  left_inv := by
    intro h
    apply PathAlgebraHom.ext
    intro x
    refine Quot.inductionOn x (fun b => ?_)
    rfl
  right_inv := by
    intro c
    apply Subtype.ext
    apply PathAlgebraHom.ext
    intro b
    rfl

end Coequalizers

/-! ## Summary -/

/-!
We defined products and equalizers as limits, and coproducts and coequalizers as
colimits, in the path category of path algebra homomorphisms, together with
their universal properties packaged as `SimpleEquiv` values.
-/

end LimitsColimits
end Path
end ComputationalPaths
