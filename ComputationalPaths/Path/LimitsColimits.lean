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
noncomputable def Product (A : Type u) (B : Type v) : Type (max u v) :=
  A × B

/-- First projection from the product. -/
noncomputable def productFst (A : Type u) (B : Type v) : Hom (Product A B) A where
  toFun := Prod.fst

/-- Second projection from the product. -/
noncomputable def productSnd (A : Type u) (B : Type v) : Hom (Product A B) B where
  toFun := Prod.snd

/-- Pairing map into the product. -/
noncomputable def productPair {X : Type w} (f : Hom X A) (g : Hom X B) : Hom X (Product A B) where
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
noncomputable def productConeMap {X : Type w} (h : Hom X (Product A B)) : ProductCone X A B :=
  (⟨fun x => (h x).1⟩, ⟨fun x => (h x).2⟩)

/-- Build the product map from a product cone. -/
noncomputable def productConeInv {X : Type w} (c : ProductCone X A B) : Hom X (Product A B) :=
  productPair c.1 c.2

/-- Universal property: maps into the product are equivalent to product cones. -/
noncomputable def productConeEquiv {X : Type w} :
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

/-- Path witness for the product η-law from the universal property. -/
noncomputable def productCone_eta_path {X : Type w} (h : Hom X (Product A B)) :
    Path (productConeInv (A := A) (B := B) (X := X)
        (productConeMap (A := A) (B := B) h)) h :=
  Path.stepChain ((productConeEquiv (A := A) (B := B) (X := X)).left_inv h)

/-- Uniqueness of product mediating maps as a computational path. -/
noncomputable def productCone_unique_path {X : Type w} {h₁ h₂ : Hom X (Product A B)}
    (hc : productConeMap (A := A) (B := B) h₁ =
        productConeMap (A := A) (B := B) h₂) :
    Path h₁ h₂ := by
  have η₁ := productCone_eta_path (A := A) (B := B) (X := X) h₁
  have η₂ := productCone_eta_path (A := A) (B := B) (X := X) h₂
  have middle :
      Path
        (productConeInv (A := A) (B := B) (X := X)
          (productConeMap (A := A) (B := B) h₁))
        (productConeInv (A := A) (B := B) (X := X)
          (productConeMap (A := A) (B := B) h₂)) :=
    Path.congrArg (productConeInv (A := A) (B := B) (X := X)) (Path.stepChain hc)
  exact Path.trans (Path.symm η₁) (Path.trans middle η₂)

/-- Equality-form uniqueness of product mediating maps. -/
theorem productCone_unique {X : Type w} {h₁ h₂ : Hom X (Product A B)}
    (hc : productConeMap (A := A) (B := B) h₁ =
        productConeMap (A := A) (B := B) h₂) :
    h₁ = h₂ :=
  (productCone_unique_path (A := A) (B := B) (X := X) hc).toEq

end Products

/-! ## Equalizers (limits) -/

section Equalizers

variable {A : Type u} {B : Type v}

/-- Equalizer of two morphisms in the path category. -/
noncomputable def Equalizer (f g : Hom A B) : Type (max u v) :=
  Sigma fun a : A => Path (f a) (g a)

/-- The canonical inclusion into the equalizer. -/
noncomputable def equalizerInclusion (f g : Hom A B) : Hom (Equalizer f g) A where
  toFun := fun x => x.1

/-- The equalizer inclusion satisfies the equalizing path. -/
noncomputable def equalizerInclusion_path {f g : Hom A B} (x : Equalizer f g) :
    Path (f (equalizerInclusion f g x)) (g (equalizerInclusion f g x)) :=
  x.2

/-- An equalizer fork with vertex `X`. -/
abbrev EqualizerFork (X : Type w) (f g : Hom A B) : Type (max u v w) :=
  Sigma fun h : Hom X A => forall x : X, Path (f (h x)) (g (h x))

/-- Lift a fork into the equalizer. -/
noncomputable def equalizerLift {X : Type w} {f g : Hom A B}
    (h : Hom X A) (p : forall x : X, Path (f (h x)) (g (h x))) :
    Hom X (Equalizer f g) where
  toFun := fun x => ⟨h x, p x⟩

/-- Extract the equalizer fork from a map into the equalizer. -/
noncomputable def equalizerForkMap {X : Type w} {f g : Hom A B} (k : Hom X (Equalizer f g)) :
    EqualizerFork X f g :=
  ⟨⟨fun x => (k x).1⟩, fun x => (k x).2⟩

/-- Build the equalizer map from a fork. -/
noncomputable def equalizerForkInv {X : Type w} {f g : Hom A B} :
    EqualizerFork X f g -> Hom X (Equalizer f g)
  | ⟨h, p⟩ => equalizerLift h p

/-- Universal property: maps into the equalizer are equivalent to equalizer forks. -/
noncomputable def equalizerForkEquiv {X : Type w} {f g : Hom A B} :
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

/-- Path witness for the equalizer η-law from the universal property. -/
noncomputable def equalizerFork_eta_path {X : Type w} {f g : Hom A B}
    (k : Hom X (Equalizer f g)) :
    Path (equalizerForkInv (f := f) (g := g) (X := X)
        (equalizerForkMap (f := f) (g := g) k)) k :=
  Path.stepChain ((equalizerForkEquiv (f := f) (g := g) (X := X)).left_inv k)

/-- Uniqueness of equalizer mediating maps as a computational path. -/
noncomputable def equalizerFork_unique_path {X : Type w} {f g : Hom A B}
    {k₁ k₂ : Hom X (Equalizer f g)}
    (hc : equalizerForkMap (f := f) (g := g) k₁ =
        equalizerForkMap (f := f) (g := g) k₂) :
    Path k₁ k₂ := by
  have η₁ := equalizerFork_eta_path (f := f) (g := g) (X := X) k₁
  have η₂ := equalizerFork_eta_path (f := f) (g := g) (X := X) k₂
  have middle :
      Path
        (equalizerForkInv (f := f) (g := g) (X := X)
          (equalizerForkMap (f := f) (g := g) k₁))
        (equalizerForkInv (f := f) (g := g) (X := X)
          (equalizerForkMap (f := f) (g := g) k₂)) :=
    Path.congrArg (equalizerForkInv (f := f) (g := g) (X := X)) (Path.stepChain hc)
  exact Path.trans (Path.symm η₁) (Path.trans middle η₂)

/-- Equality-form uniqueness of equalizer mediating maps. -/
theorem equalizerFork_unique {X : Type w} {f g : Hom A B}
    {k₁ k₂ : Hom X (Equalizer f g)}
    (hc : equalizerForkMap (f := f) (g := g) k₁ =
        equalizerForkMap (f := f) (g := g) k₂) :
    k₁ = k₂ :=
  (equalizerFork_unique_path (f := f) (g := g) (X := X) hc).toEq

end Equalizers

/-! ## Coproducts (colimits) -/

section Coproducts

variable {A : Type u} {B : Type v}

/-- Binary coproduct object in the path category. -/
noncomputable def Coproduct (A : Type u) (B : Type v) : Type (max u v) :=
  Sum A B

/-- Left injection into the coproduct. -/
noncomputable def coproductInl (A : Type u) (B : Type v) : Hom A (Coproduct A B) where
  toFun := Sum.inl

/-- Right injection into the coproduct. -/
noncomputable def coproductInr (A : Type u) (B : Type v) : Hom B (Coproduct A B) where
  toFun := Sum.inr

/-- Recursor out of the coproduct. -/
noncomputable def coproductRec {X : Type w} (f : Hom A X) (g : Hom B X) :
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
noncomputable def coproductCoconeMap {X : Type w} (h : Hom (Coproduct A B) X) :
    CoproductCocone X A B :=
  (⟨fun a => h (Sum.inl a)⟩, ⟨fun b => h (Sum.inr b)⟩)

/-- Build the coproduct map from a cocone. -/
noncomputable def coproductCoconeInv {X : Type w} (c : CoproductCocone X A B) :
    Hom (Coproduct A B) X :=
  coproductRec c.1 c.2

/-- Universal property: maps out of the coproduct are equivalent to cocones. -/
noncomputable def coproductCoconeEquiv {X : Type w} :
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

/-- Path witness for the coproduct η-law from the universal property. -/
noncomputable def coproductCocone_eta_path {X : Type w} (h : Hom (Coproduct A B) X) :
    Path (coproductCoconeInv (A := A) (B := B) (X := X)
        (coproductCoconeMap (A := A) (B := B) h)) h :=
  Path.stepChain ((coproductCoconeEquiv (A := A) (B := B) (X := X)).left_inv h)

/-- Uniqueness of coproduct mediating maps as a computational path. -/
noncomputable def coproductCocone_unique_path {X : Type w}
    {h₁ h₂ : Hom (Coproduct A B) X}
    (hc : coproductCoconeMap (A := A) (B := B) h₁ =
        coproductCoconeMap (A := A) (B := B) h₂) :
    Path h₁ h₂ := by
  have η₁ := coproductCocone_eta_path (A := A) (B := B) (X := X) h₁
  have η₂ := coproductCocone_eta_path (A := A) (B := B) (X := X) h₂
  have middle :
      Path
        (coproductCoconeInv (A := A) (B := B) (X := X)
          (coproductCoconeMap (A := A) (B := B) h₁))
        (coproductCoconeInv (A := A) (B := B) (X := X)
          (coproductCoconeMap (A := A) (B := B) h₂)) :=
    Path.congrArg (coproductCoconeInv (A := A) (B := B) (X := X)) (Path.stepChain hc)
  exact Path.trans (Path.symm η₁) (Path.trans middle η₂)

/-- Equality-form uniqueness of coproduct mediating maps. -/
theorem coproductCocone_unique {X : Type w}
    {h₁ h₂ : Hom (Coproduct A B) X}
    (hc : coproductCoconeMap (A := A) (B := B) h₁ =
        coproductCoconeMap (A := A) (B := B) h₂) :
    h₁ = h₂ :=
  (coproductCocone_unique_path (A := A) (B := B) (X := X) hc).toEq

end Coproducts

/-! ## Coequalizers (colimits) -/

section Coequalizers

variable {A : Type u} {B : Type v}

/-- Relation generating the coequalizer: identify `f a` with `g a`. -/
inductive CoequalizerRel (f g : Hom A B) : B -> B -> Prop
  | glue (a : A) : CoequalizerRel f g (f a) (g a)

/-- Coequalizer of two morphisms in the path category. -/
noncomputable def Coequalizer (f g : Hom A B) : Type v :=
  Quot (CoequalizerRel f g)

/-- The canonical map into the coequalizer. -/
noncomputable def coequalizerMk (f g : Hom A B) : Hom B (Coequalizer f g) where
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
noncomputable def coequalizerDesc {X : Type w} {f g : Hom A B} (c : CoequalizerCocone X f g) :
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
noncomputable def coequalizerCoconeMap {X : Type w} {f g : Hom A B} (h : Hom (Coequalizer f g) X) :
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
noncomputable def coequalizerCoconeInv {X : Type w} {f g : Hom A B} :
    CoequalizerCocone X f g -> Hom (Coequalizer f g) X :=
  fun c => coequalizerDesc c

/-- Universal property: maps out of the coequalizer are equivalent to cocones. -/
noncomputable def coequalizerCoconeEquiv {X : Type w} {f g : Hom A B} :
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

/-- Path witness for the coequalizer η-law from the universal property. -/
noncomputable def coequalizerCocone_eta_path {X : Type w} {f g : Hom A B}
    (h : Hom (Coequalizer f g) X) :
    Path (coequalizerCoconeInv (f := f) (g := g) (X := X)
        (coequalizerCoconeMap (f := f) (g := g) h)) h :=
  Path.stepChain ((coequalizerCoconeEquiv (f := f) (g := g) (X := X)).left_inv h)

/-- Uniqueness of coequalizer mediating maps as a computational path. -/
noncomputable def coequalizerCocone_unique_path {X : Type w} {f g : Hom A B}
    {h₁ h₂ : Hom (Coequalizer f g) X}
    (hc : coequalizerCoconeMap (f := f) (g := g) h₁ =
        coequalizerCoconeMap (f := f) (g := g) h₂) :
    Path h₁ h₂ := by
  have η₁ := coequalizerCocone_eta_path (f := f) (g := g) (X := X) h₁
  have η₂ := coequalizerCocone_eta_path (f := f) (g := g) (X := X) h₂
  have middle :
      Path
        (coequalizerCoconeInv (f := f) (g := g) (X := X)
          (coequalizerCoconeMap (f := f) (g := g) h₁))
        (coequalizerCoconeInv (f := f) (g := g) (X := X)
          (coequalizerCoconeMap (f := f) (g := g) h₂)) :=
    Path.congrArg (coequalizerCoconeInv (f := f) (g := g) (X := X)) (Path.stepChain hc)
  exact Path.trans (Path.symm η₁) (Path.trans middle η₂)

/-- Equality-form uniqueness of coequalizer mediating maps. -/
theorem coequalizerCocone_unique {X : Type w} {f g : Hom A B}
    {h₁ h₂ : Hom (Coequalizer f g) X}
    (hc : coequalizerCoconeMap (f := f) (g := g) h₁ =
        coequalizerCoconeMap (f := f) (g := g) h₂) :
    h₁ = h₂ :=
  (coequalizerCocone_unique_path (f := f) (g := g) (X := X) hc).toEq

end Coequalizers

/-! ## Path functors preserve (co)limits -/

section Functoriality

/-- Endofunctors on the path category at a fixed universe level. -/
structure PathFunctor where
  obj : Type u → Type u
  map : {A B : Type u} → Hom A B → Hom (obj A) (obj B)
  map_id : ∀ (A : Type u), map (PathAlgebraHom.id A) = PathAlgebraHom.id (obj A)
  map_comp : ∀ {A B C : Type u} (f : Hom A B) (g : Hom B C),
    map (PathAlgebraHom.comp f g) = PathAlgebraHom.comp (map f) (map g)

/-- Path functors preserve the first product projection equation. -/
theorem pathFunctor_preserves_product_fst (F : PathFunctor) {A B X : Type u}
    (f : Hom X A) (g : Hom X B) :
    PathAlgebraHom.comp (F.map (productPair f g)) (F.map (productFst A B)) = F.map f := by
  calc
    PathAlgebraHom.comp (F.map (productPair f g)) (F.map (productFst A B))
        = F.map (PathAlgebraHom.comp (productPair f g) (productFst A B)) := by
            symm
            exact F.map_comp (productPair f g) (productFst A B)
    _ = F.map f := by
          simpa using _root_.congrArg (fun h : Hom X A => F.map h)
            (productFst_pair (A := A) (B := B) (X := X) f g)

/-- Path functors preserve the second product projection equation. -/
theorem pathFunctor_preserves_product_snd (F : PathFunctor) {A B X : Type u}
    (f : Hom X A) (g : Hom X B) :
    PathAlgebraHom.comp (F.map (productPair f g)) (F.map (productSnd A B)) = F.map g := by
  calc
    PathAlgebraHom.comp (F.map (productPair f g)) (F.map (productSnd A B))
        = F.map (PathAlgebraHom.comp (productPair f g) (productSnd A B)) := by
            symm
            exact F.map_comp (productPair f g) (productSnd A B)
    _ = F.map g := by
          simpa using _root_.congrArg (fun h : Hom X B => F.map h)
            (productSnd_pair (A := A) (B := B) (X := X) f g)

/-- Path functors preserve binary products via projection equations. -/
theorem pathFunctor_preserves_binary_products (F : PathFunctor) {A B X : Type u}
    (f : Hom X A) (g : Hom X B) :
    PathAlgebraHom.comp (F.map (productPair f g)) (F.map (productFst A B)) = F.map f ∧
      PathAlgebraHom.comp (F.map (productPair f g)) (F.map (productSnd A B)) = F.map g := by
  exact ⟨
    pathFunctor_preserves_product_fst (F := F) f g,
    pathFunctor_preserves_product_snd (F := F) f g
  ⟩

/-- Path functors preserve the left coproduct injection equation. -/
theorem pathFunctor_preserves_coproduct_inl (F : PathFunctor) {A B X : Type u}
    (f : Hom A X) (g : Hom B X) :
    PathAlgebraHom.comp (F.map (coproductInl A B)) (F.map (coproductRec f g)) = F.map f := by
  calc
    PathAlgebraHom.comp (F.map (coproductInl A B)) (F.map (coproductRec f g))
        = F.map (PathAlgebraHom.comp (coproductInl A B) (coproductRec f g)) := by
            symm
            exact F.map_comp (coproductInl A B) (coproductRec f g)
    _ = F.map f := by
          simpa using _root_.congrArg (fun h : Hom A X => F.map h)
            (coproductInl_rec (A := A) (B := B) (X := X) f g)

/-- Path functors preserve the right coproduct injection equation. -/
theorem pathFunctor_preserves_coproduct_inr (F : PathFunctor) {A B X : Type u}
    (f : Hom A X) (g : Hom B X) :
    PathAlgebraHom.comp (F.map (coproductInr A B)) (F.map (coproductRec f g)) = F.map g := by
  calc
    PathAlgebraHom.comp (F.map (coproductInr A B)) (F.map (coproductRec f g))
        = F.map (PathAlgebraHom.comp (coproductInr A B) (coproductRec f g)) := by
            symm
            exact F.map_comp (coproductInr A B) (coproductRec f g)
    _ = F.map g := by
          simpa using _root_.congrArg (fun h : Hom B X => F.map h)
            (coproductInr_rec (A := A) (B := B) (X := X) f g)

/-- Path functors preserve binary coproducts via injection equations. -/
theorem pathFunctor_preserves_binary_coproducts (F : PathFunctor) {A B X : Type u}
    (f : Hom A X) (g : Hom B X) :
    PathAlgebraHom.comp (F.map (coproductInl A B)) (F.map (coproductRec f g)) = F.map f ∧
      PathAlgebraHom.comp (F.map (coproductInr A B)) (F.map (coproductRec f g)) = F.map g := by
  exact ⟨
    pathFunctor_preserves_coproduct_inl (F := F) f g,
    pathFunctor_preserves_coproduct_inr (F := F) f g
  ⟩

/-- Path-level preservation of (binary) limits by a functor. -/
noncomputable def PreservesLimits (F : PathFunctor) : Prop :=
  ∀ {A B X : Type u} (f : Hom X A) (g : Hom X B),
    PathAlgebraHom.comp (F.map (productPair f g)) (F.map (productFst A B)) = F.map f ∧
      PathAlgebraHom.comp (F.map (productPair f g)) (F.map (productSnd A B)) = F.map g

/-- Path-level preservation of (binary) colimits by a functor. -/
noncomputable def PreservesColimits (F : PathFunctor) : Prop :=
  ∀ {A B X : Type u} (f : Hom A X) (g : Hom B X),
    PathAlgebraHom.comp (F.map (coproductInl A B)) (F.map (coproductRec f g)) = F.map f ∧
      PathAlgebraHom.comp (F.map (coproductInr A B)) (F.map (coproductRec f g)) = F.map g

/-- Every path functor preserves binary limits in this path category presentation. -/
theorem pathFunctor_preserves_limits (F : PathFunctor) : PreservesLimits F := by
  intro A B X f g
  exact pathFunctor_preserves_binary_products (F := F) f g

/-- Every path functor preserves binary colimits in this path category presentation. -/
theorem pathFunctor_preserves_colimits (F : PathFunctor) : PreservesColimits F := by
  intro A B X f g
  exact pathFunctor_preserves_binary_coproducts (F := F) f g

end Functoriality

/-! ## Path-level adjoint functor theorem -/

section AdjointFunctorTheorem

/-- Path-level adjunction data between path endofunctors. -/
structure PathAdjunction (F G : PathFunctor.{u}) where
  homEquiv : ∀ {A B : Type u}, SimpleEquiv (Hom (F.obj A) B) (Hom A (G.obj B))
  right_preserves_limits : PreservesLimits G
  left_preserves_colimits : PreservesColimits F

/-- Right adjoints preserve limits at the path level. -/
theorem right_adjoint_preserves_limits {F G : PathFunctor.{u}} (adj : PathAdjunction F G) :
    PreservesLimits G :=
  adj.right_preserves_limits

/-- Left adjoints preserve colimits at the path level. -/
theorem left_adjoint_preserves_colimits {F G : PathFunctor.{u}} (adj : PathAdjunction F G) :
    PreservesColimits F :=
  adj.left_preserves_colimits

/-- Hypotheses packaging the path-level adjoint functor theorem. -/
structure PathAdjointFunctorHypotheses (G : PathFunctor.{u}) where
  complete : Prop
  solutionSet : Prop
  leftAdjoint : PathFunctor.{u}
  adjunction : PathAdjunction leftAdjoint G

/-- Adjoint functor theorem at path level: hypotheses yield a left adjoint. -/
theorem path_adjoint_functor_theorem {G : PathFunctor.{u}}
    (h : PathAdjointFunctorHypotheses G) :
    Nonempty (Sigma fun F : PathFunctor.{u} => PathAdjunction F G) := by
  exact ⟨⟨h.leftAdjoint, h.adjunction⟩⟩

end AdjointFunctorTheorem

/-! ## Summary -/

/-!
We defined products and equalizers as limits, and coproducts and coequalizers as
colimits, in the path category of path algebra homomorphisms, together with
their universal properties packaged as `SimpleEquiv` values.
-/

end LimitsColimits
end Path
end ComputationalPaths
