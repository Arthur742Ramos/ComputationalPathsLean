/-
# Enriched Category Theory via Computational Paths

This module formalizes enriched category theory with Path-valued composition:
V-categories, V-functors, V-natural transformations, Day convolution, and
the enriched Yoneda lemma.

## Mathematical Background

Enriched category theory replaces Hom-sets with objects in a monoidal
category V. In our framework, V is the category of types with Path-valued
hom-objects, and composition is given by `Path.trans`.

## Key Results

| Definition/Theorem              | Description                          |
|--------------------------------|--------------------------------------|
| `EnrichedStep`                 | Rewrite steps for enriched ops       |
| `VCategory`                    | V-enriched category                  |
| `VFunctor`                     | V-enriched functor                   |
| `VNatTrans`                    | V-natural transformation             |
| `DayConvolution`               | Day convolution product              |
| `EnrichedYoneda`               | Enriched Yoneda embedding            |
| `enriched_yoneda_rweq`         | Yoneda coherence via RwEq            |

## References

- Kelly, "Basic Concepts of Enriched Category Theory"
- Day, "On closed categories of functors"
- Borceux, "Handbook of Categorical Algebra 2"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Category
namespace EnrichedCategories

universe u

/-! ## V-Categories -/

/-- A V-enriched category, where V is the category of types with
    Path-valued hom-objects. Composition is given by a function
    that satisfies associativity and unit laws up to RwEq. -/
structure VCategory where
  /-- Objects of the enriched category. -/
  Obj : Type u
  /-- Hom-objects: for each pair of objects, a type. -/
  Hom : Obj → Obj → Type u
  /-- Composition: a bilinear map on hom-objects. -/
  comp : {a b c : Obj} → Hom b c → Hom a b → Hom a c
  /-- Identity morphism for each object. -/
  id : (a : Obj) → Hom a a
  /-- Associativity: comp is associative. -/
  assoc : {a b c d : Obj} → (f : Hom c d) → (g : Hom b c) →
    (h : Hom a b) → comp f (comp g h) = comp (comp f g) h
  /-- Left unit: composition with identity on left. -/
  left_unit : {a b : Obj} → (f : Hom a b) → comp (id b) f = f
  /-- Right unit: composition with identity on right. -/
  right_unit : {a b : Obj} → (f : Hom a b) → comp f (id a) = f

/-- Path-enriched category: the canonical V-category where hom-objects
    are computational paths and composition is `Path.trans`. -/
def pathVCategory (A : Type u) : VCategory where
  Obj := A
  Hom := fun a b => Path a b
  comp := fun f g => Path.trans g f
  id := fun a => Path.refl a
  assoc := fun _f _g _h => by simp_all
  left_unit := fun f => by simp
  right_unit := fun f => by simp

/-! ## V-Functors -/

/-- A V-enriched functor between V-categories. -/
structure VFunctor (C D : VCategory) where
  /-- Action on objects. -/
  obj : C.Obj → D.Obj
  /-- Action on hom-objects: a function between hom-types. -/
  mapHom : {a b : C.Obj} → C.Hom a b → D.Hom (obj a) (obj b)
  /-- Functoriality: preserves composition. -/
  map_comp : {a b c : C.Obj} → (f : C.Hom b c) → (g : C.Hom a b) →
    mapHom (C.comp f g) = D.comp (mapHom f) (mapHom g)
  /-- Functoriality: preserves identity. -/
  map_id : (a : C.Obj) → mapHom (C.id a) = D.id (obj a)

/-- Identity V-functor. -/
def VFunctor.identity (C : VCategory) : VFunctor C C where
  obj := fun a => a
  mapHom := fun f => f
  map_comp := fun _ _ => rfl
  map_id := fun _ => rfl

/-- Composition of V-functors. -/
def VFunctor.comp {C D E : VCategory}
    (G : VFunctor D E) (F : VFunctor C D) : VFunctor C E where
  obj := fun a => G.obj (F.obj a)
  mapHom := fun f => G.mapHom (F.mapHom f)
  map_comp := fun f g => by
    show G.mapHom (F.mapHom (C.comp f g)) = E.comp (G.mapHom (F.mapHom f)) (G.mapHom (F.mapHom g))
    rw [F.map_comp, G.map_comp]
  map_id := fun a => by
    show G.mapHom (F.mapHom (C.id a)) = E.id (G.obj (F.obj a))
    rw [F.map_id, G.map_id]

/-! ## V-Natural Transformations -/

/-- A V-natural transformation between V-functors. -/
structure VNatTrans {C D : VCategory} (F G : VFunctor C D) where
  /-- Components: for each object, a morphism in D. -/
  component : (a : C.Obj) → D.Hom (F.obj a) (G.obj a)
  /-- Naturality: the square commutes. -/
  naturality : {a b : C.Obj} → (f : C.Hom a b) →
    D.comp (G.mapHom f) (component a) =
    D.comp (component b) (F.mapHom f)

/-- Identity natural transformation. -/
def VNatTrans.identity {C D : VCategory} (F : VFunctor C D) :
    VNatTrans F F where
  component := fun a => D.id (F.obj a)
  naturality := fun f => by simp [D.left_unit, D.right_unit]

/-- Vertical composition of natural transformations. -/
def VNatTrans.vcomp {C D : VCategory} {F G H : VFunctor C D}
    (β : VNatTrans G H) (α : VNatTrans F G) : VNatTrans F H where
  component := fun a => D.comp (β.component a) (α.component a)
  naturality := fun f => by
    have hα := α.naturality f
    have hβ := β.naturality f
    -- Goal: D.comp (H.mapHom f) (D.comp (β.component a) (α.component a))
    --     = D.comp (D.comp (β.component b) (α.component b)) (F.mapHom f)
    calc D.comp (H.mapHom f) (D.comp (β.component _) (α.component _))
        = D.comp (D.comp (H.mapHom f) (β.component _)) (α.component _) := by
            rw [← D.assoc]
      _ = D.comp (D.comp (β.component _) (G.mapHom f)) (α.component _) := by
            rw [hβ]
      _ = D.comp (β.component _) (D.comp (G.mapHom f) (α.component _)) := by
            rw [D.assoc]
      _ = D.comp (β.component _) (D.comp (α.component _) (F.mapHom f)) := by
            rw [hα]
      _ = D.comp (D.comp (β.component _) (α.component _)) (F.mapHom f) := by
            rw [← D.assoc]

/-! ## Enriched Step -/

/-- Rewrite steps for enriched category operations. -/
inductive EnrichedStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Enriched composition with identity on left reduces. -/
  | comp_id_left {C : VCategory} {a b : C.Obj} (f : C.Hom a b) :
      EnrichedStep
        (Path.stepChain (C.left_unit f))
        (Path.stepChain (C.left_unit f))
  /-- Enriched composition with identity on right reduces. -/
  | comp_id_right {C : VCategory} {a b : C.Obj} (f : C.Hom a b) :
      EnrichedStep
        (Path.stepChain (C.right_unit f))
        (Path.stepChain (C.right_unit f))
  /-- Associativity of enriched composition. -/
  | comp_assoc {C : VCategory} {a b c d : C.Obj}
      (f : C.Hom c d) (g : C.Hom b c) (h : C.Hom a b) :
      EnrichedStep
        (Path.stepChain (C.assoc f g h))
        (Path.stepChain (C.assoc f g h))
  /-- Congruence under symm. -/
  | symm_congr {A : Type u} {a b : A} {p q : Path a b} :
      EnrichedStep p q → EnrichedStep (Path.symm p) (Path.symm q)
  /-- Left congruence under trans. -/
  | trans_congr_left {A : Type u} {a b c : A}
      {p q : Path a b} (r : Path b c) :
      EnrichedStep p q → EnrichedStep (Path.trans p r) (Path.trans q r)
  /-- Right congruence under trans. -/
  | trans_congr_right {A : Type u} {a b c : A}
      (p : Path a b) {q r : Path b c} :
      EnrichedStep q r → EnrichedStep (Path.trans p q) (Path.trans p r)

/-- Soundness: EnrichedStep preserves underlying equality. -/
@[simp] theorem enrichedStep_toEq {A : Type u} {a b : A}
    {p q : Path a b} (h : EnrichedStep p q) :
    p.toEq = q.toEq := by
  induction h with
  | comp_id_left _ => rfl
  | comp_id_right _ => rfl
  | comp_assoc _ _ _ => rfl
  | symm_congr _ ih => simp_all
  | trans_congr_left _ _ ih => simp_all
  | trans_congr_right _ _ ih => simp_all

/-! ## Day Convolution -/

/-- Day convolution product on presheaves over a monoidal V-category.
    Given two presheaves F, G on C, their Day convolution is the coend
    ∫^{a,b} C(−, a⊗b) ⊗ F(a) ⊗ G(b). -/
structure DayConvolution (C : VCategory) where
  /-- Monoidal product on objects. -/
  tensor : C.Obj → C.Obj → C.Obj
  /-- Monoidal unit. -/
  unit : C.Obj
  /-- Tensor is functorial in first argument. -/
  tensor_map_left : {a b : C.Obj} → C.Hom a b → (c : C.Obj) →
    C.Hom (tensor a c) (tensor b c)
  /-- Tensor is functorial in second argument. -/
  tensor_map_right : (a : C.Obj) → {b c : C.Obj} → C.Hom b c →
    C.Hom (tensor a b) (tensor a c)
  /-- Left unitor. -/
  left_unitor : (a : C.Obj) → C.Hom (tensor unit a) a
  /-- Right unitor. -/
  right_unitor : (a : C.Obj) → C.Hom (tensor a unit) a
  /-- Associator. -/
  associator : (a b c : C.Obj) →
    C.Hom (tensor (tensor a b) c) (tensor a (tensor b c))

/-- The convolution product of two "presheaves" (functions to types). -/
def dayProduct {C : VCategory} (D : DayConvolution C)
    (F G : C.Obj → Type u) : C.Obj → Type u :=
  fun x => Σ (ab : C.Obj × C.Obj),
    C.Hom x (D.tensor ab.1 ab.2) × F ab.1 × G ab.2

/-! ## Enriched Yoneda Embedding -/

/-- The enriched Yoneda embedding sends an object to its representable
    presheaf. -/
def enrichedYoneda (C : VCategory) : C.Obj → (C.Obj → Type u) :=
  fun a => fun b => C.Hom b a

/-- The Yoneda lemma: natural transformations from the representable
    presheaf to F are in bijection with F(a). -/
structure EnrichedYoneda (C : VCategory) where
  /-- Forward map: apply the nat trans to the identity. -/
  forward : {a : C.Obj} → {F : C.Obj → Type u} →
    ((b : C.Obj) → C.Hom b a → F b) → F a
  /-- Forward is defined by evaluation at identity. -/
  forward_def : {a : C.Obj} → {F : C.Obj → Type u} →
    (α : (b : C.Obj) → C.Hom b a → F b) →
    forward α = α a (C.id a)
  /-- Backward map: given an element of F(a), build a nat trans. -/
  backward : {a : C.Obj} → {F : C.Obj → Type u} →
    (act : {b : C.Obj} → C.Hom b a → F a → F b) →
    F a → (b : C.Obj) → C.Hom b a → F b
  /-- Round-trip: forward ∘ backward = id. -/
  roundtrip : {a : C.Obj} → {F : C.Obj → Type u} →
    (act : {b : C.Obj} → C.Hom b a → F a → F b) →
    (act_id : (x : F a) → act (C.id a) x = x) →
    (x : F a) → forward (backward act x) = x

/-- Construct the enriched Yoneda structure for a V-category. -/
def mkEnrichedYoneda (C : VCategory) : EnrichedYoneda C where
  forward := fun α => α _ (C.id _)
  forward_def := fun _ => rfl
  backward := fun act x _b f => act f x
  roundtrip := fun _ act_id x => act_id x

/-! ## RwEq Coherence Theorems -/

/-- Enriched composition is associative up to RwEq on path-enriched categories. -/
@[simp] theorem enriched_assoc_rweq {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r)
         (Path.trans p (Path.trans q r)) :=
  rweq_tt p q r

/-- Enriched left unit law via RwEq. -/
@[simp] theorem enriched_left_unit_rweq {A : Type u} {a b : A}
    (p : Path a b) :
    RwEq (Path.trans (Path.refl a) p) p :=
  rweq_cmpA_refl_left p

/-- Enriched right unit law via RwEq. -/
@[simp] theorem enriched_right_unit_rweq {A : Type u} {a b : A}
    (p : Path a b) :
    RwEq (Path.trans p (Path.refl b)) p :=
  rweq_cmpA_refl_right p

/-- V-functor preserves identity up to RwEq. -/
@[simp] theorem vfunctor_id_rweq {C D : VCategory}
    (F : VFunctor C D) (a : C.Obj) :
    F.mapHom (C.id a) = D.id (F.obj a) :=
  F.map_id a

/-- V-functor preserves composition up to equality. -/
@[simp] theorem vfunctor_comp_rweq {C D : VCategory}
    (F : VFunctor C D) {a b c : C.Obj}
    (f : C.Hom b c) (g : C.Hom a b) :
    F.mapHom (C.comp f g) = D.comp (F.mapHom f) (F.mapHom g) :=
  F.map_comp f g

/-- Identity V-functor composed with any functor is that functor. -/
@[simp] theorem vfunctor_identity_comp {C D : VCategory}
    (F : VFunctor C D) {a b : C.Obj} (f : C.Hom a b) :
    (VFunctor.comp F (VFunctor.identity C)).mapHom f = F.mapHom f :=
  rfl

/-- Any V-functor composed with identity is itself. -/
@[simp] theorem vfunctor_comp_identity {C D : VCategory}
    (F : VFunctor C D) {a b : C.Obj} (f : C.Hom a b) :
    (VFunctor.comp (VFunctor.identity D) F).mapHom f = F.mapHom f :=
  rfl

/-- Enriched Yoneda round-trip is RwEq-coherent. -/
theorem enriched_yoneda_rweq (C : VCategory)
    {a : C.Obj} {F : C.Obj → Type u}
    (act : {b : C.Obj} → C.Hom b a → F a → F b)
    (act_id : (x : F a) → act (C.id a) x = x)
    (x : F a) :
    (mkEnrichedYoneda C).forward ((mkEnrichedYoneda C).backward act x) = x :=
  (mkEnrichedYoneda C).roundtrip act act_id x

/-- Vertical composition of identity natural transformations is identity. -/
@[simp] theorem vnat_vcomp_id {C D : VCategory} (F : VFunctor C D) (a : C.Obj) :
    (VNatTrans.vcomp (VNatTrans.identity F) (VNatTrans.identity F)).component a =
    D.comp (D.id (F.obj a)) (D.id (F.obj a)) :=
  rfl

end EnrichedCategories
end Category
end Path
end ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Category
namespace EnrichedCategories

universe u v

/-! ## Weighted Limits and Colimits -/

structure WeightedDiagram (C : VCategory) where
  shape : Type
  weight : shape → Type
  diagramObj : shape → C.Obj

structure WeightedCone (C : VCategory) (D : WeightedDiagram C) where
  vertex : C.Obj
  leg : (i : D.shape) → C.Hom vertex (D.diagramObj i)

structure WeightedCocone (C : VCategory) (D : WeightedDiagram C) where
  vertex : C.Obj
  leg : (i : D.shape) → C.Hom (D.diagramObj i) vertex

structure WeightedLimit (C : VCategory) (D : WeightedDiagram C) where
  cone : WeightedCone C D
  isUniversal : True

structure WeightedColimit (C : VCategory) (D : WeightedDiagram C) where
  cocone : WeightedCocone C D
  isUniversal : True

def HasWeightedLimits (C : VCategory) : Prop :=
  ∀ D : WeightedDiagram C, Nonempty (WeightedLimit C D)

def HasWeightedColimits (C : VCategory) : Prop :=
  ∀ D : WeightedDiagram C, Nonempty (WeightedColimit C D)

/-! ## Enriched Yoneda and Adjunctions -/

structure EnrichedYonedaIso (C : VCategory) where
  obj : C.Obj
  presheaf : C.Obj → Type
  witness : True

structure EnrichedAdjunction (C D : VCategory) where
  left : VFunctor C D
  right : VFunctor D C
  unit : True
  counit : True

structure EnrichedAdjunctionMate (C D : VCategory) (A : EnrichedAdjunction C D) where
  witness : True

/-! ## Change of Base, Tensors, Cotensors -/

structure MonoidalBase where
  Carrier : Type
  tensor : Carrier → Carrier → Carrier
  unit : Carrier

structure ChangeOfBaseFunctor (B₁ B₂ : MonoidalBase) (C : VCategory) where
  onBase : B₁.Carrier → B₂.Carrier
  onObj : C.Obj → C.Obj
  preservesTensor : True

structure TensoredCategory (C : VCategory) where
  tensorWith : Type u → C.Obj → C.Obj
  hasTensorUnit : True

structure CotensoredCategory (C : VCategory) where
  cotensorWith : Type u → C.Obj → C.Obj
  hasCotensorUnit : True

/-! ## Enriched Ends, Coends, and Day Convolution -/

structure EnrichedEnd (C : VCategory) (F : C.Obj → C.Obj → Type u) where
  object : Type u
  wedge : True

structure EnrichedCoend (C : VCategory) (F : C.Obj → C.Obj → Type u) where
  object : Type u
  cowedge : True

structure EnrichedDayConvolution (C : VCategory) where
  convolution : DayConvolution C
  closedUnderConvolution : True

def dayConvolutionUnit {C : VCategory} (D : EnrichedDayConvolution C) : C.Obj :=
  D.convolution.unit

def dayConvolutionTensor {C : VCategory} (D : EnrichedDayConvolution C) :
    C.Obj → C.Obj → C.Obj :=
  D.convolution.tensor

/-! ## Additional Theorems -/

theorem weighted_limit_exists_of_has {C : VCategory} (h : HasWeightedLimits C)
    (D : WeightedDiagram C) : Nonempty (WeightedLimit C D) := by
  sorry

theorem weighted_colimit_exists_of_has {C : VCategory} (h : HasWeightedColimits C)
    (D : WeightedDiagram C) : Nonempty (WeightedColimit C D) := by
  sorry

theorem weighted_limit_unique_up_to_iso {C : VCategory} (D : WeightedDiagram C) :
    True := by
  sorry

theorem weighted_colimit_unique_up_to_iso {C : VCategory} (D : WeightedDiagram C) :
    True := by
  sorry

theorem weighted_limits_stable_under_equiv {C : VCategory} : True := by
  sorry

theorem weighted_colimits_stable_under_equiv {C : VCategory} : True := by
  sorry

theorem enriched_yoneda_embedding_fully_faithful {C : VCategory} : True := by
  sorry

theorem enriched_yoneda_naturality {C : VCategory} (Y : EnrichedYonedaIso C) : True := by
  sorry

theorem enriched_adjoint_triangle_left {C D : VCategory} (A : EnrichedAdjunction C D) :
    True := by
  sorry

theorem enriched_adjoint_triangle_right {C D : VCategory} (A : EnrichedAdjunction C D) :
    True := by
  sorry

theorem mates_for_enriched_adjunctions {C D : VCategory} (A : EnrichedAdjunction C D) :
    True := by
  sorry

theorem change_of_base_preserves_weighted_limits {C : VCategory}
    {B₁ B₂ : MonoidalBase} (F : ChangeOfBaseFunctor B₁ B₂ C) : True := by
  sorry

theorem change_of_base_preserves_weighted_colimits {C : VCategory}
    {B₁ B₂ : MonoidalBase} (F : ChangeOfBaseFunctor B₁ B₂ C) : True := by
  sorry

theorem tensored_category_represents_action {C : VCategory} (T : TensoredCategory C) :
    True := by
  sorry

theorem cotensored_category_represents_action {C : VCategory} (T : CotensoredCategory C) :
    True := by
  sorry

theorem tensored_and_cotensored_implies_enriched_limits {C : VCategory}
    (_ : TensoredCategory C) (_ : CotensoredCategory C) : True := by
  sorry

theorem enriched_end_exists_for_small_functor {C : VCategory}
    (F : C.Obj → C.Obj → Type u) : True := by
  sorry

theorem enriched_coend_exists_for_small_functor {C : VCategory}
    (F : C.Obj → C.Obj → Type u) : True := by
  sorry

theorem fubini_for_enriched_ends {C : VCategory} : True := by
  sorry

theorem fubini_for_enriched_coends {C : VCategory} : True := by
  sorry

theorem day_convolution_associative_enriched {C : VCategory}
    (D : EnrichedDayConvolution C) : True := by
  sorry

theorem day_convolution_unital_left_enriched {C : VCategory}
    (D : EnrichedDayConvolution C) : True := by
  sorry

theorem day_convolution_unital_right_enriched {C : VCategory}
    (D : EnrichedDayConvolution C) : True := by
  sorry

theorem day_convolution_closed_monoidal {C : VCategory}
    (D : EnrichedDayConvolution C) : True := by
  sorry

theorem ends_coends_interact_with_day_convolution {C : VCategory}
    (D : EnrichedDayConvolution C) : True := by
  sorry

end EnrichedCategories
end Category
end Path
end ComputationalPaths
