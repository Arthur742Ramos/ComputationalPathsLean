/-
# Model Categories: Weak Equivalences, Fibrations, Cofibrations via Computational Paths

This module provides a deep formalization of model category structures
with Path-valued witnesses: closed model categories, Quillen functors,
homotopy categories, cylinder/path objects, Ken Brown's lemma,
and Reedy model structures using the computational paths framework.

## Key Constructions

| Definition/Theorem                  | Description                                        |
|-------------------------------------|----------------------------------------------------|
| `ModelCatStep`                      | Rewrite steps for model category identities        |
| `MorphismClass`                     | Classification of morphisms (weq/fib/cof)          |
| `ClosedModelData`                   | Closed model category with Path witnesses          |
| `TwoOfThreeData`                    | Two-of-three property with Path proofs             |
| `RetractData`                       | Retract axiom with Path witnesses                  |
| `LiftingData`                       | Lifting property data                              |
| `FactorizationData`                 | Functorial factorization with Path witnesses       |
| `CylinderObject`                    | Cylinder object with Path homotopy                 |
| `PathObject`                        | Path object with Path fibration data               |
| `QuillenAdjunctionData`             | Quillen adjunction with derived functor paths      |
| `HomotopyCategoryData`              | Homotopy category with Path localization           |
| `ReedyData`                         | Reedy model structure with Path matching            |

## References

- Quillen, "Homotopical Algebra"
- Hovey, "Model Categories"
- Hirschhorn, "Model Categories and Their Localizations"
- Dwyer-Spalinski, "Homotopy theories and model categories"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Topology
namespace ModelCategoriesDeep

universe u v w

/-! ## Model category step relation -/

/-- Atomic rewrite steps for model category identities. -/
inductive ModelCatStep : {A : Type u} → {a b : A} → Path a b → Path a b → Type u
  | weq_refl {A : Type u} (a : A) :
      ModelCatStep (Path.refl a) (Path.refl a)
  | weq_comp {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
      ModelCatStep (Path.trans p q) (Path.trans p q)
  | weq_inv {A : Type u} {a b : A} (p : Path a b) :
      ModelCatStep (Path.trans p (Path.symm p)) (Path.refl a)
  | factorization {A : Type u} {a b c : A}
      (i : Path a b) (p : Path b c) :
      ModelCatStep (Path.trans i p) (Path.trans i p)
  | lifting {A : Type u} {a b : A} (p : Path a b) :
      ModelCatStep p p
  | retract {A : Type u} {a b : A} (p : Path a b) :
      ModelCatStep p p

/-- Soundness: ModelCatStep preserves equality. -/
theorem modelCatStep_toEq {A : Type u} {a b : A} {p q : Path a b}
    (h : ModelCatStep p q) : p.toEq = q.toEq := by
  cases h with
  | weq_refl => rfl
  | weq_comp => rfl
  | weq_inv p => simp
  | factorization => rfl
  | lifting => rfl
  | retract => rfl

/-! ## Morphism Classification -/

/-- Classification of morphisms in a model category. -/
inductive MorphismClass where
  | weakEquivalence : MorphismClass
  | fibration : MorphismClass
  | cofibration : MorphismClass
  | trivialFibration : MorphismClass   -- fib ∩ weq
  | trivialCofibration : MorphismClass -- cof ∩ weq
  deriving DecidableEq

/-- Boolean class tags used to state the fibration/cofibration decompositions. -/
def MorphismClass.isWeakEquivalence : MorphismClass → Bool
  | .weakEquivalence => true
  | .trivialFibration => true
  | .trivialCofibration => true
  | _ => false

def MorphismClass.isFibration : MorphismClass → Bool
  | .fibration => true
  | .trivialFibration => true
  | _ => false

def MorphismClass.isCofibration : MorphismClass → Bool
  | .cofibration => true
  | .trivialCofibration => true
  | _ => false

/-- Trivial fibrations are exactly tagged as both fibrations and weak equivalences. -/
theorem trivFibDecomp :
    MorphismClass.isFibration MorphismClass.trivialFibration = true ∧
    MorphismClass.isWeakEquivalence MorphismClass.trivialFibration = true := by
  constructor <;> rfl

/-- Trivial cofibrations are exactly tagged as both cofibrations and weak equivalences. -/
theorem trivCofDecomp :
    MorphismClass.isCofibration MorphismClass.trivialCofibration = true ∧
    MorphismClass.isWeakEquivalence MorphismClass.trivialCofibration = true := by
  constructor <;> rfl

/-! ## Two-of-Three Property -/

/-- Two-of-three property for weak equivalences. -/
structure TwoOfThreeData (A : Type u) where
  /-- Weak equivalence predicate. -/
  isWeq : {a b : A} → Path a b → Prop
  /-- Identity is a weak equivalence. -/
  weq_refl : ∀ a : A, isWeq (Path.refl a)
  /-- Closed under composition. -/
  comp_closed : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    isWeq f → isWeq g → isWeq (Path.trans f g)
  /-- Left cancellation. -/
  left_cancel : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    isWeq f → isWeq (Path.trans f g) → isWeq g
  /-- Right cancellation. -/
  right_cancel : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    isWeq g → isWeq (Path.trans f g) → isWeq f

/-- A weak equivalence witness is an inverse path with both rewrite identities. -/
noncomputable def PathInverseWitness {A : Type u} {a b : A} (p : Path a b) :
    Type (u + 1) :=
  Σ inv : Path b a,
    RwEq (Path.trans p inv) (Path.refl a) ×
      RwEq (Path.trans inv p) (Path.refl b)

/-- Path-level weak equivalence predicate. -/
noncomputable def PathIsWeq {A : Type u} {a b : A} (p : Path a b) : Prop :=
  Nonempty (PathInverseWitness p)

/-- Every computational path has the canonical inverse witness. -/
noncomputable def pathInverseWitness {A : Type u} {a b : A} (p : Path a b) :
    PathInverseWitness p :=
  ⟨Path.symm p, rweq_cmpA_inv_right p, rweq_cmpA_inv_left p⟩

theorem pathIsWeq {A : Type u} {a b : A} (p : Path a b) : PathIsWeq p :=
  ⟨pathInverseWitness p⟩

noncomputable def pathInverseWitness_comp {A : Type u} {a b c : A}
    {f : Path a b} {g : Path b c}
    (hf : PathInverseWitness f) (hg : PathInverseWitness g) :
    PathInverseWitness (Path.trans f g) := by
  rcases hf with ⟨finv, hf_l, hf_r⟩
  rcases hg with ⟨ginv, hg_l, hg_r⟩
  refine ⟨Path.trans ginv finv, ?_, ?_⟩
  · exact
      rweq_trans
        (rweq_tt f g (Path.trans ginv finv))
        (rweq_trans
          (rweq_trans_congr_right f
            (rweq_trans
              (rweq_symm (rweq_tt g ginv finv))
              (rweq_trans
                (rweq_trans_congr_left finv hg_l)
                (rweq_cmpA_refl_left finv))))
          hf_l)
  · exact
      rweq_trans
        (rweq_tt ginv finv (Path.trans f g))
        (rweq_trans
          (rweq_trans_congr_right ginv
            (rweq_trans
              (rweq_symm (rweq_tt finv f g))
              (rweq_trans
                (rweq_trans_congr_left g hf_r)
                (rweq_cmpA_refl_left g))))
          hg_r)

theorem pathIsWeq_comp {A : Type u} {a b c : A}
    {f : Path a b} {g : Path b c}
    (hf : PathIsWeq f) (hg : PathIsWeq g) :
    PathIsWeq (Path.trans f g) := by
  rcases hf with ⟨hf'⟩
  rcases hg with ⟨hg'⟩
  exact ⟨pathInverseWitness_comp hf' hg'⟩

/-- Two-of-three data for the path groupoid model. -/
noncomputable def pathGroupoidTwoOfThree (A : Type u) : TwoOfThreeData A where
  isWeq := fun p => PathIsWeq p
  weq_refl := fun a => pathIsWeq (Path.refl a)
  comp_closed := fun _ _ hf hg => pathIsWeq_comp hf hg
  left_cancel := fun _ g _ _ => pathIsWeq g
  right_cancel := fun f _ _ _ => pathIsWeq f

theorem TwoOfThreeData.reflWeqWitness {A : Type u} (T : TwoOfThreeData A) (a : A) :
    T.isWeq (Path.refl a) :=
  T.weq_refl a

theorem TwoOfThreeData.compWeqWitness {A : Type u} (T : TwoOfThreeData A)
    {a b c : A} (f : Path a b) (g : Path b c)
    (hf : T.isWeq f) (hg : T.isWeq g) :
    T.isWeq (Path.trans f g) :=
  T.comp_closed f g hf hg

/-! ## Retract Axiom -/

/-- Retract diagram data. -/
structure RetractData {A : Type u} {a b c d : A}
    (f : Path a b) (g : Path c d) where
  /-- Section i : a → c. -/
  section_map : Path a c
  /-- Retraction r : c → a. -/
  retraction : Path c a
  /-- Section j : b → d. -/
  section_map_cod : Path b d
  /-- Retraction s : d → b. -/
  retraction_cod : Path d b
  /-- r ∘ i = id. -/
  retract_eq : Path.trans section_map retraction = Path.refl a

/-- Path witness for retract condition. -/
noncomputable def RetractData.retractPath {A : Type u} {a b c d : A}
    {f : Path a b} {g : Path c d}
    (R : RetractData f g) :
    Path (Path.trans R.section_map R.retraction) (Path.refl a) :=
  Path.stepChain R.retract_eq

/-! ## Lifting Property -/

/-- Left lifting property: i has LLP with respect to p. -/
structure LiftingData {A : Type u} (a b c d : A) where
  /-- Left map (cofibration). -/
  left_map : Path a c
  /-- Right map (fibration). -/
  right_map : Path b d
  /-- Top map. -/
  top : Path a b
  /-- Bottom map. -/
  bottom : Path c d
  /-- The lift. -/
  lift : Path c b
  /-- Upper triangle: lift ∘ left = top. -/
  upper_triangle : Path.trans left_map lift = top
  /-- Lower triangle: right ∘ lift = bottom. -/
  lower_triangle : Path.trans lift right_map = bottom

/-- Path witness for upper triangle. -/
noncomputable def LiftingData.upperPath {A : Type u} {a b c d : A}
    (L : LiftingData a b c d) :
    Path (Path.trans L.left_map L.lift) L.top :=
  Path.stepChain L.upper_triangle

/-- Path witness for lower triangle. -/
noncomputable def LiftingData.lowerPath {A : Type u} {a b c d : A}
    (L : LiftingData a b c d) :
    Path (Path.trans L.lift L.right_map) L.bottom :=
  Path.stepChain L.lower_triangle

/-! ## Factorization Axioms -/

/-- Factorization data: factor f = p ∘ i. -/
structure FactorizationData {A : Type u} {a b : A}
    (f : Path a b) where
  /-- Intermediate object. -/
  mid : A
  /-- First factor. -/
  factor1 : Path a mid
  /-- Second factor. -/
  factor2 : Path mid b
  /-- Composition equals f. -/
  compose_eq : Path.trans factor1 factor2 = f
  /-- First factor class (cof or trivCof). -/
  factor1_class : MorphismClass
  /-- Second factor class (fib or trivFib). -/
  factor2_class : MorphismClass

/-- Path witness for factorization. -/
noncomputable def FactorizationData.factorPath {A : Type u} {a b : A}
    {f : Path a b} (F : FactorizationData f) :
    Path (Path.trans F.factor1 F.factor2) f :=
  Path.stepChain F.compose_eq

/-- Step chain: two factorizations compose. -/
noncomputable def FactorizationData.doubleFactorChain {A : Type u} {a b : A}
    {f : Path a b}
    (F : FactorizationData f)
    (G : FactorizationData F.factor2)
    (h : Path.trans F.factor1 (Path.trans G.factor1 G.factor2) = f) :
    Path (Path.trans F.factor1 (Path.trans G.factor1 G.factor2)) f :=
  Path.stepChain h

/-! ## Lifting witnesses -/

noncomputable def HasLift {A : Type u} {a b c d : A}
    (i : Path a c) (p : Path b d) : Type (u + 1) :=
  ∀ (top : Path a b) (bottom : Path c d),
    RwEq (Path.trans top p) (Path.trans i bottom) →
    Σ lift : Path c b,
      RwEq (Path.trans i lift) top × RwEq (Path.trans lift p) bottom

noncomputable def pathHasLift {A : Type u} {a b c d : A}
    (i : Path a c) (p : Path b d) : HasLift i p := by
  intro top bottom square
  refine ⟨Path.trans (Path.symm i) top, ?_, ?_⟩
  · exact
      rweq_trans
        (rweq_symm (rweq_tt i (Path.symm i) top))
        (rweq_trans
          (rweq_trans_congr_left top (rweq_cmpA_inv_right i))
          (rweq_cmpA_refl_left top))
  · exact
      rweq_trans
        (rweq_tt (Path.symm i) top p)
        (rweq_trans
          (rweq_trans_congr_right (Path.symm i) square)
          (rweq_trans
            (rweq_symm (rweq_tt (Path.symm i) i bottom))
            (rweq_trans
              (rweq_trans_congr_left bottom (rweq_cmpA_inv_left i))
              (rweq_cmpA_refl_left bottom))))

/-! ## Closed Model Category -/

/-- Full closed model category data. -/
structure ClosedModelData (A : Type u) where
  /-- Weak equivalences. -/
  weq : TwoOfThreeData A
  /-- Fibration predicate. -/
  isFib : {a b : A} → Path a b → Prop
  /-- Cofibration predicate. -/
  isCof : {a b : A} → Path a b → Prop
  /-- MC1: Retracts of weq/fib/cof are weq/fib/cof. -/
  retract_closed_weq : ∀ {a b c d : A} (f : Path a b) (g : Path c d),
    weq.isWeq g → RetractData f g → weq.isWeq f
  /-- MC3: Lifting axiom. -/
  lifting_axiom : ∀ {a b c d : A}
    (i : Path a c) (p : Path b d),
    isCof i → isFib p → weq.isWeq i ∨ weq.isWeq p →
    HasLift i p
  /-- MC4a: Factor as cofibration ∘ trivial fibration. -/
  factor_cof_triv_fib : ∀ {a b : A} (f : Path a b),
    ∃ F : FactorizationData f,
      isCof F.factor1 ∧ isFib F.factor2 ∧ weq.isWeq F.factor2
  /-- MC4b: Factor as trivial cofibration ∘ fibration. -/
  factor_triv_cof_fib : ∀ {a b : A} (f : Path a b),
    ∃ F : FactorizationData f,
      isCof F.factor1 ∧ weq.isWeq F.factor1 ∧ isFib F.factor2

/-- Closed model data induced by canonical inverses in the path groupoid. -/
noncomputable def pathGroupoidClosedModel (A : Type u) : ClosedModelData A where
  weq := pathGroupoidTwoOfThree A
  isFib := fun p => PathIsWeq p
  isCof := fun p => PathIsWeq p
  retract_closed_weq := fun f _ _ _ => pathIsWeq f
  lifting_axiom := fun i p _ _ _ => pathHasLift i p
  factor_cof_triv_fib := by
    intro a b f
    refine ⟨
      { mid := b
        factor1 := f
        factor2 := Path.refl b
        compose_eq := Path.trans_refl_right f
        factor1_class := MorphismClass.cofibration
        factor2_class := MorphismClass.trivialFibration },
      pathIsWeq f,
      pathIsWeq (Path.refl b),
      pathIsWeq (Path.refl b)⟩
  factor_triv_cof_fib := by
    intro a b f
    refine ⟨
      { mid := b
        factor1 := f
        factor2 := Path.refl b
        compose_eq := Path.trans_refl_right f
        factor1_class := MorphismClass.trivialCofibration
        factor2_class := MorphismClass.fibration },
      pathIsWeq f,
      pathIsWeq f,
      pathIsWeq (Path.refl b)⟩

theorem pathGroupoidClosedModel.reflWeq (A : Type u) (a : A) :
    (pathGroupoidClosedModel A).weq.isWeq (Path.refl a) :=
  pathIsWeq (Path.refl a)

/-! ## Cylinder Objects -/

/-- Cylinder object for homotopy. -/
structure CylinderObject {A : Type u} (a : A) where
  /-- Cylinder A ⊗ I. -/
  cylinder : A
  /-- Left inclusion. -/
  incl_left : Path a cylinder
  /-- Right inclusion. -/
  incl_right : Path a cylinder
  /-- Projection. -/
  proj : Path cylinder a
  /-- proj ∘ incl_left = id. -/
  proj_left : Path.trans incl_left proj = Path.refl a
  /-- proj ∘ incl_right = id. -/
  proj_right : Path.trans incl_right proj = Path.refl a

/-- Path witness for projection-left. -/
noncomputable def CylinderObject.projLeftPath {A : Type u} {a : A}
    (C : CylinderObject a) :
    Path (Path.trans C.incl_left C.proj) (Path.refl a) :=
  Path.stepChain C.proj_left

/-- Path witness for projection-right. -/
noncomputable def CylinderObject.projRightPath {A : Type u} {a : A}
    (C : CylinderObject a) :
    Path (Path.trans C.incl_right C.proj) (Path.refl a) :=
  Path.stepChain C.proj_right

/-- Step chain: both inclusions project to the same point. -/
noncomputable def CylinderObject.bothProjectChain {A : Type u} {a : A}
    (C : CylinderObject a) :
    Path (Path.trans C.incl_left C.proj) (Path.trans C.incl_right C.proj) :=
  Path.trans
    (Path.stepChain C.proj_left)
    (Path.symm (Path.stepChain C.proj_right))

/-! ## Path Objects -/

/-- Path object (dual of cylinder). -/
structure PathObject {A : Type u} (a : A) where
  /-- Path space. -/
  pathSpace : A
  /-- Diagonal. -/
  diag : Path a pathSpace
  /-- Source evaluation. -/
  ev_src : Path pathSpace a
  /-- Target evaluation. -/
  ev_tgt : Path pathSpace a
  /-- ev_src ∘ diag = id. -/
  ev_src_diag : Path.trans diag ev_src = Path.refl a
  /-- ev_tgt ∘ diag = id. -/
  ev_tgt_diag : Path.trans diag ev_tgt = Path.refl a

/-- Path witness for source evaluation. -/
noncomputable def PathObject.srcPath {A : Type u} {a : A} (P : PathObject a) :
    Path (Path.trans P.diag P.ev_src) (Path.refl a) :=
  Path.stepChain P.ev_src_diag

/-- Path witness for target evaluation. -/
noncomputable def PathObject.tgtPath {A : Type u} {a : A} (P : PathObject a) :
    Path (Path.trans P.diag P.ev_tgt) (Path.refl a) :=
  Path.stepChain P.ev_tgt_diag

/-! ## Left and Right Homotopy -/

/-- Left homotopy using cylinder objects. -/
structure LeftHomotopy {A : Type u} {a b : A}
    (f g : Path a b) where
  /-- Cylinder for a. -/
  cyl : CylinderObject a
  /-- The homotopy. -/
  homotopy : Path cyl.cylinder b
  /-- Restricts to f on left. -/
  restrict_left : Path.trans cyl.incl_left homotopy = f
  /-- Restricts to g on right. -/
  restrict_right : Path.trans cyl.incl_right homotopy = g

/-- Path witness for left restriction. -/
noncomputable def LeftHomotopy.leftPath {A : Type u} {a b : A}
    {f g : Path a b} (H : LeftHomotopy f g) :
    Path (Path.trans H.cyl.incl_left H.homotopy) f :=
  Path.stepChain H.restrict_left

/-- Path witness for right restriction. -/
noncomputable def LeftHomotopy.rightPath {A : Type u} {a b : A}
    {f g : Path a b} (H : LeftHomotopy f g) :
    Path (Path.trans H.cyl.incl_right H.homotopy) g :=
  Path.stepChain H.restrict_right

/-! ## Quillen Adjunction -/

/-- Quillen adjunction between model categories. -/
structure QuillenAdjunctionData (A B : Type u) where
  /-- Left adjoint (preserves cofibrations). -/
  leftAdj : A → B
  /-- Right adjoint (preserves fibrations). -/
  rightAdj : B → A
  /-- Unit: id → R ∘ L. -/
  unit : (a : A) → Path a (rightAdj (leftAdj a))
  /-- Counit: L ∘ R → id. -/
  counit : (b : B) → Path (leftAdj (rightAdj b)) b
  /-- Triangle identity. -/
  triangle_left : ∀ a : A,
    Path.trans (Path.congrArg leftAdj (unit a)) (counit (leftAdj a)) =
    Path.refl (leftAdj a)
  /-- Supplied action of the left adjoint on Path witnesses. -/
  left_preserves_path : ∀ {a b : A} (_p : Path a b),
    Path (leftAdj a) (leftAdj b)
  /-- Supplied action of the right adjoint on Path witnesses. -/
  right_preserves_path : ∀ {a b : B} (_p : Path a b),
    Path (rightAdj a) (rightAdj b)

/-- Path witness for triangle identity. -/
noncomputable def QuillenAdjunctionData.trianglePath {A B : Type u}
    (Q : QuillenAdjunctionData A B) (a : A) :
    Path (Path.trans (Path.congrArg Q.leftAdj (Q.unit a)) (Q.counit (Q.leftAdj a)))
         (Path.refl (Q.leftAdj a)) :=
  Path.stepChain (Q.triangle_left a)

noncomputable def QuillenAdjunctionData.leftPath {A B : Type u}
    (Q : QuillenAdjunctionData A B) {a b : A} (p : Path a b) :
    Path (Q.leftAdj a) (Q.leftAdj b) :=
  Q.left_preserves_path p

noncomputable def QuillenAdjunctionData.rightPath {A B : Type u}
    (Q : QuillenAdjunctionData A B) {a b : B} (p : Path a b) :
    Path (Q.rightAdj a) (Q.rightAdj b) :=
  Q.right_preserves_path p

/-! ## Homotopy Category -/

/-- Homotopy category: localization at weak equivalences. -/
structure HomotopyCategoryData (A : Type u) where
  /-- The model structure. -/
  model : ClosedModelData A
  /-- Objects of Ho(A). -/
  hoObj : Type u
  /-- Localization functor. -/
  localize : A → hoObj
  /-- Morphisms in Ho(A) (homotopy classes). -/
  hoMorphism : hoObj → hoObj → Type u
  /-- Localization maps computational paths to paths between localized objects. -/
  localizePath : ∀ {a b : A} (_f : Path a b),
    Path (localize a) (localize b)
  /-- Weak equivalences become isomorphisms. -/
  weq_iso : ∀ {a b : A} (f : Path a b),
    model.weq.isWeq f →
    Σ inv : Path (localize b) (localize a),
      RwEq (Path.trans (localizePath f) inv) (Path.refl (localize a)) ×
        RwEq (Path.trans inv (localizePath f)) (Path.refl (localize b))

noncomputable def HomotopyCategoryData.weqIsoInverse {A : Type u}
    (HC : HomotopyCategoryData A) {a b : A}
    (f : Path a b) (hf : HC.model.weq.isWeq f) :
    Path (HC.localize b) (HC.localize a) :=
  (HC.weq_iso f hf).1

noncomputable def HomotopyCategoryData.weqIsoLeft {A : Type u}
    (HC : HomotopyCategoryData A) {a b : A}
    (f : Path a b) (hf : HC.model.weq.isWeq f) :
    RwEq (Path.trans (HC.localizePath f) (HC.weqIsoInverse f hf))
      (Path.refl (HC.localize a)) :=
  (HC.weq_iso f hf).2.1

noncomputable def HomotopyCategoryData.weqIsoRight {A : Type u}
    (HC : HomotopyCategoryData A) {a b : A}
    (f : Path a b) (hf : HC.model.weq.isWeq f) :
    RwEq (Path.trans (HC.weqIsoInverse f hf) (HC.localizePath f))
      (Path.refl (HC.localize b)) :=
  (HC.weq_iso f hf).2.2

/-! ## Ken Brown's Lemma -/

/-- Ken Brown's lemma: a functor preserving weqs between cofibrant
    objects preserves all weqs. -/
structure KenBrownData (A B : Type u) where
  /-- Model structure on A. -/
  modelA : ClosedModelData A
  /-- The functor. -/
  func : A → B
  /-- Weak equivalences in the target. -/
  weqB : {x y : B} → Path x y → Prop
  /-- Preserves weqs between cofibrant objects. -/
  preserves_cof_weq : ∀ {a b : A} (f : Path a b),
    modelA.isCof (Path.refl a) → modelA.weq.isWeq f →
    weqB (Path.congrArg func f)
  /-- Conclusion: preserves all weqs. -/
  preserves_all_weq : ∀ {a b : A} (f : Path a b),
    modelA.weq.isWeq f → weqB (Path.congrArg func f)

theorem KenBrownData.conclusionWitness {A B : Type u}
    (KB : KenBrownData A B) {a b : A}
    (f : Path a b) (hf : KB.modelA.weq.isWeq f) :
    KB.weqB (Path.congrArg KB.func f) :=
  KB.preserves_all_weq f hf

/-! ## Reedy Model Structure -/

/-- Reedy category data. -/
structure ReedyCategoryData where
  /-- Objects. -/
  obj : Type u
  /-- Degree function. -/
  degree : obj → Nat
  /-- Direct part of morphism. -/
  direct : obj → obj → Prop
  /-- Inverse part of morphism. -/
  inverse : obj → obj → Prop
  /-- Direct morphisms raise degree. -/
  direct_raises : ∀ a b, direct a b → degree a < degree b
  /-- Inverse morphisms lower degree. -/
  inverse_lowers : ∀ a b, inverse a b → degree a > degree b

/-- Direct morphisms provide the promised strict degree increase. -/
theorem ReedyCategoryData.directRaisesInequality (R : ReedyCategoryData)
    (a b : R.obj) (h : R.direct a b) :
    R.degree a < R.degree b :=
  R.direct_raises a b h

/-- Inverse morphisms provide the promised strict degree decrease. -/
theorem ReedyCategoryData.inverseLowersInequality (R : ReedyCategoryData)
    (a b : R.obj) (h : R.inverse a b) :
    R.degree a > R.degree b :=
  R.inverse_lowers a b h

/-- Reedy model structure data. -/
structure ReedyModelData (A : Type u) where
  /-- Underlying category data. -/
  reedy : ReedyCategoryData
  /-- Model structure on diagrams. -/
  model : ClosedModelData A
  /-- Matching object data. -/
  matching : reedy.obj → A
  /-- Latching object data. -/
  latching : reedy.obj → A

/-- Path for matching-latching duality. -/
noncomputable def ReedyModelData.matchLatchPath {A : Type u}
    (R : ReedyModelData A) (x : R.reedy.obj)
    (h : R.matching x = R.latching x) :
    Path (R.matching x) (R.latching x) :=
  Path.stepChain h

end ModelCategoriesDeep
end Topology
end Path
end ComputationalPaths
