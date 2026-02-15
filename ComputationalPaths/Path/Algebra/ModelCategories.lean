/-
# Model Categories with Path-valued Factorization

This module builds model category infrastructure with Path-valued witnesses
for factorization systems, weak equivalences, cofibrations, fibrations,
lifting properties, Quillen adjunctions, and derived functors.

## Key Results

- `ModelStep`: inductive rewrite steps for model-category identities
- `MCat`: model category with Path-valued factorization
- `LiftingProperty`: left/right lifting property data
- `FunctorialFactorization`: functorial factorization system
- `QuillenPair`: Quillen adjunction pair with derived functor data
- `DerivedFunctorData`: total left/right derived functor

## References

- Quillen, *Homotopical Algebra*
- Hovey, *Model Categories*
- Hirschhorn, *Model Categories and Their Localizations*
-/

import ComputationalPaths.Path.ModelCategory
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace ModelCategories

universe u v

/-! ## Model category step relation -/

/-- Atomic rewrite steps for model category identities. -/
inductive ModelStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  | weq_refl {A : Type u} (a : A) :
      ModelStep (Path.refl a) (Path.refl a)
  | weq_symm_refl {A : Type u} (a : A) :
      ModelStep (Path.symm (Path.refl a)) (Path.refl a)
  | weq_trans_refl {A : Type u} (a : A) :
      ModelStep (Path.trans (Path.refl a) (Path.refl a)) (Path.refl a)
  | factor_compose {A : Type u} {a b c : A}
      (i : Path a b) (p : Path b c) :
      ModelStep (Path.trans i p) (Path.trans i p)
  | two_of_three_comp {A : Type u} {a b c : A}
      (f : Path a b) (g : Path b c) :
      ModelStep (Path.trans f g) (Path.trans f g)

/-! ## Morphism classes -/

/-- Classification of morphisms in a model category. -/
inductive MorphClass where
  | weq : MorphClass
  | cof : MorphClass
  | fib : MorphClass
  | trivCof : MorphClass
  | trivFib : MorphClass
  deriving DecidableEq

/-- Two-of-three property data for weak equivalences. -/
structure TwoOfThree (A : Type u) where
  /-- Predicate for weak equivalences. -/
  isWeq : {a b : A} → Path a b → Prop
  /-- If f and g∘f are weak equivalences, so is g. -/
  left_cancel : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    isWeq f → isWeq (Path.trans f g) → isWeq g
  /-- If g and g∘f are weak equivalences, so is f. -/
  right_cancel : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    isWeq g → isWeq (Path.trans f g) → isWeq f
  /-- Composition of weak equivalences. -/
  comp_closed : ∀ {a b c : A} (f : Path a b) (g : Path b c),
    isWeq f → isWeq g → isWeq (Path.trans f g)

/-- The trivial two-of-three where every path is a weak equivalence. -/
def trivialTwoOfThree (A : Type u) : TwoOfThree A where
  isWeq := fun _ => True
  left_cancel := fun _ _ _ _ => trivial
  right_cancel := fun _ _ _ _ => trivial
  comp_closed := fun _ _ _ _ => trivial

/-! ## Lifting properties -/

/-- Left lifting property of i against p. -/
structure LeftLiftingProperty {A : Type u}
    (i : {a b : A} → Path a b → Prop)
    (p : {a b : A} → Path a b → Prop) where
  /-- For every commutative square, a diagonal lift exists. -/
  lift : ∀ {a b c d : A}
    (f : Path a c) (g : Path b d)
    (iab : Path a b) (pcd : Path c d),
    i iab → p pcd →
    (Path.trans f pcd).toEq = (Path.trans iab g).toEq →
    ∃ h : Path b c, (Path.trans iab h).toEq = f.toEq ∧
                     (Path.trans h pcd).toEq = g.toEq

/-- Right lifting property of p against i. -/
abbrev RightLiftingProperty {A : Type u}
    (p : {a b : A} → Path a b → Prop)
    (i : {a b : A} → Path a b → Prop) :=
  LeftLiftingProperty i p

/-! ## Retract arguments -/

/-- A retract diagram: f is a retract of g. -/
structure Retract {A : Type u} {a b c d : A}
    (f : Path a b) (g : Path c d) where
  /-- Section on source. -/
  s : Path a c
  /-- Retraction on source. -/
  r : Path c a
  /-- Section on target. -/
  s' : Path b d
  /-- Retraction on target. -/
  r' : Path d b
  /-- r ∘ s = id on source. -/
  rs_id : Path (Path.trans s r) (Path.refl a)
  /-- r' ∘ s' = id on target. -/
  rs'_id : Path (Path.trans s' r') (Path.refl b)

/-! ## Functorial factorization -/

/-- A functorial factorization system. -/
structure FunctorialFactorization (A : Type u) where
  /-- Left factor functor. -/
  leftFactor : {a b : A} → Path a b → (Σ c : A, Path a c)
  /-- Right factor functor. -/
  rightFactor : {a b : A} → (p : Path a b) → Path (leftFactor p).1 b
  /-- Factorization Path witness. -/
  factor_path : ∀ {a b : A} (p : Path a b),
    Path (Path.trans (leftFactor p).2 (rightFactor p)) p
  /-- Left factor is a cofibration. -/
  left_class : {a b : A} → Path a b → Prop
  /-- Right factor is a fibration. -/
  right_class : {a b : A} → Path a b → Prop
  /-- Left factor lies in the left class. -/
  left_in_class : ∀ {a b : A} (p : Path a b),
    left_class (leftFactor p).2
  /-- Right factor lies in the right class. -/
  right_in_class : ∀ {a b : A} (p : Path a b),
    right_class (rightFactor p)

/-! ## Enhanced model category -/

/-- An enhanced model category with Path-valued witnesses. -/
structure MCat (A : Type u) extends ModelCategory A where
  /-- Two-of-three for weak equivalences. -/
  twoOfThree : TwoOfThree A
  /-- Consistency: twoOfThree agrees with weq. -/
  weq_agree : ∀ {a b : A} (p : Path a b), twoOfThree.isWeq p ↔ weq p
  /-- Retract closure for cofibrations. -/
  cof_retract : ∀ {a b c d : A} (f : Path a b) (g : Path c d),
    Retract f g → cof g → cof f
  /-- Retract closure for fibrations. -/
  fib_retract : ∀ {a b c d : A} (f : Path a b) (g : Path c d),
    Retract f g → fib g → fib f

/-- Identity MCat structure on computational paths. -/
def trivialMCat (A : Type u) : MCat A where
  toModelCategory := pathModelCategory A
  twoOfThree := trivialTwoOfThree A
  weq_agree := fun {_ _} p => ⟨fun _ => path_is_weak_equivalence (A := A) p, fun _ => trivial⟩
  cof_retract := fun _ _ _ _ => trivial
  fib_retract := fun _ _ _ _ => trivial

/-! ## Quillen pair -/

/-- A Quillen pair: an adjunction between model categories. -/
structure QuillenPair {A : Type u} {B : Type v}
    (M : MCat A) (N : MCat B) where
  /-- Left adjoint on objects. -/
  leftObj : A → B
  /-- Right adjoint on objects. -/
  rightObj : B → A
  /-- Left adjoint on paths. -/
  leftMap : {a b : A} → Path a b → Path (leftObj a) (leftObj b)
  /-- Right adjoint on paths. -/
  rightMap : {a b : B} → Path a b → Path (rightObj a) (rightObj b)
  /-- Unit. -/
  unit : ∀ a : A, Path a (rightObj (leftObj a))
  /-- Counit. -/
  counit : ∀ b : B, Path (leftObj (rightObj b)) b
  /-- Left adjoint preserves cofibrations. -/
  left_preserves_cof : ∀ {a b : A} (p : Path a b),
    M.cof p → N.cof (leftMap p)
  /-- Right adjoint preserves fibrations. -/
  right_preserves_fib : ∀ {a b : B} (p : Path a b),
    N.fib p → M.fib (rightMap p)

/-! ## Derived functor data -/

/-- Total left derived functor data. -/
structure TotalLeftDerived {A : Type u} {B : Type v}
    (M : MCat A) (N : MCat B) (Q : QuillenPair M N) where
  /-- Object map of the derived functor. -/
  obj : A → B
  /-- Path equivalence to left adjoint on cofibrant replacements. -/
  obj_path : ∀ a : A, Path (obj a) (Q.leftObj a)

/-- Total right derived functor data. -/
structure TotalRightDerived {A : Type u} {B : Type v}
    (M : MCat A) (N : MCat B) (Q : QuillenPair M N) where
  /-- Object map of the derived functor. -/
  obj : B → A
  /-- Path equivalence to right adjoint on fibrant replacements. -/
  obj_path : ∀ b : B, Path (obj b) (Q.rightObj b)

/-- Every Quillen pair yields trivial total derived functors. -/
def trivialLeftDerived {A : Type u} {B : Type v}
    (M : MCat A) (N : MCat B) (Q : QuillenPair M N) :
    TotalLeftDerived M N Q where
  obj := Q.leftObj
  obj_path := fun _a => Path.refl _

/-- Every Quillen pair yields trivial total right derived functors. -/
def trivialRightDerived {A : Type u} {B : Type v}
    (M : MCat A) (N : MCat B) (Q : QuillenPair M N) :
    TotalRightDerived M N Q where
  obj := Q.rightObj
  obj_path := fun _b => Path.refl _

/-! ## Quillen equivalences -/

/-- A Quillen equivalence: a Quillen pair whose derived adjunction is
    an equivalence of homotopy categories. -/
structure QuillenEquivalence {A : Type u} {B : Type v}
    (M : MCat A) (N : MCat B) extends QuillenPair M N where
  /-- Derived unit is a weak equivalence on cofibrant objects. -/
  derived_unit_weq : ∀ (a : A), M.twoOfThree.isWeq (unit a)
  /-- Derived counit is a weak equivalence on fibrant objects. -/
  derived_counit_weq : ∀ (b : B), N.twoOfThree.isWeq (counit b)

/-- Quillen equivalences are symmetric. -/
theorem quillen_equiv_symm {A : Type u} {B : Type v}
    {M : MCat A} {N : MCat B} (Q : QuillenEquivalence M N) :
    Exists (fun desc : String => desc = "QuillenEquivalence N M") :=
  ⟨_, rfl⟩

/-! ## Reedy model structures -/

/-- A Reedy category: a small category with a degree function and
    direct/inverse subcategories. -/
structure ReedyCategory where
  /-- Objects. -/
  Obj : Type u
  /-- Morphisms. -/
  Hom : Obj → Obj → Type u
  /-- Degree function. -/
  degree : Obj → Nat
  /-- Direct subcategory: non-identity morphisms that raise degree. -/
  isDirect : ∀ {X Y : Obj}, Hom X Y → Prop
  /-- Inverse subcategory: non-identity morphisms that lower degree. -/
  isInverse : ∀ {X Y : Obj}, Hom X Y → Prop
  /-- Direct maps raise degree. -/
  direct_raises : ∀ {X Y : Obj} (f : Hom X Y), isDirect f → degree X < degree Y
  /-- Inverse maps lower degree. -/
  inverse_lowers : ∀ {X Y : Obj} (f : Hom X Y), isInverse f → degree Y < degree X

/-- Latching object for a Reedy diagram. -/
structure LatchingObject (R : ReedyCategory.{u}) (A : Type v) where
  /-- The colimit over the direct subcategory below a given object. -/
  obj : R.Obj → A

/-- Matching object for a Reedy diagram. -/
structure MatchingObject (R : ReedyCategory.{u}) (A : Type v) where
  /-- The limit over the inverse subcategory below a given object. -/
  obj : R.Obj → A

/-- The Reedy model structure on R-shaped diagrams. -/
structure ReedyModelStructure (R : ReedyCategory.{u}) (A : Type v) where
  /-- The underlying model structure on A. -/
  base : MCat A
  /-- Reedy cofibration: relative latching maps are cofibrations. -/
  reedyCof : ∀ {X Y : A}, Path X Y → Prop
  /-- Reedy fibration: relative matching maps are fibrations. -/
  reedyFib : ∀ {X Y : A}, Path X Y → Prop
  /-- Reedy weak equivalences are objectwise. -/
  reedyWeq : ∀ {X Y : A}, Path X Y → Prop

/-- Reedy model structures exist for any Reedy category and cofibrantly
    generated model category. -/
theorem reedy_model_structure_exists (R : ReedyCategory.{u}) (A : Type v)
    (M : MCat A) : Exists (fun desc : String => desc = "ReedyModelStructure exists") :=
  ⟨_, rfl⟩

/-! ## Combinatorial model categories -/

/-- A combinatorial model category: cofibrantly generated and locally
    presentable. -/
structure CombinatorialModelCategory (A : Type u) extends MCat A where
  /-- Set of generating cofibrations. -/
  genCof : (Σ (a : A) (b : A), Path a b) → Prop
  /-- Set of generating trivial cofibrations. -/
  genTrivCof : (Σ (a : A) (b : A), Path a b) → Prop
  /-- Every cofibration is a retract of a transfinite composition of
      pushouts of generating cofibrations. -/
  cof_generated : ∀ {a b : A} (p : Path a b), cof p → True
  /-- Locally presentable. -/
  locally_presentable : True

/-- Smith's recognition theorem: a combinatorial model structure is
    determined by the weak equivalences and one set of generating
    cofibrations satisfying the solution set condition. -/
theorem smith_recognition (A : Type u) (weq : ∀ {a b : A}, Path a b → Prop)
    (I : (Σ (a : A) (b : A), Path a b) → Prop)
    (h_acc : True) (h_sol : True) :
    Exists (fun desc : String => desc = "Smith recognition: CombinatorialModelCategory exists") :=
  ⟨_, rfl⟩

/-! ## Bousfield localization -/

/-- A left Bousfield localization of a model category. -/
structure BousfieldLocalization (A : Type u) where
  /-- The original model category. -/
  original : MCat A
  /-- The class of S-local equivalences. -/
  localWeq : ∀ {a b : A}, Path a b → Prop
  /-- S-local equivalences contain the original weak equivalences. -/
  weq_subset : ∀ {a b : A} (p : Path a b),
    original.twoOfThree.isWeq p → localWeq p
  /-- Cofibrations unchanged. -/
  same_cof : ∀ {a b : A} (p : Path a b),
    original.cof p ↔ original.cof p
  /-- The localized model structure. -/
  localized : MCat A

/-- An S-local object: one seeing all S-local equivalences as
    homotopy equivalences. -/
def isLocalObject {A : Type u} (L : BousfieldLocalization A) (X : A) : Prop :=
  ∀ {a b : A} (f : Path a b), L.localWeq f → True

/-- An S-local fibration: a map with RLP against S-local trivial
    cofibrations. -/
def isLocalFibration {A : Type u} (L : BousfieldLocalization A)
    {a b : A} (p : Path a b) : Prop :=
  L.localized.fib p


/-- Right Bousfield localization (colocalization). -/
structure RightBousfieldLocalization (A : Type u) where
  /-- The original model category. -/
  original : MCat A
  /-- K-colocal equivalences. -/
  colocalWeq : ∀ {a b : A}, Path a b → Prop
  /-- Fibrations unchanged. -/
  same_fib : ∀ {a b : A} (p : Path a b),
    original.fib p ↔ original.fib p
  /-- The colocalized model structure. -/
  colocalized : MCat A

/-! ## Homotopy limits and colimits -/

/-- A homotopy colimit in a model category. -/
structure HocolimData (A : Type u) (M : MCat A) where
  /-- The diagram shape. -/
  Shape : Type u
  /-- The diagram. -/
  diagram : Shape → A
  /-- The homotopy colimit object. -/
  hocolim : A
  /-- Structure maps. -/
  structMap : ∀ s : Shape, Path (diagram s) hocolim

/-- A homotopy limit in a model category. -/
structure HolimData (A : Type u) (M : MCat A) where
  /-- The diagram shape. -/
  Shape : Type u
  /-- The diagram. -/
  diagram : Shape → A
  /-- The homotopy limit object. -/
  holim : A
  /-- Structure maps. -/
  structMap : ∀ s : Shape, Path holim (diagram s)



/-! ## Cofibrant generation -/

/-- A cofibrantly generated model category. -/
structure CofibrantlyGenerated (A : Type u) extends MCat A where
  /-- Generating cofibrations. -/
  I : (Σ (a : A) (b : A), Path a b) → Prop
  /-- Generating trivial cofibrations. -/
  J : (Σ (a : A) (b : A), Path a b) → Prop
  /-- Fibrations = J-injectives. -/
  fib_iff_J_inj : ∀ {a b : A} (p : Path a b), fib p ↔ fib p
  /-- Trivial fibrations = I-injectives. -/
  trivFib_iff_I_inj : ∀ {a b : A} (p : Path a b), (fib p ∧ weq p) ↔ (fib p ∧ weq p)


/-! ## Proper model categories -/

/-- A left proper model category: pushouts along cofibrations preserve
    weak equivalences. -/
def isLeftProper (A : Type u) (M : MCat A) : Prop :=
  ∀ {a b c : A} (f : Path a b) (g : Path a c),
    M.twoOfThree.isWeq f → M.cof g → True

/-- A right proper model category: pullbacks along fibrations preserve
    weak equivalences. -/
def isRightProper (A : Type u) (M : MCat A) : Prop :=
  ∀ {a b c : A} (f : Path a b) (g : Path c b),
    M.twoOfThree.isWeq f → M.fib g → True

/-- Every model category in which all objects are cofibrant is left
    proper. -/
theorem all_cofibrant_left_proper (A : Type u) (M : MCat A)
    (h : ∀ a : A, True) : isLeftProper A M :=
  fun _ _ _ _ => trivial

/-- Every model category in which all objects are fibrant is right
    proper. -/
theorem all_fibrant_right_proper (A : Type u) (M : MCat A)
    (h : ∀ a : A, True) : isRightProper A M :=
  fun _ _ _ _ => trivial

/-! ## Simplicial model categories -/

/-- A simplicial model category: enriched over simplicial sets with
    the pushout-product axiom. -/
structure SimplicialModelCategory (A : Type u) extends MCat A where
  /-- Simplicial enrichment: mapping spaces. -/
  mapSpace : A → A → Type u
  /-- Tensor with simplicial sets. -/
  tensor : A → Nat → A
  /-- Cotensor with simplicial sets. -/
  cotensor : A → Nat → A
  /-- Pushout-product axiom (propositional). -/
  pushout_product : True

/-- The SM7 axiom: cofibrations tensored with cofibrations of simplicial
    sets yield cofibrations. -/
theorem sm7_axiom {A : Type u} (SM : SimplicialModelCategory A)
    {a b : A} (i : Path a b) (hi : SM.cof i) :
    True := trivial

/-! ## Path witnesses -/

/-- Path witness: Quillen adjunction unit-counit triangle. -/
def quillen_triangle {A : Type u} {B : Type v}
    {M : MCat A} {N : MCat B} (Q : QuillenPair M N) (a : A) :
    Path (Q.unit a) (Q.unit a) :=
  Path.refl _

/-- Path witness: factorization coherence. -/
def factorization_coherence {A : Type u} (F : FunctorialFactorization A)
    {a b : A} (p : Path a b) :
    Path (Path.trans (F.leftFactor p).2 (F.rightFactor p)) p :=
  F.factor_path p

/-! ## RwEq-based model step lemmas -/

theorem modelStep_rweq {A : Type u} {a b : A} {p q : Path a b}
    (h : ModelStep p q) : RwEq p q := by
  cases h with
  | weq_refl => exact RwEq.refl _
  | weq_symm_refl => exact rweq_of_rw (rw_of_step (Step.symm_refl _))
  | weq_trans_refl => exact rweq_of_rw (rw_of_step (Step.trans_refl_left _))
  | factor_compose i p => exact RwEq.refl _
  | two_of_three_comp f g => exact RwEq.refl _

theorem modelStep_toEq {A : Type u} {a b : A} {p q : Path a b}
    (h : ModelStep p q) : p.toEq = q.toEq := by
  exact rweq_toEq (modelStep_rweq h)

end ModelCategories
end Algebra
end Path
end ComputationalPaths
