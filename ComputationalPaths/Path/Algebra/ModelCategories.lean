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
  obj_path := fun a => Path.refl _

/-- Every Quillen pair yields trivial total right derived functors. -/
def trivialRightDerived {A : Type u} {B : Type v}
    (M : MCat A) (N : MCat B) (Q : QuillenPair M N) :
    TotalRightDerived M N Q where
  obj := Q.rightObj
  obj_path := fun b => Path.refl _

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
