/-
# Truncation levels: contractible types, propositions, sets, groupoids, n-types

Hierarchy of homotopy truncation levels via iterated path spaces,
building on the computational-path infrastructure from `Path.Basic.Core`.
Includes Hedberg's theorem (decidable equality → set) fully proved.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Path

universe u v

/-! ## Contractible types -/

/-- A type is contractible if it has a center and every element equals it. -/
structure IsContr (A : Type u) where
  center : A
  contr : ∀ x : A, center = x

namespace IsContr

variable {A : Type u}

/-- Any two elements in a contractible type are equal. -/
theorem eq_of_contr (h : IsContr A) (x y : A) : x = y :=
  (h.contr x).symm.trans (h.contr y)

/-- A type with a point and all equalities is contractible. -/
def ofEqCenter (c : A) (h : ∀ x, x = c) : IsContr A :=
  ⟨c, fun x => (h x).symm⟩

/-- The unit type is contractible. -/
def unitContr : IsContr Unit :=
  ⟨(), fun _ => rfl⟩

/-- A subsingleton with an element is contractible. -/
def ofSubsingleton [Subsingleton A] (a : A) : IsContr A :=
  ⟨a, fun x => Subsingleton.elim a x⟩

/-- Product of contractible types is contractible. -/
def prodContr {B : Type v} (ha : IsContr A) (hb : IsContr B) :
    IsContr (A × B) :=
  ⟨(ha.center, hb.center), fun ⟨a, b⟩ =>
    Prod.ext (ha.eq_of_contr ha.center a) (hb.eq_of_contr hb.center b)⟩

/-- Sigma over contractible base with contractible fibers. -/
def sigmaContr {B : A → Type v} (ha : IsContr A) (hb : ∀ x, IsContr (B x)) :
    IsContr (Σ x, B x) :=
  ⟨⟨ha.center, (hb ha.center).center⟩, fun ⟨a, b⟩ => by
    obtain rfl := ha.contr a
    exact congrArg (Sigma.mk _) ((hb ha.center).contr b)⟩

/-- If A is contractible then any function from A is extensionally constant. -/
theorem funContr_eval {B : Type v} (h : IsContr A) (f : A → B) :
    f = fun _ => f h.center :=
  funext (fun x => congrArg f ((h.contr x).symm))

end IsContr

/-! ## Propositions: all elements equal -/

/-- A type is a proposition if any two elements are equal. -/
def IsProp (A : Type u) : Prop :=
  ∀ (x y : A), x = y

namespace IsProp

variable {A : Type u}

/-- A proposition with a point is contractible. -/
def toContr (h : IsProp A) (a : A) : IsContr A :=
  ⟨a, fun x => h a x⟩

/-- Contractible → proposition. -/
theorem ofContr (h : IsContr A) : IsProp A :=
  h.eq_of_contr

/-- Propositions are closed under products. -/
theorem prod {B : Type v} (ha : IsProp A) (hb : IsProp B) :
    IsProp (A × B) :=
  fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => Prod.ext (ha a₁ a₂) (hb b₁ b₂)

/-- Propositions are closed under dependent functions. -/
theorem pi {B : A → Type v} (h : ∀ x, IsProp (B x)) :
    IsProp (∀ x, B x) :=
  fun f g => funext (fun x => h x (f x) (g x))

/-- In a proposition, any two equalities are equal. -/
theorem eq_eq (h : IsProp A) {x y : A} (p q : x = y) : p = q :=
  Subsingleton.elim p q

/-- Two computational paths in a proposition have equal toEq. -/
theorem path_toEq_eq (h : IsProp A) {x y : A} (p q : Path x y) :
    p.toEq = q.toEq :=
  Subsingleton.elim p.toEq q.toEq

end IsProp

/-! ## Sets: UIP holds -/

/-- A type is a set if the equality type between any two elements is a proposition. -/
def IsSet (A : Type u) : Prop :=
  ∀ (x y : A) (p q : x = y), p = q

namespace IsSet

variable {A : Type u}

/-- Alternate: a set satisfies UIP. -/
theorem uip (h : IsSet A) {x y : A} (p q : x = y) : p = q :=
  h x y p q

/-- Every proposition is a set. -/
theorem ofIsProp (h : IsProp A) : IsSet A :=
  fun _ _ _ _ => Subsingleton.elim _ _

/-- Nat is a set. -/
theorem natIsSet : IsSet Nat :=
  fun _ _ _ _ => Subsingleton.elim _ _

/-- Bool is a set. -/
theorem boolIsSet : IsSet Bool :=
  fun _ _ _ _ => Subsingleton.elim _ _

/-- Products of sets are sets. -/
theorem prod {B : Type v} (ha : IsSet A) (hb : IsSet B) :
    IsSet (A × B) :=
  fun _ _ _ _ => Subsingleton.elim _ _

/-- Dependent function types into sets are sets. -/
theorem pi {B : A → Type v} (h : ∀ x, IsSet (B x)) :
    IsSet (∀ x, B x) :=
  fun _ _ _ _ => Subsingleton.elim _ _

/-- In a set, paths with same endpoints have equal toEq. -/
theorem path_toEq_eq (h : IsSet A) {x y : A} (p q : Path x y) :
    p.toEq = q.toEq :=
  h x y p.toEq q.toEq

/-- Empty is a set. -/
theorem emptyIsSet : IsSet Empty :=
  fun x => x.elim

/-- Fin is a set. -/
theorem finIsSet (n : Nat) : IsSet (Fin n) :=
  fun _ _ _ _ => Subsingleton.elim _ _

/-- Int is a set. -/
theorem intIsSet : IsSet Int :=
  fun _ _ _ _ => Subsingleton.elim _ _

end IsSet

/-! ## Groupoids: equality of equalities satisfies UIP -/

/-- A type is a 1-groupoid if for all x y : A, the equality x = y satisfies UIP. -/
def IsGroupoid (A : Type u) : Prop :=
  ∀ (x y : A) (p q : x = y) (r s : p = q), r = s

namespace IsGroupoid

variable {A : Type u}

/-- Every set is a groupoid. -/
theorem ofIsSet (h : IsSet A) : IsGroupoid A :=
  fun x y p q r s => Subsingleton.elim r s

/-- Products of groupoids are groupoids. -/
theorem prod {B : Type v} (ha : IsGroupoid A) (hb : IsGroupoid B) :
    IsGroupoid (A × B) :=
  fun _ _ _ _ r s => Subsingleton.elim r s

/-- Nat is a groupoid (via being a set). -/
theorem natIsGroupoid : IsGroupoid Nat :=
  ofIsSet IsSet.natIsSet

end IsGroupoid

/-! ## n-truncation via Prop-valued hierarchy -/

/-- Truncation level predicate (purely Prop-valued).
  We define the first few levels directly to avoid universe issues
  with Lean's `Eq` living in `Prop` rather than `Type u`. -/
def IsTruncLevel : Nat → Type u → Prop
  | 0 => IsProp
  | 1 => IsSet
  | (n + 2) => IsGroupoid  -- For n ≥ 2, all collapse to groupoid in UIP

namespace IsTruncLevel

variable {A : Type u}

/-- Level 0 is proposition. -/
theorem zero_iff_prop : IsTruncLevel 0 A ↔ IsProp A :=
  Iff.rfl

/-- Level 1 is set. -/
theorem one_iff_set : IsTruncLevel 1 A ↔ IsSet A :=
  Iff.rfl

/-- Level 2+ is groupoid. -/
theorem two_iff_groupoid : IsTruncLevel 2 A ↔ IsGroupoid A :=
  Iff.rfl

/-- Truncation levels are cumulative: prop → set. -/
theorem prop_to_set (h : IsTruncLevel 0 A) : IsTruncLevel 1 A :=
  fun _ _ _ _ => Subsingleton.elim _ _

/-- Truncation levels are cumulative: set → groupoid. -/
theorem set_to_groupoid (h : IsTruncLevel 1 A) : IsTruncLevel 2 A :=
  fun _ _ _ _ _ _ => Subsingleton.elim _ _

/-- Propositions are sets (named corollary). -/
theorem prop_is_set (h : IsProp A) : IsSet A :=
  prop_to_set h

/-- Sets are groupoids (named corollary). -/
theorem set_is_groupoid (h : IsSet A) : IsGroupoid A :=
  set_to_groupoid h

end IsTruncLevel

/-! ## Hedberg's theorem: decidable equality implies set -/

namespace Hedberg

variable {A : Type u}

/-- A constant endofunction on equalities via decidability. -/
private def constPath (dec : DecidableEq A) (x y : A) :
    x = y → x = y :=
  fun _ =>
    match dec x y with
    | isTrue h => h
    | isFalse h' => absurd (by assumption) h'

/-- The constant path is indeed constant. -/
private theorem constPath_const (dec : DecidableEq A) (x y : A)
    (p q : x = y) : constPath dec x y p = constPath dec x y q := by
  unfold constPath
  cases dec x y with
  | isTrue _ => rfl
  | isFalse h => exact absurd p h

/-- Key lemma: every equality factors through constPath. -/
private theorem factorization (dec : DecidableEq A) {x y : A}
    (p : x = y) :
    p = (constPath dec x x rfl).symm.trans (constPath dec x y p) := by
  cases p; simp [Eq.trans]

/-- **Hedberg's theorem**: a type with decidable equality is a set. -/
theorem hedberg (dec : DecidableEq A) : IsSet A := by
  intro x y p q
  have hp := factorization dec p
  have hq := factorization dec q
  have : constPath dec x y p = constPath dec x y q :=
    constPath_const dec x y p q
  rw [hp, hq, this]

/-- Corollary: Nat is a set via Hedberg. -/
theorem nat_isSet : IsSet Nat := hedberg inferInstance

/-- Corollary: Bool is a set via Hedberg. -/
theorem bool_isSet : IsSet Bool := hedberg inferInstance

/-- Corollary: Fin n is a set via Hedberg. -/
theorem fin_isSet (n : Nat) : IsSet (Fin n) := hedberg inferInstance

/-- Corollary: String is a set via Hedberg. -/
theorem string_isSet : IsSet String := hedberg inferInstance

/-- Corollary: Int is a set via Hedberg. -/
theorem int_isSet : IsSet Int := hedberg inferInstance

/-- Any type with DecidableEq is a set. -/
theorem ofDecEq [DecidableEq A] : IsSet A := hedberg inferInstance

end Hedberg

/-! ## Additional truncation results -/

namespace TruncExtra

variable {A : Type u} {B : Type v}

/-- Propositions are trivially sets. -/
theorem prop_isSet (h : IsProp A) : IsSet A :=
  fun _ _ _ _ => Subsingleton.elim _ _

/-- Retract of a set is a set. -/
theorem set_of_retract {f : A → B} {g : B → A}
    (ret : ∀ a, g (f a) = a) (hB : IsSet B) : IsSet A := by
  intro x y p q
  have : congrArg f p = congrArg f q := hB _ _ _ _
  have hp : p = (ret x).symm.trans ((congrArg g (congrArg f p)).trans (ret y)) := by
    cases p; simp
  have hq : q = (ret x).symm.trans ((congrArg g (congrArg f q)).trans (ret y)) := by
    cases q; simp
  rw [hp, hq, this]

/-- Embedding into a set gives a set. -/
theorem set_of_injective {f : A → B} (hf : Function.Injective f)
    (hB : IsSet B) : IsSet A :=
  fun _ _ _ _ => Subsingleton.elim _ _

/-- Sigma of propositions over a proposition is a proposition. -/
theorem sigma_prop {B : A → Type v}
    (hA : IsProp A) (hB : ∀ x, IsProp (B x)) :
    IsProp (Σ x, B x) :=
  fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => by
    obtain rfl := hA a₁ a₂
    exact congrArg (Sigma.mk a₁) (hB a₁ b₁ b₂)

/-- IsProp is closed under logical equivalence. -/
theorem isProp_of_equiv (f : A → B) (g : B → A)
    (hA : IsProp A) (hfg : ∀ b, f (g b) = b) : IsProp B :=
  fun x y => (hfg x).symm.trans ((congrArg f (hA (g x) (g y))).trans (hfg y))

end TruncExtra

end ComputationalPaths
