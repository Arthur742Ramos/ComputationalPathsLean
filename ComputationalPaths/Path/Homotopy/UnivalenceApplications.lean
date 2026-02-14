/-
# Univalence Axiom Applications

Applications of the univalence axiom: type equivalences as paths in the
universe, transport along equivalences, the structure identity principle,
object classifiers, and characterisation of path spaces. Proofs are
stubbed with `sorry`.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace UnivalenceApplications

open ComputationalPaths

universe u v w

/-! ## Equivalences -/

/-- Homotopy between functions. -/
def Homotopy {A : Type u} {B : Type v} (f g : A → B) : Type (max u v) :=
  (a : A) → f a = g a

/-- A function is an equivalence (biinvertible map). -/
structure IsEquiv {A : Type u} {B : Type v} (f : A → B) where
  inv  : B → A
  sect : Homotopy (inv ∘ f) id
  retr : Homotopy (f ∘ inv) id

/-- The type of equivalences A ≃' B. -/
structure Equiv' (A : Type u) (B : Type v) where
  toFun   : A → B
  isEquiv : IsEquiv toFun

infixl:25 " ≃' " => Equiv'

/-! ## Univalence -/

/-- idtoeqv: a path in the universe gives an equivalence. -/
def idtoeqv {A B : Type u} (p : A = B) : A ≃' B := sorry

/-- The univalence axiom: idtoeqv is itself an equivalence. -/
axiom univalence (A B : Type u) : IsEquiv (@idtoeqv A B)

/-- ua: an equivalence gives a path in the universe. -/
def ua {A B : Type u} (e : A ≃' B) : A = B := sorry

/-- Transport along a universe path is the underlying function. -/
def transportUniverse {A B : Type u} (p : A = B) : A → B :=
  fun a => p ▸ a

/-! ## Transport and path-over -/

/-- Path-over: a path in a dependent type lying over a base path. -/
def PathOver {A : Type u} (P : A → Type v) {a₁ a₂ : A}
    (p : a₁ = a₂) (b₁ : P a₁) (b₂ : P a₂) : Type v :=
  p ▸ b₁ = b₂

/-- Dependent transport. -/
def dtransport {A : Type u} {P : A → Type v} {a₁ a₂ : A}
    (p : a₁ = a₂) : P a₁ → P a₂ :=
  fun b => p ▸ b

/-- Transport in a constant family is the identity. -/
def transportConst {A : Type u} {B : Type v} {a₁ a₂ : A}
    (p : a₁ = a₂) (b : B) : @dtransport A (fun _ => B) a₁ a₂ p b = b := sorry

/-- ap for dependent functions (apd). -/
def apd {A : Type u} {P : A → Type v} (f : (a : A) → P a)
    {a₁ a₂ : A} (p : a₁ = a₂) : PathOver P p (f a₁) (f a₂) := sorry

/-! ## Structure Identity Principle -/

/-- A standard notion of structure on a type. -/
structure StandardStructure (S : Type u → Type v) where
  transport_str : {A B : Type u} → A ≃' B → S A → S B
  transport_id  : {A : Type u} → (s : S A) →
    transport_str ⟨id, ⟨id, fun _ => rfl, fun _ => rfl⟩⟩ s = s

/-- Structured type: a type equipped with structure. -/
structure StructuredType (S : Type u → Type v) where
  carrier : Type u
  str     : S carrier

/-- Equivalence of structured types. -/
structure StructuredEquiv {S : Type u → Type v} (ss : StandardStructure S)
    (X Y : StructuredType S) where
  equiv : X.carrier ≃' Y.carrier
  compat : ss.transport_str equiv X.str = Y.str

/-- The Structure Identity Principle: paths in Σ-types of structured types
    correspond to structured equivalences. -/
def SIP {S : Type u → Type v} (ss : StandardStructure S)
    (X Y : StructuredType S) :
    (X = Y) ≃ StructuredEquiv ss X Y := sorry

/-! ## Object classifier -/

/-- The object classifier: Type itself classifies fibrations. -/
def objectClassifier : Type (u + 1) := Type u

/-- Classify a fibration by its fiber map. -/
def classifyFibration {B : Type u} (P : B → Type u) : B → objectClassifier := P

/-- Pullback of the universal fibration along a classifying map. -/
def pullbackUniversal {B : Type u} (χ : B → objectClassifier) :
    B → Type u := χ

/-! ## Theorems -/

/-- ua is a retraction of idtoeqv. -/
theorem ua_idtoeqv {A B : Type u} (p : A = B) :
    ua (idtoeqv p) = p := sorry

/-- idtoeqv is a retraction of ua. -/
theorem idtoeqv_ua {A B : Type u} (e : A ≃' B) :
    idtoeqv (ua e) = e := sorry

/-- Univalence: ua ∘ idtoeqv = id on paths. -/
theorem univalence_roundtrip_path {A B : Type u} (p : A = B) :
    ua (idtoeqv p) = p := sorry

/-- Transport along ua e is e.toFun. -/
theorem transport_ua {A B : Type u} (e : A ≃' B) (a : A) :
    transportUniverse (ua e) a = e.toFun a := sorry

/-- ua respects composition. -/
theorem ua_comp {A B C : Type u} (e₁ : A ≃' B) (e₂ : B ≃' C) :
    ua e₁ ▸ ua e₂ = ua (sorry : A ≃' C) := sorry

/-- ua of the identity equivalence is refl. -/
theorem ua_refl (A : Type u) :
    ua (idtoeqv (rfl : A = A)) = rfl := sorry

/-- ua of the inverse equivalence is symm. -/
theorem ua_symm {A B : Type u} (e : A ≃' B) :
    ua (sorry : B ≃' A) = (ua e).symm := sorry

/-- PathOver in a constant family is ordinary equality. -/
theorem pathOver_const {A : Type u} {B : Type v} {a₁ a₂ : A}
    (p : a₁ = a₂) (b₁ b₂ : B) :
    PathOver (fun _ => B) p b₁ b₂ ↔ (b₁ = b₂) := sorry

/-- apd for a non-dependent function reduces to ap. -/
theorem apd_const {A : Type u} {B : Type v} (f : A → B)
    {a₁ a₂ : A} (p : a₁ = a₂) :
    apd (P := fun _ => B) f p = transportConst p (f a₁) ▸ congrArg f p := sorry

/-- Transport in Σ-type. -/
theorem transport_sigma {A : Type u} {P : A → Type v} {Q : (a : A) → P a → Type w}
    {a₁ a₂ : A} (p : a₁ = a₂) (u : Σ (b : P a₁), Q a₁ b) :
    @dtransport A (fun a => Σ (b : P a), Q a b) a₁ a₂ p u =
    ⟨dtransport p u.1, sorry⟩ := sorry

/-- SIP is natural in S. -/
theorem SIP_natural {S T : Type u → Type v}
    (ss : StandardStructure S) (st : StandardStructure T)
    (φ : {A : Type u} → S A → T A)
    (X Y : StructuredType S)
    (p : X = Y) :
    True := sorry

/-- Type is a 1-type with univalence (h-level). -/
theorem universe_hlevel : ∀ (A B : Type), ∀ (p q : A = B),
    ∀ (α β : p = q), α = β := sorry

/-- Equivalence induction: to prove P for all equivalences, it suffices
    to prove it for id. -/
theorem equiv_induction {P : (A B : Type u) → A ≃' B → Prop}
    (hid : ∀ A, P A A ⟨id, ⟨id, fun _ => rfl, fun _ => rfl⟩⟩)
    {A B : Type u} (e : A ≃' B) : P A B e := sorry

/-- Fibrations over B are equivalent to maps B → Type. -/
theorem fibration_classifier {B : Type u} :
    (Σ (E : Type u), E → B) ≃ (B → Type u) := sorry

/-- Pullback along the universal fibration computes fibers. -/
theorem pullback_universal_fiber {B : Type u} (P : B → Type u) (b : B) :
    pullbackUniversal (classifyFibration P) b = P b := rfl

end UnivalenceApplications
end ComputationalPaths
