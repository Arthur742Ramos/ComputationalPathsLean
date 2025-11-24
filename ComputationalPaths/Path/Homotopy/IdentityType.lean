/-
# Identity Type Transport Lemmas

This module formalizes transport lemmas for identity type families.
These lemmas characterize how transport behaves when the type family
involves the identity type (paths) itself.

## Key Results

- `transport_pathTo_toEq`: Transport in `x ↦ (a = x)` is right composition
- `transport_pathFrom_toEq`: Transport in `x ↦ (x = a)` is left composition with inverse
- `transport_pathLoop_toEq`: Transport in `x ↦ (x = x)` is conjugation
- `transport_funPath_toEq`: Transport for function path families `x ↦ (f x = g x)`
- `transport_depFunPath_toEq`: Dependent version using `apd`
- `transport_loop_iff_toEq`: Path equivalence for self-identity transport
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Homotopy.HoTT

namespace ComputationalPaths
namespace Path
namespace IdentityType

universe u v

variable {A : Type u}

/-! ## Lemma 5.20: Transport along identity type families

These theorems express the key insight that transport in identity type families
can be computed using path composition and inversion.
-/

section Lemma520

variable {a x₁ x₂ : A}

/-- Transport along the family `x ↦ (a = x)` yields composition on the right.
    `transport^{x ↦ (a = x)}(p, q) = q · p`

    For `q : a = x₁` and `p : x₁ = x₂`, transporting `q` along `p` gives
    `q · p : a = x₂`. -/
@[simp] theorem transport_pathTo_toEq (p : Path x₁ x₂) (q : Path a x₁) :
    (Path.transport (A := A) (D := fun x => Path a x) p q).toEq =
      (Path.trans q p).toEq := by
  cases p with
  | mk steps proof =>
      cases proof
      simp

/-- Transport along the family `x ↦ (x = a)` yields composition with the inverse.
    `transport^{x ↦ (x = a)}(p, q) = p⁻¹ · q`

    For `q : x₁ = a` and `p : x₁ = x₂`, transporting `q` along `p` gives
    `p⁻¹ · q : x₂ = a`. -/
@[simp] theorem transport_pathFrom_toEq (p : Path x₁ x₂) (q : Path x₁ a) :
    (Path.transport (A := A) (D := fun x => Path x a) p q).toEq =
      (Path.trans (Path.symm p) q).toEq := by
  cases p with
  | mk steps proof =>
      cases proof
      simp

/-- Transport along the family `x ↦ (x = x)` gives conjugation.
    `transport^{x ↦ (x = x)}(p, q) = p⁻¹ · q · p`

    For a loop `q : x₁ = x₁` and `p : x₁ = x₂`, transporting `q` along `p`
    gives the conjugate loop `p⁻¹ · q · p : x₂ = x₂`. -/
@[simp] theorem transport_pathLoop_toEq (p : Path x₁ x₂) (q : Path x₁ x₁) :
    (Path.transport (A := A) (D := fun x => Path x x) p q).toEq =
      (Path.trans (Path.symm p) (Path.trans q p)).toEq := by
  cases p with
  | mk steps proof =>
      cases proof
      simp

end Lemma520

/-! ## Transport for function path families -/

section FunPathTransport

variable {B : Type v} {a a' : A}

/-- Transport along the family `x ↦ (f(x) = g(x))` for non-dependent functions.
    `transport^{x ↦ (f(x) = g(x))}(p, q) = (ap f p)⁻¹ · q · (ap g p)`

    For `q : f(a) = g(a)` and `p : a = a'`, transporting `q` along `p` gives
    `(ap f p)⁻¹ · q · (ap g p) : f(a') = g(a')`. -/
@[simp] theorem transport_funPath_toEq {f g : A → B}
    (p : Path a a') (q : Path (f a) (g a)) :
    (Path.transport (A := A) (D := fun x => Path (f x) (g x)) p q).toEq =
      (Path.trans
        (Path.trans
          (Path.symm (Path.congrArg f p))
          q)
        (Path.congrArg g p)).toEq := by
  cases p with
  | mk steps proof =>
      cases proof
      simp

end FunPathTransport

/-! ## Dependent version with apd -/

section DepFunPathTransport

variable {P : A → Type v} {a a' : A}

/-- Dependent application of a function to a path (apd).
    For `f : Π(x:A), P(x)` and `p : a = a'`, we get `apd f p : p*(f(a)) = f(a')`. -/
@[simp] def apd (f : (x : A) → P x) (p : Path a a') :
    Path (Path.transport (A := A) (D := P) p (f a)) (f a') :=
  match p with
  | ⟨_, proof⟩ => by cases proof; exact Path.refl (f a)

/-- Transport along the family `x ↦ (f(x) = g(x))` for dependent functions.
    Uses apd instead of congrArg. -/
@[simp] theorem transport_depFunPath_toEq {f g : (x : A) → P x}
    (p : Path a a') (q : Path (f a) (g a)) :
    (Path.transport (A := A) (D := fun x => Path (f x) (g x)) p q).toEq =
      (Path.trans
        (Path.trans
          (Path.symm (apd (P := P) f p))
          (Path.congrArg (Path.transport (A := A) (D := P) p) q))
        (apd (P := P) g p)).toEq := by
  cases p with
  | mk steps proof =>
      cases proof
      simp

end DepFunPathTransport

/-! ## Path equivalence for self-identity transport

The key equivalence: transport in (x = x) relates to path rearrangement.
`(transport^{x → (x = x)}(p, q) = r) ⟺ (τ(q, p) = τ(p, r))`

This characterizes when a loop `q` at `a` transports to a loop `r` at `a'`.
-/

section SelfIdentityTransport

variable {a a' : A}

/-- Forward direction: from transport equality to path equality. -/
theorem transport_loop_eq_implies_toEq (p : Path a a') (q : Path a a) (r : Path a' a') :
    (Path.transport (A := A) (D := fun x => Path x x) p q).toEq = r.toEq →
    (Path.trans q p).toEq = (Path.trans p r).toEq := by
  cases p with
  | mk steps proof =>
      cases proof
      simp

/-- Backward direction: from path equality to transport equality. -/
theorem path_eq_implies_transport_loop_toEq (p : Path a a') (q : Path a a) (r : Path a' a') :
    (Path.trans q p).toEq = (Path.trans p r).toEq →
    (Path.transport (A := A) (D := fun x => Path x x) p q).toEq = r.toEq := by
  cases p with
  | mk steps proof =>
      cases proof
      simp

/-- Main equivalence: transport in self-identity relates to path rearrangement. -/
theorem transport_loop_iff_toEq (p : Path a a') (q : Path a a) (r : Path a' a') :
    (Path.transport (A := A) (D := fun x => Path x x) p q).toEq = r.toEq ↔
    (Path.trans q p).toEq = (Path.trans p r).toEq :=
  ⟨transport_loop_eq_implies_toEq p q r, path_eq_implies_transport_loop_toEq p q r⟩

end SelfIdentityTransport

/-! ## Additional useful lemmas -/

section Additional

variable {a b c : A}

/-- Transport in (a = x) followed by composition equals direct composition. -/
theorem transport_pathTo_trans_toEq (p : Path a b) (q : Path b c) (r : Path a a) :
    (Path.transport (D := fun x => Path a x) (Path.trans p q) r).toEq =
      (Path.trans r (Path.trans p q)).toEq := by
  cases p with
  | mk steps₁ proof₁ =>
      cases proof₁
      cases q with
      | mk steps₂ proof₂ =>
          cases proof₂
          simp

/-- Transport in (x = c) is contravariant in the first argument. -/
theorem transport_pathFrom_symm_toEq (p : Path a b) (q : Path a c) :
    (Path.transport (D := fun x => Path x c) p q).toEq =
      (Path.trans (Path.symm p) q).toEq := by
  cases p with
  | mk steps proof =>
      cases proof
      simp

/-- Naturality: transport commutes with path operations. -/
theorem transport_pathTo_naturality_toEq (p : Path a b) (q : Path c a) (r : Path a a) :
    (Path.trans
      (Path.transport (D := fun x => Path c x) p q)
      (Path.transport (D := fun x => Path x x) p r)).toEq =
    (Path.transport (D := fun x => Path c x) p (Path.trans q r)).toEq := by
  cases p with
  | mk steps proof =>
      cases proof
      simp

end Additional

end IdentityType
end Path
end ComputationalPaths
