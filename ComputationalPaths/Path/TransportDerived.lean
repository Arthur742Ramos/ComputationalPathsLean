/-
# Derived Transport Lemmas

Derived transport and substitution identities for computational paths.
We build on the core transport infrastructure to prove naturality squares,
functoriality laws, and compatibility with path algebra operations.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace TransportDerived

universe u v w

variable {A : Type u}

/-! ## Transport functoriality -/

/-- Transport along `refl` is definitionally the identity. -/
@[simp] theorem transport_refl_id {D : A → Type v} {a : A} (x : D a) :
    Path.transport (Path.refl a) x = x := rfl

/-- Transport along `symm (symm p)` equals transport along `p`. -/
theorem transport_symm_symm {D : A → Type v}
    {a b : A} (p : Path a b) (x : D a) :
    Path.transport (Path.symm (Path.symm p)) x = Path.transport p x := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

/-- Transport along `ofEq (Eq.symm h)` equals transport along `symm (ofEq h)`. -/
theorem transport_ofEq_symm_eq {D : A → Type v}
    {a b : A} (h : a = b) (y : D b) :
    Path.transport (Path.stepChain h.symm) y =
      Path.transport (Path.symm (Path.stepChain h)) y := by
  cases h
  rfl

/-- Transport is injective: if `transport p x = transport p y` then `x = y`. -/
theorem transport_injective {D : A → Type v}
    {a b : A} (p : Path a b) (x y : D a)
    (h : Path.transport p x = Path.transport p y) : x = y := by
  have hx := Path.transport_symm_left (D := D) p x
  have hy := Path.transport_symm_left (D := D) p y
  calc x = Path.transport (Path.symm p) (Path.transport p x) := hx.symm
       _ = Path.transport (Path.symm p) (Path.transport p y) := by rw [h]
       _ = y := hy

/-- Transport along a composite path decomposes into sequential transports. -/
theorem transport_trans_decompose {D : A → Type v}
    {a b c : A} (p : Path a b) (q : Path b c) (x : D a) :
    Path.transport (Path.trans p q) x =
      Path.transport q (Path.transport p x) :=
  Path.transport_trans p q x

/-! ## Substitution derived lemmas -/

/-- Subst along `trans p (symm p)` is the identity. -/
theorem subst_trans_symm_cancel {D : A → Type v}
    {a b : A} (p : Path a b) (x : D a) :
    Path.subst (Path.subst x p) (Path.symm p) = x :=
  Path.subst_symm_left x p

/-- Subst along `trans (symm p) p` is the identity. -/
theorem subst_symm_trans_cancel {D : A → Type v}
    {a b : A} (p : Path a b) (y : D b) :
    Path.subst (Path.subst y (Path.symm p)) p = y :=
  Path.subst_symm_right y p

/-- Subst is associative over triple composition. -/
theorem subst_trans_assoc {D : A → Type v}
    {a b c d₀ : A} (x : D a)
    (p : Path a b) (q : Path b c) (r : Path c d₀) :
    Path.subst x (Path.trans (Path.trans p q) r) =
      Path.subst x (Path.trans p (Path.trans q r)) := by
  simp

/-! ## Transport–congruence naturality -/

/-- Naturality of transport with respect to dependent functions:
    `f b (transport p x) = transport p (f a x)`. -/
theorem transport_naturality_uniform {D E : A → Type v}
    (f : ∀ x : A, D x → E x) {a b : A} (p : Path a b) (d : D a) :
    Path.transport (D := E) p (f a d) =
      f b (Path.transport (D := D) p d) := by
  cases p with
  | mk steps proof =>
    cases proof
    rfl

/-- Transport in a constant family is the identity. -/
theorem transport_const_family {D : Type v}
    {a b : A} (p : Path a b) (x : D) :
    Path.transport (D := fun _ => D) p x = x := by
  cases p with
  | mk steps proof =>
    cases proof
    rfl

/-! ## Transport₂ derived lemmas -/

/-- Binary transport along a pair of reflexive paths is the identity. -/
theorem transport₂_refl_refl {B' : Type v} {D : A → B' → Type w}
    {a : A} {b : B'} (x : D a b) :
    Path.transport₂ (D := D) (Path.refl a) (Path.refl b) x = x :=
  Path.transport₂_refl x

/-- Binary transport is injective. -/
theorem transport₂_injective {B' : Type v}
    {D : A → B' → Type w}
    {a₁ a₂ : A} {b₁ b₂ : B'}
    (p : Path a₁ a₂) (q : Path b₁ b₂) (x y : D a₁ b₁)
    (h : Path.transport₂ (D := D) p q x =
         Path.transport₂ (D := D) p q y) : x = y := by
  cases p with
  | mk steps₁ proof₁ =>
    cases proof₁
    cases q with
    | mk steps₂ proof₂ =>
      cases proof₂
      simp [Path.transport₂, Path.transport] at h
      exact h

/-! ## Path coherence witnesses -/

/-- The `ofEq` witness that double symmetry transport is idempotent. -/
noncomputable def transport_symm_symm_path {D : A → Type v}
    {a b : A} (p : Path a b) (x : D a) :
    Path (Path.transport (Path.symm (Path.symm p)) x)
         (Path.transport p x) :=
  Path.stepChain (transport_symm_symm p x)

/-- The `ofEq` witness for transport along a composite path. -/
noncomputable def transport_trans_path {D : A → Type v}
    {a b c : A} (p : Path a b) (q : Path b c) (x : D a) :
    Path (Path.transport (Path.trans p q) x)
         (Path.transport q (Path.transport p x)) :=
  Path.stepChain (Path.transport_trans p q x)

/-- The `ofEq` witness for left-cancellation of transport. -/
noncomputable def transport_cancel_left_path {D : A → Type v}
    {a b : A} (p : Path a b) (x : D a) :
    Path (Path.transport (Path.symm p) (Path.transport p x)) x :=
  Path.stepChain (Path.transport_symm_left p x)

/-- The `ofEq` witness for right-cancellation of transport. -/
noncomputable def transport_cancel_right_path {D : A → Type v}
    {a b : A} (p : Path a b) (y : D b) :
    Path (Path.transport p (Path.transport (Path.symm p) y)) y :=
  Path.stepChain (Path.transport_symm_right p y)

/-! ## Transport interaction with congrArg -/

/-- Transport along `congrArg f p` in a family `D` equals transport
    along `p` in `D ∘ f`. -/
theorem transport_congrArg_compose {B' : Type u} {D : B' → Type v}
    (f : A → B') {a b : A} (p : Path a b) (x : D (f a)) :
    Path.transport (D := D) (Path.congrArg f p) x =
      Path.transport (D := D ∘ f) p x := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

/-! ## Concrete transport examples -/

/-- Transport in a constant family is always the identity, concretely. -/
example (p : Path (0 : Nat) 0) (x : Bool) :
    Path.transport (D := fun _ => Bool) p x = x := by
  exact Path.transport_const p x

/-- Double cancellation: transport back and forth is the identity. -/
example {a b : A} (p : Path a b) {D : A → Type v} (x : D a) :
    Path.transport (Path.symm p) (Path.transport p x) = x :=
  Path.transport_symm_left p x

/-! ## Transport and path algebra coherence -/

/-- Transporting along `refl ∘ p` equals transporting along `p`. -/
theorem transport_trans_refl_left {D : A → Type v}
    {a b : A} (p : Path a b) (x : D a) :
    Path.transport (Path.trans (Path.refl a) p) x =
      Path.transport p x := by
  simp

/-- Transporting along `p ∘ refl` equals transporting along `p`. -/
theorem transport_trans_refl_right {D : A → Type v}
    {a b : A} (p : Path a b) (x : D a) :
    Path.transport (Path.trans p (Path.refl b)) x =
      Path.transport p x := by
  simp

/-- Transport along `symm (symm p)` equals transport along `p`, as a path. -/
theorem transport_symm_symm_eq {D : A → Type v}
    {a b : A} (p : Path a b) (x : D a) :
    Path.transport (Path.symm (Path.symm p)) x =
      Path.transport p x :=
  transport_symm_symm p x

/-- Transport along `ofEq rfl` is the identity, stated for `ofEq`. -/
theorem transport_ofEq_rfl_eq {D : A → Type v} (a : A) (x : D a) :
    Path.transport (Path.stepChain (rfl : a = a)) x = x := by
  rfl

/-- Transport along the composition of two `ofEq` paths. -/
theorem transport_ofEq_ofEq_trans {D : A → Type v}
    {a b c : A} (h₁ : a = b) (h₂ : b = c) (x : D a) :
    Path.transport (Path.trans (Path.stepChain h₁) (Path.stepChain h₂)) x =
      Path.transport (Path.stepChain h₂) (Path.transport (Path.stepChain h₁) x) := by
  cases h₁; cases h₂; rfl

/-- Subst along two `ofEq` paths decomposes. -/
theorem subst_ofEq_ofEq_trans {D : A → Type v}
    {a b c : A} (h₁ : a = b) (h₂ : b = c) (x : D a) :
    Path.subst x (Path.trans (Path.stepChain h₁) (Path.stepChain h₂)) =
      Path.subst (Path.subst x (Path.stepChain h₁)) (Path.stepChain h₂) := by
  cases h₁; cases h₂; rfl

end TransportDerived
end Path
end ComputationalPaths
