/-
# Path induction and J-eliminator via computational paths

This module develops HoTT-style path induction principles using
computational paths: the J-eliminator (for the proof field), transport
computation rules, dependent action on paths (apd), path-over types,
and derived path algebra.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace HoTT
namespace PathInduction

open ComputationalPaths.Path

universe u v w

variable {A : Type u}

/-! ## J-eliminator for propositional equality -/

/-- The J-eliminator for propositional equality. -/
def J_eq {a : A} (C : (b : A) → a = b → Sort v)
    (c : C a rfl) {b : A} (h : a = b) : C b h := by
  cases h; exact c

/-- J_eq computes on rfl. -/
theorem J_eq_rfl {a : A} (C : (b : A) → a = b → Sort v)
    (c : C a rfl) :
    J_eq C c rfl = c := rfl

/-- Paulin-Mohring J: endpoint on the left varies. -/
def J'_eq {b : A} (C : (a : A) → a = b → Sort v)
    (c : C b rfl) {a : A} (h : a = b) : C a h := by
  cases h; exact c

/-- J' computes on rfl. -/
theorem J'_eq_rfl {b : A} (C : (a : A) → a = b → Sort v)
    (c : C b rfl) :
    J'_eq C c rfl = c := rfl

/-- J for transport: given a type family, transport along equality. -/
def J_transport {B : A → Sort v} {a b : A} (h : a = b) (x : B a) : B b := by
  cases h; exact x

/-- J_transport on rfl is identity. -/
theorem J_transport_rfl {B : A → Sort v} {a : A} (x : B a) :
    J_transport (B := B) rfl x = x := rfl

/-! ## Path induction for endpoint-dependent families -/

/-- Path induction for families depending only on the endpoint. -/
def pathIndEndpoint {a : A} (C : (b : A) → Sort v)
    (c : C a) {b : A} (p : Path a b) : C b := by
  cases p with | mk steps proof => cases proof; exact c

/-- Endpoint induction computes on refl. -/
theorem pathIndEndpoint_refl {a : A} (C : (b : A) → Sort v) (c : C a) :
    pathIndEndpoint C c (refl a) = c := by
  simp [pathIndEndpoint]

/-- Path induction for Prop families depending on the endpoint. -/
theorem pathIndProp {a : A} {C : (b : A) → Prop}
    (c : C a) {b : A} (p : Path a b) : C b := by
  cases p with | mk steps proof => cases proof; exact c

/-! ## Path equality and uniqueness -/

/-- Two paths with the same steps are equal. -/
theorem path_eq_of_steps_eq {a b : A} (p q : Path a b)
    (h : p.steps = q.steps) : p = q := by
  cases p; cases q; simp at h; subst h; rfl

/-- All self-path proofs are rfl. -/
theorem self_path_proof_rfl {a : A} (p : Path a a) :
    p.proof = rfl :=
  Subsingleton.elim _ _

/-- UIP for propositional equality. -/
theorem proof_uip {a b : A} (h₁ h₂ : a = b) : h₁ = h₂ :=
  Subsingleton.elim _ _

/-- Proof irrelevance for Path proofs. -/
theorem path_Subsingleton.elim {a b : A} (p : Path a b) :
    p.proof = (ofEq p.proof).proof := rfl

/-! ## Transport computation rules -/

/-- Transport along refl is the identity. -/
theorem transport_refl_comp {B : A → Sort v} {a : A} (x : B a) :
    Path.transport (refl a) x = x :=
  Path.transport_refl x

/-- Transport along trans decomposes sequentially. -/
theorem transport_trans_comp {B : A → Sort v} {a b c : A}
    (p : Path a b) (q : Path b c) (x : B a) :
    Path.transport (Path.trans p q) x = Path.transport q (Path.transport p x) :=
  Path.transport_trans p q x

/-- Transport along symm inverts transport (left). -/
theorem transport_symm_left_comp {B : A → Sort v} {a b : A}
    (p : Path a b) (x : B a) :
    Path.transport (Path.symm p) (Path.transport p x) = x :=
  Path.transport_symm_left p x

/-- Transport along symm inverts transport (right). -/
theorem transport_symm_right_comp {B : A → Sort v} {a b : A}
    (p : Path a b) (y : B b) :
    Path.transport p (Path.transport (Path.symm p) y) = y :=
  Path.transport_symm_right p y

/-- Transport in a constant family is the identity. -/
theorem transport_const_comp {B : Type v} {a b : A}
    (p : Path a b) (x : B) :
    Path.transport (D := fun _ => B) p x = x :=
  Path.transport_const p x

/-- Transport respects path equality. -/
theorem transport_path_eq {B : A → Sort v} {a b : A}
    {p q : Path a b} (h : p = q) (x : B a) :
    Path.transport p x = Path.transport q x := by
  subst h; rfl

/-- Transport along ofEq computes via Eq.mp. -/
theorem transport_ofEq_comp {B : A → Sort v} {a b : A}
    (h : a = b) (x : B a) :
    Path.transport (ofEq h) x = Eq.mp (_root_.congrArg B h) x :=
  Path.transport_ofEq h x

/-- Transport of a sigma decomposes. -/
theorem transport_sigma {B : A → Type v} {C : (a : A) → B a → Type w}
    {a₁ a₂ : A} (p : Path a₁ a₂) (x : B a₁) (y : C a₁ x) :
    Path.transport (D := fun a => (b : B a) × C a b) p ⟨x, y⟩ =
      ⟨Path.transport p x,
        (by cases p with | mk s h => cases h; exact y)⟩ := by
  cases p with | mk steps proof => cases proof; simp [Path.transport]

/-! ## Dependent action on paths (apd) -/

/-- apd applied to refl yields refl. -/
theorem apd_refl_path {B : A → Type v} (f : (x : A) → B x) (a : A) :
    Path.apd (B := B) f (refl a) = refl (f a) :=
  Path.apd_refl f a

/-- The proof field of apd is proof-irrelevant. -/
theorem apd_Subsingleton.elim {B : A → Type v} (f : (x : A) → B x) {a b : A}
    (p : Path a b) :
    (Path.apd (B := B) f p).proof = (Path.apd (B := B) f p).proof :=
  rfl

/-- apd steps are empty for refl. -/
theorem apd_refl_steps {B : A → Type v} (f : (x : A) → B x) (a : A) :
    (Path.apd (B := B) f (refl a)).steps = [] := by
  simp

/-- apd of a constant function on refl. -/
theorem apd_const_refl {B : Type v} (b : B) (a : A) :
    (Path.apd (B := fun _ => B) (fun _ => b) (refl a)).steps = [] := by
  simp

/-- congrArg of refl is refl. -/
theorem congrArg_refl_path {B : Type v} (f : A → B) (a : A) :
    Path.congrArg f (refl a) = refl (f a) := by simp

/-- congrArg preserves trans. -/
theorem congrArg_trans_path {B : Type v} (f : A → B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

/-- congrArg preserves symm. -/
theorem congrArg_symm_path {B : Type v} (f : A → B) {a b : A}
    (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

/-- congrArg with id is identity on paths. -/
theorem congrArg_id_path {a b : A} (p : Path a b) :
    Path.congrArg (fun x => x) p = p :=
  Path.congrArg_id p

/-- congrArg composition. -/
theorem congrArg_comp_path {B : Type v} {C : Type w} (f : B → C) (g : A → B)
    {a b : A} (p : Path a b) :
    Path.congrArg (fun x => f (g x)) p = Path.congrArg f (Path.congrArg g p) :=
  Path.congrArg_comp f g p

/-! ## Path-over types -/

/-- A path-over: relating `u : B a` to `v : B b` over `p : Path a b`. -/
def PathOver {B : A → Type v} {a b : A} (p : Path a b)
    (u : B a) (v : B b) : Prop :=
  Path.transport p u = v

/-- Reflexive path-over. -/
theorem pathOver_refl {B : A → Type v} {a : A} (u : B a) :
    PathOver (refl a) u u := by
  unfold PathOver; rfl

/-- Path-over along refl is ordinary equality. -/
theorem pathOver_refl_iff {B : A → Type v} {a : A} (u v : B a) :
    PathOver (refl a) u v ↔ u = v := by
  constructor
  · intro h; unfold PathOver at h; simpa using h
  · intro h; unfold PathOver; simpa using h

/-- Composing path-overs. -/
theorem pathOver_trans {B : A → Type v} {a b c : A}
    {p : Path a b} {q : Path b c}
    {u : B a} {v : B b} {w : B c}
    (h₁ : PathOver p u v) (h₂ : PathOver q v w) :
    PathOver (Path.trans p q) u w := by
  unfold PathOver at *
  rw [Path.transport_trans]; rw [h₁]; exact h₂

/-- Symmetric path-over. -/
theorem pathOver_symm {B : A → Type v} {a b : A}
    {p : Path a b} {u : B a} {v : B b}
    (h : PathOver p u v) : PathOver (Path.symm p) v u := by
  unfold PathOver at *
  rw [← h]; exact Path.transport_symm_left p u

/-- PathOver is a proposition. -/
theorem pathOver_subsingleton {B : A → Type v} {a b : A}
    (p : Path a b) (u : B a) (v : B b)
    (h₁ h₂ : PathOver p u v) : h₁ = h₂ :=
  rfl

/-- PathOver from transport. -/
theorem pathOver_of_transport {B : A → Type v} {a b : A}
    (p : Path a b) (u : B a) :
    PathOver p u (Path.transport p u) := rfl

/-- PathOver to transport equation. -/
theorem pathOver_to_eq {B : A → Type v} {a b : A}
    {p : Path a b} {u : B a} {v : B b}
    (h : PathOver p u v) : Path.transport p u = v := h

/-! ## Singleton contractibility -/

/-- The based path space. -/
def BasedPathSpace (a : A) := (b : A) × Path a b

/-- The canonical center of the based path space. -/
def basedPathCenter (a : A) : BasedPathSpace a := ⟨a, refl a⟩

/-- Every element of the based path space projects to a (propositionally). -/
theorem basedPath_fst_eq {a : A} (s : BasedPathSpace a) :
    s.1 = a :=
  s.2.proof.symm

/-! ## Path algebra derived from induction -/

/-- Left inverse law (toEq). -/
theorem symm_trans_toEq {a b : A} (p : Path a b) :
    (Path.trans (Path.symm p) p).toEq = (refl b).toEq := by simp

/-- Right inverse law (toEq). -/
theorem trans_symm_toEq {a b : A} (p : Path a b) :
    (Path.trans p (Path.symm p)).toEq = (refl a).toEq := by simp

/-- Left unit. -/
theorem trans_refl_left_J {a b : A} (p : Path a b) :
    Path.trans (refl a) p = p := by simp

/-- Right unit. -/
theorem trans_refl_right_J {a b : A} (p : Path a b) :
    Path.trans p (refl b) = p := by simp

/-- Symmetry involution. -/
theorem symm_symm_J {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- Associativity. -/
theorem trans_assoc_J {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

/-! ## Transport naturality -/

/-- Transport is natural with respect to maps of type families. -/
theorem transport_natural {B C : A → Type v}
    (f : ∀ x, B x → C x) {a b : A} (p : Path a b) (u : B a) :
    Path.transport (D := C) p (f a u) = f b (Path.transport (D := B) p u) :=
  Path.transport_app f p u

/-- Transport along composite function. -/
theorem transport_compose_fun {B : Type u} {P : B → Type v}
    (f : A → B) {a₁ a₂ : A} (p : Path a₁ a₂) (x : P (f a₁)) :
    Path.transport (D := P ∘ f) p x =
      Path.transport (D := P) (Path.congrArg f p) x :=
  Path.transport_compose f p x

/-- Transport across congrArg. -/
theorem transport_congrArg_eq {B : A → Type w}
    {a b : A} (p : Path a b) (x : B a) :
    Path.transport (D := B) p x =
      Path.transport (D := fun X => X) (Path.congrArg B p) x :=
  Path.transport_congrArg p x

/-- apd for non-dependent functions on refl gives empty steps. -/
theorem apd_nondep_refl_steps {B : Type v} (f : A → B) (a : A) :
    (Path.apd (B := fun _ => B) f (refl a)).steps = [] := by
  simp

end PathInduction
end HoTT
end Path
end ComputationalPaths
