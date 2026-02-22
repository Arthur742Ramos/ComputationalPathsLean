/-
# Dependent paths (pathover), transport as path action, apd, sigma paths

Dependent path constructions over type families, building on the
computational-path infrastructure from `Path.Basic.Core`.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Path

universe u v w

variable {A : Type u}

/-! ## PathOver: dependent paths in type families -/

/-- A dependent path (pathover): given `p : Path a b` in the base,
a `PathOver` witnesses that transporting `x` along `p` equals `y`. -/
structure PathOver {A : Type u} (D : A → Type v) {a b : A}
    (p : Path a b) (x : D a) (y : D b) where
  eq : Path.transport (D := D) p x = y

namespace PathOver

variable {D : A → Type v} {a b c : A}
variable {p : Path a b} {q : Path b c}
variable {x : D a} {y : D b} {z : D c}

/-- Reflexive dependent path over `refl`. -/
@[simp] noncomputable def refl (x : D a) : PathOver D (Path.refl a) x x :=
  ⟨rfl⟩

/-- Construct a pathover from a transport equation. -/
noncomputable def ofTransportEq (p : Path a b) (x : D a) (y : D b)
    (h : Path.transport (D := D) p x = y) : PathOver D p x y :=
  ⟨h⟩

/-- Every pathover yields a propositional transport equation. -/
noncomputable def toTransportEq (po : PathOver D p x y) :
    Path.transport (D := D) p x = y :=
  po.eq

/-- Compose dependent paths along composed base paths. -/
noncomputable def trans (po₁ : PathOver D p x y) (po₂ : PathOver D q y z) :
    PathOver D (Path.trans p q) x z :=
  ⟨by rw [Path.transport_trans]; rw [po₁.eq]; exact po₂.eq⟩

/-- Inverse of a dependent path. -/
noncomputable def symm (po : PathOver D p x y) :
    PathOver D (Path.symm p) y x :=
  ⟨by rw [← po.eq]; exact Path.transport_symm_left (D := D) p x⟩

/-- All pathovers between the same endpoints are equal (proof irrelevance). -/
theorem subsingleton (po₁ po₂ : PathOver D p x y) :
    po₁ = po₂ := by
  cases po₁; cases po₂; rfl

/-- Pathover from `apd`. -/
noncomputable def ofApd (f : ∀ x, D x) (p : Path a b) :
    PathOver D p (f a) (f b) :=
  ⟨(Path.apd f p).toEq⟩

@[simp] theorem ofApd_refl (f : ∀ x, D x) :
    ofApd f (Path.refl a) = PathOver.refl (f a) := by
  simp [ofApd]

/-- Pathover is transitive (three-fold). -/
theorem trans' {d : A} {r : Path c d} {w : D d}
    (po₁ : PathOver D p x y)
    (po₂ : PathOver D q y z)
    (po₃ : PathOver D r z w) :
    PathOver D (Path.trans (Path.trans p q) r) x w :=
  (po₁.trans po₂).trans po₃

end PathOver

/-! ## Transport as path action on fibers -/

namespace Path

variable {D : A → Type v} {a b c : A}

/-- Transport is functorial: composing transports = transport along composition. -/
theorem transport_functorial (p : Path a b) (q : Path b c) (x : D a) :
    transport (D := D) q (transport (D := D) p x) =
      transport (D := D) (trans p q) x := by
  rw [transport_trans]

/-- Transport along symm p is left-inverse. -/
theorem transport_leftInv (p : Path a b) (x : D a) :
    transport (D := D) (Path.symm p) (transport (D := D) p x) = x :=
  transport_symm_left (D := D) p x

/-- Transport along p ∘ symm is right-inverse. -/
theorem transport_rightInv (p : Path a b) (y : D b) :
    transport (D := D) p (transport (D := D) (Path.symm p) y) = y :=
  transport_symm_right (D := D) p y

/-- Transport is injective. -/
theorem transport_injective (p : Path a b) {x y : D a}
    (h : transport (D := D) p x = transport (D := D) p y) : x = y := by
  have l := transport_symm_left (D := D) p x
  have r := transport_symm_left (D := D) p y
  rw [← l, ← r, h]

/-- Transport is surjective. -/
theorem transport_surjective (p : Path a b) (y : D b) :
    ∃ x : D a, transport (D := D) p x = y :=
  ⟨transport (D := D) (Path.symm p) y, transport_rightInv p y⟩

/-- Transport respects path equality. -/
theorem transport_path_eq {p q : Path a b} (h : p = q) (x : D a) :
    transport (D := D) p x = transport (D := D) q x := by
  rw [h]

/-- Transport along two paths with same proof agrees. -/
theorem transport_Subsingleton.elim (p q : Path a b) (x : D a) :
    transport (D := D) p x = transport (D := D) q x := by
  cases p with | mk sp hp => cases q with | mk sq hq =>
    cases hp; cases hq; rfl

end Path

/-! ## Apd properties -/

namespace Path

variable {D : A → Type v} {a b c : A}

/-- `apd` for a non-dependent function reduces to congrArg + transport_const. -/
theorem apd_nondep {B : Type v} (f : A → B) (p : Path a b) :
    (apd (B := fun _ => B) f p).toEq =
      ((transport_const p (f a)).trans (Path.congrArg f p).toEq) := by
  cases p with | mk s h => cases h; simp [transport]

/-- `apd` along `symm p` inverts at the proof level. -/
theorem apd_symm_toEq (f : ∀ x, D x) (p : Path a b) :
    (apd f (Path.symm p)).toEq =
      (by rw [← (apd f p).toEq]; exact transport_symm_left (D := D) p (f a)) := by
  cases p with | mk s h => cases h; simp [transport]

end Path

/-! ## Sigma type paths -/

namespace SigmaPath

variable {A : Type u} {D : A → Type v}

/-- Forward direction: sigma equality gives base equality and fiber equation. -/
noncomputable def decompose {s₁ s₂ : Σ x, D x} (h : s₁ = s₂) :
    (s₁.1 = s₂.1) := congrArg Sigma.fst h

/-- Backward direction: a base equality plus fiber alignment gives sigma equality. -/
noncomputable def compose {a₁ a₂ : A} {b₁ : D a₁} {b₂ : D a₂}
    (p : a₁ = a₂) (h : p ▸ b₁ = b₂) :
    (⟨a₁, b₁⟩ : Σ x, D x) = ⟨a₂, b₂⟩ := by
  cases p; cases h; rfl

/-- Round-trip for compose. -/
@[simp] theorem compose_rfl (a : A) (b : D a) :
    compose (rfl : a = a) (rfl : b = b) = rfl := rfl

/-- Sigma extensionality: two sigma elements are equal iff components match. -/
theorem sigma_ext {a₁ a₂ : A} {b₁ : D a₁} {b₂ : D a₂} :
    (⟨a₁, b₁⟩ : Σ x, D x) = ⟨a₂, b₂⟩ ↔
      ∃ (p : a₁ = a₂), p ▸ b₁ = b₂ := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · intro ⟨p, h⟩; exact compose p h

/-- Sigma extensionality using Path and transport. -/
theorem sigma_ext_path {a₁ a₂ : A} {b₁ : D a₁} {b₂ : D a₂} :
    (⟨a₁, b₁⟩ : Σ x, D x) = ⟨a₂, b₂⟩ ↔
      ∃ (p : Path a₁ a₂), Path.transport (D := D) p b₁ = b₂ := by
  constructor
  · intro h; cases h; exact ⟨Path.refl _, rfl⟩
  · intro ⟨p, h⟩
    cases p with | mk s hp => cases hp; simp [Path.transport] at h; exact h ▸ rfl

/-- Pair constructor is injective. -/
theorem mk_injective {a₁ a₂ : A} {b₁ : D a₁} {b₂ : D a₂}
    (h : (⟨a₁, b₁⟩ : Σ x, D x) = ⟨a₂, b₂⟩) :
    ∃ (p : a₁ = a₂), p ▸ b₁ = b₂ := by
  cases h; exact ⟨rfl, rfl⟩

/-- Symmetry for sigma equalities. -/
theorem compose_symm {a₁ a₂ : A} {b₁ : D a₁} {b₂ : D a₂}
    (p : a₁ = a₂) (h : p ▸ b₁ = b₂) :
    (compose p h).symm = compose p.symm (by cases p; cases h; rfl) := by
  cases p; cases h; rfl

/-- Transitivity for sigma equalities. -/
theorem compose_trans {a₁ a₂ a₃ : A} {b₁ : D a₁} {b₂ : D a₂} {b₃ : D a₃}
    (p₁ : a₁ = a₂) (h₁ : p₁ ▸ b₁ = b₂)
    (p₂ : a₂ = a₃) (h₂ : p₂ ▸ b₂ = b₃) :
    (compose p₁ h₁).trans (compose p₂ h₂) =
      compose (p₁.trans p₂) (by cases p₁; cases p₂; cases h₁; cases h₂; rfl) := by
  cases p₁; cases p₂; cases h₁; cases h₂; rfl

/-- Congruence for sigma mk in the second component. -/
theorem mk_eq_second {a : A} {b₁ b₂ : D a}
    (h : b₁ = b₂) : (⟨a, b₁⟩ : Σ x, D x) = ⟨a, b₂⟩ :=
  congrArg (Sigma.mk a) h

/-- First projection from sigma equality. -/
theorem fst_eq {s₁ s₂ : Σ x, D x} (h : s₁ = s₂) :
    s₁.1 = s₂.1 :=
  congrArg Sigma.fst h

/-- Second projection from sigma equality (same base). -/
theorem snd_eq {a : A} {b₁ b₂ : D a} (h : (⟨a, b₁⟩ : Σ x, D x) = ⟨a, b₂⟩) :
    b₁ = b₂ := by
  cases h; rfl

end SigmaPath

end ComputationalPaths
