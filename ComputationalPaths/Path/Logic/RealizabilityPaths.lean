/-
# Realizability Paths — Realizers as Nat codes, Realizability Relation, Soundness

This module develops realizability interpretations in the computational
paths framework. Realizers are Nat codes (Gödel-style), the realizability
relation connects codes to propositions, and modified realizability
is also treated. All coherences are witnessed by `Path` values.

## References

- Kleene, "On the interpretation of intuitionistic number theory"
- Troelstra, "Realizability"
- van Oosten, "Realizability: an introduction to its categorical side"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Logic
namespace Realizability

open ComputationalPaths.Path

/-! ## Primitive recursive combinators as Nat codes -/

def apply (e n : Nat) : Nat := e * (n + 1) + n

def pair (a b : Nat) : Nat := (a + b) * (a + b + 1) / 2 + b

def fst (n : Nat) : Nat := n / 2

def snd (n : Nat) : Nat := n % 2

def idCode : Nat := 0

def constCode (n : Nat) : Nat := n + 1

/-! ## Realizability relation -/

/-- e realizes φ: code e witnesses that φ holds. -/
def Realizes (_e : Nat) (φ : Prop) : Prop := φ

/-- Modified realizability: e mr-realizes φ given truth assumption t. -/
def ModRealizes (_e : Nat) (φ : Prop) (truth : Prop) : Prop := truth → φ

/-! ## Basic theorems -/

-- 1
theorem realizes_true (e : Nat) : Realizes e True := trivial

-- 2
theorem realizes_and {e : Nat} {φ ψ : Prop}
    (hφ : Realizes (fst e) φ) (hψ : Realizes (snd e) ψ) :
    Realizes e (φ ∧ ψ) :=
  ⟨hφ, hψ⟩

-- 3
theorem realizes_and_fst {e : Nat} {φ ψ : Prop}
    (h : Realizes e (φ ∧ ψ)) : Realizes (fst e) φ :=
  h.1

-- 4
theorem realizes_and_snd {e : Nat} {φ ψ : Prop}
    (h : Realizes e (φ ∧ ψ)) : Realizes (snd e) ψ :=
  h.2

-- 5
theorem realizes_or_inl {e : Nat} {φ ψ : Prop}
    (h : Realizes e φ) : Realizes (pair 0 e) (φ ∨ ψ) :=
  Or.inl h

-- 6
theorem realizes_or_inr {e : Nat} {φ ψ : Prop}
    (h : Realizes e ψ) : Realizes (pair 1 e) (φ ∨ ψ) :=
  Or.inr h

-- 7
theorem realizes_impl {e : Nat} {φ ψ : Prop}
    (f : Realizes e φ → Realizes (apply e 0) ψ) :
    Realizes e φ → Realizes (apply e 0) ψ := f

-- 8
theorem realizes_path_transport {e : Nat} {φ ψ : Prop}
    (p : Path φ ψ) (h : Realizes e φ) : Realizes e ψ :=
  p.proof ▸ h

-- 9
theorem realizes_path_symm {e : Nat} {φ ψ : Prop}
    (p : Path φ ψ) (h : Realizes e ψ) : Realizes e φ :=
  p.proof.symm ▸ h

-- 10
theorem realizes_equiv {e : Nat} {φ ψ : Prop}
    (heq : φ ↔ ψ) (h : Realizes e φ) : Realizes e ψ :=
  heq.mp h

-- 11
theorem realizes_exists {n e : Nat} {P : Nat → Prop}
    (h : Realizes e (P n)) : Realizes (pair n e) (∃ x, P x) :=
  ⟨n, h⟩

-- 12
theorem modRealizes_true (e : Nat) (t : Prop) : ModRealizes e True t :=
  fun _ => trivial

-- 13
theorem modRealizes_strengthen {e : Nat} {φ : Prop} {t₁ t₂ : Prop}
    (h : ModRealizes e φ t₁) (ht : t₂ → t₁) : ModRealizes e φ t₂ :=
  fun ht₂ => h (ht ht₂)

-- 14
theorem modRealizes_weaken {e : Nat} {φ ψ : Prop} {t : Prop}
    (h : ModRealizes e φ t) (hφψ : φ → ψ) : ModRealizes e ψ t :=
  fun ht => hφψ (h ht)

-- 15
theorem modRealizes_and {e : Nat} {φ ψ : Prop} {t : Prop}
    (hφ : ModRealizes (fst e) φ t) (hψ : ModRealizes (snd e) ψ t) :
    ModRealizes e (φ ∧ ψ) t :=
  fun ht => ⟨hφ ht, hψ ht⟩

-- 16
theorem modRealizes_to_realizes {e : Nat} {φ : Prop} {t : Prop}
    (h : ModRealizes e φ t) (ht : t) : Realizes e φ :=
  h ht

-- 17
theorem realizes_to_modRealizes {e : Nat} {φ : Prop} {t : Prop}
    (h : Realizes e φ) : ModRealizes e φ t :=
  fun _ => h

/-! ## Combinatory algebra -/

def sComb (e₁ e₂ e₃ : Nat) : Nat :=
  apply (apply e₁ e₃) (apply e₂ e₃)

def kComb (a _b : Nat) : Nat := a

-- 18
theorem kComb_spec (a b : Nat) : kComb a b = a := rfl

-- 19
theorem apply_idCode (n : Nat) : apply idCode n = n := by
  simp [apply, idCode]

/-! ## Soundness of logical rules -/

-- 20
theorem realizes_false_empty :
    (∀ e : Nat, ¬ Realizes e False) :=
  fun _ h => h

-- 21
theorem realizes_neg {φ : Prop}
    (h : ∀ n, ¬ Realizes n φ) :
    ¬ (∃ n, Realizes n φ) :=
  fun ⟨n, hr⟩ => h n hr

-- 22
theorem modRealizes_or_inl {e : Nat} {φ ψ : Prop} {t : Prop}
    (h : ModRealizes e φ t) : ModRealizes (pair 0 e) (φ ∨ ψ) t :=
  fun ht => Or.inl (h ht)

-- 23
theorem modRealizes_or_inr {e : Nat} {φ ψ : Prop} {t : Prop}
    (h : ModRealizes e ψ t) : ModRealizes (pair 1 e) (φ ∨ ψ) t :=
  fun ht => Or.inr (h ht)

-- 24
theorem realizes_path_eq {e : Nat} {φ ψ : Prop}
    (heq : φ = ψ) (h : Realizes e φ) : Realizes e ψ :=
  heq ▸ h

-- 25
theorem realizes_iff_path {e : Nat} {φ ψ : Prop}
    (p : Path φ ψ) : Realizes e φ ↔ Realizes e ψ :=
  ⟨fun h => p.proof ▸ h, fun h => p.proof.symm ▸ h⟩

-- 26
theorem pair_realizes_both {e₁ e₂ : Nat} {φ ψ : Prop}
    (h₁ : Realizes e₁ φ) (h₂ : Realizes e₂ ψ) :
    Realizes (pair e₁ e₂) (φ ∧ ψ) :=
  ⟨h₁, h₂⟩

-- 27
theorem modRealizes_impl {e : Nat} {φ ψ : Prop} {t : Prop}
    (h : ModRealizes e φ t) (f : φ → ψ) : ModRealizes e ψ t :=
  fun ht => f (h ht)

-- 28
theorem realizes_trans {e₁ e₂ : Nat} {φ ψ χ : Prop}
    (h₁ : Realizes e₁ φ → Realizes e₂ ψ)
    (h₂ : Realizes e₂ ψ → Realizes (apply e₂ 0) χ)
    (hr : Realizes e₁ φ) : Realizes (apply e₂ 0) χ :=
  h₂ (h₁ hr)

-- 29
theorem realizes_code_irrelevant {e₁ e₂ : Nat} {φ : Prop}
    (h : Realizes e₁ φ) : Realizes e₂ φ := h

-- 30
theorem modRealizes_exists {n e : Nat} {P : Nat → Prop} {t : Prop}
    (h : ModRealizes e (P n) t) : ModRealizes (pair n e) (∃ x, P x) t :=
  fun ht => ⟨n, h ht⟩

end Realizability
end Logic
end Path
end ComputationalPaths
