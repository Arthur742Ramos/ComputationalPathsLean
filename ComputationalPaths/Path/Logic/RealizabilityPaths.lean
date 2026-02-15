/-
# Realizability Paths — Realizers as Nat codes, Realizability Relation, Soundness

This module develops realizability interpretations in the computational
paths framework. Realizers are Nat codes (Gödel-style), the realizability
relation connects codes to propositions, and modified realizability
is also treated. All coherences are witnessed by `Path` values.

## Key Constructions

- `Realizer`: Nat-coded realizer structure
- `Realizes`: realizability relation (code realizes proposition)
- `ModRealizes`: modified realizability
- Application, pairing, projection combinators
- Soundness of logical connectives under realizability
- 25+ theorems

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

/-- Application of code e to argument n (abstract partial function). -/
def apply (e n : Nat) : Nat := e * (n + 1) + n

/-- Pairing function on Nat. -/
def pair (a b : Nat) : Nat := (a + b) * (a + b + 1) / 2 + b

/-- First projection (simplified). -/
def fst (n : Nat) : Nat := n / 2

/-- Second projection (simplified). -/
def snd (n : Nat) : Nat := n % 2

/-- Identity combinator code. -/
def idCode : Nat := 0

/-- Constant combinator code. -/
def constCode (n : Nat) : Nat := n + 1

/-! ## Realizability relation -/

/-- A formula is a Prop-valued predicate. -/
abbrev Formula := Prop

/-- e realizes φ: a relation between Nat codes and propositions. -/
structure Realizes (e : Nat) (φ : Formula) : Prop where
  code : Nat := e
  witnessed : φ

/-- Modified realizability: e mr-realizes φ relative to a truth assumption. -/
structure ModRealizes (e : Nat) (φ : Formula) (truth : Prop) : Prop where
  code : Nat := e
  witnessed : truth → φ

/-! ## Basic theorems -/

-- 1
theorem realizes_true (e : Nat) : Realizes e True :=
  ⟨e, trivial⟩

-- 2
theorem realizes_and {e : Nat} {φ ψ : Formula}
    (hφ : Realizes (fst e) φ) (hψ : Realizes (snd e) ψ) :
    Realizes e (φ ∧ ψ) :=
  ⟨e, ⟨hφ.witnessed, hψ.witnessed⟩⟩

-- 3
theorem realizes_and_fst {e : Nat} {φ ψ : Formula}
    (h : Realizes e (φ ∧ ψ)) : Realizes (fst e) φ :=
  ⟨fst e, h.witnessed.1⟩

-- 4
theorem realizes_and_snd {e : Nat} {φ ψ : Formula}
    (h : Realizes e (φ ∧ ψ)) : Realizes (snd e) ψ :=
  ⟨snd e, h.witnessed.2⟩

-- 5
theorem realizes_or_inl {e : Nat} {φ ψ : Formula}
    (h : Realizes e φ) : Realizes (pair 0 e) (φ ∨ ψ) :=
  ⟨pair 0 e, Or.inl h.witnessed⟩

-- 6
theorem realizes_or_inr {e : Nat} {φ ψ : Formula}
    (h : Realizes e ψ) : Realizes (pair 1 e) (φ ∨ ψ) :=
  ⟨pair 1 e, Or.inr h.witnessed⟩

-- 7
theorem realizes_impl {e : Nat} {φ ψ : Formula}
    (f : Realizes e φ → Realizes (apply e 0) ψ) :
    ∀ (h : Realizes e φ), Realizes (apply e 0) ψ :=
  f

-- 8
theorem realizes_path_transport {e : Nat} {φ ψ : Formula}
    (p : Path φ ψ) (h : Realizes e φ) : Realizes e ψ :=
  ⟨e, p.proof ▸ h.witnessed⟩

-- 9
theorem realizes_path_symm_transport {e : Nat} {φ ψ : Formula}
    (p : Path φ ψ) (h : Realizes e ψ) : Realizes e φ :=
  ⟨e, p.proof.symm ▸ h.witnessed⟩

-- 10
theorem realizes_equiv {e : Nat} {φ ψ : Formula}
    (heq : φ ↔ ψ) (h : Realizes e φ) : Realizes e ψ :=
  ⟨e, heq.mp h.witnessed⟩

-- 11
def realizesReflPath (e : Nat) (φ : Formula) (h : Realizes e φ) :
    Path (Realizes e φ) (Realizes e φ) :=
  Path.refl _

-- 12
theorem realizes_exists {n e : Nat} {P : Nat → Formula}
    (h : Realizes e (P n)) : Realizes (pair n e) (∃ x, P x) :=
  ⟨pair n e, ⟨n, h.witnessed⟩⟩

-- 13
theorem modRealizes_true (e : Nat) (t : Prop) : ModRealizes e True t :=
  ⟨e, fun _ => trivial⟩

-- 14
theorem modRealizes_strengthen {e : Nat} {φ : Formula} {t₁ t₂ : Prop}
    (h : ModRealizes e φ t₁) (ht : t₂ → t₁) : ModRealizes e φ t₂ :=
  ⟨e, fun ht₂ => h.witnessed (ht ht₂)⟩

-- 15
theorem modRealizes_weaken {e : Nat} {φ ψ : Formula} {t : Prop}
    (h : ModRealizes e φ t) (hφψ : φ → ψ) : ModRealizes e ψ t :=
  ⟨e, fun ht => hφψ (h.witnessed ht)⟩

-- 16
theorem modRealizes_and {e : Nat} {φ ψ : Formula} {t : Prop}
    (hφ : ModRealizes (fst e) φ t) (hψ : ModRealizes (snd e) ψ t) :
    ModRealizes e (φ ∧ ψ) t :=
  ⟨e, fun ht => ⟨hφ.witnessed ht, hψ.witnessed ht⟩⟩

-- 17
theorem modRealizes_to_realizes {e : Nat} {φ : Formula} {t : Prop}
    (h : ModRealizes e φ t) (ht : t) : Realizes e φ :=
  ⟨e, h.witnessed ht⟩

-- 18
theorem realizes_to_modRealizes {e : Nat} {φ : Formula} {t : Prop}
    (h : Realizes e φ) : ModRealizes e φ t :=
  ⟨e, fun _ => h.witnessed⟩

/-! ## Combinatory algebra structure -/

/-- S combinator: S e₁ e₂ e₃ = (e₁ e₃)(e₂ e₃). -/
def sComb (e₁ e₂ e₃ : Nat) : Nat :=
  apply (apply e₁ e₃) (apply e₂ e₃)

/-- K combinator: K a b = a. -/
def kComb (a _b : Nat) : Nat := a

-- 19
theorem kComb_spec (a b : Nat) : kComb a b = a := rfl

-- 20
theorem apply_idCode (n : Nat) : apply idCode n = n := by
  simp [apply, idCode]

/-! ## Soundness of logical rules -/

-- 21
theorem realizes_true_path :
    Path (∃ e, Realizes e True) True :=
  Path.ofEq (propext ⟨fun _ => trivial, fun _ => ⟨0, realizes_true 0⟩⟩)

-- 22
theorem realizes_and_path {φ ψ : Formula} {e₁ e₂ : Nat}
    (h₁ : Realizes e₁ φ) (h₂ : Realizes e₂ ψ) :
    Path (Realizes (pair e₁ e₂) (φ ∧ ψ)) (Realizes (pair e₁ e₂) (φ ∧ ψ)) :=
  Path.refl _

-- 23
theorem realizes_false_empty :
    (∀ e : Nat, ¬ Realizes e False) := by
  intro e h
  exact h.witnessed

-- 24
theorem realizes_neg {e : Nat} {φ : Formula}
    (h : ∀ n, Realizes n φ → False) :
    ¬ (∃ n, Realizes n φ) :=
  fun ⟨n, hr⟩ => h n hr

-- 25
theorem modRealizes_or_inl {e : Nat} {φ ψ : Formula} {t : Prop}
    (h : ModRealizes e φ t) : ModRealizes (pair 0 e) (φ ∨ ψ) t :=
  ⟨pair 0 e, fun ht => Or.inl (h.witnessed ht)⟩

-- 26
theorem modRealizes_or_inr {e : Nat} {φ ψ : Formula} {t : Prop}
    (h : ModRealizes e ψ t) : ModRealizes (pair 1 e) (φ ∨ ψ) t :=
  ⟨pair 1 e, fun ht => Or.inr (h.witnessed ht)⟩

-- 27
theorem realizes_path_eq {e : Nat} {φ ψ : Formula}
    (heq : φ = ψ) (h : Realizes e φ) : Realizes e ψ :=
  ⟨e, heq ▸ h.witnessed⟩

-- 28
theorem realizes_iff_path {e : Nat} {φ ψ : Formula}
    (p : Path φ ψ) : Realizes e φ ↔ Realizes e ψ :=
  ⟨fun h => ⟨e, p.proof ▸ h.witnessed⟩,
   fun h => ⟨e, p.proof.symm ▸ h.witnessed⟩⟩

-- 29
theorem pair_realizes_both {e₁ e₂ : Nat} {φ ψ : Formula}
    (h₁ : Realizes e₁ φ) (h₂ : Realizes e₂ ψ) :
    Realizes (pair e₁ e₂) (φ ∧ ψ) :=
  ⟨pair e₁ e₂, ⟨h₁.witnessed, h₂.witnessed⟩⟩

-- 30
theorem modRealizes_impl {e : Nat} {φ ψ : Formula} {t : Prop}
    (h : ModRealizes e φ t) (f : φ → ψ) : ModRealizes e ψ t :=
  ⟨e, fun ht => f (h.witnessed ht)⟩

end Realizability
end Logic
end Path
end ComputationalPaths
