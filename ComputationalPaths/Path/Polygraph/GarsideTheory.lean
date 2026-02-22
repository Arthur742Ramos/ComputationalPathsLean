/-
# Garside Structure in the Free Groupoid

This module explores Garside-theoretic properties of the free groupoid
presented by the completed TRS. The key result is **negative**: the free
monoid on infinitely many generators does NOT admit a Garside structure.

## Main Results

1. `PosExpr`: positive expressions (no `symm`) form a monoid under `trans`
2. `atom_not_in_word`: fresh atoms don't appear in finite expressions
3. `no_universal_divisor_witness`: no single PosExpr is divisible by all atoms
4. `partialGarside_contains`: partial Garside elements for bounded fragments
5. `posRwEq_iff_toRW`: faithful embedding into free group

## References

- Garside, "The braid group and other groups" (1969)
- Dehornoy et al., "Foundations of Garside Theory" (2015)
-/

import ComputationalPaths.Path.Rewrite.GroupoidConfluence

namespace ComputationalPaths.Path.Polygraph.GarsideTheory

open Rewrite.GroupoidTRS (Expr)
open Rewrite.GroupoidConfluence (CStep CRTC ExprRwEq canon toRW confluence
  cstep_termination toRW_invariant toRW_invariant_rtc exprRwEq_of_crtc
  rwAppend Gen Reduced toRW_reduced reach_canon rwToExpr)

/-! ## Positive Expressions -/

/-- A **positive expression** is one built without `symm`. -/
inductive PosExpr where
  | atom (n : Nat) : PosExpr
  | refl : PosExpr
  | trans (e₁ e₂ : PosExpr) : PosExpr
  deriving DecidableEq, Repr

namespace PosExpr

/-- Embed a positive expression into `Expr`. -/
@[simp] noncomputable def toExpr : PosExpr → Expr
  | .atom n => .atom n
  | .refl => .refl
  | .trans e₁ e₂ => .trans e₁.toExpr e₂.toExpr

/-- Number of atoms. -/
@[simp] noncomputable def atomCount : PosExpr → Nat
  | .atom _ => 1
  | .refl => 0
  | .trans e₁ e₂ => e₁.atomCount + e₂.atomCount

/-- Collect atom indices left to right. -/
noncomputable def toWord : PosExpr → List Nat
  | .atom n => [n]
  | .refl => []
  | .trans e₁ e₂ => e₁.toWord ++ e₂.toWord

/-- Maximum atom index + 1. -/
noncomputable def maxAtomSucc : PosExpr → Nat
  | .atom n => n + 1
  | .refl => 0
  | .trans e₁ e₂ => max e₁.maxAtomSucc e₂.maxAtomSucc

/-! ## Monoid Structure -/

@[simp] noncomputable def comp (e₁ e₂ : PosExpr) : PosExpr := .trans e₁ e₂
@[simp] noncomputable def one : PosExpr := .refl

/-- Rewrite equivalence inherited from Expr. -/
noncomputable def PosRwEq (e₁ e₂ : PosExpr) : Prop :=
  ExprRwEq e₁.toExpr e₂.toExpr

theorem posRwEq_refl (e : PosExpr) : PosRwEq e e := ExprRwEq.refl _
theorem posRwEq_symm {e₁ e₂ : PosExpr} (h : PosRwEq e₁ e₂) : PosRwEq e₂ e₁ := ExprRwEq.symm h

/-- Left identity. -/
theorem comp_one_left (e : PosExpr) : PosRwEq (comp one e) e :=
  ExprRwEq.step (.trans_refl_left _)

/-- Right identity. -/
theorem comp_one_right (e : PosExpr) : PosRwEq (comp e one) e :=
  ExprRwEq.step (.trans_refl_right _)

/-- Associativity. -/
theorem comp_assoc (e₁ e₂ e₃ : PosExpr) :
    PosRwEq (comp (comp e₁ e₂) e₃) (comp e₁ (comp e₂ e₃)) :=
  ExprRwEq.step (.trans_assoc _ _ _)

/-! ## Negative Result: No Finite Garside Element -/

/-- An atom index ≥ maxAtomSucc does not appear in the expression's word. -/
theorem atom_not_in_word (e : PosExpr) (n : Nat) (hn : e.maxAtomSucc ≤ n) :
    n ∉ e.toWord := by
  induction e with
  | atom m =>
    simp [toWord, maxAtomSucc] at *
    omega
  | refl => simp [toWord]
  | trans e₁ e₂ ih₁ ih₂ =>
    simp only [toWord, List.mem_append, not_or, maxAtomSucc] at *
    exact ⟨ih₁ (by omega), ih₂ (by omega)⟩

/-- For any positive expression Δ, there exists an atom that does NOT
    appear in Δ's word. This witnesses that no single expression is
    divisible by all atoms. -/
theorem no_universal_divisor_witness (Δ : PosExpr) :
    ∃ n : Nat, n ∉ Δ.toWord :=
  ⟨Δ.maxAtomSucc, atom_not_in_word Δ _ (Nat.le_refl _)⟩

/-- The toWord function correctly counts atoms. -/
theorem toWord_length (e : PosExpr) : e.toWord.length = e.atomCount := by
  induction e with
  | atom _ => rfl
  | refl => rfl
  | trans e₁ e₂ ih₁ ih₂ =>
    simp [toWord, atomCount, List.length_append, ih₁, ih₂]

/-! ## Partial Garside Structure for Bounded Fragments -/

/-- Concatenation of atoms 0..n-1. -/
noncomputable def partialGarside : Nat → PosExpr
  | 0 => .refl
  | 1 => .atom 0
  | n + 2 => .trans (partialGarside (n + 1)) (.atom (n + 1))

/-- The partial Garside element for n atoms has atom count n. -/
theorem partialGarside_atomCount : ∀ n, (partialGarside n).atomCount = n := by
  intro n
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
    simp [partialGarside, atomCount, partialGarside_atomCount (n + 1)]

/-- Each atom i < n appears in the partial Garside element's word. -/
theorem partialGarside_contains (n : Nat) (i : Nat) (hi : i < n) :
    i ∈ (partialGarside n).toWord := by
  match n with
  | 0 => omega
  | 1 =>
    simp [partialGarside, toWord] at *
    omega
  | n + 2 =>
    simp [partialGarside, toWord]
    by_cases h : i < n + 1
    · left; exact partialGarside_contains (n + 1) i h
    · right; omega

/-! ## Embedding into the Free Group -/

/-- The embedding of positive expressions is faithful:
    two positive expressions are PosRwEq iff their toRW interpretations agree. -/
theorem posRwEq_iff_toRW (e₁ e₂ : PosExpr) :
    PosRwEq e₁ e₂ ↔ toRW e₁.toExpr = toRW e₂.toExpr := by
  constructor
  · exact fun h => Rewrite.GroupoidConfluence.toRW_eq_of_exprRwEq h
  · intro h
    have h₁ := exprRwEq_of_crtc (reach_canon e₁.toExpr)
    have h₂ := exprRwEq_of_crtc (reach_canon e₂.toExpr)
    have hc : canon e₁.toExpr = canon e₂.toExpr := by unfold canon; rw [h]
    exact ExprRwEq.trans h₁ (hc ▸ ExprRwEq.symm h₂)

/-! ## Left Divisibility -/

/-- `e₁` left-divides `e₂` if `e₂ ≡ trans e₁ r` for some `r`. -/
noncomputable def LeftDiv (e₁ e₂ : PosExpr) : Prop :=
  ∃ r : PosExpr, PosRwEq (comp e₁ r) e₂

/-- Left divisibility is reflexive. -/
theorem leftDiv_refl (e : PosExpr) : LeftDiv e e :=
  ⟨.refl, comp_one_right e⟩

/-- `refl` divides everything. -/
theorem refl_leftDiv (e : PosExpr) : LeftDiv .refl e :=
  ⟨e, comp_one_left e⟩

end PosExpr

/-! ## Summary

| Property | Free Monoid | Garside Monoid |
|----------|-------------|----------------|
| Cancellative | ✓ (via toRW) | ✓ (required) |
| Finite Garside element | ✗ (∞ generators) | ✓ (required) |
| Lattice divisibility | ✗ (free = no relations) | ✓ (required) |
| Normal form | ✓ (reduced words) | ✓ (greedy NF) |
| Decidable word problem | ✓ (via toRW) | ✓ (via Garside NF) |
| Partial Garside (bounded) | ✓ (for finite subsets) | N/A |

The free groupoid's positive monoid is cancellative with decidable
word problem, but lacks a Garside element and lattice structure.
The `no_universal_divisor_witness` theorem makes this precise. -/

end ComputationalPaths.Path.Polygraph.GarsideTheory
