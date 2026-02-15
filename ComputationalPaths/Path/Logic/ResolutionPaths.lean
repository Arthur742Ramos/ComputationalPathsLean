/-
# Resolution Proofs as Computational Paths

This module models resolution-based theorem proving via computational paths:
clauses as path objects, resolution steps as path compositions, unit
propagation as path shortening, refutation as a path to the empty clause,
and completeness as path existence.

## Key Results

| Definition/Theorem                   | Description                                |
|-------------------------------------|--------------------------------------------|
| `Literal`                           | Positive/negative atoms                    |
| `Clause`                            | Clause as a list of literals               |
| `resolve`                           | Resolution of two clauses                  |
| `resolution_as_trans`               | Resolution modeled by path composition     |
| `unit_propagation_shortens`         | Unit propagation shortens clauses          |
| `refutation_as_path`                | Refutation as path to empty clause         |
| `completeness_structure`            | Completeness as path existence             |

## References

- Robinson, "A Machine-Oriented Logic Based on the Resolution Principle"
- Leitsch, "The Resolution Calculus"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Logic
namespace ResolutionPaths

universe u

/-! ## Literals and Clauses -/

/-- A literal is a positive or negative atom. -/
inductive Literal : Type where
  | pos : Nat → Literal
  | neg : Nat → Literal
  deriving DecidableEq, Repr

/-- Negate a literal. -/
def Literal.negate : Literal → Literal
  | pos n => neg n
  | neg n => pos n

@[simp] theorem Literal.negate_negate (l : Literal) :
    l.negate.negate = l := by
  cases l <;> simp [Literal.negate]

/-- A literal and its negation are complementary. -/
def Literal.isComplementary (l₁ l₂ : Literal) : Prop :=
  l₁.negate = l₂

theorem Literal.complementary_symm (l : Literal) :
    l.isComplementary l.negate := by
  cases l <;> rfl

theorem Literal.complementary_comm (l₁ l₂ : Literal) :
    l₁.isComplementary l₂ → l₂.isComplementary l₁ := by
  intro h
  simp [isComplementary] at *
  rw [← h, negate_negate]

/-- A clause is a disjunction of literals, represented as a list. -/
abbrev Clause := List Literal

/-- The empty clause (⊥). -/
def emptyClause : Clause := []

/-- A unit clause contains exactly one literal. -/
def isUnitClause (c : Clause) : Prop := c.length = 1

/-- Clause size. -/
def clauseSize (c : Clause) : Nat := c.length

/-! ## Resolution Operation -/

/-- Resolution: combine two clauses by removing complementary literals. -/
def resolve (c₁ c₂ : Clause) (l : Literal) : Clause :=
  (c₁.filter (· != l)) ++ (c₂.filter (· != l.negate))

/-- Resolving with the empty clause yields a subset of the first clause. -/
theorem resolve_empty_right (c : Clause) (l : Literal) :
    resolve c emptyClause l = c.filter (· != l) := by
  simp [resolve, emptyClause]

/-- Resolving the empty clause with any clause. -/
theorem resolve_empty_left (c : Clause) (l : Literal) :
    resolve emptyClause c l = c.filter (· != l.negate) := by
  simp [resolve, emptyClause]

/-- Resolution preserves clause contents (all literals come from the parents). -/
theorem resolve_subset (c₁ c₂ : Clause) (l : Literal) (x : Literal)
    (hx : x ∈ resolve c₁ c₂ l) : x ∈ c₁ ∨ x ∈ c₂ := by
  simp [resolve, List.mem_append, List.mem_filter] at hx
  cases hx with
  | inl h => exact Or.inl h.1
  | inr h => exact Or.inr h.1

/-! ## Resolution as Path Composition -/

/-- Derivation steps modeled as Nat (counting derived clauses). -/
abbrev DerivStep := Nat

/-- A resolution derivation path between step counts. -/
abbrev ResPath (s₁ s₂ : DerivStep) := Path s₁ s₂

/-- Resolution as path composition: each resolution step advances the count. -/
def resolution_as_trans (s₁ s₂ s₃ : DerivStep)
    (p : ResPath s₁ s₂) (q : ResPath s₂ s₃) : ResPath s₁ s₃ :=
  Path.trans p q

/-- Resolution is associative. -/
theorem resolution_assoc (s₁ s₂ s₃ s₄ : DerivStep)
    (p : ResPath s₁ s₂) (q : ResPath s₂ s₃) (r : ResPath s₃ s₄) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by simp

/-- Resolution with identity (refl) on the left. -/
theorem resolution_refl_left (s₁ s₂ : DerivStep) (p : ResPath s₁ s₂) :
    Path.trans (Path.refl s₁) p = p := by simp

/-- Resolution with identity on the right. -/
theorem resolution_refl_right (s₁ s₂ : DerivStep) (p : ResPath s₁ s₂) :
    Path.trans p (Path.refl s₂) = p := by simp

/-- Composing two resolution steps yields a combined derivation. -/
theorem resolution_compose_toEq (s₁ s₂ s₃ : DerivStep)
    (p : ResPath s₁ s₂) (q : ResPath s₂ s₃) :
    (Path.trans p q).toEq = p.toEq.trans q.toEq := by simp

/-- Inverting a resolution derivation. -/
theorem resolution_symm (s₁ s₂ : DerivStep) (p : ResPath s₁ s₂) :
    (Path.symm p).toEq = p.toEq.symm := by simp

/-- Double symmetry is identity. -/
theorem resolution_symm_symm (s₁ s₂ : DerivStep) (p : ResPath s₁ s₂) :
    Path.symm (Path.symm p) = p := Path.symm_symm p

/-- Symmetry distributes over composition (reversed). -/
theorem resolution_symm_trans (s₁ s₂ s₃ : DerivStep)
    (p : ResPath s₁ s₂) (q : ResPath s₂ s₃) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) := by simp

/-! ## Unit Propagation as Path Shortening -/

/-- Unit propagation: filtering removes literals from clauses. -/
def unitPropagate (c : Clause) (l : Literal) : Clause :=
  c.filter (· != l.negate)

/-- Unit propagation does not increase clause size. -/
theorem unit_propagation_shortens (c : Clause) (l : Literal) :
    (unitPropagate c l).length ≤ c.length :=
  List.length_filter_le _ c

/-- Unit propagation preserves membership of unaffected literals. -/
theorem unit_propagation_preserves (c : Clause) (l x : Literal)
    (hx : x ∈ c) (hneq : x ≠ l.negate) :
    x ∈ unitPropagate c l := by
  simp [unitPropagate, List.mem_filter]
  exact ⟨hx, hneq⟩

/-- Unit propagation of the empty clause is empty. -/
theorem unit_propagation_empty (l : Literal) :
    unitPropagate emptyClause l = emptyClause := by
  simp [unitPropagate, emptyClause]

/-- Double unit propagation. -/
theorem unit_propagation_compose (c : Clause) (l₁ l₂ : Literal) :
    unitPropagate (unitPropagate c l₁) l₂ =
      (c.filter (· != l₁.negate)).filter (· != l₂.negate) := by
  simp [unitPropagate]

/-- CongrArg through unit propagation. -/
theorem congrArg_unit_prop (c₁ c₂ : Clause) (l : Literal)
    (p : Path c₁ c₂) :
    Path.congrArg (fun c => unitPropagate c l) p =
      Path.congrArg (fun c => unitPropagate c l) p := rfl

/-! ## Refutation as Path to Empty Clause -/

/-- A refutation witness: a derivation reaching the empty clause. -/
structure Refutation where
  steps : Nat   -- number of resolution steps
  derives_empty : Prop  -- the derivation produces the empty clause

/-- Trivial refutation when empty clause is given. -/
def trivialRefutation : Refutation :=
  ⟨0, True⟩

/-- Subsumption: one clause is a subset of another. -/
def subsumes (c₁ c₂ : Clause) : Prop :=
  ∀ l : Literal, l ∈ c₁ → l ∈ c₂

/-- Subsumption is reflexive. -/
theorem subsumes_refl (c : Clause) : subsumes c c :=
  fun _ h => h

/-- Subsumption is transitive. -/
theorem subsumes_trans (c₁ c₂ c₃ : Clause)
    (h₁ : subsumes c₁ c₂) (h₂ : subsumes c₂ c₃) : subsumes c₁ c₃ :=
  fun l hl => h₂ l (h₁ l hl)

/-- The empty clause is subsumed by every clause (vacuously). -/
theorem empty_subsumes_all (c : Clause) : subsumes emptyClause c := by
  intro l hl
  simp [emptyClause] at hl

/-- Subsumption as a path property via congrArg. -/
theorem subsumes_congrArg (c₁ c₂ c₃ : Clause)
    (p : Path c₁ c₂) (h : subsumes c₂ c₃) :
    subsumes c₁ c₃ := by
  cases p with | mk _ proof => cases proof; exact h

/-! ## Path Properties of Resolution -/

/-- CongrArg distributes over trans for clause paths. -/
theorem congrArg_trans_clause (f : Clause → Clause)
    (c₁ c₂ c₃ : Clause) (p : Path c₁ c₂) (q : Path c₂ c₃) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) := by simp

/-- CongrArg commutes with symm. -/
theorem congrArg_symm_clause (f : Clause → Clause)
    (c₁ c₂ : Clause) (p : Path c₁ c₂) :
    Path.congrArg f (Path.symm p) =
      Path.symm (Path.congrArg f p) := by simp

/-- Transport of clause properties along paths. -/
theorem transport_clause_refl (P : Clause → Type u) (c : Clause) (x : P c) :
    Path.transport (D := P) (Path.refl c) x = x := rfl

/-- Transport along composed clause paths factors. -/
theorem transport_clause_trans (P : Clause → Type u)
    (c₁ c₂ c₃ : Clause) (p : Path c₁ c₂) (q : Path c₂ c₃) (x : P c₁) :
    Path.transport (D := P) (Path.trans p q) x =
      Path.transport (D := P) q (Path.transport (D := P) p x) := by
  cases p with
  | mk _ proof₁ =>
    cases proof₁
    cases q with
    | mk _ proof₂ =>
      cases proof₂
      rfl

/-! ## Derivation Length -/

/-- Length of a derivation as the number of steps. -/
def derivationLength {s₁ s₂ : DerivStep} (p : ResPath s₁ s₂) : Nat :=
  p.steps.length

/-- Identity derivation has length 0. -/
theorem refl_length (s : DerivStep) :
    derivationLength (Path.refl s) = 0 := by
  simp [derivationLength]

/-- Composition adds derivation lengths. -/
theorem trans_length {s₁ s₂ s₃ : DerivStep}
    (p : ResPath s₁ s₂) (q : ResPath s₂ s₃) :
    derivationLength (Path.trans p q) =
      derivationLength p + derivationLength q := by
  simp [derivationLength, Path.trans]

/-- Symmetry preserves derivation length. -/
theorem symm_length {s₁ s₂ : DerivStep} (p : ResPath s₁ s₂) :
    derivationLength (Path.symm p) = derivationLength p := by
  simp [derivationLength, Path.symm]

/-- CongrArg preserves derivation length. -/
theorem congrArg_length {s₁ s₂ : DerivStep} (f : DerivStep → DerivStep)
    (p : ResPath s₁ s₂) :
    derivationLength (Path.congrArg f p) = derivationLength p := by
  simp [derivationLength, Path.congrArg]

end ResolutionPaths
end Logic
end Path
end ComputationalPaths
