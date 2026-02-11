/-
# Complexity bounds for LND_EQ-TRS rewriting

Defines lightweight complexity measures for LND_EQ-TRS reductions together
with predicates expressing bounds for reductions, word problem certificates,
Dehn functions, and isoperimetric inequalities.

## Key Results

- `pathLength`, `rwLength`, `rweqLength`: size measures for paths and
  rewrite certificates.
- `reductionBound`, `wordProblemBound`, `dehnBound`, `isoperimetricBound`:
  complexity bounds for the rewrite system.
- Monotonicity lemmas and implications between the bounds.

## Mathematical Background

Complexity bounds and Dehn functions measure the cost of solving word problems
in rewrite systems and express isoperimetric inequalities in the induced
groupoid structure.

## References

- de Queiroz, de Oliveira & Ramos, "Propositional equality, identity types,
  and direct computational paths", SAJL 2016
- Ramos et al., "Explicit Computational Paths", SAJL 2018
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace Complexity

universe u

/-! ## Path sizes -/

/-- Length of a path expression, measured by the recorded rewrite trace. -/
@[simp] def pathLength {A : Type u} {a b : A} (p : Path a b) : Nat :=
  p.steps.length

/-- Combined size of two paths, used for symmetric bounds. -/
@[simp] def pairLength {A : Type u} {a b : A} (p q : Path a b) : Nat :=
  pathLength p + pathLength q

/-- The reflexive path has zero length. -/
@[simp] theorem pathLength_refl {A : Type u} (a : A) :
    pathLength (Path.refl a) = 0 := by
  simp [pathLength]

/-- Path length is additive over composition. -/
@[simp] theorem pathLength_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    pathLength (Path.trans p q) = pathLength p + pathLength q := by
  simp [pathLength]

/-- Symmetry preserves path length. -/
@[simp] theorem pathLength_symm {A : Type u} {a b : A} (p : Path a b) :
    pathLength (Path.symm p) = pathLength p := by
  simp [pathLength]

/-! ## Derivation lengths -/

/-- Length of a reflexive-transitive reduction certificate. -/
def rwLength {A : Type u} {a b : A} {p q : Path a b} (h : Rw p q) : Nat :=
  match h with
  | Rw.refl _ => 0
  | Rw.tail h _ => rwLength h + 1

/-- Reflexive reductions have length zero. -/
@[simp] theorem rwLength_refl {A : Type u} {a b : A} (p : Path a b) :
    rwLength (Rw.refl p) = 0 := rfl

/-- Adding a tail step increments the length. -/
@[simp] theorem rwLength_tail {A : Type u} {a b : A}
    {p q r : Path a b} (h : Rw p q) (step : Step q r) :
    rwLength (Rw.tail h step) = rwLength h + 1 := rfl

/-- Length of a symmetric rewrite certificate. -/
def rweqLength {A : Type u} {a b : A} {p q : Path a b} (h : RwEq p q) : Nat :=
  match h with
  | RwEq.refl _ => 0
  | RwEq.step _ => 1
  | RwEq.symm h => rweqLength h
  | RwEq.trans h₁ h₂ => rweqLength h₁ + rweqLength h₂

/-- Reflexive rewrite equality certificates have length zero. -/
@[simp] theorem rweqLength_refl {A : Type u} {a b : A} (p : Path a b) :
    rweqLength (RwEq.refl p) = 0 := rfl

/-- A single rewrite step has length one. -/
@[simp] theorem rweqLength_step {A : Type u} {a b : A} {p q : Path a b}
    (h : Step p q) :
    rweqLength (RwEq.step h) = 1 := rfl

/-- Symmetry does not change the measured length. -/
@[simp] theorem rweqLength_symm {A : Type u} {a b : A} {p q : Path a b}
    (h : RwEq p q) :
    rweqLength (RwEq.symm h) = rweqLength h := rfl

/-- Concatenating certificates adds their lengths. -/
@[simp] theorem rweqLength_trans {A : Type u} {a b : A} {p q r : Path a b}
    (h₁ : RwEq p q) (h₂ : RwEq q r) :
    rweqLength (RwEq.trans h₁ h₂) = rweqLength h₁ + rweqLength h₂ := rfl

/-! ## Complexity bounds -/

/-- A complexity bound for LND_EQ-TRS reductions. -/
def reductionBound (f : Nat → Nat) : Prop :=
  ∀ {A : Type u} {a b : A} (p q : Path a b) (h : Rw p q),
    rwLength h ≤ f (pairLength p q)

/-- Monotonicity of reduction bounds. -/
theorem reductionBound_of_le {f g : Nat → Nat} (hfg : ∀ n, f n ≤ g n) :
    reductionBound f → reductionBound g := by
  intro hf A a b p q h
  exact le_trans (hf p q h) (hfg (pairLength p q))

/-- Word problem complexity bound for rewrite equality. -/
def wordProblemBound (f : Nat → Nat) : Prop :=
  ∀ {A : Type u} {a b : A} (p q : Path a b),
    RwEq p q → ∃ h : RwEq p q, rweqLength h ≤ f (pairLength p q)

/-- Monotonicity of word problem bounds. -/
theorem wordProblemBound_of_le {f g : Nat → Nat} (hfg : ∀ n, f n ≤ g n) :
    wordProblemBound f → wordProblemBound g := by
  intro hf A a b p q h
  rcases hf p q h with ⟨h', bound⟩
  exact ⟨h', le_trans bound (hfg (pairLength p q))⟩

/-- Dehn bounds for null-homotopic loops. -/
def dehnBound (f : Nat → Nat) : Prop :=
  ∀ {A : Type u} {a : A} (p : Path a a),
    RwEq p (Path.refl a) →
      ∃ h : RwEq p (Path.refl a), rweqLength h ≤ f (pathLength p)

/-- Monotonicity of Dehn bounds. -/
theorem dehnBound_of_le {f g : Nat → Nat} (hfg : ∀ n, f n ≤ g n) :
    dehnBound f → dehnBound g := by
  intro hf A a p hEq
  rcases hf p hEq with ⟨h', bound⟩
  exact ⟨h', le_trans bound (hfg (pathLength p))⟩

/-- Word problem bounds imply Dehn bounds. -/
theorem dehnBound_of_wordProblem {f : Nat → Nat} :
    wordProblemBound f → dehnBound f := by
  intro hf A a p hEq
  rcases hf (A := A) (a := a) (b := a) p (Path.refl a) hEq with ⟨h', bound⟩
  refine ⟨h', ?_⟩
  simpa [pairLength] using bound

/-- Isoperimetric inequality for the rewrite system. -/
def isoperimetricBound (f : Nat → Nat) : Prop :=
  dehnBound f

/-- Dehn bounds are isoperimetric inequalities. -/
theorem isoperimetricBound_of_dehn {f : Nat → Nat} :
    dehnBound f → isoperimetricBound f := by
  intro hf
  exact hf

end Complexity
end Rewrite
end Path
end ComputationalPaths
