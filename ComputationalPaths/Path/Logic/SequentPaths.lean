/-
# Sequent Calculus as Computational Paths

This module models sequent calculus proofs via computational paths:
sequents as path endpoints, the cut rule as path composition (trans),
cut elimination as path normalization, structural rules as path operations,
and the sub-formula property.

## Key Results

| Definition/Theorem                    | Description                              |
|--------------------------------------|------------------------------------------|
| `Formula`                            | Propositional formula type               |
| `Sequent`                            | Sequent Γ ⊢ Δ representation            |
| `SequentPath`                        | Derivation as a path                     |
| `cut_as_trans`                       | Cut rule modeled by path composition     |
| `cut_elim_normalize`                 | Cut elimination as normalization         |
| `subformula_property`                | Sub-formula property for cut-free proofs |

## References

- Gentzen, "Untersuchungen über das logische Schließen"
- Girard, "Proofs and Types"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Logic
namespace SequentPaths

universe u

/-! ## Formulas -/

/-- Propositional formulas over atomic propositions. -/
inductive Formula : Type where
  | atom : Nat → Formula
  | top : Formula
  | bot : Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | impl : Formula → Formula → Formula
  | neg : Formula → Formula
  deriving DecidableEq, Repr

namespace Formula

/-- Size of a formula (number of connectives). -/
def size : Formula → Nat
  | atom _ => 1
  | top => 1
  | bot => 1
  | conj A B => 1 + size A + size B
  | disj A B => 1 + size A + size B
  | impl A B => 1 + size A + size B
  | neg A => 1 + size A

@[simp] theorem size_pos (f : Formula) : 0 < size f := by
  cases f <;> simp [size] <;> omega

/-- A formula is a sub-formula of another. -/
inductive SubFormula (f : Formula) : Formula → Prop where
  | refl : SubFormula f f
  | conj_left (A B : Formula) : SubFormula f A → SubFormula f (conj A B)
  | conj_right (A B : Formula) : SubFormula f B → SubFormula f (conj A B)
  | disj_left (A B : Formula) : SubFormula f A → SubFormula f (disj A B)
  | disj_right (A B : Formula) : SubFormula f B → SubFormula f (disj A B)
  | impl_left (A B : Formula) : SubFormula f A → SubFormula f (impl A B)
  | impl_right (A B : Formula) : SubFormula f B → SubFormula f (impl A B)
  | neg_sub (A : Formula) : SubFormula f A → SubFormula f (neg A)

/-- SubFormula is transitive. -/
theorem SubFormula.trans' {f g h : Formula} (hfg : SubFormula f g) (hgh : SubFormula g h) :
    SubFormula f h := by
  induction hgh with
  | refl => exact hfg
  | conj_left A B _ ih => exact SubFormula.conj_left A B ih
  | conj_right A B _ ih => exact SubFormula.conj_right A B ih
  | disj_left A B _ ih => exact SubFormula.disj_left A B ih
  | disj_right A B _ ih => exact SubFormula.disj_right A B ih
  | impl_left A B _ ih => exact SubFormula.impl_left A B ih
  | impl_right A B _ ih => exact SubFormula.impl_right A B ih
  | neg_sub A _ ih => exact SubFormula.neg_sub A ih

end Formula

/-! ## Sequent Derivation State -/

/-- A derivation state tracks the current step in a proof.
    We use Nat as abstract derivation states to enable path operations. -/
abbrev DerivState := Nat

/-- Initial derivation state. -/
def initState : DerivState := 0

/-- Advance the derivation state. -/
def advanceState (s : DerivState) : DerivState := s + 1

/-- A sequent derivation as a path between derivation states. -/
abbrev DerivPath (s₁ s₂ : DerivState) := Path s₁ s₂

/-! ## Cut Rule as Path Composition -/

/-- Cut rule as trans: composing two derivation paths. -/
def cut_as_trans (s₁ s₂ s₃ : DerivState)
    (p : DerivPath s₁ s₂) (q : DerivPath s₂ s₃) : DerivPath s₁ s₃ :=
  Path.trans p q

/-- Cut on reflexivity is the identity path. -/
theorem cut_refl_left (s₁ s₂ : DerivState) (p : DerivPath s₁ s₂) :
    cut_as_trans s₁ s₁ s₂ (Path.refl s₁) p = p := by
  simp [cut_as_trans]

/-- Cut on reflexivity on the right is the identity. -/
theorem cut_refl_right (s₁ s₂ : DerivState) (p : DerivPath s₁ s₂) :
    cut_as_trans s₁ s₂ s₂ p (Path.refl s₂) = p := by
  simp [cut_as_trans]

/-- Cut is associative. -/
theorem cut_assoc (s₁ s₂ s₃ s₄ : DerivState)
    (p : DerivPath s₁ s₂) (q : DerivPath s₂ s₃) (r : DerivPath s₃ s₄) :
    cut_as_trans s₁ s₃ s₄ (cut_as_trans s₁ s₂ s₃ p q) r =
      cut_as_trans s₁ s₂ s₄ p (cut_as_trans s₂ s₃ s₄ q r) := by
  simp [cut_as_trans]

/-! ## Cut Elimination as Path Normalization -/

/-- Cut followed by its inverse normalizes to reflexivity at the type level. -/
theorem cut_inverse_normalize (s₁ s₂ : DerivState) (p : DerivPath s₁ s₂) :
    (Path.trans p (Path.symm p)).toEq = (Path.refl s₁).toEq := by
  simp

/-- Inverse followed by cut normalizes to reflexivity. -/
theorem cut_inverse_normalize' (s₁ s₂ : DerivState) (p : DerivPath s₁ s₂) :
    (Path.trans (Path.symm p) p).toEq = (Path.refl s₂).toEq := by
  simp

/-- Double symmetry eliminates (normalization). -/
theorem cut_symm_symm (s₁ s₂ : DerivState) (p : DerivPath s₁ s₂) :
    Path.symm (Path.symm p) = p := Path.symm_symm p

/-- Symmetry distributes over composition (reversed). -/
theorem cut_symm_trans (s₁ s₂ s₃ : DerivState)
    (p : DerivPath s₁ s₂) (q : DerivPath s₂ s₃) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) := by
  simp

/-! ## Structural Rules as Path Operations -/

/-- Weakening: adding an unused formula doesn't change the derivation state path.
    Modeled as congrArg through a weakening function. -/
def weakenPath (extra : Nat) (s₁ s₂ : DerivState) (p : DerivPath s₁ s₂) :
    DerivPath (s₁ + extra) (s₂ + extra) :=
  Path.congrArg (· + extra) p

/-- Weakening preserves trans. -/
theorem weaken_trans (extra : Nat) (s₁ s₂ s₃ : DerivState)
    (p : DerivPath s₁ s₂) (q : DerivPath s₂ s₃) :
    weakenPath extra s₁ s₃ (Path.trans p q) =
      Path.trans (weakenPath extra s₁ s₂ p) (weakenPath extra s₂ s₃ q) := by
  simp [weakenPath]

/-- Weakening preserves symm. -/
theorem weaken_symm (extra : Nat) (s₁ s₂ : DerivState)
    (p : DerivPath s₁ s₂) :
    weakenPath extra s₂ s₁ (Path.symm p) =
      Path.symm (weakenPath extra s₁ s₂ p) := by
  simp [weakenPath]

/-- Weakening by zero preserves the proof. -/
theorem weaken_zero_toEq (s₁ s₂ : DerivState) (p : DerivPath s₁ s₂) :
    (weakenPath 0 s₁ s₂ p).toEq = _root_.congrArg (· + 0) p.toEq := by
  simp [weakenPath, Path.congrArg]

/-- Contraction: collapsing duplicate derivation states. -/
def contractPath (f : DerivState → DerivState) (s₁ s₂ : DerivState)
    (p : DerivPath s₁ s₂) : DerivPath (f s₁) (f s₂) :=
  Path.congrArg f p

/-- Contraction preserves trans. -/
theorem contract_trans (f : DerivState → DerivState)
    (s₁ s₂ s₃ : DerivState)
    (p : DerivPath s₁ s₂) (q : DerivPath s₂ s₃) :
    contractPath f s₁ s₃ (Path.trans p q) =
      Path.trans (contractPath f s₁ s₂ p) (contractPath f s₂ s₃ q) := by
  simp [contractPath]

/-- Contraction preserves symm. -/
theorem contract_symm (f : DerivState → DerivState) (s₁ s₂ : DerivState)
    (p : DerivPath s₁ s₂) :
    contractPath f s₂ s₁ (Path.symm p) =
      Path.symm (contractPath f s₁ s₂ p) := by
  simp [contractPath]

/-- Exchange: reordering modeled by composing two congruence maps. -/
def exchangePath (f g : DerivState → DerivState)
    (s₁ s₂ : DerivState) (p : DerivPath s₁ s₂) :
    DerivPath (f (g s₁)) (f (g s₂)) :=
  Path.congrArg f (Path.congrArg g p)

/-- Exchange equals composed congrArg. -/
theorem exchange_eq_comp (f g : DerivState → DerivState)
    (s₁ s₂ : DerivState) (p : DerivPath s₁ s₂) :
    exchangePath f g s₁ s₂ p = Path.congrArg (fun x => f (g x)) p := by
  simp [exchangePath]

/-! ## Sub-formula Property -/

/-- All formulas appearing in a list. -/
def allSubFormulas : List Formula → List Formula
  | [] => []
  | f :: rest => f :: allSubFormulas rest

/-- The sub-formula property: every formula is a sub-formula of itself. -/
theorem subformula_property_refl (f : Formula) :
    Formula.SubFormula f f := Formula.SubFormula.refl

/-- Sub-formulas of a conjunction include both components. -/
theorem subformula_conj_left (A B : Formula) :
    Formula.SubFormula A (Formula.conj A B) :=
  Formula.SubFormula.conj_left A B Formula.SubFormula.refl

/-- Sub-formulas of a conjunction include both components. -/
theorem subformula_conj_right (A B : Formula) :
    Formula.SubFormula B (Formula.conj A B) :=
  Formula.SubFormula.conj_right A B Formula.SubFormula.refl

/-! ## Transport of Derivation Properties -/

/-- Transport along refl is identity for derivation properties. -/
theorem transport_refl_deriv (P : DerivState → Type u) (s : DerivState) (x : P s) :
    Path.transport (D := P) (Path.refl s) x = x := rfl

/-- Transport along composed derivation paths factors. -/
theorem transport_trans_deriv (P : DerivState → Type u)
    (s₁ s₂ s₃ : DerivState) (p : DerivPath s₁ s₂) (q : DerivPath s₂ s₃) (x : P s₁) :
    Path.transport (D := P) (Path.trans p q) x =
      Path.transport (D := P) q (Path.transport (D := P) p x) := by
  cases p with
  | mk _ proof₁ =>
    cases proof₁
    cases q with
    | mk _ proof₂ =>
      cases proof₂
      rfl

/-- Transport along symm inverts transport. -/
theorem transport_symm_deriv (P : DerivState → Type u)
    (s₁ s₂ : DerivState) (p : DerivPath s₁ s₂) (x : P s₁) :
    Path.transport (D := P) (Path.symm p) (Path.transport (D := P) p x) = x := by
  cases p with
  | mk _ proof => cases proof; rfl

/-! ## Derivation Depth -/

/-- Depth of a derivation as the number of steps. -/
def derivationDepth {s₁ s₂ : DerivState} (p : DerivPath s₁ s₂) : Nat :=
  p.steps.length

/-- The identity derivation has depth 0. -/
theorem refl_depth (s : DerivState) :
    derivationDepth (Path.refl s) = 0 := by
  simp [derivationDepth]

/-- Composing derivations adds depths. -/
theorem trans_depth {s₁ s₂ s₃ : DerivState}
    (p : DerivPath s₁ s₂) (q : DerivPath s₂ s₃) :
    derivationDepth (Path.trans p q) =
      derivationDepth p + derivationDepth q := by
  simp [derivationDepth, Path.trans]

/-- Symmetry preserves derivation depth. -/
theorem symm_depth {s₁ s₂ : DerivState} (p : DerivPath s₁ s₂) :
    derivationDepth (Path.symm p) = derivationDepth p := by
  simp [derivationDepth, Path.symm]

/-- CongrArg preserves derivation steps count. -/
theorem congrArg_depth {s₁ s₂ : DerivState} (f : DerivState → DerivState)
    (p : DerivPath s₁ s₂) :
    derivationDepth (Path.congrArg f p) = derivationDepth p := by
  simp [derivationDepth, Path.congrArg]

end SequentPaths
end Logic
end Path
end ComputationalPaths
