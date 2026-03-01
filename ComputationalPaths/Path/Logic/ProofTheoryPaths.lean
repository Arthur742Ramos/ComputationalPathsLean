/-
# Proof Theory via Computational Paths

Models proof-theoretic constructions through computational paths:
formal proofs as paths, cut elimination as path reduction, proof normalization,
Curry-Howard correspondence aspects, proof terms, and detour reduction.

## References

- Girard, "Proofs and Types"
- Troelstra & Schwichtenberg, "Basic Proof Theory"
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Logic
namespace ProofTheoryPaths

universe u

open ComputationalPaths.Path

/-! ## Proof states -/

/-- Abstract proof state, encoding derivation progress. -/
abbrev ProofState := Nat

/-- A proof-theoretic derivation path between states. -/
abbrev ProofPath (s₁ s₂ : ProofState) := Path s₁ s₂

/-! ## Proof constructors as path operations -/

/-- Assumption rule: identity on proof states. -/
noncomputable def assumeOp : ProofState → ProofState := id

/-- Introduction rule: advances proof state. -/
noncomputable def introOp : ProofState → ProofState := fun n => n + 1

/-- Elimination rule: processes proof state. -/
noncomputable def elimOp : ProofState → ProofState := fun n => 2 * n

/-- Application rule (modus ponens). -/
noncomputable def appOp : ProofState → ProofState := fun n => n + 2

/-- Abstraction (lambda). -/
noncomputable def absOp : ProofState → ProofState := fun n => 3 * n

/-! ## Introduction paths -/

/-- Introduction path: applying intro rule along a derivation. -/
noncomputable def introPath (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    Path (introOp s₁) (introOp s₂) :=
  Path.congrArg introOp p

/-- Introduction preserves composition. -/
theorem intro_trans (s₁ s₂ s₃ : ProofState)
    (p : ProofPath s₁ s₂) (q : ProofPath s₂ s₃) :
    introPath s₁ s₃ (Path.trans p q) =
      Path.trans (introPath s₁ s₂ p) (introPath s₂ s₃ q) := by
  simp [introPath]

/-- Introduction preserves symmetry. -/
theorem intro_symm (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    introPath s₂ s₁ (Path.symm p) = Path.symm (introPath s₁ s₂ p) := by
  simp [introPath]

/-! ## Elimination paths -/

/-- Elimination path: applying elim rule along a derivation. -/
noncomputable def elimPath (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    Path (elimOp s₁) (elimOp s₂) :=
  Path.congrArg elimOp p

/-- Elimination preserves composition. -/
theorem elim_trans (s₁ s₂ s₃ : ProofState)
    (p : ProofPath s₁ s₂) (q : ProofPath s₂ s₃) :
    elimPath s₁ s₃ (Path.trans p q) =
      Path.trans (elimPath s₁ s₂ p) (elimPath s₂ s₃ q) := by
  simp [elimPath]

/-- Elimination preserves symmetry. -/
theorem elim_symm (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    elimPath s₂ s₁ (Path.symm p) = Path.symm (elimPath s₁ s₂ p) := by
  simp [elimPath]

/-! ## Cut elimination as path normalization -/

/-- Cut as composition of proof paths. -/
noncomputable def cutPath (s₁ s₂ s₃ : ProofState)
    (p : ProofPath s₁ s₂) (q : ProofPath s₂ s₃) : ProofPath s₁ s₃ :=
  Path.trans p q

/-- Cut with identity on left is identity. -/
theorem cut_refl_left (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    cutPath s₁ s₁ s₂ (Path.refl s₁) p = p := by
  simp [cutPath]

/-- Cut with identity on right is identity. -/
theorem cut_refl_right (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    cutPath s₁ s₂ s₂ p (Path.refl s₂) = p := by
  simp [cutPath]

/-- Cut is associative. -/
theorem cut_assoc (s₁ s₂ s₃ s₄ : ProofState)
    (p : ProofPath s₁ s₂) (q : ProofPath s₂ s₃) (r : ProofPath s₃ s₄) :
    cutPath s₁ s₃ s₄ (cutPath s₁ s₂ s₃ p q) r =
      cutPath s₁ s₂ s₄ p (cutPath s₂ s₃ s₄ q r) := by
  simp [cutPath]

/-- Cut elimination: cut followed by inverse normalizes. -/
theorem cut_elim_normalize (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    (Path.trans p (Path.symm p)).toEq = (Path.refl s₁).toEq := by
  simp

/-- Cut elimination: inverse then cut normalizes. -/
theorem cut_elim_normalize' (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    (Path.trans (Path.symm p) p).toEq = (Path.refl s₂).toEq := by
  simp

/-! ## Proof normalization -/

/-- Double negation elimination as double symmetry. -/
theorem double_neg_elim (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    Path.symm (Path.symm p) = p := Path.symm_symm p

/-- Symmetry distributes over composition (reversed). -/
theorem symm_over_trans (s₁ s₂ s₃ : ProofState)
    (p : ProofPath s₁ s₂) (q : ProofPath s₂ s₃) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) := by
  simp

/-! ## Curry-Howard correspondence -/

/-- Application path: modus ponens as path operation. -/
noncomputable def appPath (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    Path (appOp s₁) (appOp s₂) :=
  Path.congrArg appOp p

/-- Abstraction path: lambda abstraction as path operation. -/
noncomputable def absPath (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    Path (absOp s₁) (absOp s₂) :=
  Path.congrArg absOp p

/-- Application preserves composition (function application distributes). -/
theorem app_trans (s₁ s₂ s₃ : ProofState)
    (p : ProofPath s₁ s₂) (q : ProofPath s₂ s₃) :
    appPath s₁ s₃ (Path.trans p q) =
      Path.trans (appPath s₁ s₂ p) (appPath s₂ s₃ q) := by
  simp [appPath]

/-- Abstraction preserves composition. -/
theorem abs_trans (s₁ s₂ s₃ : ProofState)
    (p : ProofPath s₁ s₂) (q : ProofPath s₂ s₃) :
    absPath s₁ s₃ (Path.trans p q) =
      Path.trans (absPath s₁ s₂ p) (absPath s₂ s₃ q) := by
  simp [absPath]

/-- Application preserves symmetry. -/
theorem app_symm (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    appPath s₂ s₁ (Path.symm p) = Path.symm (appPath s₁ s₂ p) := by
  simp [appPath]

/-- Abstraction preserves symmetry. -/
theorem abs_symm (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    absPath s₂ s₁ (Path.symm p) = Path.symm (absPath s₁ s₂ p) := by
  simp [absPath]

/-- Beta reduction: composition of abs then app. -/
theorem beta_compose (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    appPath (absOp s₁) (absOp s₂) (absPath s₁ s₂ p) =
      Path.congrArg (fun x => appOp (absOp x)) p := by
  simp [appPath, absPath]

/-! ## Proof terms and depth -/

/-- Proof depth: number of steps in a proof path. -/
noncomputable def proofDepth {s₁ s₂ : ProofState} (p : ProofPath s₁ s₂) : Nat :=
  p.steps.length

/-- Reflexive proof has depth 0. -/
theorem refl_proof_depth (s : ProofState) :
    proofDepth (Path.refl s) = 0 := by
  simp [proofDepth]

/-- Composition adds proof depths. -/
theorem trans_proof_depth (s₁ s₂ s₃ : ProofState)
    (p : ProofPath s₁ s₂) (q : ProofPath s₂ s₃) :
    proofDepth (Path.trans p q) = proofDepth p + proofDepth q := by
  simp [proofDepth]

/-- Symmetry preserves proof depth. -/
theorem symm_proof_depth (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    proofDepth (Path.symm p) = proofDepth p := by
  simp [proofDepth]

/-- CongrArg preserves proof depth. -/
theorem congrArg_proof_depth (f : ProofState → ProofState) (s₁ s₂ : ProofState)
    (p : ProofPath s₁ s₂) :
    proofDepth (Path.congrArg f p) = proofDepth p := by
  simp [proofDepth]

/-! ## Transport of proof properties -/

/-- Transport proof properties along paths. -/
theorem proof_transport_refl (P : ProofState → Type u) (s : ProofState) (x : P s) :
    Path.transport (D := P) (Path.refl s) x = x := rfl

/-- Transport along composed proof paths factors. -/
theorem proof_transport_trans (P : ProofState → Type u)
    (s₁ s₂ s₃ : ProofState) (p : ProofPath s₁ s₂) (q : ProofPath s₂ s₃) (x : P s₁) :
    Path.transport (D := P) (Path.trans p q) x =
      Path.transport (D := P) q (Path.transport (D := P) p x) := by
  cases p with | mk _ proof₁ => cases proof₁; cases q with | mk _ proof₂ => cases proof₂; rfl

/-- Transport along symm inverts. -/
theorem proof_transport_symm (P : ProofState → Type u)
    (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) (x : P s₁) :
    Path.transport (D := P) (Path.symm p) (Path.transport (D := P) p x) = x := by
  cases p with | mk _ proof => cases proof; rfl

/-! ## Structural rules -/

/-- Weakening: adding unused hypotheses. -/
noncomputable def weakenProof (extra : Nat) (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    ProofPath (s₁ + extra) (s₂ + extra) :=
  Path.congrArg (· + extra) p

/-- Weakening preserves composition. -/
theorem weaken_trans (extra : Nat) (s₁ s₂ s₃ : ProofState)
    (p : ProofPath s₁ s₂) (q : ProofPath s₂ s₃) :
    weakenProof extra s₁ s₃ (Path.trans p q) =
      Path.trans (weakenProof extra s₁ s₂ p) (weakenProof extra s₂ s₃ q) := by
  simp [weakenProof]

/-- Weakening preserves symmetry. -/
theorem weaken_symm (extra : Nat) (s₁ s₂ : ProofState)
    (p : ProofPath s₁ s₂) :
    weakenProof extra s₂ s₁ (Path.symm p) =
      Path.symm (weakenProof extra s₁ s₂ p) := by
  simp [weakenProof]

/-- Contraction: merging duplicate hypotheses. -/
noncomputable def contractProof (f : ProofState → ProofState) (s₁ s₂ : ProofState)
    (p : ProofPath s₁ s₂) : ProofPath (f s₁) (f s₂) :=
  Path.congrArg f p

/-- Contraction preserves composition. -/
theorem contract_trans (f : ProofState → ProofState) (s₁ s₂ s₃ : ProofState)
    (p : ProofPath s₁ s₂) (q : ProofPath s₂ s₃) :
    contractProof f s₁ s₃ (Path.trans p q) =
      Path.trans (contractProof f s₁ s₂ p) (contractProof f s₂ s₃ q) := by
  simp [contractProof]

/-- Exchange: reordering hypotheses via composed congruence. -/
noncomputable def exchangeProof (f g : ProofState → ProofState) (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    ProofPath (f (g s₁)) (f (g s₂)) :=
  Path.congrArg f (Path.congrArg g p)

/-- Exchange equals composed congrArg. -/
theorem exchange_eq_comp (f g : ProofState → ProofState)
    (s₁ s₂ : ProofState) (p : ProofPath s₁ s₂) :
    exchangeProof f g s₁ s₂ p = Path.congrArg (fun x => f (g x)) p := by
  simp [exchangeProof]

end ProofTheoryPaths
end Logic
end Path
end ComputationalPaths
