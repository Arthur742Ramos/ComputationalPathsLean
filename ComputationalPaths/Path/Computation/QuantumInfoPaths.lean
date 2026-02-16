/-
# Quantum Information via Computational Paths

Density matrices, von Neumann entropy, quantum channels, fidelity,
trace distance modeled via computational paths with genuine Path operations.
All paths use `refl`, `trans`, `symm`, `congrArg`, `transport` — zero `Path.ofEq`.

## Main results (50 theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Computation.QuantumInfoPaths

open ComputationalPaths.Path

/-! ## Qubit state model -/

/-- A 2x2 density matrix (simplified to Nat components). -/
structure DensityMatrix where
  p00 : Nat
  p11 : Nat
  coh : Nat
deriving DecidableEq, Repr

@[simp] def DensityMatrix.trace (ρ : DensityMatrix) : Nat := ρ.p00 + ρ.p11
@[simp] def DensityMatrix.entropy (ρ : DensityMatrix) : Nat := ρ.p00 * ρ.p11 - ρ.coh * ρ.coh

def isPure (ρ : DensityMatrix) : Prop := ρ.coh * ρ.coh = ρ.p00 * ρ.p11
def isMixed (ρ : DensityMatrix) : Prop := ρ.coh * ρ.coh < ρ.p00 * ρ.p11

/-! ## Named states -/

@[simp] def pureZero : DensityMatrix := ⟨1, 0, 0⟩
@[simp] def pureOne : DensityMatrix := ⟨0, 1, 0⟩
@[simp] def maxMixed : DensityMatrix := ⟨1, 1, 0⟩
@[simp] def purePlus : DensityMatrix := ⟨1, 1, 1⟩

/-! ## Quantum operations -/

/-- Elementary quantum operations. -/
inductive QOp : Type where
  | identity   : QOp
  | dephase    : QOp
  | bitFlip    : QOp
  | depolarize : QOp
  | ampDamp    : QOp
deriving DecidableEq, Repr

@[simp] def QOp.apply : QOp → DensityMatrix → DensityMatrix
  | .identity,   ρ => ρ
  | .dephase,    ρ => ⟨ρ.p00, ρ.p11, 0⟩
  | .bitFlip,    ρ => ⟨ρ.p11, ρ.p00, ρ.coh⟩
  | .depolarize, _ => maxMixed
  | .ampDamp,    ρ => ⟨ρ.p00 + ρ.p11, 0, 0⟩

/-- A quantum channel is a list of operations applied sequentially. -/
abbrev QChannel := List QOp

@[simp] def QChannel.apply : QChannel → DensityMatrix → DensityMatrix
  | [],        ρ => ρ
  | op :: ops, ρ => QChannel.apply ops (op.apply ρ)

@[simp] def QChannel.compose (c1 c2 : QChannel) : QChannel :=
  (c1 : List QOp) ++ (c2 : List QOp)

/-! ## Basic property theorems -/

-- 1
theorem identity_apply (ρ : DensityMatrix) : QOp.identity.apply ρ = ρ := by rfl
-- 2
theorem bitFlip_involution (ρ : DensityMatrix) :
    QOp.bitFlip.apply (QOp.bitFlip.apply ρ) = ρ := by cases ρ; simp
-- 3
theorem dephase_idempotent (ρ : DensityMatrix) :
    QOp.dephase.apply (QOp.dephase.apply ρ) = QOp.dephase.apply ρ := by rfl
-- 4
theorem depolarize_const (ρ σ : DensityMatrix) :
    QOp.depolarize.apply ρ = QOp.depolarize.apply σ := by rfl
-- 5
theorem dephase_coh_zero (ρ : DensityMatrix) :
    (QOp.dephase.apply ρ).coh = 0 := by rfl
-- 6
theorem ampDamp_coh_zero (ρ : DensityMatrix) :
    (QOp.ampDamp.apply ρ).coh = 0 := by rfl
-- 7
theorem ampDamp_trace (ρ : DensityMatrix) :
    (QOp.ampDamp.apply ρ).trace = ρ.trace := by simp [DensityMatrix.trace]
-- 8
theorem pureZero_trace : pureZero.trace = 1 := by rfl
-- 9
theorem pureOne_trace : pureOne.trace = 1 := by rfl
-- 10
theorem maxMixed_trace : maxMixed.trace = 2 := by rfl
-- 11
theorem pureZero_entropy : pureZero.entropy = 0 := by rfl
-- 12
theorem maxMixed_entropy : maxMixed.entropy = 1 := by rfl
-- 13
theorem purePlus_entropy : purePlus.entropy = 0 := by rfl
-- 14
theorem pureZero_isPure : isPure pureZero := by simp [isPure]
-- 15
theorem maxMixed_isMixed : isMixed maxMixed := by simp [isMixed]
-- 16
theorem dephase_trace (ρ : DensityMatrix) :
    (QOp.dephase.apply ρ).trace = ρ.trace := by rfl
-- 17
theorem bitFlip_trace (ρ : DensityMatrix) :
    (QOp.bitFlip.apply ρ).trace = ρ.trace := by
  simp [DensityMatrix.trace, Nat.add_comm]
-- 18
theorem bitFlip_entropy (ρ : DensityMatrix) :
    (QOp.bitFlip.apply ρ).entropy = ρ.entropy := by
  simp [DensityMatrix.entropy, Nat.mul_comm]
-- 19
theorem dephase_entropy (ρ : DensityMatrix) :
    (QOp.dephase.apply ρ).entropy = ρ.p00 * ρ.p11 := by
  simp [DensityMatrix.entropy]
-- 20
theorem depolarize_trace (ρ : DensityMatrix) :
    (QOp.depolarize.apply ρ).trace = 2 := by rfl

/-! ## Fidelity and distance -/

@[simp] def fidelity (ρ σ : DensityMatrix) : Nat :=
  ρ.p00 * σ.p00 + ρ.p11 * σ.p11 + ρ.coh * σ.coh

@[simp] def traceDistance (ρ σ : DensityMatrix) : Nat :=
  (if ρ.p00 ≥ σ.p00 then ρ.p00 - σ.p00 else σ.p00 - ρ.p00) +
  (if ρ.p11 ≥ σ.p11 then ρ.p11 - σ.p11 else σ.p11 - ρ.p11)

-- 21
theorem fidelity_comm (ρ σ : DensityMatrix) :
    fidelity ρ σ = fidelity σ ρ := by simp [Nat.mul_comm]
-- 22
theorem traceDistance_self (ρ : DensityMatrix) : traceDistance ρ ρ = 0 := by simp
-- 23
theorem traceDistance_comm (ρ σ : DensityMatrix) :
    traceDistance ρ σ = traceDistance σ ρ := by
  simp only [traceDistance]; congr 1 <;> (split <;> split <;> omega)
-- 24
theorem fidelity_orthogonal : fidelity pureZero pureOne = 0 := by rfl
-- 25
theorem traceDistance_orthogonal : traceDistance pureZero pureOne = 2 := by rfl
-- 26
theorem fidelity_self (ρ : DensityMatrix) :
    fidelity ρ ρ = ρ.p00 * ρ.p00 + ρ.p11 * ρ.p11 + ρ.coh * ρ.coh := by rfl

/-! ## Channel algebra theorems -/

-- 27
theorem channel_compose_assoc (c1 c2 c3 : QChannel) :
    QChannel.compose (QChannel.compose c1 c2) c3 =
    QChannel.compose c1 (QChannel.compose c2 c3) := by
  simp [List.append_assoc]
-- 28
theorem channel_empty_apply (ρ : DensityMatrix) : QChannel.apply [] ρ = ρ := by rfl
-- 29
theorem channel_singleton (op : QOp) (ρ : DensityMatrix) :
    QChannel.apply [op] ρ = op.apply ρ := by rfl
-- 30
theorem channel_compose_apply (c1 c2 : QChannel) (ρ : DensityMatrix) :
    QChannel.apply (QChannel.compose c1 c2) ρ =
    QChannel.apply c2 (QChannel.apply c1 ρ) := by
  induction c1 generalizing ρ with
  | nil => simp [QChannel.compose, QChannel.apply]
  | cons op ops ih =>
    simp only [QChannel.compose, List.cons_append, QChannel.apply]
    exact ih (op.apply ρ)
-- 31
theorem channel_compose_nil_left (c : QChannel) (ρ : DensityMatrix) :
    QChannel.apply (QChannel.compose [] c) ρ = QChannel.apply c ρ := by
  simp [QChannel.compose, QChannel.apply]
-- 32
theorem channel_compose_nil_right (c : QChannel) (ρ : DensityMatrix) :
    QChannel.apply (QChannel.compose c []) ρ = QChannel.apply c ρ := by
  rw [channel_compose_apply]; rfl
-- 33
theorem depol_then_dephase (ρ : DensityMatrix) :
    QChannel.apply [.depolarize, .dephase] ρ = QChannel.apply [.depolarize] ρ := by
  simp [QChannel.apply]
-- 34
theorem bitFlip_twice_channel (ρ : DensityMatrix) :
    QChannel.apply [.bitFlip, .bitFlip] ρ = ρ := by
  cases ρ; simp [QChannel.apply, QOp.apply]

/-! ## Genuine Path constructions via refl / trans / symm / congrArg -/

-- 35. Identity channel gives refl path
def identity_path (ρ : DensityMatrix) : Path (QOp.identity.apply ρ) ρ :=
  Path.refl ρ

-- 36. CongrArg through trace
def trace_congrArg {ρ σ : DensityMatrix} (p : Path ρ σ) :
    Path ρ.trace σ.trace :=
  Path.congrArg DensityMatrix.trace p

-- 37. CongrArg through entropy
def entropy_congrArg {ρ σ : DensityMatrix} (p : Path ρ σ) :
    Path ρ.entropy σ.entropy :=
  Path.congrArg DensityMatrix.entropy p

-- 38. CongrArg through QOp.apply
def qop_congrArg (op : QOp) {ρ σ : DensityMatrix} (p : Path ρ σ) :
    Path (op.apply ρ) (op.apply σ) :=
  Path.congrArg op.apply p

-- 39. CongrArg through fidelity (left)
def fidelity_congrArg_left {ρ₁ ρ₂ : DensityMatrix} (σ : DensityMatrix)
    (p : Path ρ₁ ρ₂) : Path (fidelity ρ₁ σ) (fidelity ρ₂ σ) :=
  Path.congrArg (fun ρ => fidelity ρ σ) p

-- 40. CongrArg through fidelity (right)
def fidelity_congrArg_right (ρ : DensityMatrix) {σ₁ σ₂ : DensityMatrix}
    (p : Path σ₁ σ₂) : Path (fidelity ρ σ₁) (fidelity ρ σ₂) :=
  Path.congrArg (fidelity ρ) p

-- 41. Symm of a density matrix path
def dm_symm {ρ σ : DensityMatrix} (p : Path ρ σ) : Path σ ρ :=
  Path.symm p

-- 42. Trans of density matrix paths
def dm_trans {ρ σ τ : DensityMatrix} (p : Path ρ σ) (q : Path σ τ) : Path ρ τ :=
  Path.trans p q

-- 43. Refl is left identity for trans
theorem dm_trans_refl_left {ρ σ : DensityMatrix} (p : Path ρ σ) :
    Path.trans (Path.refl ρ) p = p := by simp

-- 44. Refl is right identity for trans
theorem dm_trans_refl_right {ρ σ : DensityMatrix} (p : Path ρ σ) :
    Path.trans p (Path.refl σ) = p := by simp

-- 45. Trans is associative
theorem dm_trans_assoc {ρ σ τ υ : DensityMatrix}
    (p : Path ρ σ) (q : Path σ τ) (r : Path τ υ) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by simp

-- 46. Symm is involutive
theorem dm_symm_symm {ρ σ : DensityMatrix} (p : Path ρ σ) :
    Path.symm (Path.symm p) = p := Path.symm_symm p

-- 47. CongrArg preserves trans
theorem congrArg_trace_trans {ρ σ τ : DensityMatrix}
    (p : Path ρ σ) (q : Path σ τ) :
    Path.congrArg DensityMatrix.trace (Path.trans p q) =
    Path.trans (Path.congrArg DensityMatrix.trace p)
              (Path.congrArg DensityMatrix.trace q) := by simp

-- 48. CongrArg preserves symm
theorem congrArg_trace_symm {ρ σ : DensityMatrix} (p : Path ρ σ) :
    Path.congrArg DensityMatrix.trace (Path.symm p) =
    Path.symm (Path.congrArg DensityMatrix.trace p) := by simp

/-! ## Transport -/

-- 49. Transport a predicate along a density matrix path
def transport_isPure {ρ σ : DensityMatrix} (p : Path ρ σ) (h : isPure ρ) :
    isPure σ :=
  Path.transport (D := isPure) p h

-- 50. Transport const along density matrix path
theorem transport_const_dm {ρ σ : DensityMatrix} (p : Path ρ σ) (n : Nat) :
    Path.transport (D := fun _ => Nat) p n = n := by simp

-- 51. Path coherence (UIP)
theorem density_path_coherence {ρ σ : DensityMatrix} (p q : Path ρ σ) :
    p.proof = q.proof :=
  Subsingleton.elim _ _

-- 52. CongrArg composition: trace ∘ apply = congrArg trace ∘ congrArg apply
theorem congrArg_comp_trace_apply (op : QOp) {ρ σ : DensityMatrix}
    (p : Path ρ σ) :
    Path.congrArg (fun x => (op.apply x).trace) p =
    Path.congrArg DensityMatrix.trace (Path.congrArg op.apply p) := by simp

end ComputationalPaths.Path.Computation.QuantumInfoPaths
