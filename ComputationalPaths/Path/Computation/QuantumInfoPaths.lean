/-
# Quantum Information via Computational Paths

Density matrices, von Neumann entropy, quantum channels, fidelity,
trace distance modeled via computational paths.

## Main results (25+ theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Computation.QuantumInfoPaths

open ComputationalPaths.Path

/-! ## Density matrix model (simplified to Nat) -/

/-- A 2x2 density matrix represented by diagonal entries (populations)
    and off-diagonal magnitude. For a valid density matrix:
    p00 + p11 = trace, coherence ≤ min(p00, p11). -/
structure DensityMatrix where
  p00 : Nat    -- ⟨0|ρ|0⟩ (population of |0⟩)
  p11 : Nat    -- ⟨1|ρ|1⟩ (population of |1⟩)
  coh : Nat    -- |⟨0|ρ|1⟩| (coherence magnitude)
deriving DecidableEq, Repr

/-- Trace of a density matrix. -/
@[simp] def trace (ρ : DensityMatrix) : Nat := ρ.p00 + ρ.p11

/-- Pure state |0⟩⟨0|. -/
@[simp] def pureZero : DensityMatrix := ⟨1, 0, 0⟩

/-- Pure state |1⟩⟨1|. -/
@[simp] def pureOne : DensityMatrix := ⟨0, 1, 0⟩

/-- Maximally mixed state (I/2). -/
@[simp] def maxMixed : DensityMatrix := ⟨1, 1, 0⟩

/-- Pure state |+⟩⟨+|. -/
@[simp] def purePlus : DensityMatrix := ⟨1, 1, 1⟩

/-- Check if state is pure (coh² = p00 * p11 in exact case). -/
def isPure (ρ : DensityMatrix) : Prop := ρ.coh * ρ.coh = ρ.p00 * ρ.p11

/-- Check if state is mixed (not pure or zero coherence with both populations). -/
def isMixed (ρ : DensityMatrix) : Prop := ρ.coh * ρ.coh < ρ.p00 * ρ.p11

/-! ## Entropy model -/

/-- Simplified von Neumann entropy: 0 for pure, positive for mixed.
    We use a simple proxy: entropy = p00 * p11 - coh * coh. -/
@[simp] def entropy (ρ : DensityMatrix) : Nat :=
  ρ.p00 * ρ.p11 - ρ.coh * ρ.coh

/-! ## Quantum channels -/

/-- A quantum channel maps density matrices to density matrices. -/
def QChannel := DensityMatrix → DensityMatrix

/-- Identity channel. -/
@[simp] def idChannel : QChannel := fun ρ => ρ

/-- Completely depolarizing channel: maps everything to maximally mixed. -/
@[simp] def depolChannel : QChannel := fun _ => maxMixed

/-- Dephasing channel: kills coherence. -/
@[simp] def dephaseChannel : QChannel := fun ρ => ⟨ρ.p00, ρ.p11, 0⟩

/-- Bit-flip channel: swaps populations. -/
@[simp] def bitFlipChannel : QChannel := fun ρ => ⟨ρ.p11, ρ.p00, ρ.coh⟩

/-- Amplitude damping (simplified): moves population toward |0⟩. -/
@[simp] def ampDampChannel : QChannel := fun ρ => ⟨ρ.p00 + ρ.p11, 0, 0⟩

/-- Channel composition. -/
@[simp] def compChannel (c1 c2 : QChannel) : QChannel := fun ρ => c2 (c1 ρ)

/-! ## Fidelity and trace distance -/

/-- Fidelity between two states (simplified). -/
@[simp] def fidelity (ρ σ : DensityMatrix) : Nat :=
  ρ.p00 * σ.p00 + ρ.p11 * σ.p11 + ρ.coh * σ.coh

/-- Trace distance (simplified: sum of absolute differences). -/
@[simp] def traceDistance (ρ σ : DensityMatrix) : Nat :=
  (if ρ.p00 ≥ σ.p00 then ρ.p00 - σ.p00 else σ.p00 - ρ.p00) +
  (if ρ.p11 ≥ σ.p11 then ρ.p11 - σ.p11 else σ.p11 - ρ.p11)

/-! ## Core theorems -/

-- 1. Pure |0⟩ has trace 1
theorem pureZero_trace : trace pureZero = 1 := by rfl

def pureZero_trace_path : Path (trace pureZero) 1 :=
  Path.ofEq pureZero_trace

-- 2. Pure |1⟩ has trace 1
theorem pureOne_trace : trace pureOne = 1 := by rfl

-- 3. Max mixed has trace 2
theorem maxMixed_trace : trace maxMixed = 2 := by rfl

-- 4. Pure |0⟩ has zero entropy
theorem pureZero_entropy : entropy pureZero = 0 := by rfl

def pureZero_entropy_path : Path (entropy pureZero) 0 :=
  Path.ofEq pureZero_entropy

-- 5. Max mixed has positive entropy
theorem maxMixed_entropy : entropy maxMixed = 1 := by rfl

-- 6. Pure plus has zero entropy
theorem purePlus_entropy : entropy purePlus = 0 := by rfl

-- 7. Identity channel preserves state
theorem idChannel_apply (ρ : DensityMatrix) : idChannel ρ = ρ := by rfl

def idChannel_path (ρ : DensityMatrix) : Path (idChannel ρ) ρ :=
  Path.ofEq (idChannel_apply ρ)

-- 8. Depolarizing channel is constant
theorem depolChannel_const (ρ σ : DensityMatrix) :
    depolChannel ρ = depolChannel σ := by rfl

def depolChannel_const_path (ρ σ : DensityMatrix) :
    Path (depolChannel ρ) (depolChannel σ) :=
  Path.ofEq (depolChannel_const ρ σ)

-- 9. Dephasing kills coherence
theorem dephase_kills_coherence (ρ : DensityMatrix) :
    (dephaseChannel ρ).coh = 0 := by rfl

-- 10. Bit flip is an involution
theorem bitFlip_involution (ρ : DensityMatrix) :
    bitFlipChannel (bitFlipChannel ρ) = ρ := by
  cases ρ; simp [bitFlipChannel]

def bitFlip_involution_path (ρ : DensityMatrix) :
    Path (bitFlipChannel (bitFlipChannel ρ)) ρ :=
  Path.ofEq (bitFlip_involution ρ)

-- 11. Channel composition associativity
theorem compChannel_assoc (c1 c2 c3 : QChannel) :
    compChannel (compChannel c1 c2) c3 = compChannel c1 (compChannel c2 c3) := by
  funext ρ; rfl

def compChannel_assoc_path (c1 c2 c3 : QChannel) :
    Path (compChannel (compChannel c1 c2) c3)
         (compChannel c1 (compChannel c2 c3)) :=
  Path.ofEq (compChannel_assoc c1 c2 c3)

-- 12. Identity channel is left identity
theorem compChannel_id_left (c : QChannel) :
    compChannel idChannel c = c := by funext ρ; rfl

def compChannel_id_left_path (c : QChannel) :
    Path (compChannel idChannel c) c :=
  Path.ofEq (compChannel_id_left c)

-- 13. Identity channel is right identity
theorem compChannel_id_right (c : QChannel) :
    compChannel c idChannel = c := by funext ρ; rfl

-- 14. Fidelity of state with itself
theorem fidelity_self (ρ : DensityMatrix) :
    fidelity ρ ρ = ρ.p00 * ρ.p00 + ρ.p11 * ρ.p11 + ρ.coh * ρ.coh := by rfl

-- 15. Fidelity is symmetric
theorem fidelity_comm (ρ σ : DensityMatrix) :
    fidelity ρ σ = fidelity σ ρ := by
  simp [fidelity, Nat.mul_comm]

def fidelity_comm_path (ρ σ : DensityMatrix) :
    Path (fidelity ρ σ) (fidelity σ ρ) :=
  Path.ofEq (fidelity_comm ρ σ)

-- 16. Trace distance is zero for identical states
theorem traceDistance_self (ρ : DensityMatrix) :
    traceDistance ρ ρ = 0 := by
  simp [traceDistance]

def traceDistance_self_path (ρ : DensityMatrix) :
    Path (traceDistance ρ ρ) 0 :=
  Path.ofEq (traceDistance_self ρ)

-- 17. Trace distance is symmetric
theorem traceDistance_comm (ρ σ : DensityMatrix) :
    traceDistance ρ σ = traceDistance σ ρ := by
  simp only [traceDistance]
  congr 1
  · split <;> split <;> omega
  · split <;> split <;> omega

def traceDistance_comm_path (ρ σ : DensityMatrix) :
    Path (traceDistance ρ σ) (traceDistance σ ρ) :=
  Path.ofEq (traceDistance_comm ρ σ)

-- 18. Depolarizing channel then dephasing = depolarizing
theorem depol_dephase (ρ : DensityMatrix) :
    dephaseChannel (depolChannel ρ) = depolChannel ρ := by rfl

-- 19. Dephasing is idempotent
theorem dephase_idempotent (ρ : DensityMatrix) :
    dephaseChannel (dephaseChannel ρ) = dephaseChannel ρ := by rfl

def dephase_idempotent_path (ρ : DensityMatrix) :
    Path (dephaseChannel (dephaseChannel ρ)) (dephaseChannel ρ) :=
  Path.ofEq (dephase_idempotent ρ)

-- 20. Amplitude damping preserves total population
theorem ampDamp_trace (ρ : DensityMatrix) :
    trace (ampDampChannel ρ) = trace ρ := by
  simp [ampDampChannel, trace]

def ampDamp_trace_path (ρ : DensityMatrix) :
    Path (trace (ampDampChannel ρ)) (trace ρ) :=
  Path.ofEq (ampDamp_trace ρ)

-- 21. CongrArg through channel application
def channel_congrArg {ρ σ : DensityMatrix} (c : QChannel) (p : Path ρ σ) :
    Path (c ρ) (c σ) :=
  Path.congrArg c p

-- 22. CongrArg through trace
def trace_congrArg {ρ σ : DensityMatrix} (p : Path ρ σ) :
    Path (trace ρ) (trace σ) :=
  Path.congrArg trace p

-- 23. Transport along channel path
theorem transport_channel (ρ : DensityMatrix) :
    Path.transport (D := fun _ => Nat)
      (idChannel_path ρ) (trace ρ) = trace ρ := by
  simp [Path.transport]

-- 24. Pure state |0⟩ is indeed pure
theorem pureZero_isPure : isPure pureZero := by
  simp [isPure, pureZero]

-- 25. Max mixed is mixed (coherence < populations product)
theorem maxMixed_isMixed : isMixed maxMixed := by
  simp [isMixed, maxMixed]

-- 26. Fidelity of orthogonal pure states
theorem fidelity_orthogonal : fidelity pureZero pureOne = 0 := by rfl

def fidelity_orthogonal_path : Path (fidelity pureZero pureOne) 0 :=
  Path.ofEq fidelity_orthogonal

-- 27. Trace distance between orthogonal pure states
theorem traceDistance_orthogonal : traceDistance pureZero pureOne = 2 := by rfl

-- 28. Step construction for density matrix evolution
def evolution_step (ρ : DensityMatrix) (c : QChannel) (h : ρ = c ρ) :
    Step DensityMatrix := ⟨ρ, c ρ, h⟩

def id_evolution_step (ρ : DensityMatrix) : Step DensityMatrix :=
  ⟨idChannel ρ, ρ, idChannel_apply ρ⟩

-- 29. Dephasing increases entropy (or keeps it same)
theorem dephase_entropy (ρ : DensityMatrix) :
    entropy (dephaseChannel ρ) = ρ.p00 * ρ.p11 := by
  simp [entropy, dephaseChannel]

-- 30. Path coherence
theorem density_path_coherence {ρ σ : DensityMatrix} (p q : Path ρ σ) :
    p.proof = q.proof :=
  Subsingleton.elim _ _

end ComputationalPaths.Path.Computation.QuantumInfoPaths
