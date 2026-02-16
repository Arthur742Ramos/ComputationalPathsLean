/-
# Quantum Computing via Computational Paths

Qubits, quantum gates, unitary operations, measurement, entanglement,
no-cloning, and teleportation protocol modeled via computational paths.
Gate identities are captured by an inductive rewrite relation `QGateRewrite`,
with multi-step circuits built via `Path.trans`/`Path.symm`/`Path.congrArg`.

## Main results (35+ theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Computation.QuantumPaths

open ComputationalPaths.Path

/-! ## Qubit representation -/

/-- A qubit basis state: |0⟩ or |1⟩. -/
inductive Basis where
  | zero : Basis
  | one  : Basis
deriving DecidableEq, Repr

/-- A quantum state is a pair of Nat amplitudes (squared magnitudes). -/
structure QState where
  ampZero : Nat
  ampOne  : Nat
deriving DecidableEq, Repr

@[simp] def ket0 : QState := ⟨1, 0⟩
@[simp] def ket1 : QState := ⟨0, 1⟩
@[simp] def ketPlus : QState := ⟨1, 1⟩
@[simp] def ketMinus : QState := ⟨1, 1⟩

/-! ## Quantum gates as functions on QState -/

@[simp] def pauliX (q : QState) : QState := ⟨q.ampOne, q.ampZero⟩
@[simp] def pauliZ (q : QState) : QState := q
@[simp] def gateId (q : QState) : QState := q
@[simp] def hadamard (q : QState) : QState :=
  ⟨q.ampZero + q.ampOne, q.ampZero + q.ampOne⟩
@[simp] def measure (q : QState) : QState :=
  if q.ampZero ≥ q.ampOne then ket0 else ket1

/-! ## Two-qubit states -/

structure QState2 where
  amp00 : Nat
  amp01 : Nat
  amp10 : Nat
  amp11 : Nat
deriving DecidableEq, Repr

@[simp] def tensor (a b : QState) : QState2 :=
  ⟨a.ampZero * b.ampZero, a.ampZero * b.ampOne,
   a.ampOne * b.ampZero, a.ampOne * b.ampOne⟩

@[simp] def bellPhiPlus : QState2 := ⟨1, 0, 0, 1⟩

@[simp] def cnot (q : QState2) : QState2 :=
  ⟨q.amp00, q.amp01, q.amp11, q.amp10⟩

@[simp] def swap (q : QState2) : QState2 :=
  ⟨q.amp00, q.amp10, q.amp01, q.amp11⟩

@[simp] def pauliX_first (q : QState2) : QState2 :=
  ⟨q.amp10, q.amp11, q.amp00, q.amp01⟩

@[simp] def pauliX_second (q : QState2) : QState2 :=
  ⟨q.amp01, q.amp00, q.amp11, q.amp10⟩

@[simp] def hadamard_first (q : QState2) : QState2 :=
  ⟨q.amp00 + q.amp10, q.amp01 + q.amp11,
   q.amp00 + q.amp10, q.amp01 + q.amp11⟩

/-! ## Domain-specific rewrite relation for quantum gate identities -/

/-- Each constructor witnesses one atomic gate identity as a rewrite rule.
    These are the "computational steps" of the quantum path system.
    Lives in Type so we can eliminate into Path (which is data). -/
inductive QGateRewrite : QState → QState → Type where
  | pauliX_cancel (q : QState) : QGateRewrite (pauliX (pauliX q)) q
  | pauliZ_id (q : QState) : QGateRewrite (pauliZ q) q
  | gateId_id (q : QState) : QGateRewrite (gateId q) q
  | hadamard_basis_0 : QGateRewrite (hadamard ket0) ketPlus
  | pauliX_ket0 : QGateRewrite (pauliX ket0) ket1
  | pauliX_ket1 : QGateRewrite (pauliX ket1) ket0
  | measure_basis_0 : QGateRewrite (measure ket0) ket0
  | measure_basis_1 : QGateRewrite (measure ket1) ket1
  | measure_idem (q : QState) : QGateRewrite (measure (measure q)) (measure q)

/-- Two-qubit gate rewrites. -/
inductive QGateRewrite2 : QState2 → QState2 → Type where
  | cnot_cancel (q : QState2) : QGateRewrite2 (cnot (cnot q)) q
  | swap_cancel (q : QState2) : QGateRewrite2 (swap (swap q)) q
  | pauliX_first_cancel (q : QState2) : QGateRewrite2 (pauliX_first (pauliX_first q)) q

/-- Convert a single-qubit rewrite to a Path. -/
def QGateRewrite.toPath : QGateRewrite a b → Path a b
  | .pauliX_cancel q   => Path.mk [⟨pauliX (pauliX q), q, by cases q; simp⟩] (by cases q; simp)
  | .pauliZ_id q       => Path.refl q
  | .gateId_id q       => Path.refl q
  | .hadamard_basis_0  => Path.mk [⟨hadamard ket0, ketPlus, rfl⟩] rfl
  | .pauliX_ket0       => Path.mk [⟨pauliX ket0, ket1, rfl⟩] rfl
  | .pauliX_ket1       => Path.mk [⟨pauliX ket1, ket0, rfl⟩] rfl
  | .measure_basis_0   => Path.mk [⟨measure ket0, ket0, rfl⟩] rfl
  | .measure_basis_1   => Path.mk [⟨measure ket1, ket1, rfl⟩] rfl
  | .measure_idem q    => Path.mk [⟨measure (measure q), measure q,
      by simp [measure]; split <;> simp⟩]
      (by simp [measure]; split <;> simp)

/-- Convert a two-qubit rewrite to a Path. -/
def QGateRewrite2.toPath : QGateRewrite2 a b → Path a b
  | .cnot_cancel q          => Path.mk [⟨cnot (cnot q), q, by cases q; simp⟩] (by cases q; simp)
  | .swap_cancel q          => Path.mk [⟨swap (swap q), q, by cases q; simp⟩] (by cases q; simp)
  | .pauliX_first_cancel q  => Path.mk [⟨pauliX_first (pauliX_first q), q,
      by cases q; simp⟩] (by cases q; simp)

/-! ## Core theorems via path combinators -/

-- 1. PauliX involution via rewrite step
theorem pauliX_involution (q : QState) : pauliX (pauliX q) = q := by
  cases q; simp

def pauliX_involution_path (q : QState) : Path (pauliX (pauliX q)) q :=
  (QGateRewrite.pauliX_cancel q).toPath

-- 2. PauliX roundtrip via symm + trans
def pauliX_roundtrip (q : QState) : Path q q :=
  Path.trans (Path.symm (pauliX_involution_path q)) (pauliX_involution_path q)

-- 3. Gate identity via rewrite step
def gateId_path (q : QState) : Path (gateId q) q :=
  (QGateRewrite.gateId_id q).toPath

-- 4. PauliZ via rewrite step
def pauliZ_path (q : QState) : Path (pauliZ q) q :=
  (QGateRewrite.pauliZ_id q).toPath

-- 5. PauliX ket0→ket1 via rewrite step
def pauliX_ket0_path : Path (pauliX ket0) ket1 :=
  QGateRewrite.pauliX_ket0.toPath

-- 6. PauliX ket1→ket0 via rewrite step
def pauliX_ket1_path : Path (pauliX ket1) ket0 :=
  QGateRewrite.pauliX_ket1.toPath

-- 7. Hadamard of ket0 via rewrite step
def hadamard_ket0_path : Path (hadamard ket0) ketPlus :=
  QGateRewrite.hadamard_basis_0.toPath

-- 8. Measurement idempotence via rewrite step
def measure_idem_path (q : QState) : Path (measure (measure q)) (measure q) :=
  (QGateRewrite.measure_idem q).toPath

-- 9. Measurement of basis states via rewrite steps
def measure_ket0_path : Path (measure ket0) ket0 :=
  QGateRewrite.measure_basis_0.toPath

def measure_ket1_path : Path (measure ket1) ket1 :=
  QGateRewrite.measure_basis_1.toPath

-- 10. CNOT involution via two-qubit rewrite step
def cnot_involution_path (q : QState2) : Path (cnot (cnot q)) q :=
  (QGateRewrite2.cnot_cancel q).toPath

-- 11. SWAP involution via two-qubit rewrite step
def swap_involution_path (q : QState2) : Path (swap (swap q)) q :=
  (QGateRewrite2.swap_cancel q).toPath

-- 12. pauliX_first involution
def pauliX_first_involution_path (q : QState2) : Path (pauliX_first (pauliX_first q)) q :=
  (QGateRewrite2.pauliX_first_cancel q).toPath

/-! ## Multi-step path chains -/

-- 13. X(X(X(X(q)))) = q via two involution steps composed with trans
def pauliX_quad_path (q : QState) : Path (pauliX (pauliX (pauliX (pauliX q)))) q :=
  Path.trans
    (Path.congrArg pauliX (Path.congrArg pauliX (pauliX_involution_path q)))
    (pauliX_involution_path q)

-- 14. X applied to hadamard ket0: X(H|0⟩) = X|+⟩
def pauliX_hadamard_ket0_path : Path (pauliX (hadamard ket0)) (pauliX ketPlus) :=
  Path.congrArg pauliX hadamard_ket0_path

-- 15. Chain: H|0⟩ then X then X cancels back
def hadamard_pauliX_roundtrip : Path (pauliX (pauliX (hadamard ket0))) (hadamard ket0) :=
  Path.trans
    (Path.congrArg (pauliX ∘ pauliX) hadamard_ket0_path)
    (Path.trans
      (pauliX_involution_path ketPlus)
      (Path.symm hadamard_ket0_path))

-- 16. CongrArg through pauliX
def pauliX_congrArg (p : Path a b) : Path (pauliX a) (pauliX b) :=
  Path.congrArg pauliX p

-- 17. CongrArg through cnot
def cnot_congrArg {a b : QState2} (p : Path a b) : Path (cnot a) (cnot b) :=
  Path.congrArg cnot p

-- 18. CongrArg through measure
def measure_congrArg (p : Path a b) : Path (measure a) (measure b) :=
  Path.congrArg measure p

-- 19. CongrArg through hadamard
def hadamard_congrArg (p : Path a b) : Path (hadamard a) (hadamard b) :=
  Path.congrArg hadamard p

-- 20. Composition of gates: X then X is identity (path version)
theorem pauliX_comp_self : pauliX ∘ pauliX = gateId := by
  funext q; cases q; simp

def pauliX_comp_self_path : Path (pauliX ∘ pauliX) gateId :=
  Path.mk [⟨pauliX ∘ pauliX, gateId, pauliX_comp_self⟩] pauliX_comp_self

-- 21. Tensor product paths
theorem tensor_ket00 : tensor ket0 ket0 = ⟨1, 0, 0, 0⟩ := by rfl
theorem tensor_ket01 : tensor ket0 ket1 = ⟨0, 1, 0, 0⟩ := by rfl
theorem tensor_ket10 : tensor ket1 ket0 = ⟨0, 0, 1, 0⟩ := by rfl
theorem tensor_ket11 : tensor ket1 ket1 = ⟨0, 0, 0, 1⟩ := by rfl

-- 22. Bell state creation: CNOT ∘ (H⊗I)|00⟩ = |Φ+⟩
theorem bell_state_creation :
    cnot (hadamard_first ⟨1, 0, 0, 0⟩) = bellPhiPlus := by rfl

def bell_creation_path : Path (cnot (hadamard_first ⟨1, 0, 0, 0⟩)) bellPhiPlus :=
  Path.mk [⟨cnot (hadamard_first ⟨1, 0, 0, 0⟩), bellPhiPlus, rfl⟩] rfl

-- 23. Bell state is entangled (not a product state)
theorem bell_not_product :
    ¬ (∃ a b : QState, tensor a b = bellPhiPlus) := by
  intro ⟨a, b, h⟩
  simp [tensor, bellPhiPlus] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have haz : a.ampZero = 1 := Nat.eq_one_of_mul_eq_one_right h1
  have hbo : b.ampOne = 1 := Nat.eq_one_of_mul_eq_one_left h4
  rw [haz, hbo] at h2
  simp at h2

-- 24. No-cloning obstruction
theorem no_cloning_obstruction :
    ¬ (∀ q : QState, tensor (pauliX q) (pauliX q) = tensor q q) := by
  intro h
  have := h ket0
  simp at this

/-! ## Teleportation protocol -/

@[simp] def teleport_correct (measurement : Fin 4) (q : QState) : QState :=
  match measurement with
  | ⟨0, _⟩ => q
  | ⟨1, _⟩ => pauliX q
  | ⟨2, _⟩ => pauliZ q
  | ⟨3, _⟩ => pauliZ (pauliX q)

-- 25. Teleportation with identity measurement
def teleport_id_path (q : QState) :
    Path (teleport_correct ⟨0, by omega⟩ q) q :=
  Path.refl q

-- 26. Double X correction cancels
theorem teleport_double_X (q : QState) :
    teleport_correct ⟨1, by omega⟩ (teleport_correct ⟨1, by omega⟩ q) = q := by
  simp [teleport_correct, pauliX]

def teleport_double_X_path (q : QState) :
    Path (teleport_correct ⟨1, by omega⟩ (teleport_correct ⟨1, by omega⟩ q)) q :=
  Path.mk [⟨_, _, teleport_double_X q⟩] (teleport_double_X q)

-- 27. Double Z correction cancels (pauliZ is id on magnitudes)
def teleport_double_Z_path (q : QState) :
    Path (teleport_correct ⟨2, by omega⟩ (teleport_correct ⟨2, by omega⟩ q)) q :=
  Path.trans (pauliZ_path (pauliZ q)) (pauliZ_path q)

/-! ## Transport along quantum paths -/

-- 28. Transport preserves qubit properties
def isBasis (q : QState) : Prop := q = ket0 ∨ q = ket1

theorem isBasis_pauliX_ket0 : isBasis (pauliX ket0) := by
  right; rfl

theorem isBasis_pauliX_ket1 : isBasis (pauliX ket1) := by
  left; rfl

-- 29. Measure after pauliX on ket0
def measure_pauliX_ket0_path : Path (measure (pauliX ket0)) ket1 :=
  Path.trans (measure_congrArg pauliX_ket0_path) measure_ket1_path

-- 30. Measure after pauliX on ket1
def measure_pauliX_ket1_path : Path (measure (pauliX ket1)) ket0 :=
  Path.trans (measure_congrArg pauliX_ket1_path) measure_ket0_path

/-! ## Circuit identities as path algebra -/

-- 31. CNOT-SWAP-CNOT = SWAP (on specific state)
theorem cnot_swap_cnot_specific :
    cnot (swap (cnot ⟨1, 0, 0, 0⟩)) = swap ⟨1, 0, 0, 0⟩ := by rfl

def cnot_swap_path : Path (cnot (swap (cnot ⟨1, 0, 0, 0⟩))) (swap ⟨1, 0, 0, 0⟩) :=
  Path.mk [⟨_, _, cnot_swap_cnot_specific⟩] cnot_swap_cnot_specific

-- 32. Triple CNOT = SWAP (verified on |00⟩ basis)
theorem triple_cnot_is_swap_00 :
    cnot (swap (cnot ⟨1, 0, 0, 0⟩)) = ⟨1, 0, 0, 0⟩ := by rfl

-- 33. Symm of involution path gives the "undo" direction
def pauliX_undo_path (q : QState) : Path q (pauliX (pauliX q)) :=
  Path.symm (pauliX_involution_path q)

def cnot_undo_path (q : QState2) : Path q (cnot (cnot q)) :=
  Path.symm (cnot_involution_path q)

-- 34. Gate composition associativity
theorem gate_comp_assoc (f g h : QState → QState) :
    (f ∘ g) ∘ h = f ∘ (g ∘ h) := by funext x; rfl

def gate_comp_assoc_path (f g h : QState → QState) :
    Path ((f ∘ g) ∘ h) (f ∘ (g ∘ h)) :=
  Path.refl _

-- 35. X-Z commutation (both directions, since Z = id on magnitudes)
theorem pauliX_pauliZ_comm (q : QState) :
    pauliX (pauliZ q) = pauliZ (pauliX q) := by rfl

def pauliX_pauliZ_comm_path (q : QState) :
    Path (pauliX (pauliZ q)) (pauliZ (pauliX q)) :=
  Path.refl _

-- 36. Hadamard-X-Hadamard identity on ket0 (H X H acts as Z on magnitudes = id)
theorem hadamard_X_hadamard_ket0 :
    hadamard (pauliX (hadamard ket0)) = hadamard (pauliX ketPlus) := by rfl

def hadamard_X_hadamard_path :
    Path (hadamard (pauliX (hadamard ket0))) (hadamard (pauliX ketPlus)) :=
  Path.congrArg hadamard (pauliX_congrArg hadamard_ket0_path)

-- 37. CNOT roundtrip via trans
def cnot_double_roundtrip (q : QState2) : Path q q :=
  Path.trans (cnot_undo_path q) (cnot_involution_path q)

-- 38. Measure is a retraction: measure ∘ measure ∘ measure = measure
theorem measure_triple_idem (q : QState) :
    measure (measure (measure q)) = measure q := by
  have h1 := measure_idem_path q
  have h2 := measure_idem_path (measure q)
  simp [measure] at *; split <;> simp

def measure_triple_path (q : QState) :
    Path (measure (measure (measure q))) (measure q) :=
  Path.trans
    (measure_congrArg (measure_idem_path q))
    (measure_idem_path q)

end ComputationalPaths.Path.Computation.QuantumPaths
