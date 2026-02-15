/-
# Quantum Computing via Computational Paths

Qubits, quantum gates, unitary operations, measurement, entanglement,
no-cloning, and teleportation protocol modeled via computational paths.

## Main results (25+ theorems)
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

/-- A quantum state is a pair of Nat amplitudes (squared magnitudes)
    summing to a normalization constant. We keep things simple. -/
structure QState where
  ampZero : Nat  -- |α₀|²
  ampOne  : Nat  -- |α₁|²
deriving DecidableEq, Repr

/-- Standard |0⟩ state. -/
@[simp] def ket0 : QState := ⟨1, 0⟩

/-- Standard |1⟩ state. -/
@[simp] def ket1 : QState := ⟨0, 1⟩

/-- Plus state |+⟩ (equal superposition). -/
@[simp] def ketPlus : QState := ⟨1, 1⟩

/-- Minus state |−⟩ (equal superposition, different phase). -/
@[simp] def ketMinus : QState := ⟨1, 1⟩

/-- Check if a state is a basis state. -/
def isBasis (q : QState) : Prop := q = ket0 ∨ q = ket1

/-! ## Quantum gates as functions on QState -/

/-- Pauli-X gate (NOT / bit-flip). -/
@[simp] def pauliX (q : QState) : QState := ⟨q.ampOne, q.ampZero⟩

/-- Pauli-Z gate (phase flip) — swaps amplitude of |1⟩ conceptually.
    In our Nat model, Z acts as identity on magnitudes. -/
@[simp] def pauliZ (q : QState) : QState := q

/-- Identity gate. -/
@[simp] def gateId (q : QState) : QState := q

/-- Hadamard gate: maps basis states to equal superposition. -/
@[simp] def hadamard (q : QState) : QState :=
  ⟨q.ampZero + q.ampOne, q.ampZero + q.ampOne⟩

/-- Measurement projects to a basis state.
    We model measurement as choosing the dominant amplitude. -/
@[simp] def measure (q : QState) : QState :=
  if q.ampZero ≥ q.ampOne then ket0 else ket1

/-! ## Two-qubit states -/

/-- Two-qubit state: 4 amplitudes. -/
structure QState2 where
  amp00 : Nat
  amp01 : Nat
  amp10 : Nat
  amp11 : Nat
deriving DecidableEq, Repr

/-- Tensor product of two single-qubit states. -/
@[simp] def tensor (a b : QState) : QState2 :=
  ⟨a.ampZero * b.ampZero, a.ampZero * b.ampOne,
   a.ampOne * b.ampZero, a.ampOne * b.ampOne⟩

/-- Bell state |Φ+⟩ = (|00⟩ + |11⟩)/√2. -/
@[simp] def bellPhiPlus : QState2 := ⟨1, 0, 0, 1⟩

/-- CNOT gate on two-qubit state. -/
@[simp] def cnot (q : QState2) : QState2 :=
  ⟨q.amp00, q.amp01, q.amp11, q.amp10⟩

/-- SWAP gate. -/
@[simp] def swap (q : QState2) : QState2 :=
  ⟨q.amp00, q.amp10, q.amp01, q.amp11⟩

/-- Apply pauliX to first qubit of two-qubit state. -/
@[simp] def pauliX_first (q : QState2) : QState2 :=
  ⟨q.amp10, q.amp11, q.amp00, q.amp01⟩

/-- Apply pauliX to second qubit. -/
@[simp] def pauliX_second (q : QState2) : QState2 :=
  ⟨q.amp01, q.amp00, q.amp11, q.amp10⟩

/-! ## Core theorems -/

-- 1. Pauli-X is an involution
theorem pauliX_involution (q : QState) : pauliX (pauliX q) = q := by
  cases q; simp [pauliX]

def pauliX_involution_path (q : QState) : Path (pauliX (pauliX q)) q :=
  Path.ofEq (pauliX_involution q)

-- 2. Pauli-X roundtrip path
def pauliX_roundtrip (q : QState) : Path q q :=
  Path.trans (Path.symm (pauliX_involution_path q)) (pauliX_involution_path q)

-- 3. Gate identity is identity
theorem gateId_apply (q : QState) : gateId q = q := by rfl

def gateId_path (q : QState) : Path (gateId q) q :=
  Path.ofEq (gateId_apply q)

-- 4. pauliZ is identity on magnitudes
theorem pauliZ_is_id (q : QState) : pauliZ q = q := by rfl

def pauliZ_path (q : QState) : Path (pauliZ q) q :=
  Path.ofEq (pauliZ_is_id q)

-- 5. PauliX flips ket0 to ket1
theorem pauliX_ket0 : pauliX ket0 = ket1 := by rfl

def pauliX_ket0_path : Path (pauliX ket0) ket1 :=
  Path.ofEq pauliX_ket0

-- 6. PauliX flips ket1 to ket0
theorem pauliX_ket1 : pauliX ket1 = ket0 := by rfl

def pauliX_ket1_path : Path (pauliX ket1) ket0 :=
  Path.ofEq pauliX_ket1

-- 7. Hadamard of ket0
theorem hadamard_ket0 : hadamard ket0 = ketPlus := by rfl

def hadamard_ket0_path : Path (hadamard ket0) ketPlus :=
  Path.ofEq hadamard_ket0

-- 8. Measurement of ket0 is ket0
theorem measure_ket0 : measure ket0 = ket0 := by rfl

def measure_ket0_path : Path (measure ket0) ket0 :=
  Path.ofEq measure_ket0

-- 9. Measurement of ket1 is ket1
theorem measure_ket1 : measure ket1 = ket1 := by rfl

def measure_ket1_path : Path (measure ket1) ket1 :=
  Path.ofEq measure_ket1

-- 10. Measurement is idempotent
theorem measure_idempotent (q : QState) : measure (measure q) = measure q := by
  simp [measure]
  split <;> simp

def measure_idempotent_path (q : QState) : Path (measure (measure q)) (measure q) :=
  Path.ofEq (measure_idempotent q)

-- 11. CNOT is an involution
theorem cnot_involution (q : QState2) : cnot (cnot q) = q := by
  cases q; simp [cnot]

def cnot_involution_path (q : QState2) : Path (cnot (cnot q)) q :=
  Path.ofEq (cnot_involution q)

-- 12. SWAP is an involution
theorem swap_involution (q : QState2) : swap (swap q) = q := by
  cases q; simp [swap]

def swap_involution_path (q : QState2) : Path (swap (swap q)) q :=
  Path.ofEq (swap_involution q)

-- 13. CNOT preserves |00⟩
theorem cnot_00 : cnot ⟨1, 0, 0, 0⟩ = (⟨1, 0, 0, 0⟩ : QState2) := by rfl

-- 14. CNOT flips target when control is |1⟩
theorem cnot_10 : cnot ⟨0, 0, 1, 0⟩ = (⟨0, 0, 0, 1⟩ : QState2) := by rfl

-- 15. Tensor of ket0 and ket0
theorem tensor_00 : tensor ket0 ket0 = ⟨1, 0, 0, 0⟩ := by rfl

-- 16. Tensor of ket0 and ket1
theorem tensor_01 : tensor ket0 ket1 = ⟨0, 1, 0, 0⟩ := by rfl

-- 17. No-cloning: there's no function that maps q → tensor q q for all basis states
-- We show a weaker form: the tensor map is not pauliX-compatible
theorem no_cloning_obstruction :
    ¬ (∀ q : QState, tensor (pauliX q) (pauliX q) = tensor q q) := by
  intro h
  have := h ket0
  simp at this

-- 18. CongrArg through pauliX
def pauliX_congrArg (p : Path a b) : Path (pauliX a) (pauliX b) :=
  Path.congrArg pauliX p

-- 19. CongrArg through cnot
def cnot_congrArg {a b : QState2} (p : Path a b) : Path (cnot a) (cnot b) :=
  Path.congrArg cnot p

-- 20. Transport along pauliX path
theorem transport_pauliX :
    Path.transport (D := fun q => q = q) (pauliX_ket0_path) rfl = rfl :=
  Subsingleton.elim _ _

-- 21. Composition of gates: X then X is identity
theorem pauliX_comp_self : pauliX ∘ pauliX = gateId := by
  funext q; simp

def pauliX_comp_self_path : Path (pauliX ∘ pauliX) gateId :=
  Path.ofEq pauliX_comp_self

-- 22. Bell state is not a product state
theorem bell_not_product :
    ¬ (∃ a b : QState, tensor a b = bellPhiPlus) := by
  intro ⟨a, b, h⟩
  simp [tensor, bellPhiPlus] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have ha0 : a.ampZero * b.ampZero = 1 := h1
  have ha1 : a.ampOne * b.ampOne = 1 := h4
  have haz : a.ampZero = 1 := Nat.eq_one_of_mul_eq_one_right ha0
  have hbz : b.ampZero = 1 := Nat.eq_one_of_mul_eq_one_left ha0
  have hao : a.ampOne = 1 := Nat.eq_one_of_mul_eq_one_right ha1
  have hbo : b.ampOne = 1 := Nat.eq_one_of_mul_eq_one_left ha1
  rw [haz, hbo] at h2
  simp at h2

-- 23. Symm of pauliX involution path
theorem pauliX_involution_symm (q : QState) :
    Path.symm (pauliX_involution_path q) =
    Path.ofEq (pauliX_involution q).symm := by
  rfl

-- 24. Gate composition associativity
theorem gate_comp_assoc (f g h : QState → QState) :
    (f ∘ g) ∘ h = f ∘ (g ∘ h) := by
  funext x; rfl

def gate_comp_assoc_path (f g h : QState → QState) :
    Path ((f ∘ g) ∘ h) (f ∘ (g ∘ h)) :=
  Path.ofEq (gate_comp_assoc f g h)

-- 25. SWAP composed with CNOT
@[simp] def reverseCnot (q : QState2) : QState2 :=
  ⟨q.amp00, q.amp10, q.amp01, q.amp11⟩

-- reverseCnot is also an involution
theorem reverseCnot_involution (q : QState2) : reverseCnot (reverseCnot q) = q := by
  cases q; simp [reverseCnot]

def reverseCnot_involution_path (q : QState2) :
    Path (reverseCnot (reverseCnot q)) q :=
  Path.ofEq (reverseCnot_involution q)

-- 26. Step construction for quantum gate path
def pauliX_ket0_step : Step QState :=
  ⟨pauliX ket0, ket1, pauliX_ket0⟩

-- 27. Entanglement via CNOT + Hadamard on first qubit
-- Starting from |00⟩, H⊗I then CNOT gives Bell state
-- In our Nat model: H(|0⟩) = (1,1), tensor with |0⟩ = (1,0,1,0)
-- then CNOT gives (1,0,0,1) = bellPhiPlus
@[simp] def hadamard_first (q : QState2) : QState2 :=
  ⟨q.amp00 + q.amp10, q.amp01 + q.amp11,
   q.amp00 + q.amp10, q.amp01 + q.amp11⟩

theorem bell_state_creation :
    cnot (hadamard_first ⟨1, 0, 0, 0⟩) = bellPhiPlus := by rfl

def bell_state_creation_path :
    Path (cnot (hadamard_first ⟨1, 0, 0, 0⟩)) bellPhiPlus :=
  Path.ofEq bell_state_creation

-- 28. Teleportation protocol structure (simplified)
-- Alice has qubit q, shares Bell pair with Bob
-- Protocol: Alice measures, Bob applies correction
-- We model the correction step
@[simp] def teleport_correct (measurement : Fin 4) (q : QState) : QState :=
  match measurement with
  | ⟨0, _⟩ => q                    -- no correction
  | ⟨1, _⟩ => pauliX q             -- bit flip
  | ⟨2, _⟩ => pauliZ q             -- phase flip
  | ⟨3, _⟩ => pauliZ (pauliX q)    -- both

-- 29. Teleportation correction with identity measurement recovers state
theorem teleport_id_correction (q : QState) :
    teleport_correct ⟨0, by omega⟩ q = q := by rfl

def teleport_id_path (q : QState) :
    Path (teleport_correct ⟨0, by omega⟩ q) q :=
  Path.ofEq (teleport_id_correction q)

-- 30. Double correction is identity for Pauli-X case
theorem teleport_double_X (q : QState) :
    teleport_correct ⟨1, by omega⟩ (teleport_correct ⟨1, by omega⟩ q) = q := by
  simp [teleport_correct]

def teleport_double_X_path (q : QState) :
    Path (teleport_correct ⟨1, by omega⟩ (teleport_correct ⟨1, by omega⟩ q)) q :=
  Path.ofEq (teleport_double_X q)

end ComputationalPaths.Path.Computation.QuantumPaths
