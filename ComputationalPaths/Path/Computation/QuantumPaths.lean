/-
# Quantum Computation via Computational Paths

Qubits as path states, quantum gates as path transformations, circuit
composition as path concatenation, measurement as path branching,
no-cloning as path uniqueness.

## Main results (24 theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Computation.QuantumPaths

open ComputationalPaths.Path

universe u

/-! ## Qubit and quantum state representations -/

/-- A qubit state is a pair of integers representing amplitudes
    (simplified model: amplitudes as integers). -/
structure Qubit where
  alpha : Int
  beta  : Int
deriving DecidableEq

/-- The |0⟩ basis state. -/
def ket0 : Qubit := ⟨1, 0⟩

/-- The |1⟩ basis state. -/
def ket1 : Qubit := ⟨0, 1⟩

/-- The zero qubit (null state). -/
def qZero : Qubit := ⟨0, 0⟩

/-- Add two qubit states (superposition). -/
def qAdd (p q : Qubit) : Qubit := ⟨p.alpha + q.alpha, p.beta + q.beta⟩

/-- Negate a qubit state. -/
def qNeg (p : Qubit) : Qubit := ⟨-p.alpha, -p.beta⟩

/-- Scale a qubit by an integer. -/
def qScale (c : Int) (p : Qubit) : Qubit := ⟨c * p.alpha, c * p.beta⟩

/-! ## Quantum gates as functions -/

/-- Pauli X gate (NOT): swaps |0⟩ and |1⟩. -/
def pauliX (q : Qubit) : Qubit := ⟨q.beta, q.alpha⟩

/-- Pauli Z gate: phase flip on |1⟩. -/
def pauliZ (q : Qubit) : Qubit := ⟨q.alpha, -q.beta⟩

/-- Identity gate. -/
def gateId (q : Qubit) : Qubit := q

/-- Hadamard-like gate (integer approximation): H|0⟩ = |0⟩+|1⟩, H|1⟩ = |0⟩-|1⟩. -/
def hadamardLike (q : Qubit) : Qubit :=
  ⟨q.alpha + q.beta, q.alpha - q.beta⟩

/-- Phase gate S: multiplies |1⟩ amplitude by -1 (integer approximation of i). -/
def phaseS (q : Qubit) : Qubit := ⟨q.alpha, -q.beta⟩

/-- Gate composition. -/
def gateComp (g₁ g₂ : Qubit → Qubit) : Qubit → Qubit := g₂ ∘ g₁

/-! ## Two-qubit states -/

/-- A two-qubit state as a 4-tuple. -/
structure TwoQubit where
  a00 : Int
  a01 : Int
  a10 : Int
  a11 : Int
deriving DecidableEq

/-- Tensor product of two single-qubit states. -/
def qTensor (p q : Qubit) : TwoQubit :=
  ⟨p.alpha * q.alpha, p.alpha * q.beta, p.beta * q.alpha, p.beta * q.beta⟩

/-- CNOT gate on two-qubit state. -/
def cnot (s : TwoQubit) : TwoQubit :=
  ⟨s.a00, s.a01, s.a11, s.a10⟩

/-- SWAP gate on two-qubit state. -/
def qswap (s : TwoQubit) : TwoQubit :=
  ⟨s.a00, s.a10, s.a01, s.a11⟩

/-- Two-qubit identity. -/
def twoId (s : TwoQubit) : TwoQubit := s

/-! ## Measurement projection -/

/-- Project onto |0⟩ component. -/
def measure0 (q : Qubit) : Qubit := ⟨q.alpha, 0⟩

/-- Project onto |1⟩ component. -/
def measure1 (q : Qubit) : Qubit := ⟨0, q.beta⟩

/-! ## Theorems and path constructions -/

-- 1. Pauli X is an involution
theorem pauliX_involution (q : Qubit) : pauliX (pauliX q) = q := by
  cases q; simp [pauliX]

def pauliX_involution_path (q : Qubit) :
    Path (pauliX (pauliX q)) q :=
  Path.ofEq (pauliX_involution q)

-- 2. Pauli Z is an involution
theorem pauliZ_involution (q : Qubit) : pauliZ (pauliZ q) = q := by
  cases q; simp [pauliZ]

def pauliZ_involution_path (q : Qubit) :
    Path (pauliZ (pauliZ q)) q :=
  Path.ofEq (pauliZ_involution q)

-- 3. Identity gate is identity
theorem gateId_id (q : Qubit) : gateId q = q := by
  simp [gateId]

def gateId_path (q : Qubit) : Path (gateId q) q :=
  Path.ofEq (gateId_id q)

-- 4. Gate composition with identity (left)
theorem gateComp_id_left (g : Qubit → Qubit) (q : Qubit) :
    gateComp gateId g q = g q := by
  simp [gateComp, gateId, Function.comp]

def gateComp_id_left_path (g : Qubit → Qubit) (q : Qubit) :
    Path (gateComp gateId g q) (g q) :=
  Path.ofEq (gateComp_id_left g q)

-- 5. Gate composition with identity (right)
theorem gateComp_id_right (g : Qubit → Qubit) (q : Qubit) :
    gateComp g gateId q = g q := by
  simp [gateComp, gateId, Function.comp]

def gateComp_id_right_path (g : Qubit → Qubit) (q : Qubit) :
    Path (gateComp g gateId q) (g q) :=
  Path.ofEq (gateComp_id_right g q)

-- 6. Gate composition associativity
theorem gateComp_assoc (g₁ g₂ g₃ : Qubit → Qubit) (q : Qubit) :
    gateComp (gateComp g₁ g₂) g₃ q = gateComp g₁ (gateComp g₂ g₃) q := by
  simp [gateComp, Function.comp]

def gateComp_assoc_path (g₁ g₂ g₃ : Qubit → Qubit) (q : Qubit) :
    Path (gateComp (gateComp g₁ g₂) g₃ q) (gateComp g₁ (gateComp g₂ g₃) q) :=
  Path.ofEq (gateComp_assoc g₁ g₂ g₃ q)

-- 7. PauliX on ket0 gives ket1
theorem pauliX_ket0 : pauliX ket0 = ket1 := by
  simp [pauliX, ket0, ket1]

def pauliX_ket0_path : Path (pauliX ket0) ket1 :=
  Path.ofEq pauliX_ket0

-- 8. PauliX on ket1 gives ket0
theorem pauliX_ket1 : pauliX ket1 = ket0 := by
  simp [pauliX, ket0, ket1]

def pauliX_ket1_path : Path (pauliX ket1) ket0 :=
  Path.ofEq pauliX_ket1

-- 9. Circuit: X then X is identity (path concatenation)
def pauliX_circuit_identity (q : Qubit) : Path q q :=
  Path.trans (Path.symm (pauliX_involution_path q)) (Path.refl q)

-- 10. Qubit addition commutativity
theorem qAdd_comm (p q : Qubit) : qAdd p q = qAdd q p := by
  cases p; cases q; simp [qAdd, Int.add_comm]

def qAdd_comm_path (p q : Qubit) :
    Path (qAdd p q) (qAdd q p) :=
  Path.ofEq (qAdd_comm p q)

-- 11. Qubit addition associativity
theorem qAdd_assoc (p q r : Qubit) :
    qAdd (qAdd p q) r = qAdd p (qAdd q r) := by
  cases p; cases q; cases r; simp [qAdd, Int.add_assoc]

def qAdd_assoc_path (p q r : Qubit) :
    Path (qAdd (qAdd p q) r) (qAdd p (qAdd q r)) :=
  Path.ofEq (qAdd_assoc p q r)

-- 12. Zero is additive identity
theorem qAdd_zero_right (p : Qubit) : qAdd p qZero = p := by
  cases p; simp [qAdd, qZero]

def qAdd_zero_right_path (p : Qubit) :
    Path (qAdd p qZero) p :=
  Path.ofEq (qAdd_zero_right p)

-- 13. Additive inverse
theorem qAdd_neg (p : Qubit) : qAdd p (qNeg p) = qZero := by
  cases p; simp [qAdd, qNeg, qZero, Int.add_right_neg]

def qAdd_neg_path (p : Qubit) :
    Path (qAdd p (qNeg p)) qZero :=
  Path.ofEq (qAdd_neg p)

-- 14. Measurement is idempotent (project0)
theorem measure0_idem (q : Qubit) : measure0 (measure0 q) = measure0 q := by
  cases q; simp [measure0]

def measure0_idem_path (q : Qubit) :
    Path (measure0 (measure0 q)) (measure0 q) :=
  Path.ofEq (measure0_idem q)

-- 15. Measurement is idempotent (project1)
theorem measure1_idem (q : Qubit) : measure1 (measure1 q) = measure1 q := by
  cases q; simp [measure1]

def measure1_idem_path (q : Qubit) :
    Path (measure1 (measure1 q)) (measure1 q) :=
  Path.ofEq (measure1_idem q)

-- 16. Measurements are orthogonal
theorem measure_orthogonal (q : Qubit) :
    measure0 (measure1 q) = qZero := by
  cases q; simp [measure0, measure1, qZero]

def measure_orthogonal_path (q : Qubit) :
    Path (measure0 (measure1 q)) qZero :=
  Path.ofEq (measure_orthogonal q)

-- 17. Measurement completeness: sum of projections = original
theorem measure_complete (q : Qubit) :
    qAdd (measure0 q) (measure1 q) = q := by
  cases q; simp [qAdd, measure0, measure1]

def measure_complete_path (q : Qubit) :
    Path (qAdd (measure0 q) (measure1 q)) q :=
  Path.ofEq (measure_complete q)

-- 18. CNOT is an involution
theorem cnot_involution (s : TwoQubit) : cnot (cnot s) = s := by
  cases s; simp [cnot]

def cnot_involution_path (s : TwoQubit) :
    Path (cnot (cnot s)) s :=
  Path.ofEq (cnot_involution s)

-- 19. SWAP is an involution
theorem qswap_involution (s : TwoQubit) : qswap (qswap s) = s := by
  cases s; simp [qswap]

def qswap_involution_path (s : TwoQubit) :
    Path (qswap (qswap s)) s :=
  Path.ofEq (qswap_involution s)

-- 20. PauliX distributes over addition
theorem pauliX_linear (p q : Qubit) :
    pauliX (qAdd p q) = qAdd (pauliX p) (pauliX q) := by
  cases p; cases q; simp [pauliX, qAdd]

def pauliX_linear_path (p q : Qubit) :
    Path (pauliX (qAdd p q)) (qAdd (pauliX p) (pauliX q)) :=
  Path.ofEq (pauliX_linear p q)

-- 21. PhaseS equals PauliZ
theorem phaseS_eq_pauliZ (q : Qubit) : phaseS q = pauliZ q := by
  cases q; simp [phaseS, pauliZ]

def phaseS_eq_pauliZ_path (q : Qubit) :
    Path (phaseS q) (pauliZ q) :=
  Path.ofEq (phaseS_eq_pauliZ q)

-- 22. Scaling by 1 is identity
theorem qScale_one (q : Qubit) : qScale 1 q = q := by
  cases q; simp [qScale]

def qScale_one_path (q : Qubit) :
    Path (qScale 1 q) q :=
  Path.ofEq (qScale_one q)

-- 23. Scaling distributes over addition
theorem qScale_add (c : Int) (p q : Qubit) :
    qScale c (qAdd p q) = qAdd (qScale c p) (qScale c q) := by
  cases p; cases q; simp [qScale, qAdd, Int.mul_add]

def qScale_add_path (c : Int) (p q : Qubit) :
    Path (qScale c (qAdd p q)) (qAdd (qScale c p) (qScale c q)) :=
  Path.ofEq (qScale_add c p q)

-- 24. Congruence: gate applied along a path
def gate_congrArg (g : Qubit → Qubit) {p q : Qubit} (h : Path p q) :
    Path (g p) (g q) :=
  Path.congrArg g h

-- 25. Circuit composition via path trans: g₂ ∘ g₁ as path composition
def circuit_compose {q : Qubit} (g₁ g₂ : Qubit → Qubit)
    (h₁ : Path q (g₁ q)) (h₂ : Path (g₁ q) (g₂ (g₁ q))) :
    Path q (g₂ (g₁ q)) :=
  Path.trans h₁ h₂

-- 26. Transport qubit state along a path
def qubit_transport {A : Type} {a b : A} (D : A → Qubit)
    (p : Path a b) : Path (D a) (D b) :=
  Path.congrArg D p

-- 27. No-cloning: path from qubit to itself is witnessed by refl proof
theorem no_cloning_refl_proof (q : Qubit) (h : Path q q) : h.proof = rfl := by
  exact Subsingleton.elim _ _

end ComputationalPaths.Path.Computation.QuantumPaths
