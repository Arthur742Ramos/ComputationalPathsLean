/-
# Spectral Theory via Computational Paths

Eigenvalues, eigenvectors, spectral decomposition, and resolvent concepts
modeled through the computational-paths framework using simple types.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Path

universe u

-- ============================================================================
-- § Matrix and vector representations (simplified over Nat)
-- ============================================================================

/-- A 2x2 matrix over Nat. -/
structure NMat2 where
  a11 : Nat
  a12 : Nat
  a21 : Nat
  a22 : Nat
  deriving Repr, DecidableEq

/-- A 2-vector over Nat. -/
structure NVec2 where
  x : Nat
  y : Nat
  deriving Repr, DecidableEq

/-- Matrix-vector multiplication. -/
def NMat2.mulVec (m : NMat2) (v : NVec2) : NVec2 :=
  ⟨m.a11 * v.x + m.a12 * v.y, m.a21 * v.x + m.a22 * v.y⟩

/-- Matrix addition. -/
def NMat2.add (m1 m2 : NMat2) : NMat2 :=
  ⟨m1.a11 + m2.a11, m1.a12 + m2.a12, m1.a21 + m2.a21, m1.a22 + m2.a22⟩

/-- Scalar multiplication of matrix. -/
def NMat2.smul (c : Nat) (m : NMat2) : NMat2 :=
  ⟨c * m.a11, c * m.a12, c * m.a21, c * m.a22⟩

/-- Scalar multiplication of vector. -/
def NVec2.smul (c : Nat) (v : NVec2) : NVec2 :=
  ⟨c * v.x, c * v.y⟩

/-- Vector addition. -/
def NVec2.add (v1 v2 : NVec2) : NVec2 :=
  ⟨v1.x + v2.x, v1.y + v2.y⟩

/-- Zero vector. -/
def NVec2.zero : NVec2 := ⟨0, 0⟩

/-- Identity matrix. -/
def NMat2.id : NMat2 := ⟨1, 0, 0, 1⟩

/-- Zero matrix. -/
def NMat2.zero : NMat2 := ⟨0, 0, 0, 0⟩

/-- Trace of a 2x2 matrix. -/
def NMat2.trace (m : NMat2) : Nat := m.a11 + m.a22

-- ============================================================================
-- § Eigenvalue condition
-- ============================================================================

/-- λ is an eigenvalue of m with eigenvector v if m*v = λ*v and v ≠ 0. -/
def isNEigenvalue (m : NMat2) (lam : Nat) (v : NVec2) : Prop :=
  m.mulVec v = NVec2.smul lam v ∧ v ≠ NVec2.zero

-- ============================================================================
-- § Core spectral theorems
-- ============================================================================

/-- Identity matrix applied to any vector gives that vector. -/
theorem nid_mulVec (v : NVec2) : NMat2.id.mulVec v = v := by
  simp [NMat2.id, NMat2.mulVec]

/-- Path witnessing identity action. -/
def nid_mulVec_path (v : NVec2) : Path (NMat2.id.mulVec v) v :=
  Path.ofEq (nid_mulVec v)

/-- Zero matrix applied to any vector gives zero. -/
theorem nzero_mulVec (v : NVec2) : NMat2.zero.mulVec v = NVec2.zero := by
  simp [NMat2.zero, NMat2.mulVec, NVec2.zero]

/-- Path for zero matrix action. -/
def nzero_mulVec_path (v : NVec2) : Path (NMat2.zero.mulVec v) NVec2.zero :=
  Path.ofEq (nzero_mulVec v)

/-- Trace of identity is 2. -/
theorem ntrace_id : NMat2.id.trace = 2 := by
  simp [NMat2.id, NMat2.trace]

/-- Trace of zero matrix is 0. -/
theorem ntrace_zero : NMat2.zero.trace = 0 := by
  simp [NMat2.zero, NMat2.trace]

/-- Path for trace of identity. -/
def ntrace_id_path : Path NMat2.id.trace 2 :=
  Path.ofEq ntrace_id

/-- Trace is additive: trace(A + B) = trace(A) + trace(B). -/
theorem ntrace_add (m1 m2 : NMat2) :
    (NMat2.add m1 m2).trace = m1.trace + m2.trace := by
  simp [NMat2.add, NMat2.trace]; omega

/-- Path for trace additivity. -/
def ntrace_add_path (m1 m2 : NMat2) :
    Path (NMat2.add m1 m2).trace (m1.trace + m2.trace) :=
  Path.ofEq (ntrace_add m1 m2)

/-- Trace of scalar multiple. -/
theorem ntrace_smul (c : Nat) (m : NMat2) :
    (NMat2.smul c m).trace = c * m.trace := by
  simp [NMat2.smul, NMat2.trace, Nat.mul_add]

/-- Path for trace scalar multiplication. -/
def ntrace_smul_path (c : Nat) (m : NMat2) :
    Path (NMat2.smul c m).trace (c * m.trace) :=
  Path.ofEq (ntrace_smul c m)

-- ============================================================================
-- § Matrix algebra paths
-- ============================================================================

/-- Matrix addition is commutative. -/
theorem nmat_add_comm (m1 m2 : NMat2) : NMat2.add m1 m2 = NMat2.add m2 m1 := by
  simp [NMat2.add]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Path for matrix addition commutativity. -/
def nmat_add_comm_path (m1 m2 : NMat2) :
    Path (NMat2.add m1 m2) (NMat2.add m2 m1) :=
  Path.ofEq (nmat_add_comm m1 m2)

/-- Adding zero matrix on right is identity. -/
theorem nmat_add_zero_right (m : NMat2) : NMat2.add m NMat2.zero = m := by
  simp [NMat2.add, NMat2.zero]

/-- Adding zero matrix on left is identity. -/
theorem nmat_add_zero_left (m : NMat2) : NMat2.add NMat2.zero m = m := by
  simp [NMat2.add, NMat2.zero]

/-- Path for adding zero (right). -/
def nmat_add_zero_right_path (m : NMat2) :
    Path (NMat2.add m NMat2.zero) m :=
  Path.ofEq (nmat_add_zero_right m)

/-- Path for adding zero (left). -/
def nmat_add_zero_left_path (m : NMat2) :
    Path (NMat2.add NMat2.zero m) m :=
  Path.ofEq (nmat_add_zero_left m)

/-- Matrix addition is associative. -/
theorem nmat_add_assoc (m1 m2 m3 : NMat2) :
    NMat2.add (NMat2.add m1 m2) m3 = NMat2.add m1 (NMat2.add m2 m3) := by
  simp [NMat2.add]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Path for matrix addition associativity. -/
def nmat_add_assoc_path (m1 m2 m3 : NMat2) :
    Path (NMat2.add (NMat2.add m1 m2) m3) (NMat2.add m1 (NMat2.add m2 m3)) :=
  Path.ofEq (nmat_add_assoc m1 m2 m3)

-- ============================================================================
-- § Scalar multiple properties
-- ============================================================================

/-- Scalar mult by 1 is identity. -/
theorem nsmul_one (m : NMat2) : NMat2.smul 1 m = m := by
  simp [NMat2.smul]

/-- Scalar mult by 0 gives zero matrix. -/
theorem nsmul_zero_mat (m : NMat2) : NMat2.smul 0 m = NMat2.zero := by
  simp [NMat2.smul, NMat2.zero]

/-- Path for scalar mult by 1. -/
def nsmul_one_path (m : NMat2) : Path (NMat2.smul 1 m) m :=
  Path.ofEq (nsmul_one m)

/-- Path for scalar mult by 0. -/
def nsmul_zero_path (m : NMat2) : Path (NMat2.smul 0 m) NMat2.zero :=
  Path.ofEq (nsmul_zero_mat m)

/-- Scalar mult distributes over addition. -/
theorem nsmul_add (c : Nat) (m1 m2 : NMat2) :
    NMat2.smul c (NMat2.add m1 m2) = NMat2.add (NMat2.smul c m1) (NMat2.smul c m2) := by
  simp [NMat2.smul, NMat2.add]
  refine ⟨Nat.left_distrib c _ _, Nat.left_distrib c _ _, Nat.left_distrib c _ _, Nat.left_distrib c _ _⟩

/-- Path for scalar distributivity. -/
def nsmul_add_path (c : Nat) (m1 m2 : NMat2) :
    Path (NMat2.smul c (NMat2.add m1 m2)) (NMat2.add (NMat2.smul c m1) (NMat2.smul c m2)) :=
  Path.ofEq (nsmul_add c m1 m2)

-- ============================================================================
-- § Diagonal matrices and eigenvalues
-- ============================================================================

/-- Diagonal matrix. -/
def diagNMat (a b : Nat) : NMat2 := ⟨a, 0, 0, b⟩

/-- Trace of diagonal matrix. -/
theorem ntrace_diag (a b : Nat) : (diagNMat a b).trace = a + b := by
  simp [diagNMat, NMat2.trace]

/-- Path for trace of diagonal. -/
def ntrace_diag_path (a b : Nat) :
    Path (diagNMat a b).trace (a + b) :=
  Path.ofEq (ntrace_diag a b)

/-- Eigenvalue a of diag(a,b) with eigenvector (1,0). -/
theorem diag_eigen_fst (a b : Nat) :
    (diagNMat a b).mulVec ⟨1, 0⟩ = NVec2.smul a ⟨1, 0⟩ := by
  simp [diagNMat, NMat2.mulVec, NVec2.smul]

/-- Eigenvalue b of diag(a,b) with eigenvector (0,1). -/
theorem diag_eigen_snd (a b : Nat) :
    (diagNMat a b).mulVec ⟨0, 1⟩ = NVec2.smul b ⟨0, 1⟩ := by
  simp [diagNMat, NMat2.mulVec, NVec2.smul]

/-- Path for first eigenvalue of diagonal matrix. -/
def diag_eigen_fst_path (a b : Nat) :
    Path ((diagNMat a b).mulVec ⟨1, 0⟩) (NVec2.smul a ⟨1, 0⟩) :=
  Path.ofEq (diag_eigen_fst a b)

/-- Path for second eigenvalue of diagonal matrix. -/
def diag_eigen_snd_path (a b : Nat) :
    Path ((diagNMat a b).mulVec ⟨0, 1⟩) (NVec2.smul b ⟨0, 1⟩) :=
  Path.ofEq (diag_eigen_snd a b)

-- ============================================================================
-- § Matrix-vector linearity
-- ============================================================================

/-- Matrix-vector distributivity: A(v + w) = Av + Aw. -/
theorem nmulVec_add (m : NMat2) (v w : NVec2) :
    m.mulVec (NVec2.add v w) = NVec2.add (m.mulVec v) (m.mulVec w) := by
  simp [NMat2.mulVec, NVec2.add, Nat.mul_add]
  constructor <;> omega

/-- Path for matrix-vector distributivity. -/
def nmulVec_add_path (m : NMat2) (v w : NVec2) :
    Path (m.mulVec (NVec2.add v w)) (NVec2.add (m.mulVec v) (m.mulVec w)) :=
  Path.ofEq (nmulVec_add m v w)

/-- Matrix-vector scalar: A(cv) = c(Av). -/
theorem nmulVec_smul (m : NMat2) (c : Nat) (v : NVec2) :
    m.mulVec (NVec2.smul c v) = NVec2.smul c (m.mulVec v) := by
  simp [NMat2.mulVec, NVec2.smul, Nat.mul_left_comm, Nat.left_distrib]

/-- Path for matrix-vector scalar. -/
def nmulVec_smul_path (m : NMat2) (c : Nat) (v : NVec2) :
    Path (m.mulVec (NVec2.smul c v)) (NVec2.smul c (m.mulVec v)) :=
  Path.ofEq (nmulVec_smul m c v)

/-- Zero vector is identity for addition. -/
theorem nvec_add_zero (v : NVec2) : NVec2.add v NVec2.zero = v := by
  simp [NVec2.add, NVec2.zero]

/-- Path for vector zero addition. -/
def nvec_add_zero_path (v : NVec2) :
    Path (NVec2.add v NVec2.zero) v :=
  Path.ofEq (nvec_add_zero v)

/-- Vector addition is commutative. -/
theorem nvec_add_comm (v w : NVec2) : NVec2.add v w = NVec2.add w v := by
  simp [NVec2.add]
  exact ⟨by omega, by omega⟩

/-- Path for vector commutativity. -/
def nvec_add_comm_path (v w : NVec2) :
    Path (NVec2.add v w) (NVec2.add w v) :=
  Path.ofEq (nvec_add_comm v w)

-- ============================================================================
-- § Spectral composition and symmetry paths
-- ============================================================================

/-- Composing eigenvalue paths via trans. -/
def spectral_trans_path (a b : Nat) :
    Path ((diagNMat a b).mulVec ⟨1, 0⟩) (NVec2.smul a ⟨1, 0⟩) :=
  Path.trans (Path.refl _) (diag_eigen_fst_path a b)

/-- Symmetry of eigenvalue path. -/
def spectral_symm_path (a b : Nat) :
    Path (NVec2.smul a ⟨1, 0⟩) ((diagNMat a b).mulVec ⟨1, 0⟩) :=
  Path.symm (diag_eigen_fst_path a b)

/-- Roundtrip spectral path. -/
def spectral_roundtrip (a b : Nat) :
    Path ((diagNMat a b).mulVec ⟨1, 0⟩) ((diagNMat a b).mulVec ⟨1, 0⟩) :=
  Path.trans (diag_eigen_fst_path a b) (spectral_symm_path a b)

/-- Scalar mult compatibility: (c₁ * c₂) * m = c₁ * (c₂ * m). -/
theorem nsmul_assoc (c1 c2 : Nat) (m : NMat2) :
    NMat2.smul (c1 * c2) m = NMat2.smul c1 (NMat2.smul c2 m) := by
  simp [NMat2.smul, Nat.mul_assoc]

/-- Path for scalar associativity. -/
def nsmul_assoc_path (c1 c2 : Nat) (m : NMat2) :
    Path (NMat2.smul (c1 * c2) m) (NMat2.smul c1 (NMat2.smul c2 m)) :=
  Path.ofEq (nsmul_assoc c1 c2 m)

end ComputationalPaths
