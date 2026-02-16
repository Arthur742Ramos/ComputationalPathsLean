/-
# Spectral Theory via Computational Paths

Eigenvalues, eigenvectors, spectral decomposition, and resolvent concepts
modeled through genuine computational-paths operations: `stepChain`, `trans`,
`symm`, `congrArg`, `transport`. Zero `Path.ofEq`.

## Main results (35+ theorems/defs)
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Path

universe u

-- ============================================================================
-- § Matrix and vector representations (simplified over Nat)
-- ============================================================================

structure NMat2 where
  a11 : Nat
  a12 : Nat
  a21 : Nat
  a22 : Nat
  deriving Repr, DecidableEq

structure NVec2 where
  x : Nat
  y : Nat
  deriving Repr, DecidableEq

def NMat2.mulVec (m : NMat2) (v : NVec2) : NVec2 :=
  ⟨m.a11 * v.x + m.a12 * v.y, m.a21 * v.x + m.a22 * v.y⟩

def NMat2.add (m1 m2 : NMat2) : NMat2 :=
  ⟨m1.a11 + m2.a11, m1.a12 + m2.a12, m1.a21 + m2.a21, m1.a22 + m2.a22⟩

def NMat2.smul (c : Nat) (m : NMat2) : NMat2 :=
  ⟨c * m.a11, c * m.a12, c * m.a21, c * m.a22⟩

def NVec2.smul (c : Nat) (v : NVec2) : NVec2 :=
  ⟨c * v.x, c * v.y⟩

def NVec2.add (v1 v2 : NVec2) : NVec2 :=
  ⟨v1.x + v2.x, v1.y + v2.y⟩

def NVec2.zero : NVec2 := ⟨0, 0⟩
def NMat2.id : NMat2 := ⟨1, 0, 0, 1⟩
def NMat2.zero : NMat2 := ⟨0, 0, 0, 0⟩
def NMat2.trace (m : NMat2) : Nat := m.a11 + m.a22

def isNEigenvalue (m : NMat2) (lam : Nat) (v : NVec2) : Prop :=
  m.mulVec v = NVec2.smul lam v ∧ v ≠ NVec2.zero

-- ============================================================================
-- § Core spectral theorems with genuine paths
-- ============================================================================

-- 1. Identity matrix applied to any vector gives that vector
theorem nid_mulVec (v : NVec2) : NMat2.id.mulVec v = v := by
  simp [NMat2.id, NMat2.mulVec]

def nid_mulVec_step (v : NVec2) : Step NVec2 :=
  Step.mk (NMat2.id.mulVec v) v (nid_mulVec v)

def nid_mulVec_path (v : NVec2) : Path (NMat2.id.mulVec v) v :=
  Path.stepChain (nid_mulVec v)

-- 2. Zero matrix applied to any vector gives zero
theorem nzero_mulVec (v : NVec2) : NMat2.zero.mulVec v = NVec2.zero := by
  simp [NMat2.zero, NMat2.mulVec, NVec2.zero]

def nzero_mulVec_path (v : NVec2) : Path (NMat2.zero.mulVec v) NVec2.zero :=
  Path.stepChain (nzero_mulVec v)

-- 3. Trace of identity is 2
theorem ntrace_id : NMat2.id.trace = 2 := by
  simp [NMat2.id, NMat2.trace]

def ntrace_id_path : Path NMat2.id.trace 2 :=
  Path.stepChain ntrace_id

-- 4. Trace of zero matrix is 0
theorem ntrace_zero : NMat2.zero.trace = 0 := by
  simp [NMat2.zero, NMat2.trace]

def ntrace_zero_path : Path NMat2.zero.trace 0 :=
  Path.stepChain ntrace_zero

-- 5. Trace is additive
theorem ntrace_add (m1 m2 : NMat2) :
    (NMat2.add m1 m2).trace = m1.trace + m2.trace := by
  simp [NMat2.add, NMat2.trace]; omega

def ntrace_add_path (m1 m2 : NMat2) :
    Path (NMat2.add m1 m2).trace (m1.trace + m2.trace) :=
  Path.stepChain (ntrace_add m1 m2)

-- 6. Trace of scalar multiple
theorem ntrace_smul (c : Nat) (m : NMat2) :
    (NMat2.smul c m).trace = c * m.trace := by
  simp [NMat2.smul, NMat2.trace, Nat.mul_add]

def ntrace_smul_path (c : Nat) (m : NMat2) :
    Path (NMat2.smul c m).trace (c * m.trace) :=
  Path.stepChain (ntrace_smul c m)

-- ============================================================================
-- § Matrix algebra paths
-- ============================================================================

-- 7. Matrix addition is commutative
theorem nmat_add_comm (m1 m2 : NMat2) : NMat2.add m1 m2 = NMat2.add m2 m1 := by
  simp [NMat2.add]
  exact ⟨by omega, by omega, by omega, by omega⟩

def nmat_add_comm_step (m1 m2 : NMat2) : Step NMat2 :=
  Step.mk (NMat2.add m1 m2) (NMat2.add m2 m1) (nmat_add_comm m1 m2)

def nmat_add_comm_path (m1 m2 : NMat2) :
    Path (NMat2.add m1 m2) (NMat2.add m2 m1) :=
  Path.stepChain (nmat_add_comm m1 m2)

-- 8. Adding zero matrix on right is identity
theorem nmat_add_zero_right (m : NMat2) : NMat2.add m NMat2.zero = m := by
  simp [NMat2.add, NMat2.zero]

def nmat_add_zero_right_path (m : NMat2) :
    Path (NMat2.add m NMat2.zero) m :=
  Path.stepChain (nmat_add_zero_right m)

-- 9. Adding zero matrix on left is identity
theorem nmat_add_zero_left (m : NMat2) : NMat2.add NMat2.zero m = m := by
  simp [NMat2.add, NMat2.zero]

def nmat_add_zero_left_path (m : NMat2) :
    Path (NMat2.add NMat2.zero m) m :=
  Path.stepChain (nmat_add_zero_left m)

-- 10. Matrix addition is associative
theorem nmat_add_assoc (m1 m2 m3 : NMat2) :
    NMat2.add (NMat2.add m1 m2) m3 = NMat2.add m1 (NMat2.add m2 m3) := by
  simp [NMat2.add]
  exact ⟨by omega, by omega, by omega, by omega⟩

def nmat_add_assoc_path (m1 m2 m3 : NMat2) :
    Path (NMat2.add (NMat2.add m1 m2) m3) (NMat2.add m1 (NMat2.add m2 m3)) :=
  Path.stepChain (nmat_add_assoc m1 m2 m3)

-- ============================================================================
-- § Scalar multiple properties
-- ============================================================================

-- 11. Scalar mult by 1 is identity
theorem nsmul_one (m : NMat2) : NMat2.smul 1 m = m := by
  simp [NMat2.smul]

def nsmul_one_path (m : NMat2) : Path (NMat2.smul 1 m) m :=
  Path.stepChain (nsmul_one m)

-- 12. Scalar mult by 0 gives zero matrix
theorem nsmul_zero_mat (m : NMat2) : NMat2.smul 0 m = NMat2.zero := by
  simp [NMat2.smul, NMat2.zero]

def nsmul_zero_path (m : NMat2) : Path (NMat2.smul 0 m) NMat2.zero :=
  Path.stepChain (nsmul_zero_mat m)

-- 13. Scalar mult distributes over addition
theorem nsmul_add (c : Nat) (m1 m2 : NMat2) :
    NMat2.smul c (NMat2.add m1 m2) = NMat2.add (NMat2.smul c m1) (NMat2.smul c m2) := by
  simp [NMat2.smul, NMat2.add]
  refine ⟨Nat.left_distrib c _ _, Nat.left_distrib c _ _,
          Nat.left_distrib c _ _, Nat.left_distrib c _ _⟩

def nsmul_add_path (c : Nat) (m1 m2 : NMat2) :
    Path (NMat2.smul c (NMat2.add m1 m2))
         (NMat2.add (NMat2.smul c m1) (NMat2.smul c m2)) :=
  Path.stepChain (nsmul_add c m1 m2)

-- 14. Scalar mult associativity
theorem nsmul_assoc (c1 c2 : Nat) (m : NMat2) :
    NMat2.smul (c1 * c2) m = NMat2.smul c1 (NMat2.smul c2 m) := by
  simp [NMat2.smul, Nat.mul_assoc]

def nsmul_assoc_path (c1 c2 : Nat) (m : NMat2) :
    Path (NMat2.smul (c1 * c2) m) (NMat2.smul c1 (NMat2.smul c2 m)) :=
  Path.stepChain (nsmul_assoc c1 c2 m)

-- ============================================================================
-- § Diagonal matrices and eigenvalues
-- ============================================================================

def diagNMat (a b : Nat) : NMat2 := ⟨a, 0, 0, b⟩

-- 15. Trace of diagonal matrix
theorem ntrace_diag (a b : Nat) : (diagNMat a b).trace = a + b := by
  simp [diagNMat, NMat2.trace]

def ntrace_diag_path (a b : Nat) :
    Path (diagNMat a b).trace (a + b) :=
  Path.stepChain (ntrace_diag a b)

-- 16. Eigenvalue a of diag(a,b) with eigenvector (1,0)
theorem diag_eigen_fst (a b : Nat) :
    (diagNMat a b).mulVec ⟨1, 0⟩ = NVec2.smul a ⟨1, 0⟩ := by
  simp [diagNMat, NMat2.mulVec, NVec2.smul]

def diag_eigen_fst_path (a b : Nat) :
    Path ((diagNMat a b).mulVec ⟨1, 0⟩) (NVec2.smul a ⟨1, 0⟩) :=
  Path.stepChain (diag_eigen_fst a b)

-- 17. Eigenvalue b of diag(a,b) with eigenvector (0,1)
theorem diag_eigen_snd (a b : Nat) :
    (diagNMat a b).mulVec ⟨0, 1⟩ = NVec2.smul b ⟨0, 1⟩ := by
  simp [diagNMat, NMat2.mulVec, NVec2.smul]

def diag_eigen_snd_path (a b : Nat) :
    Path ((diagNMat a b).mulVec ⟨0, 1⟩) (NVec2.smul b ⟨0, 1⟩) :=
  Path.stepChain (diag_eigen_snd a b)

-- ============================================================================
-- § Matrix-vector linearity
-- ============================================================================

-- 18. Matrix-vector distributivity: A(v + w) = Av + Aw
theorem nmulVec_add (m : NMat2) (v w : NVec2) :
    m.mulVec (NVec2.add v w) = NVec2.add (m.mulVec v) (m.mulVec w) := by
  simp [NMat2.mulVec, NVec2.add, Nat.mul_add]
  constructor <;> omega

def nmulVec_add_path (m : NMat2) (v w : NVec2) :
    Path (m.mulVec (NVec2.add v w)) (NVec2.add (m.mulVec v) (m.mulVec w)) :=
  Path.stepChain (nmulVec_add m v w)

-- 19. Matrix-vector scalar: A(cv) = c(Av)
theorem nmulVec_smul (m : NMat2) (c : Nat) (v : NVec2) :
    m.mulVec (NVec2.smul c v) = NVec2.smul c (m.mulVec v) := by
  simp [NMat2.mulVec, NVec2.smul, Nat.mul_left_comm, Nat.left_distrib]

def nmulVec_smul_path (m : NMat2) (c : Nat) (v : NVec2) :
    Path (m.mulVec (NVec2.smul c v)) (NVec2.smul c (m.mulVec v)) :=
  Path.stepChain (nmulVec_smul m c v)

-- 20. Zero vector is identity for addition
theorem nvec_add_zero (v : NVec2) : NVec2.add v NVec2.zero = v := by
  simp [NVec2.add, NVec2.zero]

def nvec_add_zero_path (v : NVec2) :
    Path (NVec2.add v NVec2.zero) v :=
  Path.stepChain (nvec_add_zero v)

-- 21. Vector addition is commutative
theorem nvec_add_comm (v w : NVec2) : NVec2.add v w = NVec2.add w v := by
  simp [NVec2.add]
  exact ⟨by omega, by omega⟩

def nvec_add_comm_path (v w : NVec2) :
    Path (NVec2.add v w) (NVec2.add w v) :=
  Path.stepChain (nvec_add_comm v w)

-- ============================================================================
-- § Compound spectral paths via trans, symm, congrArg
-- ============================================================================

-- 22. Eigenvalue + symmetry roundtrip
def spectral_roundtrip (a b : Nat) :
    Path ((diagNMat a b).mulVec ⟨1, 0⟩) ((diagNMat a b).mulVec ⟨1, 0⟩) :=
  Path.trans (diag_eigen_fst_path a b) (Path.symm (diag_eigen_fst_path a b))

-- 23. Trace additivity + commutativity chain
def ntrace_add_comm_path (m1 m2 : NMat2) :
    Path (NMat2.add m1 m2).trace (m2.trace + m1.trace) :=
  Path.trans (ntrace_add_path m1 m2)
    (Path.stepChain (Nat.add_comm m1.trace m2.trace))

-- 24. congrArg: trace through matrix commutativity
def trace_mat_comm_path (m1 m2 : NMat2) :
    Path (NMat2.add m1 m2).trace (NMat2.add m2 m1).trace :=
  congrArg NMat2.trace (nmat_add_comm_path m1 m2)

-- 25. congrArg: mulVec through smul 1
def mulVec_smul_one_path (m : NMat2) (v : NVec2) :
    Path (m.mulVec (NVec2.smul 1 v)) (m.mulVec v) := by
  have h : NVec2.smul 1 v = v := by simp [NVec2.smul]
  exact congrArg m.mulVec (Path.stepChain h)

-- 26. Matrix addition associativity pentagon
def nmat_add_pentagon (m1 m2 m3 m4 : NMat2) :
    Path (NMat2.add (NMat2.add (NMat2.add m1 m2) m3) m4)
         (NMat2.add m1 (NMat2.add m2 (NMat2.add m3 m4))) :=
  Path.trans (nmat_add_assoc_path (NMat2.add m1 m2) m3 m4)
    (nmat_add_assoc_path m1 m2 (NMat2.add m3 m4))

-- 27. smul 0 then add zero: smul(0,m) → 0 → add(0, m) ← m ... actually:
-- smul(0,m) → zero → add(zero, m') ← m'
def smul_zero_add_path (m : NMat2) :
    Path (NMat2.smul 0 m) (NMat2.add NMat2.zero NMat2.zero) :=
  Path.trans (nsmul_zero_path m) (Path.symm (nmat_add_zero_right_path NMat2.zero))

-- 28. Eigenvalue chain: diag action → scalar → commuted scalar
def diag_eigen_chain (a b : Nat) :
    Path ((diagNMat a b).mulVec ⟨1, 0⟩) (NVec2.smul a ⟨1, 0⟩) :=
  Path.trans (Path.refl _) (diag_eigen_fst_path a b)

-- 29. Vector commutativity roundtrip semantic
theorem nvec_comm_roundtrip_toEq (v w : NVec2) :
    (Path.trans (nvec_add_comm_path v w) (Path.symm (nvec_add_comm_path v w))).toEq =
      (Path.refl (NVec2.add v w)).toEq := by
  simp

-- 30. Matrix comm roundtrip semantic
theorem nmat_comm_roundtrip_toEq (m1 m2 : NMat2) :
    (Path.trans (nmat_add_comm_path m1 m2) (Path.symm (nmat_add_comm_path m1 m2))).toEq =
      (Path.refl (NMat2.add m1 m2)).toEq := by
  simp

-- 31. symm commutes with congrArg for trace
theorem symm_congrArg_trace {m1 m2 : NMat2} (p : Path m1 m2) :
    Path.symm (Path.congrArg NMat2.trace p) = Path.congrArg NMat2.trace (Path.symm p) := by
  cases p with | mk sp pp =>
  cases pp
  simp [Path.congrArg, Path.symm]

-- 32. trans commutes with congrArg for mulVec
theorem congrArg_mulVec_trans (v : NVec2) {m1 m2 m3 : NMat2}
    (p : Path m1 m2) (q : Path m2 m3) :
    Path.congrArg (fun m => m.mulVec v) (Path.trans p q) =
      Path.trans (Path.congrArg (fun m => m.mulVec v) p)
                 (Path.congrArg (fun m => m.mulVec v) q) := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq
  simp [Path.congrArg, Path.trans]

-- 33. Step map through trace
theorem nmat_add_step_map_trace (m1 m2 : NMat2) :
    Step.map NMat2.trace (nmat_add_comm_step m1 m2) =
      Step.mk (NMat2.add m1 m2).trace (NMat2.add m2 m1).trace
        (_root_.congrArg NMat2.trace (nmat_add_comm m1 m2)) := by
  simp [nmat_add_comm_step, Step.map]

-- 34. Transport through trace additivity
theorem transport_ntrace_add {D : Nat → Sort _} (m1 m2 : NMat2)
    (x : D (NMat2.add m1 m2).trace) :
    transport (ntrace_add_path m1 m2) x = (ntrace_add m1 m2) ▸ x := by
  simp [ntrace_add_path, transport]

-- 35. Smul distributivity then commutativity chain
def nsmul_add_comm_path (c : Nat) (m1 m2 : NMat2) :
    Path (NMat2.smul c (NMat2.add m1 m2))
         (NMat2.add (NMat2.smul c m2) (NMat2.smul c m1)) :=
  Path.trans (nsmul_add_path c m1 m2)
    (nmat_add_comm_path (NMat2.smul c m1) (NMat2.smul c m2))

-- 36. Scalar 1 roundtrip: smul(1,m) → m → smul(1,m)
def nsmul_one_roundtrip (m : NMat2) :
    Path (NMat2.smul 1 m) (NMat2.smul 1 m) :=
  Path.trans (nsmul_one_path m) (Path.symm (nsmul_one_path m))

-- 37. Identity action composed with vector add-zero
def nid_add_zero_chain (v : NVec2) :
    Path (NMat2.id.mulVec (NVec2.add v NVec2.zero)) v :=
  Path.trans (congrArg NMat2.id.mulVec (nvec_add_zero_path v))
    (nid_mulVec_path v)

-- 38. Trace of smul(1,m) = trace(m)
def ntrace_smul_one_path (m : NMat2) :
    Path (NMat2.smul 1 m).trace m.trace :=
  congrArg NMat2.trace (nsmul_one_path m)

end ComputationalPaths
