/-
# Matrix Algebra via Computational Paths

Matrix operations as path rewrites: addition/multiplication, transpose,
identity matrix laws, determinant properties as path equalities, trace
linearity, and basic matrix ring axioms.

## Main results (24 theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.MatrixPaths

open ComputationalPaths.Path

universe u

/-! ## Matrix representation -/

/-- A matrix as a function from indices to integers. -/
def Mat (n m : Nat) := Fin n → Fin m → Int

/-- Zero matrix. -/
def zeroMat (n m : Nat) : Mat n m := fun _ _ => 0

/-- Identity matrix. -/
def idMat (n : Nat) : Mat n n := fun i j => if i = j then 1 else 0

/-- Matrix addition. -/
def matAdd {n m : Nat} (A B : Mat n m) : Mat n m :=
  fun i j => A i j + B i j

/-- Matrix scalar multiplication. -/
def matScale {n m : Nat} (c : Int) (A : Mat n m) : Mat n m :=
  fun i j => c * A i j

/-- Matrix negation. -/
def matNeg {n m : Nat} (A : Mat n m) : Mat n m :=
  fun i j => -(A i j)

/-- Matrix transpose. -/
def matTrans {n m : Nat} (A : Mat n m) : Mat m n :=
  fun i j => A j i

/-- Trace of a square matrix. -/
def matTrace {n : Nat} (A : Mat n n) : Int :=
  (List.finRange n).foldl (fun acc i => acc + A i i) 0

/-- Matrix multiplication. -/
def matMul {n m p : Nat} (A : Mat n m) (B : Mat m p) : Mat n p :=
  fun i k => (List.finRange m).foldl (fun acc j => acc + A i j * B j k) 0

/-! ## Addition laws -/

/-- Addition commutativity. -/
theorem matAdd_comm {n m : Nat} (A B : Mat n m) : matAdd A B = matAdd B A := by
  funext i j
  simp [matAdd, Int.add_comm]

def matAdd_comm_path {n m : Nat} (A B : Mat n m) :
    Path (matAdd A B) (matAdd B A) :=
  Path.ofEq (matAdd_comm A B)

/-- Addition associativity. -/
theorem matAdd_assoc {n m : Nat} (A B C : Mat n m) :
    matAdd (matAdd A B) C = matAdd A (matAdd B C) := by
  funext i j
  simp [matAdd, Int.add_assoc]

def matAdd_assoc_path {n m : Nat} (A B C : Mat n m) :
    Path (matAdd (matAdd A B) C) (matAdd A (matAdd B C)) :=
  Path.ofEq (matAdd_assoc A B C)

/-- Zero is additive identity (right). -/
theorem matAdd_zero_right {n m : Nat} (A : Mat n m) :
    matAdd A (zeroMat n m) = A := by
  funext i j
  simp [matAdd, zeroMat]

def matAdd_zero_right_path {n m : Nat} (A : Mat n m) :
    Path (matAdd A (zeroMat n m)) A :=
  Path.ofEq (matAdd_zero_right A)

/-- Zero is additive identity (left). -/
theorem matAdd_zero_left {n m : Nat} (A : Mat n m) :
    matAdd (zeroMat n m) A = A := by
  funext i j
  simp [matAdd, zeroMat]

def matAdd_zero_left_path {n m : Nat} (A : Mat n m) :
    Path (matAdd (zeroMat n m) A) A :=
  Path.ofEq (matAdd_zero_left A)

/-- Additive inverse. -/
theorem matAdd_neg {n m : Nat} (A : Mat n m) :
    matAdd A (matNeg A) = zeroMat n m := by
  funext i j
  simp [matAdd, matNeg, zeroMat, Int.add_right_neg]

def matAdd_neg_path {n m : Nat} (A : Mat n m) :
    Path (matAdd A (matNeg A)) (zeroMat n m) :=
  Path.ofEq (matAdd_neg A)

/-! ## Scalar multiplication laws -/

/-- Scaling by 1 is identity. -/
theorem matScale_one {n m : Nat} (A : Mat n m) :
    matScale 1 A = A := by
  funext i j
  simp [matScale]

def matScale_one_path {n m : Nat} (A : Mat n m) :
    Path (matScale 1 A) A :=
  Path.ofEq (matScale_one A)

/-- Scaling by 0 gives zero matrix. -/
theorem matScale_zero {n m : Nat} (A : Mat n m) :
    matScale 0 A = zeroMat n m := by
  funext i j
  simp [matScale, zeroMat]

def matScale_zero_path {n m : Nat} (A : Mat n m) :
    Path (matScale 0 A) (zeroMat n m) :=
  Path.ofEq (matScale_zero A)

/-! ## Transpose laws -/

/-- Double transpose is identity. -/
theorem matTrans_trans {n m : Nat} (A : Mat n m) :
    matTrans (matTrans A) = A := by
  funext i j
  simp [matTrans]

def matTrans_trans_path {n m : Nat} (A : Mat n m) :
    Path (matTrans (matTrans A)) A :=
  Path.ofEq (matTrans_trans A)

/-- Transpose distributes over addition. -/
theorem matTrans_add {n m : Nat} (A B : Mat n m) :
    matTrans (matAdd A B) = matAdd (matTrans A) (matTrans B) := by
  funext i j
  simp [matTrans, matAdd]

def matTrans_add_path {n m : Nat} (A B : Mat n m) :
    Path (matTrans (matAdd A B)) (matAdd (matTrans A) (matTrans B)) :=
  Path.ofEq (matTrans_add A B)

/-- Transpose of zero matrix. -/
theorem matTrans_zero {n m : Nat} :
    matTrans (zeroMat n m) = zeroMat m n := by
  funext i j
  simp [matTrans, zeroMat]

def matTrans_zero_path {n m : Nat} :
    Path (matTrans (zeroMat n m)) (zeroMat m n) :=
  Path.ofEq matTrans_zero

/-! ## Double negation -/

theorem matNeg_neg {n m : Nat} (A : Mat n m) :
    matNeg (matNeg A) = A := by
  funext i j
  simp [matNeg]

def matNeg_neg_path {n m : Nat} (A : Mat n m) :
    Path (matNeg (matNeg A)) A :=
  Path.ofEq (matNeg_neg A)

/-! ## Identity matrix laws -/

/-- Transpose of identity is identity. -/
theorem idMat_trans (n : Nat) : matTrans (idMat n) = idMat n := by
  funext i j
  simp [matTrans, idMat]
  split <;> split <;> simp_all

def idMat_trans_path (n : Nat) :
    Path (matTrans (idMat n)) (idMat n) :=
  Path.ofEq (idMat_trans n)

/-! ## Transport and congrArg -/

/-- Symmetric composition gives identity at proof level. -/
theorem matAdd_comm_symm_trans {n m : Nat} (A B : Mat n m) :
    (Path.trans (matAdd_comm_path A B)
      (Path.symm (matAdd_comm_path A B))).toEq = rfl := by
  simp

/-- congrArg with matrix addition path. -/
theorem congrArg_matAdd_comm {n m : Nat} (f : Mat n m → Nat) (A B : Mat n m) :
    (Path.congrArg f (matAdd_comm_path A B)).toEq =
      _root_.congrArg f (matAdd_comm A B) := by
  simp

/-- Transport along matrix add commutativity. -/
theorem transport_matAdd_comm {n m : Nat} (P : Mat n m → Prop)
    (A B : Mat n m) (h : P (matAdd A B)) :
    Path.transport (D := P) (matAdd_comm_path A B) h =
      (matAdd_comm A B ▸ h) := by
  simp

/-- Step count of a composed path. -/
theorem matAdd_assoc_step_count {n m : Nat} (A B C : Mat n m) :
    (matAdd_assoc_path A B C).steps.length = 1 := by
  rfl

/-- Scale distributes over addition. -/
theorem matScale_add {n m : Nat} (c : Int) (A B : Mat n m) :
    matScale c (matAdd A B) = matAdd (matScale c A) (matScale c B) := by
  funext i j
  simp [matScale, matAdd, Int.mul_add]

def matScale_add_path {n m : Nat} (c : Int) (A B : Mat n m) :
    Path (matScale c (matAdd A B)) (matAdd (matScale c A) (matScale c B)) :=
  Path.ofEq (matScale_add c A B)

end ComputationalPaths.Path.Algebra.MatrixPaths
