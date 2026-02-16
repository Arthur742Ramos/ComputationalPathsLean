/-
# Matrix Algebra via Computational Paths (deepened)

This file eliminates `Path.ofEq` scaffolding.  We provide a small
matrix-expression language:

* `MatObj`  — expressions for matrices (addition/negation/scaling)
* `MatStep` — elementary algebraic rewrite steps
* `MatPath` — generated paths using `refl`/`trans`/`symm`

We then export concrete `Path` witnesses for standard matrix laws using
explicit one-step traces (`Path.mk` + `Step.mk`) and genuine path operations
(`trans`, `symm`, `congrArg`).
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

/-! ## Matrix laws as equalities (semantic) -/

section Laws

variable {n m : Nat}

theorem matAdd_comm (A B : Mat n m) : matAdd A B = matAdd B A := by
  funext i j
  simp [matAdd, Int.add_comm]

theorem matAdd_assoc (A B C : Mat n m) :
    matAdd (matAdd A B) C = matAdd A (matAdd B C) := by
  funext i j
  simp [matAdd, Int.add_assoc]

theorem matAdd_zero_right (A : Mat n m) : matAdd A (zeroMat n m) = A := by
  funext i j
  simp [matAdd, zeroMat]

theorem matAdd_zero_left (A : Mat n m) : matAdd (zeroMat n m) A = A := by
  funext i j
  simp [matAdd, zeroMat]

theorem matAdd_neg_right (A : Mat n m) : matAdd A (matNeg A) = zeroMat n m := by
  funext i j
  simp [matAdd, matNeg, zeroMat, Int.add_right_neg]

theorem matNeg_neg (A : Mat n m) : matNeg (matNeg A) = A := by
  funext i j
  simp [matNeg]

theorem matNeg_zero : matNeg (zeroMat n m) = zeroMat n m := by
  funext i j
  simp [matNeg, zeroMat]

theorem matNeg_add (A B : Mat n m) : matNeg (matAdd A B) = matAdd (matNeg A) (matNeg B) := by
  funext i j
  simp [matNeg, matAdd, Int.neg_add]

theorem matScale_one (A : Mat n m) : matScale 1 A = A := by
  funext i j
  simp [matScale]

theorem matScale_zero (A : Mat n m) : matScale 0 A = zeroMat n m := by
  funext i j
  simp [matScale, zeroMat]

theorem matScale_add (c : Int) (A B : Mat n m) :
    matScale c (matAdd A B) = matAdd (matScale c A) (matScale c B) := by
  funext i j
  simp [matScale, matAdd, Int.mul_add]

theorem matScale_neg (c : Int) (A : Mat n m) : matScale c (matNeg A) = matNeg (matScale c A) := by
  funext i j
  simp [matScale, matNeg, Int.mul_neg]

end Laws

section Transpose

variable {n m : Nat}

theorem matTrans_trans (A : Mat n m) : matTrans (matTrans A) = A := by
  funext i j
  simp [matTrans]

theorem matTrans_add (A B : Mat n m) :
    matTrans (matAdd A B) = matAdd (matTrans A) (matTrans B) := by
  funext i j
  simp [matTrans, matAdd]

theorem matTrans_zero : matTrans (zeroMat n m) = zeroMat m n := by
  funext i j
  simp [matTrans, zeroMat]

theorem matTrans_neg (A : Mat n m) : matTrans (matNeg A) = matNeg (matTrans A) := by
  funext i j
  simp [matTrans, matNeg]

theorem matTrans_scale (c : Int) (A : Mat n m) :
    matTrans (matScale c A) = matScale c (matTrans A) := by
  funext i j
  simp [matTrans, matScale]

theorem idMat_trans (n : Nat) : matTrans (idMat n) = idMat n := by
  funext i j
  by_cases h : i = j
  · simp [matTrans, idMat, h]
  · have h' : j ≠ i := by intro hji; exact h hji.symm
    simp [matTrans, idMat, h, h']

end Transpose

/-! ## Domain language: objects, steps, paths -/

section Domain

variable {n m : Nat}

/-- Matrix expressions. -/
inductive MatObj (n m : Nat) : Type
  | base : Mat n m → MatObj n m
  | zero : MatObj n m
  | add : MatObj n m → MatObj n m → MatObj n m
  | neg : MatObj n m → MatObj n m
  | scale : Int → MatObj n m → MatObj n m

namespace MatObj

/-- Evaluate a matrix expression. -/
def eval : MatObj n m → Mat n m
  | base A => A
  | zero => zeroMat n m
  | add A B => matAdd (eval A) (eval B)
  | neg A => matNeg (eval A)
  | scale c A => matScale c (eval A)

@[simp] theorem eval_base (A : Mat n m) : eval (base A) = A := rfl
@[simp] theorem eval_zero : eval (zero (n := n) (m := m)) = zeroMat n m := rfl
@[simp] theorem eval_add (A B : MatObj n m) : eval (add A B) = matAdd (eval A) (eval B) := rfl
@[simp] theorem eval_neg (A : MatObj n m) : eval (neg A) = matNeg (eval A) := rfl
@[simp] theorem eval_scale (c : Int) (A : MatObj n m) : eval (scale c A) = matScale c (eval A) := rfl

end MatObj

/-- Elementary rewrite steps. -/
inductive MatStep : MatObj n m → MatObj n m → Type
  | addComm (A B : MatObj n m) : MatStep (.add A B) (.add B A)
  | addAssoc (A B C : MatObj n m) : MatStep (.add (.add A B) C) (.add A (.add B C))
  | addZeroR (A : MatObj n m) : MatStep (.add A .zero) A
  | addZeroL (A : MatObj n m) : MatStep (.add .zero A) A
  | addNegR (A : MatObj n m) : MatStep (.add A (.neg A)) .zero
  | negNeg (A : MatObj n m) : MatStep (.neg (.neg A)) A
  | scaleOne (A : MatObj n m) : MatStep (.scale 1 A) A
  | scaleZero (A : MatObj n m) : MatStep (.scale 0 A) .zero
  | scaleAdd (c : Int) (A B : MatObj n m) :
      MatStep (.scale c (.add A B)) (.add (.scale c A) (.scale c B))
  | scaleNeg (c : Int) (A : MatObj n m) :
      MatStep (.scale c (.neg A)) (.neg (.scale c A))
  | addCongL {A B : MatObj n m} (s : MatStep A B) (C : MatObj n m) :
      MatStep (.add A C) (.add B C)
  | addCongR (C : MatObj n m) {A B : MatObj n m} (s : MatStep A B) :
      MatStep (.add C A) (.add C B)
  | negCong {A B : MatObj n m} (s : MatStep A B) : MatStep (.neg A) (.neg B)
  | scaleCong (c : Int) {A B : MatObj n m} (s : MatStep A B) : MatStep (.scale c A) (.scale c B)

namespace MatStep

/-- Correctness of steps. -/
theorem eval_eq {A B : MatObj n m} (s : MatStep A B) : MatObj.eval A = MatObj.eval B := by
  cases s <;> simp [MatObj.eval, matAdd_comm, matAdd_assoc, matAdd_zero_right, matAdd_zero_left, matAdd_neg_right, matNeg_neg, matScale_one, matScale_zero, matScale_add, matScale_neg, eval_eq]

/-- Interpret a step as a `Path`. -/
def toPath {A B : MatObj n m} (s : MatStep A B) : Path (MatObj.eval A) (MatObj.eval B) :=
  match s with
  | addCongL s C => Path.congrArg (fun X => matAdd X (MatObj.eval C)) (toPath s)
  | addCongR C s => Path.congrArg (fun X => matAdd (MatObj.eval C) X) (toPath s)
  | negCong s => Path.congrArg matNeg (toPath s)
  | scaleCong c s => Path.congrArg (matScale c) (toPath s)
  | _ => Path.mk [Step.mk _ _ (eval_eq s)] (eval_eq s)

end MatStep

/-- Paths generated from matrix steps. -/
inductive MatPath : MatObj n m → MatObj n m → Type
  | refl (A : MatObj n m) : MatPath A A
  | step {A B : MatObj n m} (s : MatStep A B) : MatPath A B
  | trans {A B C : MatObj n m} (p : MatPath A B) (q : MatPath B C) : MatPath A C
  | symm {A B : MatObj n m} (p : MatPath A B) : MatPath B A

namespace MatPath

def toPath {A B : MatObj n m} : MatPath A B → Path (MatObj.eval A) (MatObj.eval B)
  | refl _ => Path.refl _
  | step s => MatStep.toPath s
  | trans p q => Path.trans (toPath p) (toPath q)
  | symm p => Path.symm (toPath p)

end MatPath

end Domain

/-! ## Exported paths -/

section Export

variable {n m : Nat}

def matAdd_comm_path (A B : Mat n m) : Path (matAdd A B) (matAdd B A) :=
  Path.mk [Step.mk _ _ (matAdd_comm A B)] (matAdd_comm A B)

def matAdd_assoc_path (A B C : Mat n m) :
    Path (matAdd (matAdd A B) C) (matAdd A (matAdd B C)) :=
  Path.mk [Step.mk _ _ (matAdd_assoc A B C)] (matAdd_assoc A B C)

def matAdd_zero_right_path (A : Mat n m) : Path (matAdd A (zeroMat n m)) A :=
  Path.mk [Step.mk _ _ (matAdd_zero_right A)] (matAdd_zero_right A)

def matAdd_zero_left_path (A : Mat n m) : Path (matAdd (zeroMat n m) A) A :=
  Path.mk [Step.mk _ _ (matAdd_zero_left A)] (matAdd_zero_left A)

def matAdd_neg_path (A : Mat n m) : Path (matAdd A (matNeg A)) (zeroMat n m) :=
  Path.mk [Step.mk _ _ (matAdd_neg_right A)] (matAdd_neg_right A)

def matScale_one_path (A : Mat n m) : Path (matScale 1 A) A :=
  Path.mk [Step.mk _ _ (matScale_one A)] (matScale_one A)

def matScale_zero_path (A : Mat n m) : Path (matScale 0 A) (zeroMat n m) :=
  Path.mk [Step.mk _ _ (matScale_zero A)] (matScale_zero A)

def matScale_add_path (c : Int) (A B : Mat n m) :
    Path (matScale c (matAdd A B)) (matAdd (matScale c A) (matScale c B)) :=
  Path.mk [Step.mk _ _ (matScale_add c A B)] (matScale_add c A B)

def matTrans_trans_path (A : Mat n m) : Path (matTrans (matTrans A)) A :=
  Path.mk [Step.mk _ _ (matTrans_trans A)] (matTrans_trans A)

def matTrans_add_path (A B : Mat n m) :
    Path (matTrans (matAdd A B)) (matAdd (matTrans A) (matTrans B)) :=
  Path.mk [Step.mk _ _ (matTrans_add A B)] (matTrans_add A B)

def matTrans_zero_path : Path (matTrans (zeroMat n m)) (zeroMat m n) :=
  Path.mk [Step.mk _ _ (matTrans_zero (n := n) (m := m))] (matTrans_zero (n := n) (m := m))

def matNeg_neg_path (A : Mat n m) : Path (matNeg (matNeg A)) A :=
  Path.mk [Step.mk _ _ (matNeg_neg A)] (matNeg_neg A)

def idMat_trans_path (n : Nat) : Path (matTrans (idMat n)) (idMat n) :=
  Path.mk [Step.mk _ _ (idMat_trans n)] (idMat_trans n)

end Export

/-! ## Path-algebra theorems -/

section PathAlgebra

variable {n m : Nat}

theorem matAdd_comm_symm_trans_toEq (A B : Mat n m) :
    (Path.trans (matAdd_comm_path A B)
      (Path.symm (matAdd_comm_path A B))).toEq = rfl := by
  simp

theorem congrArg_matAdd_comm_toEq (f : Mat n m → Nat) (A B : Mat n m) :
    (Path.congrArg f (matAdd_comm_path A B)).toEq =
      _root_.congrArg f (matAdd_comm A B) := rfl

theorem transport_matAdd_comm (P : Mat n m → Prop) (A B : Mat n m) (h : P (matAdd A B)) :
    Path.transport (matAdd_comm_path A B) h =
      (matAdd_comm A B ▸ h) := by
  simp [Path.transport, matAdd_comm_path]

theorem matAdd_assoc_step_count (A B C : Mat n m) :
    (matAdd_assoc_path A B C).steps.length = 1 := rfl

end PathAlgebra

end ComputationalPaths.Path.Algebra.MatrixPaths
