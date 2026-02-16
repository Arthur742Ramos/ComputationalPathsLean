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

/-! ## Helper: explicit one-step `Path` (no `Path.ofEq`) -/

/-- A one-step `Path` with an explicit trace. -/
@[simp] def oneStep {A : Type u} {a b : A} (h : a = b) : Path a b :=
  Path.mk [Step.mk a b h] h

@[simp] theorem oneStep_toEq {A : Type u} {a b : A} (h : a = b) : (oneStep h).toEq = h := rfl

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
  · have h' : j ≠ i := by
        intro hji
        exact h hji.symm
    simp [matTrans, idMat, h, h']

end Transpose

/-! ## Domain language: objects, steps, paths (for add/neg/scale) -/

section Domain

variable {n m : Nat}

/-- Matrix expressions (add/neg/scale) over base matrices. -/
inductive MatObj (n m : Nat) : Type
  | base : Mat n m → MatObj n m
  | zero : MatObj n m
  | add : MatObj n m → MatObj n m → MatObj n m
  | neg : MatObj n m → MatObj n m
  | scale : Int → MatObj n m → MatObj n m

namespace MatObj

/-- Evaluate an expression to a concrete matrix. -/
def eval : MatObj n m → Mat n m
  | base A => A
  | zero => zeroMat n m
  | add A B => matAdd (eval A) (eval B)
  | neg A => matNeg (eval A)
  | scale c A => matScale c (eval A)

@[simp] theorem eval_base (A : Mat n m) : eval (MatObj.base A : MatObj n m) = A := rfl
@[simp] theorem eval_zero : eval (MatObj.zero : MatObj n m) = zeroMat n m := rfl
@[simp] theorem eval_add (A B : MatObj n m) : eval (MatObj.add A B) = matAdd (eval A) (eval B) := rfl
@[simp] theorem eval_neg (A : MatObj n m) : eval (MatObj.neg A) = matNeg (eval A) := rfl
@[simp] theorem eval_scale (c : Int) (A : MatObj n m) : eval (MatObj.scale c A) = matScale c (eval A) := rfl

end MatObj

/-- Elementary rewrite steps on matrix expressions. -/
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

/-- Semantic correctness of a step. -/
theorem eval_eq {A B : MatObj n m} : MatStep (n := n) (m := m) A B → MatObj.eval A = MatObj.eval B
  | addComm A B => by
      simp [MatObj.eval, matAdd_comm]
  | addAssoc A B C => by
      simp [MatObj.eval, matAdd_assoc]
  | addZeroR A => by
      simp [MatObj.eval, matAdd_zero_right]
  | addZeroL A => by
      simp [MatObj.eval, matAdd_zero_left]
  | addNegR A => by
      simp [MatObj.eval, matAdd_neg_right]
  | negNeg A => by
      simp [MatObj.eval, matNeg_neg]
  | scaleOne A => by
      simp [MatObj.eval, matScale_one]
  | scaleZero A => by
      simp [MatObj.eval, matScale_zero]
  | scaleAdd c A B => by
      simp [MatObj.eval, matScale_add]
  | scaleNeg c A => by
      simp [MatObj.eval, matScale_neg]
  | addCongL s C => by
      simp [MatObj.eval, eval_eq s]
  | addCongR C s => by
      simp [MatObj.eval, eval_eq s]
  | negCong s => by
      simp [MatObj.eval, eval_eq s]
  | scaleCong c s => by
      simp [MatObj.eval, eval_eq s]

/-- Interpret a step as a `Path` on evaluated matrices.

For congruence steps we use `Path.congrArg` over the recursively interpreted
sub-step.
-/
def toPath {A B : MatObj n m} : MatStep (n := n) (m := m) A B → Path (MatObj.eval A) (MatObj.eval B)
  | addComm A B => oneStep (eval_eq (addComm A B))
  | addAssoc A B C => oneStep (eval_eq (addAssoc A B C))
  | addZeroR A => oneStep (eval_eq (addZeroR A))
  | addZeroL A => oneStep (eval_eq (addZeroL A))
  | addNegR A => oneStep (eval_eq (addNegR A))
  | negNeg A => oneStep (eval_eq (negNeg A))
  | scaleOne A => oneStep (eval_eq (scaleOne A))
  | scaleZero A => oneStep (eval_eq (scaleZero A))
  | scaleAdd c A B => oneStep (eval_eq (scaleAdd c A B))
  | scaleNeg c A => oneStep (eval_eq (scaleNeg c A))
  | addCongL s C =>
      Path.congrArg (fun X => matAdd X (MatObj.eval C)) (toPath s)
  | addCongR C s =>
      Path.congrArg (fun X => matAdd (MatObj.eval C) X) (toPath s)
  | negCong s => Path.congrArg matNeg (toPath s)
  | scaleCong c s => Path.congrArg (matScale c) (toPath s)

end MatStep

/-- Paths generated from matrix steps. -/
inductive MatPath : MatObj n m → MatObj n m → Type
  | refl (A : MatObj n m) : MatPath A A
  | step {A B : MatObj n m} (s : MatStep (n := n) (m := m) A B) : MatPath A B
  | trans {A B C : MatObj n m} (p : MatPath A B) (q : MatPath B C) : MatPath A C
  | symm {A B : MatObj n m} (p : MatPath A B) : MatPath B A

namespace MatPath

/-- Interpret a generated path as a `Path` of evaluated matrices. -/
def toPath {A B : MatObj n m} : MatPath (n := n) (m := m) A B → Path (MatObj.eval A) (MatObj.eval B)
  | refl A => Path.refl _
  | step s => MatStep.toPath s
  | trans p q => Path.trans (toPath p) (toPath q)
  | symm p => Path.symm (toPath p)

/-- The underlying semantic equality of a generated path. -/
theorem toEq {A B : MatObj n m} (p : MatPath (n := n) (m := m) A B) : MatObj.eval A = MatObj.eval B :=
  (toPath p).toEq

/-- Round-trip semantic equality is reflexive. -/
theorem roundtrip_toEq {A B : MatObj n m} (p : MatPath (n := n) (m := m) A B) :
    (Path.trans (toPath p) (Path.symm (toPath p))).toEq = rfl := by
  simp

end MatPath

end Domain

/-! ## Exported `Path` witnesses (no `Path.ofEq`) -/

section Export

variable {n m : Nat}

def matAdd_comm_path (A B : Mat n m) : Path (matAdd A B) (matAdd B A) :=
  oneStep (matAdd_comm (n := n) (m := m) A B)

def matAdd_assoc_path (A B C : Mat n m) :
    Path (matAdd (matAdd A B) C) (matAdd A (matAdd B C)) :=
  oneStep (matAdd_assoc (n := n) (m := m) A B C)

def matAdd_zero_right_path (A : Mat n m) : Path (matAdd A (zeroMat n m)) A :=
  oneStep (matAdd_zero_right (n := n) (m := m) A)

def matAdd_zero_left_path (A : Mat n m) : Path (matAdd (zeroMat n m) A) A :=
  oneStep (matAdd_zero_left (n := n) (m := m) A)

def matAdd_neg_path (A : Mat n m) : Path (matAdd A (matNeg A)) (zeroMat n m) :=
  oneStep (matAdd_neg_right (n := n) (m := m) A)

def matScale_one_path (A : Mat n m) : Path (matScale 1 A) A :=
  oneStep (matScale_one (n := n) (m := m) A)

def matScale_zero_path (A : Mat n m) : Path (matScale 0 A) (zeroMat n m) :=
  oneStep (matScale_zero (n := n) (m := m) A)

def matScale_add_path (c : Int) (A B : Mat n m) :
    Path (matScale c (matAdd A B)) (matAdd (matScale c A) (matScale c B)) :=
  oneStep (matScale_add (n := n) (m := m) c A B)

def matTrans_trans_path (A : Mat n m) : Path (matTrans (matTrans A)) A :=
  oneStep (matTrans_trans (n := n) (m := m) A)

def matTrans_add_path (A B : Mat n m) :
    Path (matTrans (matAdd A B)) (matAdd (matTrans A) (matTrans B)) :=
  oneStep (matTrans_add (n := n) (m := m) A B)

def matTrans_zero_path : Path (matTrans (zeroMat n m)) (zeroMat m n) :=
  oneStep (matTrans_zero (n := n) (m := m))

def matNeg_neg_path (A : Mat n m) : Path (matNeg (matNeg A)) A :=
  oneStep (matNeg_neg (n := n) (m := m) A)

def idMat_trans_path (n : Nat) : Path (matTrans (idMat n)) (idMat n) :=
  oneStep (idMat_trans n)

end Export

/-! ## Path-algebra example theorems (genuine operations) -/

section PathAlgebra

variable {n m : Nat}

theorem matAdd_comm_symm_trans_toEq (A B : Mat n m) :
    (Path.trans (matAdd_comm_path (n := n) (m := m) A B)
      (Path.symm (matAdd_comm_path (n := n) (m := m) A B))).toEq = rfl := by
  simp

theorem congrArg_matAdd_comm_toEq {n m : Nat} (f : Mat n m → Nat) (A B : Mat n m) :
    (Path.congrArg f (matAdd_comm_path (n := n) (m := m) A B)).toEq =
      _root_.congrArg f (matAdd_comm (n := n) (m := m) A B) := by
  rfl

theorem transport_matAdd_comm {n m : Nat} (P : Mat n m → Prop) (A B : Mat n m) (h : P (matAdd A B)) :
    Path.transport (D := P) (matAdd_comm_path (n := n) (m := m) A B) h =
      (matAdd_comm (n := n) (m := m) A B ▸ h) := by
  simp [Path.transport, matAdd_comm_path, oneStep]

theorem matAdd_assoc_step_count (A B C : Mat n m) :
    (matAdd_assoc_path (n := n) (m := m) A B C).steps.length = 1 := by
  rfl

end PathAlgebra

end ComputationalPaths.Path.Algebra.MatrixPaths
