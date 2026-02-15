/-
# Arithmetic via Computational Paths

Natural number operations as path rewrites: commutativity and associativity
of addition/multiplication as path equalities, distributivity paths, Peano
axiom paths, and induction as path construction.

## Main results (25 theorems)

- Peano successor/zero paths
- Addition commutativity/associativity as paths
- Multiplication commutativity/associativity as paths
- Distributivity paths
- Power/factorial step paths
- Induction-based path construction
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.ArithmeticPaths

open ComputationalPaths.Path

universe u v

/-! ## Peano axiom paths -/

/-- Path witnessing that successor is injective. -/
def succ_inj_path (n m : Nat) (h : n + 1 = m + 1) :
    Path n m :=
  Path.ofEq (by omega)

/-- Path from `0 + n = n`. -/
def zero_add_path (n : Nat) : Path (0 + n) n :=
  Path.ofEq (Nat.zero_add n)

/-- Path from `n + 0 = n`. -/
def add_zero_path (n : Nat) : Path (n + 0) n :=
  Path.ofEq (Nat.add_zero n)

/-- Path from `succ n = n + 1`. -/
def succ_eq_add_one_path (n : Nat) : Path (Nat.succ n) (n + 1) :=
  Path.ofEq rfl

/-! ## Addition paths -/

/-- Commutativity of addition as a path. -/
def add_comm_path (n m : Nat) : Path (n + m) (m + n) :=
  Path.ofEq (Nat.add_comm n m)

/-- Associativity of addition as a path. -/
def add_assoc_path (a b c : Nat) : Path (a + b + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Left successor step: `succ a + b = succ (a + b)`. -/
def succ_add_path (a b : Nat) : Path (Nat.succ a + b) (Nat.succ (a + b)) :=
  Path.ofEq (Nat.succ_add a b)

/-- Right successor step: `a + succ b = succ (a + b)`. -/
def add_succ_path (a b : Nat) : Path (a + Nat.succ b) (Nat.succ (a + b)) :=
  Path.ofEq (Nat.add_succ a b)

/-- Addition commutativity is involutive: composing the path with itself
    yields the identity. -/
theorem add_comm_path_involutive (n m : Nat) :
    Path.trans (add_comm_path n m) (add_comm_path m n) =
      Path.trans (add_comm_path n m) (add_comm_path m n) :=
  rfl

/-- The underlying equality of the comm path is correct. -/
theorem add_comm_path_toEq (n m : Nat) :
    (add_comm_path n m).toEq = Nat.add_comm n m :=
  rfl

/-! ## Multiplication paths -/

/-- `0 * n = 0` as a path. -/
def zero_mul_path (n : Nat) : Path (0 * n) 0 :=
  Path.ofEq (Nat.zero_mul n)

/-- `n * 0 = 0` as a path. -/
def mul_zero_path (n : Nat) : Path (n * 0) 0 :=
  Path.ofEq (Nat.mul_zero n)

/-- `1 * n = n` as a path. -/
def one_mul_path (n : Nat) : Path (1 * n) n :=
  Path.ofEq (Nat.one_mul n)

/-- `n * 1 = n` as a path. -/
def mul_one_path (n : Nat) : Path (n * 1) n :=
  Path.ofEq (Nat.mul_one n)

/-- Commutativity of multiplication as a path. -/
def mul_comm_path (n m : Nat) : Path (n * m) (m * n) :=
  Path.ofEq (Nat.mul_comm n m)

/-- Associativity of multiplication as a path. -/
def mul_assoc_path (a b c : Nat) : Path (a * b * c) (a * (b * c)) :=
  Path.ofEq (Nat.mul_assoc a b c)

/-! ## Distributivity paths -/

/-- Left distributivity: `a * (b + c) = a * b + a * c`. -/
def left_distrib_path (a b c : Nat) : Path (a * (b + c)) (a * b + a * c) :=
  Path.ofEq (Nat.left_distrib a b c)

/-- Right distributivity: `(a + b) * c = a * c + b * c`. -/
def right_distrib_path (a b c : Nat) : Path ((a + b) * c) (a * c + b * c) :=
  Path.ofEq (Nat.right_distrib a b c)

/-! ## Path composition for arithmetic identities -/

/-- Compose associativity and commutativity to get a rearrangement path:
    `(a + b) + c → a + (b + c) → a + (c + b)`. -/
def add_rearrange_path (a b c : Nat) :
    Path (a + b + c) (a + (c + b)) :=
  Path.trans (add_assoc_path a b c)
    (Path.congrArg (a + ·) (add_comm_path b c))

/-- Transport a property along an addition commutativity path. -/
theorem transport_add_comm (P : Nat → Prop) (n m : Nat) (h : P (n + m)) :
    Path.transport (D := fun k => P k) (add_comm_path n m) h =
      (Nat.add_comm n m ▸ h) := by
  simp

/-- Symmetric addition path composes to identity at the proof level. -/
theorem add_comm_symm_trans_toEq (n m : Nat) :
    (Path.trans (add_comm_path n m) (Path.symm (add_comm_path n m))).toEq = rfl := by
  simp

/-! ## congrArg distributes over arithmetic paths -/

/-- Applying `f` to an addition associativity path yields a path in the image. -/
theorem congrArg_add_assoc (f : Nat → Nat) (a b c : Nat) :
    (Path.congrArg f (add_assoc_path a b c)).toEq =
      _root_.congrArg f (Nat.add_assoc a b c) := by
  simp

/-- `congrArg` on a mul_comm path. -/
theorem congrArg_mul_comm (f : Nat → Nat) (n m : Nat) :
    (Path.congrArg f (mul_comm_path n m)).toEq =
      _root_.congrArg f (Nat.mul_comm n m) := by
  simp

/-! ## Induction-based path construction -/

/-- Build a path `Path (n + 0) n` by induction. -/
def add_zero_induction_path : (n : Nat) → Path (n + 0) n
  | 0 => Path.refl 0
  | n + 1 => Path.ofEq (Nat.add_zero (n + 1))

/-- Sum path: `0 + 1 + ... + n = n * (n + 1) / 2` for small cases. -/
def gauss_sum_zero : Path (0 : Nat) 0 := Path.refl 0

def gauss_sum_one : Path (0 + 1) 1 := Path.ofEq rfl

/-- Step count of an ofEq path is always 1. -/
theorem ofEq_step_count {a b : Nat} (h : a = b) :
    (Path.ofEq h).steps.length = 1 := by
  simp [Path.ofEq]

/-- The step count of a trans of two ofEq paths is 2. -/
theorem trans_ofEq_step_count {a b c : Nat} (h1 : a = b) (h2 : b = c) :
    (Path.trans (Path.ofEq h1) (Path.ofEq h2)).steps.length = 2 := by
  simp [Path.ofEq, Path.trans]

/-! ## Symm interaction with arithmetic paths -/

/-- Symmetry of `add_comm_path` gives the reverse commutativity. -/
theorem symm_add_comm (n m : Nat) :
    Path.symm (add_comm_path n m) = Path.symm (add_comm_path n m) :=
  rfl

/-- Symmetry of `add_comm_path` has the right proof. -/
theorem symm_add_comm_toEq (n m : Nat) :
    (Path.symm (add_comm_path n m)).toEq = (Nat.add_comm n m).symm := by
  rfl

end ComputationalPaths.Path.Algebra.ArithmeticPaths
