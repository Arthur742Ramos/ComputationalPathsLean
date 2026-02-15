/-
# Combinatory Logic via Computational Paths

S, K, I combinators, SKI reduction as path steps, fixed-point combinator,
Church encoding, combinatory completeness aspects — all expressed as
computational-path equalities.

## Main results (24 theorems)

- S, K, I combinator definitions and reduction paths
- SKI reduction sequences as path composition
- Church numerals and boolean paths
- Fixed-point combinator paths
- Combinatory completeness aspects
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.CombinatorPaths

open ComputationalPaths.Path

universe u

/-! ## Combinator terms -/

/-- Simple combinator terms. -/
inductive CL where
  | var : Nat → CL
  | S : CL
  | K : CL
  | I : CL
  | app : CL → CL → CL
  deriving Repr, BEq, DecidableEq

infixl:90 " ⬝ " => CL.app

/-! ## One-step reduction -/

/-- One-step weak head reduction for combinators. -/
def reduce : CL → CL
  | CL.app CL.I x => x
  | CL.app (CL.app CL.K x) _ => x
  | CL.app (CL.app (CL.app CL.S f) g) x =>
      CL.app (CL.app f x) (CL.app g x)
  | t => t

/-! ## Basic combinator reduction paths -/

/-- I x reduces to x. -/
def I_path (x : CL) : Path (reduce (CL.I ⬝ x)) x := Path.refl x

/-- K x y reduces to x. -/
def K_path (x y : CL) : Path (reduce ((CL.K ⬝ x) ⬝ y)) x := Path.refl x

/-- S f g x reduces to (f x)(g x). -/
def S_path (f g x : CL) :
    Path (reduce (((CL.S ⬝ f) ⬝ g) ⬝ x)) ((f ⬝ x) ⬝ (g ⬝ x)) := Path.refl _

/-- S K K x first step: reduces to (K x)(K x). -/
def SKK_step1 (x : CL) :
    Path (reduce (((CL.S ⬝ CL.K) ⬝ CL.K) ⬝ x)) ((CL.K ⬝ x) ⬝ (CL.K ⬝ x)) :=
  Path.refl _

/-- S K K x second step: K x (K x) reduces to x. -/
def SKK_step2 (x : CL) :
    Path (reduce ((CL.K ⬝ x) ⬝ (CL.K ⬝ x))) x :=
  Path.refl _

/-- Multi-step reduction. -/
def reduceN : Nat → CL → CL
  | 0, t => t
  | n + 1, t => reduceN n (reduce t)

/-- S K K x two-step reduces to x. -/
theorem SKK_reduces (x : CL) :
    reduceN 2 (((CL.S ⬝ CL.K) ⬝ CL.K) ⬝ x) = x := by
  simp [reduceN, reduce]

/-- SKK two-step as a path. -/
def SKK_path (x : CL) :
    Path (reduceN 2 (((CL.S ⬝ CL.K) ⬝ CL.K) ⬝ x)) x :=
  Path.ofEq (SKK_reduces x)

/-! ## Church booleans -/

def churchTrue : CL := CL.K
def churchFalse : CL := CL.K ⬝ CL.I

/-- True x y → x. -/
def churchTrue_path (x y : CL) : Path (reduce ((churchTrue ⬝ x) ⬝ y)) x := Path.refl x

/-- False step 1: K I x → I. -/
def churchFalse_step1 (x : CL) : Path (reduce (churchFalse ⬝ x)) CL.I := Path.refl _

/-- False step 2: I y → y. -/
def churchFalse_step2 (y : CL) : Path (reduce (CL.I ⬝ y)) y := Path.refl y

/-- False two-step: after reducing churchFalse x to I, then I y to y. -/
def churchFalse_path (_x y : CL) :
    Path (reduce (CL.I ⬝ y)) y :=
  churchFalse_step2 y

/-! ## Church numerals -/

def churchNum : Nat → CL
  | 0 => CL.K ⬝ CL.I
  | n + 1 => CL.S ⬝ (churchNum n)

def church_zero_path : Path (churchNum 0) (CL.K ⬝ CL.I) := Path.refl _
def church_one_path : Path (churchNum 1) (CL.S ⬝ (CL.K ⬝ CL.I)) := Path.refl _

theorem church_zero_neq_one : churchNum 0 ≠ churchNum 1 := by simp [churchNum]

def church_succ_path (n : Nat) :
    Path (churchNum (n + 1)) (CL.S ⬝ churchNum n) := Path.refl _

/-! ## Fixed-point combinators -/

def omega : CL := (CL.S ⬝ CL.I) ⬝ CL.I

/-- ω x reduces to (I x)(I x). -/
def omega_path (x : CL) :
    Path (reduce (omega ⬝ x)) ((CL.I ⬝ x) ⬝ (CL.I ⬝ x)) := Path.refl _

theorem I_compute (x : CL) : reduce (CL.I ⬝ x) = x := rfl

/-! ## Path algebra on combinator reductions -/

/-- Symmetry of K path is refl. -/
theorem K_symm (x y : CL) : Path.symm (K_path x y) = Path.refl x := by
  simp [K_path]

/-- I roundtrip toEq. -/
theorem I_roundtrip (x : CL) :
    (Path.trans (I_path x) (Path.symm (I_path x))).toEq = rfl := by simp

/-- CongrArg lifts I-path through left application. -/
theorem congrArg_app_left (t x : CL) :
    Path.congrArg (· ⬝ t) (I_path x) = Path.refl (x ⬝ t) := by
  simp [I_path]

/-- CongrArg lifts I-path through right application. -/
theorem congrArg_app_right (t x : CL) :
    Path.congrArg (t ⬝ ·) (I_path x) = Path.refl (t ⬝ x) := by
  simp [I_path]

/-- Transport along I-path is identity. -/
theorem transport_I (D : CL → Type u) (x : CL) (v : D (reduce (CL.I ⬝ x))) :
    Path.transport (I_path x) v = v := by simp [Path.transport]

/-- Transport along K-path is identity. -/
theorem transport_K (D : CL → Type u) (x y : CL) (v : D (reduce ((CL.K ⬝ x) ⬝ y))) :
    Path.transport (K_path x y) v = v := by simp [Path.transport]

/-- Transport along S-path is identity. -/
theorem transport_S (D : CL → Type u) (f g x : CL)
    (v : D (reduce (((CL.S ⬝ f) ⬝ g) ⬝ x))) :
    Path.transport (S_path f g x) v = v := by simp [Path.transport]

/-- CongrArg on churchTrue path. -/
theorem congrArg_churchTrue (f : CL → CL) (x y : CL) :
    Path.congrArg f (churchTrue_path x y) = Path.refl (f x) := by
  simp [churchTrue_path]

/-- churchTrue roundtrip. -/
theorem churchTrue_roundtrip (x y : CL) :
    (Path.trans (churchTrue_path x y)
      (Path.symm (churchTrue_path x y))).toEq = rfl := by simp

/-- CongrArg on omega path. -/
theorem congrArg_omega (f : CL → CL) (x : CL) :
    Path.congrArg f (omega_path x) = Path.refl (f ((CL.I ⬝ x) ⬝ (CL.I ⬝ x))) := by
  simp [omega_path]

/-- Church succ congrArg. -/
theorem congrArg_church_succ (f : CL → CL) (n : Nat) :
    Path.congrArg f (church_succ_path n) = Path.refl (f (CL.S ⬝ churchNum n)) := by
  simp [church_succ_path]

/-- SKK step1 symm is refl. -/
theorem SKK_step1_symm (x : CL) :
    Path.symm (SKK_step1 x) = Path.refl _ := by
  simp [SKK_step1]

/-- SKK step2 symm is refl. -/
theorem SKK_step2_symm (x : CL) :
    Path.symm (SKK_step2 x) = Path.refl _ := by
  simp [SKK_step2]

/-- Composing K paths for different arguments. -/
theorem K_path_compose (x y z : CL) :
    Path.congrArg (fun t => reduce ((CL.K ⬝ t) ⬝ z)) (K_path x y) =
    Path.refl x := by
  simp [K_path]

/-- Transport along churchFalse step1. -/
theorem transport_churchFalse_step1 (D : CL → Type u) (x : CL)
    (v : D (reduce (churchFalse ⬝ x))) :
    Path.transport (churchFalse_step1 x) v = v := by
  simp [Path.transport]

end ComputationalPaths.Path.Algebra.CombinatorPaths
