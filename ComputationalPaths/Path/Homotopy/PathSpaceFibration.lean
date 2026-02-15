/-
# Path Space Fibration

This module formalizes the based path space fibration

  Omega(X, a) -> P(X, a) -> X

using the propositional equality `a = x` as the path space.

## Key Results

- `PathSpace`: based path space `P(X, a)`
- `pathSpaceContr`: `P(X, a)` is contractible
- `loopSpaceEquivFiber`: the fiber over `a` is the loop space
- `pathSpaceFiberSeq`: the canonical fiber sequence

## References

- HoTT Book, Sections 2.1 and 8.1
- May, "A Concise Course in Algebraic Topology"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Homotopy.Truncation
import ComputationalPaths.Path.Homotopy.Loops

namespace ComputationalPaths
namespace Path
namespace PathSpaceFibration

open Truncation Fibration

universe u

/-! ## Equality lifts -/

/-- Lift a propositional equality into `Type` as explicit data. -/
inductive LiftEq {A : Type u} (a b : A) : Type u where
  | mk : (a = b) → LiftEq a b

/-- Extract the underlying propositional equality. -/
def LiftEq.toEq {A : Type u} {a b : A} : LiftEq a b → a = b
  | LiftEq.mk h => h

/-- Reflexivity in the lifted equality type. -/
def liftEqRefl {A : Type u} (a : A) : LiftEq a a :=
  LiftEq.mk rfl

@[simp] theorem liftEq_toEq_mk {A : Type u} {a b : A} (h : a = b) :
    (LiftEq.mk h : LiftEq a b).toEq = h := by
  sorry

@[simp] theorem liftEq_mk_toEq {A : Type u} {a b : A} (p : LiftEq a b) :
    LiftEq.mk p.toEq = p := by
  sorry

theorem liftEq_trans_assoc {A : Type u} {a b c d : A}
    (p : LiftEq a b) (q : LiftEq b c) (r : LiftEq c d) :
    Eq.trans (Eq.trans p.toEq q.toEq) r.toEq =
      Eq.trans p.toEq (Eq.trans q.toEq r.toEq) := by
  sorry

theorem liftEq_trans_refl_left {A : Type u} {a b : A} (p : LiftEq a b) :
    Eq.trans rfl p.toEq = p.toEq := by
  sorry

theorem liftEq_trans_refl_right {A : Type u} {a b : A} (p : LiftEq a b) :
    Eq.trans p.toEq rfl = p.toEq := by
  sorry

theorem liftEq_symm_trans {A : Type u} {a b : A} (p : LiftEq a b) :
    Eq.trans (Eq.symm p.toEq) p.toEq = rfl := by
  sorry

theorem liftEq_trans_symm {A : Type u} {a b : A} (p : LiftEq a b) :
    Eq.trans p.toEq (Eq.symm p.toEq) = rfl := by
  sorry

theorem liftEq_congrArg_comp {A B C : Type u} {a b : A}
    (f : A → B) (g : B → C) (p : LiftEq a b) :
    Path.congrArg (fun x => g (f x)) (Path.stepChain p.toEq) =
      Path.congrArg g (Path.congrArg f (Path.stepChain p.toEq)) := by
  sorry

/-! ## Path space -/

/-- Based path space `P(X, a)` implemented with propositional equality. -/
def PathSpace (A : Type u) (a : A) : Type u :=
  Σ x : A, LiftEq a x

/-- Endpoint projection from the path space to the base. -/
def pathSpaceProj {A : Type u} {a : A} : PathSpace A a → A :=
  Sigma.fst

/-- Basepoint in the path space. -/
def pathSpaceBase (A : Type u) (a : A) : PathSpace A a :=
  ⟨a, liftEqRefl a⟩

@[simp] theorem pathSpaceProj_mk {A : Type u} {a x : A} (p : LiftEq a x) :
    pathSpaceProj (A := A) (a := a) ⟨x, p⟩ = x := by
  sorry

@[simp] theorem pathSpaceProj_pathSpaceBase (A : Type u) (a : A) :
    pathSpaceProj (A := A) (a := a) (pathSpaceBase A a) = a := by
  sorry

/-! ## Contractibility -/

/-- The based path space is contractible. -/
def pathSpaceContr (A : Type u) (a : A) : IsContr (PathSpace A a) :=
  { center := pathSpaceBase A a
    contr := by
      intro x
      cases x with
      | mk x p =>
        cases p with
        | mk p =>
          cases p
          exact Path.refl _ }

theorem pathSpaceContr_center (A : Type u) (a : A) :
    (pathSpaceContr A a).center = pathSpaceBase A a := by
  sorry

/-! ## Loop space as a fiber -/

/-- Loop space defined as propositional loops at the basepoint. -/
abbrev LoopSpaceEq (A : Type u) (a : A) : Type u :=
  LiftEq a a

/-- Fiber of the path space projection over the basepoint. -/
abbrev PathSpaceFiber (A : Type u) (a : A) : Type u :=
  Fiber (pathSpaceProj (A := A) (a := a)) a

/-- The path space fiber is equivalent to the based loop space. -/
def loopSpaceEquivFiber (A : Type u) (a : A) :
    SimpleEquiv (PathSpaceFiber A a) (LoopSpaceEq A a) :=
  fiberEquivFamily (P := fun x => LiftEq a x) (b := a)

/-- Map from propositional loops to computational loops. -/
def loopSpaceEqToPath {A : Type u} {a : A} :
    LoopSpaceEq A a → LoopSpace A a :=
  fun p => Path.stepChain p.toEq

@[simp] theorem loopSpaceEqToPath_toEq {A : Type u} {a : A}
    (p : LoopSpaceEq A a) :
    (loopSpaceEqToPath (A := A) (a := a) p).toEq = p.toEq := rfl

theorem loopSpaceEqToPath_naturality {A B : Type u} (f : A → B) {a : A}
    (p : LoopSpaceEq A a) :
    Path.congrArg f (loopSpaceEqToPath (A := A) (a := a) p) =
      loopSpaceEqToPath (A := B) (a := f a)
        (LiftEq.mk (Path.congrArg f (loopSpaceEqToPath (A := A) (a := a) p)).toEq) := by
  sorry

theorem loopSpaceEquivFiber_left_inv (A : Type u) (a : A) (x : PathSpaceFiber A a) :
    (loopSpaceEquivFiber A a).invFun ((loopSpaceEquivFiber A a).toFun x) = x := by
  sorry

theorem loopSpaceEquivFiber_right_inv (A : Type u) (a : A) (y : LoopSpaceEq A a) :
    (loopSpaceEquivFiber A a).toFun ((loopSpaceEquivFiber A a).invFun y) = y := by
  sorry

/-! ## Fiber sequence -/

/-- The canonical path space fiber sequence `Omega -> P -> X`. -/
def pathSpaceFiberSeq (A : Type u) (a : A) :
    FiberSeq (LoopSpaceEq A a) (PathSpace A a) A :=
  canonicalFiberSeq (P := fun x => LiftEq a x) (b := a) (x₀ := liftEqRefl a)

def pathSpaceFiberSeq_exact (A : Type u) (a : A) :
    IsExactAt (pathSpaceFiberSeq A a) :=
  canonicalFiberSeq_exact (P := fun x => LiftEq a x) (b := a) (x₀ := liftEqRefl a)

@[simp] theorem pathSpaceFiberSeq_proj_baseE (A : Type u) (a : A) :
    (pathSpaceFiberSeq A a).proj (pathSpaceBase A a) = a := by
  sorry

end PathSpaceFibration
end Path
end ComputationalPaths
