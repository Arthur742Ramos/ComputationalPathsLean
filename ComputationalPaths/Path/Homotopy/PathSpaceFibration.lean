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
noncomputable def LiftEq.toEq {A : Type u} {a b : A} : LiftEq a b → a = b
  | LiftEq.mk h => h

/-- Reflexivity in the lifted equality type. -/
noncomputable def liftEqRefl {A : Type u} (a : A) : LiftEq a a :=
  LiftEq.mk rfl






theorem liftEq_symm_trans {A : Type u} {a b : A} (p : LiftEq a b) :
    Eq.trans (Eq.symm p.toEq) p.toEq = rfl := by
  rfl

theorem liftEq_trans_symm {A : Type u} {a b : A} (p : LiftEq a b) :
    Eq.trans p.toEq (Eq.symm p.toEq) = rfl := by
  rfl


/-! ## Path space -/

/-- Based path space `P(X, a)` implemented with propositional equality. -/
noncomputable def PathSpace (A : Type u) (a : A) : Type u :=
  Σ x : A, LiftEq a x

/-- Endpoint projection from the path space to the base. -/
noncomputable def pathSpaceProj {A : Type u} {a : A} : PathSpace A a → A :=
  Sigma.fst

/-- Basepoint in the path space. -/
noncomputable def pathSpaceBase (A : Type u) (a : A) : PathSpace A a :=
  ⟨a, liftEqRefl a⟩



/-! ## Contractibility -/

/-- The based path space is contractible. -/
noncomputable def pathSpaceContr (A : Type u) (a : A) : IsContr (PathSpace A a) :=
  { center := pathSpaceBase A a
    contr := by
      intro x
      cases x with
      | mk x p =>
        cases p with
        | mk p =>
          cases p
          exact Path.refl _ }


/-! ## Loop space as a fiber -/

/-- Loop space defined as propositional loops at the basepoint. -/
abbrev LoopSpaceEq (A : Type u) (a : A) : Type u :=
  LiftEq a a

/-- Fiber of the path space projection over the basepoint. -/
abbrev PathSpaceFiber (A : Type u) (a : A) : Type u :=
  Fiber (pathSpaceProj (A := A) (a := a)) a

/-- The path space fiber is equivalent to the based loop space. -/
noncomputable def loopSpaceEquivFiber (A : Type u) (a : A) :
    SimpleEquiv (PathSpaceFiber A a) (LoopSpaceEq A a) :=
  fiberEquivFamily (P := fun x => LiftEq a x) (b := a)

/-- Map from propositional loops to computational loops. -/
noncomputable def loopSpaceEqToPath {A : Type u} {a : A} :
    LoopSpaceEq A a → LoopSpace A a :=
  fun p => Path.stepChain p.toEq

@[simp] theorem loopSpaceEqToPath_toEq {A : Type u} {a : A}
    (p : LoopSpaceEq A a) :
    (loopSpaceEqToPath (A := A) (a := a) p).toEq = p.toEq := rfl




/-! ## Fiber sequence -/

/-- The canonical path space fiber sequence `Omega -> P -> X`. -/
noncomputable def pathSpaceFiberSeq (A : Type u) (a : A) :
    FiberSeq (LoopSpaceEq A a) (PathSpace A a) A :=
  canonicalFiberSeq (P := fun x => LiftEq a x) (b := a) (x₀ := liftEqRefl a)

noncomputable def pathSpaceFiberSeq_exact (A : Type u) (a : A) :
    IsExactAt (pathSpaceFiberSeq A a) :=
  canonicalFiberSeq_exact (P := fun x => LiftEq a x) (b := a) (x₀ := liftEqRefl a)


end PathSpaceFibration
end Path
end ComputationalPaths
