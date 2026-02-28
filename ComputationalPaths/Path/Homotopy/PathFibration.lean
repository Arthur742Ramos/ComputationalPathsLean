/-
# Path Fibration

The path-space fibration and related constructions.
-/

import ComputationalPaths.Path.Homotopy.PathSpaceFibration
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths.Path.Homotopy.PathFibration

open ComputationalPaths.Path
open ComputationalPaths.Path.PathSpaceFibration

universe u

noncomputable def loopSpaceEqToPath_refl {A : Type u} {a : A} :
    RwEq (loopSpaceEqToPath (A := A) (a := a) (liftEqRefl a)) (Path.refl a) := by
  change RwEq (Path.stepChain (rfl : a = a)) (Path.refl a)
  exact RwEq.step
    (ComputationalPaths.Path.Step.transport_refl_beta
      (A := PUnit) (B := fun _ : PUnit => A) (a := PUnit.unit) (x := a))

noncomputable def loopSpaceEqToPath_symm_trans_rweq {A : Type u} {a : A}
    (ℓ : LoopSpaceEq A a) :
    RwEq
      (Path.trans (Path.symm (loopSpaceEqToPath (A := A) (a := a) ℓ))
        (loopSpaceEqToPath (A := A) (a := a) ℓ))
      (Path.refl a) :=
  rweq_cmpA_inv_left (loopSpaceEqToPath (A := A) (a := a) ℓ)

noncomputable def pathSpaceFiberSeq_exact' (A : Type u) (a : A) :
    Fibration.IsExactAt (pathSpaceFiberSeq A a) :=
  pathSpaceFiberSeq_exact A a

theorem loopSpaceEquivFiber_roundtrip {A : Type u} (a : A)
    (x : PathSpaceFiber A a) (ℓ : LoopSpaceEq A a) :
    (loopSpaceEquivFiber A a).invFun ((loopSpaceEquivFiber A a).toFun x) = x ∧
      (loopSpaceEquivFiber A a).toFun ((loopSpaceEquivFiber A a).invFun ℓ) = ℓ := by
  exact ⟨(loopSpaceEquivFiber A a).left_inv x, (loopSpaceEquivFiber A a).right_inv ℓ⟩

end ComputationalPaths.Path.Homotopy.PathFibration
