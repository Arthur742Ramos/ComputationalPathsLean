/- 
# Deep suspension constructions

This module deepens suspension development in `ComputationalPaths` with explicit
computational-path witnesses (`Path.trans`, `Step`, `RwEq`) and reuses
existing suspension-circle and loop-suspension adjunction infrastructure.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.CompPath.SuspensionSpace
import ComputationalPaths.Path.CompPath.SuspensionCircle
import ComputationalPaths.Path.Homotopy.LoopSpaceAdjunction
import ComputationalPaths.Path.Homotopy.LoopSpaceSuspension
namespace ComputationalPaths
namespace HIT
namespace SuspensionDeep

open ComputationalPaths.Path
open ComputationalPaths.Path.CompPath
open ComputationalPaths.Path.SuspensionLoop
open ComputationalPaths.Path.Homotopy.LoopSpaceAdjunction
open ComputationalPaths.Path.Homotopy.LoopSpaceSuspension

universe u

/-! ## 1) Suspension via computational paths -/

abbrev Susp (A : Type u) : Type u := SuspensionCompPath A

noncomputable abbrev north (A : Type u) : Susp A :=
  SuspensionCompPath.north (X := A)

noncomputable abbrev south (A : Type u) : Susp A :=
  SuspensionCompPath.south (X := A)

noncomputable abbrev merid {A : Type u} (a : A) : Path (north A) (south A) :=
  SuspensionCompPath.merid (X := A) a

/-- A suspension loop written as an explicit `Path.trans` chain. -/
noncomputable def meridLoop {A : Type u} (a b : A) : Path (north A) (north A) :=
  Path.trans (merid (A := A) a) (Path.symm (merid (A := A) b))

noncomputable def meridLoop_rightUnit_rwEq {A : Type u} (a b : A) :
    RwEq
      (Path.trans (meridLoop (A := A) a b) (Path.refl (north A)))
      (meridLoop (A := A) a b) :=
  rweq_of_step (Step.trans_refl_right (meridLoop (A := A) a b))

noncomputable def meridLoop_cancel_rwEq {A : Type u} (a : A) :
    RwEq (meridLoop (A := A) a a) (Path.refl (north A)) := by
  simpa [meridLoop] using
    (rweq_of_step (Step.trans_symm (merid (A := A) a)))

/-! ## 2) `Susp(S¹)` has trivial `π₁` -/

abbrev SuspS1 : Type := SuspensionCircleCompPath

theorem suspS1_pi1_trivial :
    ∀ α : π₁(SuspS1, (suspensionCircleBasepoint : SuspS1)),
      α = Quot.mk _ (Path.refl _) := by
  intro α
  simpa [SuspS1] using suspensionCircleCompPath_pi1_trivial (α := α)

noncomputable def suspS1_pi1_equiv_unit :
    SimpleEquiv (π₁(SuspS1, (suspensionCircleBasepoint : SuspS1))) Unit := by
  simpa [SuspS1] using suspensionCircleCompPath_pi1_equiv_unit

/-! ## 3) Freeness: suspension is left adjoint to loop space (path level) -/

noncomputable def susp_leftAdjoint_loop
    (X Y : Pointed) :
    PathSimpleEquiv
      (PointedMap (sigmaPointed X) Y)
      (PointedMap X (omegaEqPointed Y)) :=
  loopSpaceSuspensionAdjunction X Y

noncomputable def susp_leftAdjoint_loop_leftInv (X Y : Pointed)
    (f : PointedMap (sigmaPointed X) Y) :
    Path ((susp_leftAdjoint_loop X Y).invFun ((susp_leftAdjoint_loop X Y).toFun f)) f :=
  (susp_leftAdjoint_loop X Y).left_inv f

noncomputable def susp_leftAdjoint_loop_rightInv (X Y : Pointed)
    (g : PointedMap X (omegaEqPointed Y)) :
    Path ((susp_leftAdjoint_loop X Y).toFun ((susp_leftAdjoint_loop X Y).invFun g)) g :=
  (susp_leftAdjoint_loop X Y).right_inv g

/-! ## 4) Iterated suspension `Σⁿ(S⁰) = Sⁿ` with explicit trans chains -/

inductive Sphere0 : Type
  | left
  | right
deriving DecidableEq, Repr

noncomputable def SphereN : Nat → Type
  | 0 => Sphere0
  | Nat.succ n => Susp (SphereN n)

theorem sigmaPowS0_eq_sphereN (n : Nat) :
    iterSusp n Sphere0 = SphereN n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simpa [iterSusp, SphereN, ih]

noncomputable abbrev sphereNorth (n : Nat) : SphereN (Nat.succ n) := north (SphereN n)

noncomputable abbrev sphereSouth (n : Nat) : SphereN (Nat.succ n) := south (SphereN n)

noncomputable abbrev sphereMerid (n : Nat) (x : SphereN n) :
    Path (sphereNorth n) (sphereSouth n) :=
  merid (A := SphereN n) x

/-- The standard suspension loop on `Sⁿ` as a trans/symm chain in `Sⁿ⁺¹`. -/
noncomputable def sphereMeridChain (n : Nat) (x y : SphereN n) :
    Path (sphereNorth n) (sphereNorth n) :=
  Path.trans (sphereMerid n x) (Path.symm (sphereMerid n y))

noncomputable def sphereMeridChain_rightUnit_rwEq (n : Nat) (x y : SphereN n) :
    RwEq
      (Path.trans (sphereMeridChain n x y) (Path.refl (sphereNorth n)))
      (sphereMeridChain n x y) :=
  rweq_of_step (Step.trans_refl_right (sphereMeridChain n x y))

noncomputable def sphereMeridChain_cancel_rwEq (n : Nat) (x : SphereN n) :
    RwEq (sphereMeridChain n x x) (Path.refl (sphereNorth n)) := by
  simpa [sphereMeridChain] using
    (rweq_of_step (Step.trans_symm (sphereMerid n x)))

end SuspensionDeep
end HIT
end ComputationalPaths
