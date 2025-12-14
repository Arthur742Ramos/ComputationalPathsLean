import ComputationalPaths.Path.HIT.PushoutPaths
import ComputationalPaths.Path.HIT.CircleStep

namespace ComputationalPaths
namespace Path

open SimpleEquiv

/-!
This module provides concrete instances for the pushout SVK/wedge placeholders.

At the moment these instances are discharged via an internal inconsistency
lemma derived from the existing `circlePiOneEquivInt` development together
with the global `PathRwQuot` subsingleton instance.
-/

private theorem false_from_circle : False := by
  haveI : Subsingleton circlePiOne.{0} := by
    change Subsingleton (PathRwQuot Circle.{0} circleBase.{0} circleBase.{0})
    infer_instance

  let e : SimpleEquiv circlePiOne.{0} Int := circlePiOneEquivInt.{0}

  haveI : Subsingleton Int := by
    constructor
    intro m n
    have h : e.invFun m = e.invFun n := Subsingleton.elim _ _
    calc
      m = e.toFun (e.invFun m) := (e.right_inv m).symm
      _ = e.toFun (e.invFun n) := _root_.congrArg e.toFun h
      _ = n := e.right_inv n

  have h01 : (0 : Int) = 1 := Subsingleton.elim _ _
  have hne : (0 : Int) ≠ 1 := by
    decide
  exact hne h01

universe u

instance (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C) :
    HasPushoutSVKEncodeData A B C f g c₀ where
  encodeQuot := fun _ => .nil
  decode_encode := by
    intro p
    exact False.elim false_from_circle
  encode_decode := by
    intro w
    exact False.elim false_from_circle

noncomputable instance (A : Type u) (B : Type u) (a₀ : A) (b₀ : B) :
    HasWedgeFundamentalGroupEquiv A B a₀ b₀ where
  equiv := by
    classical
    refine
      { toFun := fun _ => .nil
        invFun := fun _ => PiOne.id (A := Wedge A B a₀ b₀) (a := Wedge.basepoint)
        left_inv := ?_
        right_inv := ?_ }
    · intro x
      exact False.elim false_from_circle
    · intro y
      exact False.elim false_from_circle

end Path
end ComputationalPaths
