/-
# π₁(S¹) ≃ ℤ

This module packages the winding-number encode/decode data from `Circle.lean`
into a `SimpleEquiv` between `π₁(S¹)` and `ℤ`.
-/

import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.Rewrite.SimpleEquiv

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path

open SimpleEquiv

universe u

noncomputable def circlePiOneEquivInt [HasCircleLoopDecode.{u}] :
    SimpleEquiv (circlePiOne.{u}) Int where
  toFun := circleWindingNumber
  invFun := circleDecode
  left_inv := by
    intro x
    change circleDecode (circleEncode x) = x
    exact circleDecode_circleEncode (x := x)
  right_inv := by
    intro z
    change circleEncode (circleDecode z) = z
    exact circleEncode_circleDecode (z := z)

@[simp] theorem circleWindingNumber_decode [HasCircleLoopDecode.{u}] (z : Int) :
    circleWindingNumber (circleDecode z) = z := by
  change circleEncode (circleDecode z) = z
  exact circleEncode_circleDecode (z := z)

end Path
end ComputationalPaths
