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

/-- A discharge-friendly interface for `π₁(S¹) ≃ ℤ`.

Unlike `HasCircleLoopDecode`, this class only talks about the loop *quotient*
(`π₁`) rather than raw loop normal forms.  Downstream developments that only
need the fundamental group can depend on this weaker hypothesis.
-/
class HasCirclePiOneEncode : Type u where
  /-- Winding-number map `π₁(S¹) → ℤ`. -/
  encode : circlePiOne.{u} → Int
  /-- Encoding after decoding is the identity on integers. -/
  encode_circleDecode : ∀ z : Int, encode (circleDecode.{u} z) = z
  /-- Decoding after encoding is the identity on `π₁(S¹)`. -/
  circleDecode_encode : ∀ x : circlePiOne.{u}, circleDecode.{u} (encode x) = x

/-- Winding-number map specialised from `HasCirclePiOneEncode`. -/
@[simp] def circlePiOneEncode [HasCirclePiOneEncode.{u}] : circlePiOne.{u} → Int :=
  HasCirclePiOneEncode.encode

@[simp] theorem circlePiOneEncode_circleDecode [HasCirclePiOneEncode.{u}] (z : Int) :
    circlePiOneEncode.{u} (circleDecode.{u} z) = z :=
  HasCirclePiOneEncode.encode_circleDecode z

@[simp] theorem circleDecode_circlePiOneEncode [HasCirclePiOneEncode.{u}] (x : circlePiOne.{u}) :
    circleDecode.{u} (circlePiOneEncode.{u} x) = x :=
  HasCirclePiOneEncode.circleDecode_encode x

/-- `HasCircleLoopDecode` (raw loop normal forms) implies the π₁-level interface. -/
instance instHasCirclePiOneEncode [HasCircleLoopDecode.{u}] : HasCirclePiOneEncode.{u} where
  encode := circleEncode
  encode_circleDecode := circleEncode_circleDecode
  circleDecode_encode := circleDecode_circleEncode

noncomputable def circlePiOneEquivInt [HasCirclePiOneEncode.{u}] :
    SimpleEquiv (circlePiOne.{u}) Int where
  toFun := circlePiOneEncode.{u}
  invFun := circleDecode.{u}
  left_inv := by
    intro x
    simpa using (circleDecode_circlePiOneEncode (x := x))
  right_inv := by
    intro z
    simpa using (circlePiOneEncode_circleDecode (z := z))

@[simp] theorem circlePiOneEncode_decode [HasCirclePiOneEncode.{u}] (z : Int) :
    circlePiOneEncode.{u} (circleDecode.{u} z) = z :=
  circlePiOneEncode_circleDecode z

end Path
end ComputationalPaths
