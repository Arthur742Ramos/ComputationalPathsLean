/-
# π₁(T²) ≃ ℤ × ℤ

This module packages the torus π₁ computation as a `SimpleEquiv`
between `π₁(T²)` and `ℤ × ℤ`.
-/

import ComputationalPaths.Path.HIT.Torus
import ComputationalPaths.Path.HIT.CircleStep
import ComputationalPaths.Path.Rewrite.SimpleEquiv

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path

open SimpleEquiv

universe u

/-- A discharge-friendly interface for `π₁(T²) ≃ ℤ × ℤ`.

Unlike `HasTorusLoopDecode`, this class only talks about the loop *quotient*
(`π₁`) rather than raw loop normal forms.  Downstream developments that only
need the fundamental group can depend on this weaker hypothesis.
-/
class HasTorusPiOneEncode : Type u where
  /-- Winding-number map `π₁(T²) → ℤ × ℤ`. -/
  encode : torusPiOne.{u} → Int × Int
  /-- Encoding after decoding is the identity on `ℤ × ℤ`. -/
  encode_torusDecode : ∀ z : Int × Int, encode (torusDecode.{u} z) = z
  /-- Decoding after encoding is the identity on `π₁(T²)`. -/
  torusDecode_encode : ∀ x : torusPiOne.{u}, torusDecode.{u} (encode x) = x

/-- Winding-number map specialised from `HasTorusPiOneEncode`. -/
@[simp] def torusPiOneEncode [HasTorusPiOneEncode.{u}] : torusPiOne.{u} → Int × Int :=
  HasTorusPiOneEncode.encode

@[simp] theorem torusPiOneEncode_torusDecode [HasTorusPiOneEncode.{u}] (z : Int × Int) :
    torusPiOneEncode.{u} (torusDecode.{u} z) = z :=
  HasTorusPiOneEncode.encode_torusDecode z

@[simp] theorem torusDecode_torusPiOneEncode [HasTorusPiOneEncode.{u}] (x : torusPiOne.{u}) :
    torusDecode.{u} (torusPiOneEncode.{u} x) = x :=
  HasTorusPiOneEncode.torusDecode_encode x

/-!
## Canonical instance from the circle π₁ computation

Because `Torus` is defined as `Circle × Circle`, we can construct the torus
π₁ encode/decode data from:
- the product fundamental group equivalence, and
- the circle π₁ encode/decode interface (`HasCirclePiOneEncode`).
-/
noncomputable instance instHasTorusPiOneEncode_ofCircle [HasCirclePiOneEncode.{u}] :
    HasTorusPiOneEncode.{u} where
  encode := fun x =>
    let yz := prodPiOneEncode (A := Circle.{u}) (B := Circle.{u})
      circleBase circleBase x
    (circlePiOneEncode.{u} yz.1, circlePiOneEncode.{u} yz.2)
  encode_torusDecode := by
    intro z
    -- Reduce to the product round-trip plus the circle round-trip.
    cases z with
    | mk m n =>
        simp [torusDecode, prodPiOne_encode_decode, -circlePiOneEncode, -circleDecode, -circleDecode_eq_concrete]
  torusDecode_encode := by
    intro x
    -- Reduce to the circle round-trip plus the product round-trip.
    -- First simplify away the circle encode/decode round-trips.
    simp [torusDecode, -circlePiOneEncode, -circleDecode, -circleDecode_eq_concrete]
    -- Then use the product round-trip, taking care of the `Prod` η-expansion.
    have heta :
        ((prodPiOneEncode circleBase circleBase x).fst, (prodPiOneEncode circleBase circleBase x).snd) =
          prodPiOneEncode circleBase circleBase x := by
      cases prodPiOneEncode circleBase circleBase x <;> rfl
    simpa [heta] using
      (prodPiOne_decode_encode (A := Circle.{u}) (B := Circle.{u}) circleBase circleBase x)

/-- Fundamental group of the torus is equivalent to `ℤ × ℤ`. -/
noncomputable def torusPiOneEquivIntProd [HasTorusPiOneEncode.{u}] :
    SimpleEquiv torusPiOne (Int × Int) where
  toFun := torusPiOneEncode.{u}
  invFun := torusDecode.{u}
  left_inv := by
    intro x
    simpa using (torusDecode_torusPiOneEncode (x := x))
  right_inv := by
    intro z
    simpa using (torusPiOneEncode_torusDecode (z := z))

end Path
end ComputationalPaths
