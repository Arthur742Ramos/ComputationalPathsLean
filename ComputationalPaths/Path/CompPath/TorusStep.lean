/-
# π₁(T²) ≃ ℤ × ℤ

This module packages the torus π₁ computation as a `SimpleEquiv`
between `π₁(T²)` and `ℤ × ℤ`.
-/

import ComputationalPaths.Path.CompPath.Torus
import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.Rewrite.SimpleEquiv

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path
open CompPath
open SimpleEquiv

universe u

/-- A discharge-friendly interface for `π₁(T²) ≃ ℤ × ℤ`.

Unlike `HasTorusLoopDecode`, this class only talks about the loop *quotient*
(`π₁`) rather than raw loop normal forms.  Downstream developments that only
need the fundamental group can depend on this weaker hypothesis.
-/
class HasTorusPiOneEncode : Type u where
  /-- Winding-number map `π₁(T²) → ℤ × ℤ`. -/
  encode : torusPiOne → Int × Int
  /-- Encoding after decoding is the identity on `ℤ × ℤ`. -/
  encode_torusDecode : ∀ z : Int × Int, encode (torusDecode z) = z
  /-- Decoding after encoding is the identity on `π₁(T²)`. -/
  torusDecode_encode : ∀ x : torusPiOne, torusDecode (encode x) = x

/-- Winding-number map specialised from `HasTorusPiOneEncode`. -/
@[simp] def torusPiOneEncode [HasTorusPiOneEncode] : torusPiOne → Int × Int :=
  HasTorusPiOneEncode.encode

@[simp] theorem torusPiOneEncode_torusDecode [HasTorusPiOneEncode] (z : Int × Int) :
    torusPiOneEncode (torusDecode z) = z :=
  HasTorusPiOneEncode.encode_torusDecode z

@[simp] theorem torusDecode_torusPiOneEncode [HasTorusPiOneEncode] (x : torusPiOne) :
    torusDecode (torusPiOneEncode x) = x :=
  HasTorusPiOneEncode.torusDecode_encode x

/-!
## Canonical instance from the circle π₁ computation

Because `Torus` is defined as `Circle × Circle`, we can construct the torus
π₁ encode/decode data from:
- the product fundamental group equivalence, and
- the circle π₁ encode/decode interface (`HasCirclePiOneEncode`).
-/
noncomputable instance instHasTorusPiOneEncode_ofCircle :
    HasTorusPiOneEncode.{u} where
  encode := fun x =>
    (circlePiOneEncode x.1, circlePiOneEncode x.2)
  encode_torusDecode := by
    intro z
    cases z
    simp only [torusDecode, circlePiOneEncode_circleDecode]
  torusDecode_encode := by
    intro x
    cases x
    simp only [torusDecode, circleDecode_circlePiOneEncode]



/-- Fundamental group of the torus is equivalent to `ℤ × ℤ`. -/
noncomputable def torusPiOneEquivIntProd [HasTorusPiOneEncode] :
    SimpleEquiv torusPiOne (Int × Int) where
  toFun := torusPiOneEncode
  invFun := torusDecode
  left_inv := by
    intro x
    simpa using (torusDecode_torusPiOneEncode (x := x))
  right_inv := by
    intro z
    simpa using (torusPiOneEncode_torusDecode (z := z))

end Path
end ComputationalPaths
