/-
# π₁(T²) ≃ ℤ × ℤ

This module packages the winding-number encode/decode data from `Torus.lean`
into a `SimpleEquiv` between `π₁(T²)` and `ℤ × ℤ`.
-/

import ComputationalPaths.Path.HIT.Torus
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

/-- `HasTorusLoopDecode` (raw loop normal forms) implies the π₁-level interface. -/
instance instHasTorusPiOneEncode [HasTorusLoopDecode.{u}] : HasTorusPiOneEncode.{u} where
  encode := torusEncode
  encode_torusDecode := torusEncode_torusDecode
  torusDecode_encode := torusDecode_torusEncode

/-- Build the raw loop encode/decode interface from the quotient-level one. -/
noncomputable def hasTorusLoopDecodeOfPiOneEncode [HasTorusPiOneEncode.{u}] :
    HasTorusLoopDecode.{u} where
  encodePath := fun p => torusPiOneEncode.{u} (Quot.mk _ p)
  encodePath_rweq := by
    intro p q hpq
    have hquot : (Quot.mk _ p : torusPiOne.{u}) = Quot.mk _ q :=
      Quot.sound hpq
    exact _root_.congrArg (torusPiOneEncode.{u}) hquot
  encodePath_torusDecodePath := by
    intro z
    -- `torusDecode z` is definitionally `Quot.mk _ (torusDecodePath z)`.
    simpa [torusDecode] using (torusPiOneEncode_torusDecode.{u} (z := z))
  torusLoop_rweq_decode := by
    intro p
    have hq :
        torusDecode.{u} (torusPiOneEncode.{u} (Quot.mk _ p)) =
          (Quot.mk _ p : torusPiOne.{u}) :=
      torusDecode_torusPiOneEncode (x := (Quot.mk _ p))
    have hq' :
        Quotient.mk (rwEqSetoid Torus torusBase torusBase)
            (torusDecodePath (torusPiOneEncode.{u} (Quot.mk _ p))) =
          Quotient.mk (rwEqSetoid Torus torusBase torusBase) p := by
      simpa [torusDecode] using hq
    have hr : RwEq (torusDecodePath (torusPiOneEncode.{u} (Quot.mk _ p))) p := by
      simpa using (Quotient.exact (s := rwEqSetoid Torus torusBase torusBase) hq')
    exact rweq_symm hr

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

