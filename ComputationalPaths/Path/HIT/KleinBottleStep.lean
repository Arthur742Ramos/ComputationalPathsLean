/-
# π₁(K) ≃ ℤ × ℤ

This module packages the normal-form encode/decode data from `KleinBottle.lean`
into a `SimpleEquiv` between `π₁(K)` and `ℤ × ℤ` (normal-form coordinates).
-/

import ComputationalPaths.Path.HIT.KleinBottle
import ComputationalPaths.Path.Rewrite.SimpleEquiv

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path

open SimpleEquiv

universe u

/-- A discharge-friendly interface for `π₁(K) ≃ ℤ × ℤ`.

Unlike `HasKleinLoopDecode`, this class only talks about the loop *quotient*
(`π₁`) rather than raw loop normal forms. Downstream developments that only need
the fundamental group can depend on this weaker hypothesis.
-/
class HasKleinPiOneEncode : Type u where
  /-- Normal-form coordinate map `π₁(K) → ℤ × ℤ`. -/
  encode : kleinPiOne.{u} → Int × Int
  /-- Encoding after decoding is the identity on `ℤ × ℤ`. -/
  encode_kleinDecode : ∀ z : Int × Int, encode (kleinDecode.{u} z) = z
  /-- Decoding after encoding is the identity on `π₁(K)`. -/
  kleinDecode_encode : ∀ x : kleinPiOne.{u}, kleinDecode.{u} (encode x) = x

/-- Coordinate map specialised from `HasKleinPiOneEncode`. -/
@[simp] def kleinPiOneEncode [HasKleinPiOneEncode.{u}] : kleinPiOne.{u} → Int × Int :=
  HasKleinPiOneEncode.encode

@[simp] theorem kleinPiOneEncode_kleinDecode [HasKleinPiOneEncode.{u}] (z : Int × Int) :
    kleinPiOneEncode.{u} (kleinDecode.{u} z) = z :=
  HasKleinPiOneEncode.encode_kleinDecode z

@[simp] theorem kleinDecode_kleinPiOneEncode [HasKleinPiOneEncode.{u}] (x : kleinPiOne.{u}) :
    kleinDecode.{u} (kleinPiOneEncode.{u} x) = x :=
  HasKleinPiOneEncode.kleinDecode_encode x

/-- `HasKleinLoopDecode` (raw loop normal forms) implies the π₁-level interface. -/
instance instHasKleinPiOneEncode [HasKleinLoopDecode.{u}] : HasKleinPiOneEncode.{u} where
  encode := kleinEncode
  encode_kleinDecode := kleinEncode_kleinDecode
  kleinDecode_encode := kleinDecode_kleinEncode

/-- Build the raw loop encode/decode interface from the quotient-level one. -/
noncomputable def hasKleinLoopDecodeOfPiOneEncode [HasKleinPiOneEncode.{u}] :
    HasKleinLoopDecode.{u} where
  encodePath := fun p => kleinPiOneEncode.{u} (Quot.mk _ p)
  encodePath_rweq := by
    intro p q hpq
    have hquot : (Quot.mk _ p : kleinPiOne.{u}) = Quot.mk _ q :=
      Quot.sound hpq
    exact _root_.congrArg (kleinPiOneEncode.{u}) hquot
  encodePath_kleinDecodePath := by
    intro z
    -- `kleinDecode z` is definitionally `Quot.mk _ (kleinDecodePath z)`.
    simpa [kleinDecode] using (kleinPiOneEncode_kleinDecode.{u} (z := z))
  kleinLoop_rweq_decode := by
    intro p
    have hq :
        kleinDecode.{u} (kleinPiOneEncode.{u} (Quot.mk _ p)) =
          (Quot.mk _ p : kleinPiOne.{u}) :=
      kleinDecode_kleinPiOneEncode (x := (Quot.mk _ p))
    have hq' :
        Quotient.mk (rwEqSetoid KleinBottle kleinBase kleinBase)
            (kleinDecodePath (kleinPiOneEncode.{u} (Quot.mk _ p))) =
          Quotient.mk (rwEqSetoid KleinBottle kleinBase kleinBase) p := by
      simpa [kleinDecode] using hq
    have hr : RwEq (kleinDecodePath (kleinPiOneEncode.{u} (Quot.mk _ p))) p := by
      simpa using (Quotient.exact (s := rwEqSetoid KleinBottle kleinBase kleinBase) hq')
    exact rweq_symm hr

/-- Fundamental group of the Klein bottle packaged as an equivalence
`π₁(K) ≃ ℤ × ℤ` (normal-form coordinates). -/
noncomputable def kleinPiOneEquivIntProd [HasKleinPiOneEncode.{u}] :
    SimpleEquiv (kleinPiOne.{u}) (Int × Int) where
  toFun := kleinPiOneEncode.{u}
  invFun := kleinDecode.{u}
  left_inv := by
    intro x
    simpa using (kleinDecode_kleinPiOneEncode (x := x))
  right_inv := by
    intro z
    simpa using (kleinPiOneEncode_kleinDecode (z := z))

end Path
end ComputationalPaths

