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

/-- Build the raw loop encode/decode interface from the quotient-level one.

This factors the raw winding number through the quotient `π₁(S¹)`, and then
uses `Quotient.exact` to recover an `RwEq` witness from the `decode ∘ encode`
equation in the quotient.  We keep this as an explicit constructor (rather than
an instance) to avoid typeclass loops between the two interfaces.
-/
noncomputable def hasCircleLoopDecodeOfPiOneEncode [HasCirclePiOneEncode.{u}] :
    HasCircleLoopDecode.{u} where
  encodePath := fun p => circlePiOneEncode.{u} (Quot.mk _ p)
  encodePath_rweq := by
    intro p q hpq
    have hquot : (Quot.mk _ p : circlePiOne.{u}) = Quot.mk _ q :=
      Quot.sound hpq
    exact _root_.congrArg (circlePiOneEncode.{u}) hquot
  encodePath_circleDecodePath := by
    intro z
    -- Reduce to the quotient-level equation `encode (decode z) = z`.
    have hDecode : (Quot.mk _ (circleDecodePath z) : circlePiOne.{u}) = circleDecode.{u} z := by
      simp [circleDecode, circleDecodePath]
    calc
      circlePiOneEncode.{u} (Quot.mk _ (circleDecodePath z))
          = circlePiOneEncode.{u} (circleDecode.{u} z) := by
              exact _root_.congrArg (circlePiOneEncode.{u}) hDecode
      _ = z := circlePiOneEncode_circleDecode (z := z)
  circleLoop_rweq_decode := by
    intro p
    -- `decode (encode [p]) = [p]` in the quotient, so the representatives are `RwEq`.
    have hq :
        circleDecode.{u} (circlePiOneEncode.{u} (Quot.mk _ p)) =
          (Quot.mk _ p : circlePiOne.{u}) :=
      circleDecode_circlePiOneEncode (x := (Quot.mk _ p))
    have hq' :
        Quotient.mk (rwEqSetoid Circle circleBase circleBase)
            (circleLoopPathZPow (circlePiOneEncode.{u} (Quot.mk _ p))) =
          Quotient.mk (rwEqSetoid Circle circleBase circleBase) p := by
      simpa [circleDecode] using hq
    have hr : RwEq (circleLoopPathZPow (circlePiOneEncode.{u} (Quot.mk _ p))) p := by
      simpa using (Quotient.exact (s := rwEqSetoid Circle circleBase circleBase) hq')
    exact rweq_symm hr

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

/-! ## Quotient-level algebra for the winding-number map -/

@[simp] theorem circlePiOneEncode_id [HasCirclePiOneEncode.{u}] :
    circlePiOneEncode.{u} (LoopQuot.id (A := Circle.{u}) (a := circleBase.{u})) = 0 := by
  -- `circleDecode 0 = id` and `encode (decode z) = z`.
  simpa [circleDecode_zero] using (circlePiOneEncode_circleDecode.{u} (z := (0 : Int)))

@[simp] theorem circlePiOneEncode_loop [HasCirclePiOneEncode.{u}] :
    circlePiOneEncode.{u} (circlePiOneLoop.{u}) = 1 := by
  -- `circlePiOneLoop = decode 1`.
  simpa [circleDecode_one] using (circlePiOneEncode_circleDecode.{u} (z := (1 : Int)))

theorem circlePiOneEncode_mul [HasCirclePiOneEncode.{u}] (α β : circlePiOne.{u}) :
    circlePiOneEncode.{u} (LoopQuot.comp (A := Circle.{u}) (a := circleBase.{u}) α β) =
      circlePiOneEncode.{u} α + circlePiOneEncode.{u} β := by
  have hα : α = circleDecode.{u} (circlePiOneEncode.{u} α) :=
    (circleDecode_circlePiOneEncode (x := α)).symm
  have hβ : β = circleDecode.{u} (circlePiOneEncode.{u} β) :=
    (circleDecode_circlePiOneEncode (x := β)).symm
  -- Reduce the multiplication law to `decode (m + n) = decode m · decode n`.
  have hComp :
      LoopQuot.comp (A := Circle.{u}) (a := circleBase.{u})
          (circleDecode.{u} (circlePiOneEncode.{u} α))
          (circleDecode.{u} (circlePiOneEncode.{u} β)) =
        circleDecode.{u} (circlePiOneEncode.{u} α + circlePiOneEncode.{u} β) := by
    -- `circleDecode` is `circleLoopZPow`, so this is `zpow_add` in the loop quotient.
    simpa [circleDecode] using
      (circleLoopZPow_add (m := circlePiOneEncode.{u} α) (n := circlePiOneEncode.{u} β)).symm
  calc
    circlePiOneEncode.{u} (LoopQuot.comp (A := Circle.{u}) (a := circleBase.{u}) α β)
        = circlePiOneEncode.{u}
            (LoopQuot.comp (A := Circle.{u}) (a := circleBase.{u})
              (circleDecode.{u} (circlePiOneEncode.{u} α)) β) := by
            -- Replace `α` using `decode (encode α) = α`.
            exact
              _root_.congrArg (circlePiOneEncode.{u}) <|
                _root_.congrArg
                  (fun t => LoopQuot.comp (A := Circle.{u}) (a := circleBase.{u}) t β) hα
    _ = circlePiOneEncode.{u}
            (LoopQuot.comp (A := Circle.{u}) (a := circleBase.{u})
              (circleDecode.{u} (circlePiOneEncode.{u} α))
              (circleDecode.{u} (circlePiOneEncode.{u} β))) := by
            -- Replace `β` using `decode (encode β) = β`.
            exact
              _root_.congrArg (circlePiOneEncode.{u}) <|
                _root_.congrArg
                  (fun t =>
                    LoopQuot.comp (A := Circle.{u}) (a := circleBase.{u})
                      (circleDecode.{u} (circlePiOneEncode.{u} α)) t) hβ
    _ = circlePiOneEncode.{u}
            (circleDecode.{u} (circlePiOneEncode.{u} α + circlePiOneEncode.{u} β)) := by
            simpa using _root_.congrArg (circlePiOneEncode.{u}) hComp
    _ = circlePiOneEncode.{u} α + circlePiOneEncode.{u} β := by
            simpa using
              (circlePiOneEncode_circleDecode.{u}
                (z := circlePiOneEncode.{u} α + circlePiOneEncode.{u} β))

end Path
end ComputationalPaths
