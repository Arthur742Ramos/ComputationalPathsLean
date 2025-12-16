/-
# π₁(RP²) ≃ ℤ₂

This module packages the boolean encode/decode data from `ProjectivePlane.lean`
into a `SimpleEquiv` between `π₁(RP²)` and `Bool` (ℤ₂).
-/

import ComputationalPaths.Path.HIT.ProjectivePlane
import ComputationalPaths.Path.Rewrite.SimpleEquiv

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path

open SimpleEquiv

universe u

/-- A discharge-friendly interface for `π₁(RP²) ≃ ℤ₂`.

Unlike `HasProjectiveLoopDecode`, this class only talks about the loop *quotient*
(`π₁`) rather than raw loop normal forms. Downstream developments that only need
the fundamental group can depend on this weaker hypothesis.
-/
class HasProjectivePiOneEncode : Type u where
  /-- Parity map `π₁(RP²) → Bool`. -/
  encode : projectivePiOne.{u} → Bool
  /-- Encoding after decoding is the identity on booleans. -/
  encode_projectiveDecode : ∀ b : Bool, encode (projectiveDecode.{u} b) = b
  /-- Decoding after encoding is the identity on `π₁(RP²)`. -/
  projectiveDecode_encode : ∀ x : projectivePiOne.{u}, projectiveDecode.{u} (encode x) = x

/-- Parity map specialised from `HasProjectivePiOneEncode`. -/
@[simp] def projectivePiOneEncode [HasProjectivePiOneEncode.{u}] :
    projectivePiOne.{u} → Bool :=
  HasProjectivePiOneEncode.encode

@[simp] theorem projectivePiOneEncode_projectiveDecode [HasProjectivePiOneEncode.{u}] (b : Bool) :
    projectivePiOneEncode.{u} (projectiveDecode.{u} b) = b :=
  HasProjectivePiOneEncode.encode_projectiveDecode b

@[simp] theorem projectiveDecode_projectivePiOneEncode [HasProjectivePiOneEncode.{u}]
    (x : projectivePiOne.{u}) :
    projectiveDecode.{u} (projectivePiOneEncode.{u} x) = x :=
  HasProjectivePiOneEncode.projectiveDecode_encode x

/-- `HasProjectiveLoopDecode` (raw loop normal forms) implies the π₁-level interface. -/
instance instHasProjectivePiOneEncode [HasProjectiveLoopDecode.{u}] :
    HasProjectivePiOneEncode.{u} where
  encode := projectiveEncode
  encode_projectiveDecode := projectiveEncode_projectiveDecode
  projectiveDecode_encode := projectiveDecode_projectiveEncode

/-- Build the raw loop encode/decode interface from the quotient-level one. -/
noncomputable def hasProjectiveLoopDecodeOfPiOneEncode [HasProjectivePiOneEncode.{u}] :
    HasProjectiveLoopDecode.{u} where
  encodePath := fun p => projectivePiOneEncode.{u} (Quot.mk _ p)
  encodePath_rweq := by
    intro p q hpq
    have hquot : (Quot.mk _ p : projectivePiOne.{u}) = Quot.mk _ q :=
      Quot.sound hpq
    exact _root_.congrArg (projectivePiOneEncode.{u}) hquot
  encodePath_decode := by
    intro b
    -- `projectiveDecode b` is definitionally `Quot.mk _ (projectiveDecodePath b)`.
    simpa [projectiveDecode] using (projectivePiOneEncode_projectiveDecode.{u} (b := b))
  loop_rweq_decode := by
    intro p
    have hq :
        projectiveDecode.{u} (projectivePiOneEncode.{u} (Quot.mk _ p)) =
          (Quot.mk _ p : projectivePiOne.{u}) :=
      projectiveDecode_projectivePiOneEncode (x := (Quot.mk _ p))
    have hq' :
        Quotient.mk (rwEqSetoid ProjectivePlane projectiveBase projectiveBase)
            (projectiveDecodePath (projectivePiOneEncode.{u} (Quot.mk _ p))) =
          Quotient.mk (rwEqSetoid ProjectivePlane projectiveBase projectiveBase) p := by
      simpa [projectiveDecode] using hq
    have hr :
        RwEq (projectiveDecodePath (projectivePiOneEncode.{u} (Quot.mk _ p))) p := by
      simpa using
        (Quotient.exact (s := rwEqSetoid ProjectivePlane projectiveBase projectiveBase) hq')
    exact rweq_symm hr

/-- Fundamental group of RP² is equivalent to `ℤ₂`, represented as `Bool`. -/
noncomputable def projectivePiOneEquivZ2 [HasProjectivePiOneEncode.{u}] :
    SimpleEquiv (projectivePiOne.{u}) Bool where
  toFun := projectivePiOneEncode.{u}
  invFun := projectiveDecode.{u}
  left_inv := by
    intro x
    simpa using (projectiveDecode_projectivePiOneEncode (x := x))
  right_inv := by
    intro b
    simpa using (projectivePiOneEncode_projectiveDecode (b := b))

end Path
end ComputationalPaths

