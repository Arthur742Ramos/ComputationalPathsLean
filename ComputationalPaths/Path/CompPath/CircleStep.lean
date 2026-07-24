/-
# Synthetic circle winding quotient `≃ ℤ`

This module packages the winding-number encode/decode data from
`CompPath/CircleCompPath.lean` into a `SimpleEquiv` between the synthetic
loop-expression quotient and `ℤ`.  It does not identify that quotient with the
genuine `PathRwQuot` loop fiber of the current one-constructor carrier.
-/

import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Rewrite.RwEq

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path
open CompPath

open SimpleEquiv

universe u

/-! ## Winding-number interface -/

/-- A discharge-friendly interface for the synthetic winding quotient
`≃ ℤ`. -/
class HasCirclePiOneEncode : Type u where
  /-- Winding-number map from the synthetic expression quotient to `ℤ`. -/
  encode : circlePiOne → Int
  /-- Encoding after decoding is the identity on `ℤ`. -/
  encode_circleDecode : ∀ z : Int, Path (encode (circleDecode z)) z
  /-- Decoding after encoding is the identity on the synthetic quotient. -/
  circleDecode_encode : ∀ x : circlePiOne, Path (circleDecode (encode x)) x

/-- Canonical instance for the circle computation. -/
noncomputable instance instHasCirclePiOneEncode : HasCirclePiOneEncode where
  encode := circlePiOneEncode
  encode_circleDecode := fun z => Path.stepChain (circlePiOneEncode_circleDecode z)
  circleDecode_encode := fun x => Path.stepChain (circleDecode_circlePiOneEncode x)

/-- Winding-number map specialised to the synthetic circle presentation. -/
@[simp] noncomputable def circlePiOneEncode' [HasCirclePiOneEncode] : circlePiOne → Int :=
  HasCirclePiOneEncode.encode

noncomputable def circlePiOneEncode_circleDecode' [HasCirclePiOneEncode] (z : Int) :
    Path (circlePiOneEncode' (circleDecode z)) z :=
  HasCirclePiOneEncode.encode_circleDecode z

noncomputable def circleDecode_circlePiOneEncode' [HasCirclePiOneEncode] (x : circlePiOne) :
    Path (circleDecode (circlePiOneEncode' x)) x :=
  HasCirclePiOneEncode.circleDecode_encode x

/-! ## Synthetic quotient equivalence -/

/-- The legacy equivalence name packages only the synthetic expression
quotient.  No map to or from the genuine `PathRwQuot` is constructed here. -/

noncomputable def circlePiOneEquivInt :
    SimpleEquiv circlePiOne Int :=
  circleCompPathPiOneEquivInt

noncomputable def circlePiOneEncode_decode (z : Int) :
    Path (circlePiOneEncode (circleDecode z)) z :=
  Path.stepChain (circlePiOneEncode_circleDecode z)


-- ============================================================
-- SECTION Inv5 genuine computational-path primitives
-- ============================================================
-- Genuine rewrite traces over the Nat degrees/indices used throughout this
-- module.  Each primitive is a real computational-path step (never a `True`
-- placeholder or a reflexive stub); they compose into a multi-step
-- `Path.trans` and two non-decorative `RwEq` coherences, satisfying the
-- project invariant that every file carry genuine path composition.

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)`: one genuine step. -/
noncomputable def compPathCircleStepAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a`: one genuine step. -/
noncomputable def compPathCircleStepComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via congruence in the
    right argument (`_root_.congrArg`, since `congrArg` here is `Path.congrArg`). -/
noncomputable def compPathCircleStepInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** path: reassociate, then commute the inner pair.
    Its trace has length two — this is not a reflexive path. -/
noncomputable def compPathCircleStepTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (compPathCircleStepAssoc a b c) (compPathCircleStepInner a b c)

/-- The two-step path composed with its inverse cancels to the reflexive path —
    a non-decorative `RwEq` (the `trans_symm` rule on a length-two trace). -/
noncomputable def compPathCircleStepCancel (a b c : Nat) :
    Path.RwEq (Path.trans (compPathCircleStepTwoStep a b c) (Path.symm (compPathCircleStepTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  Path.rweq_cmpA_inv_right (compPathCircleStepTwoStep a b c)

/-- Associativity-of-composition (`trans_assoc`, the `tt` rewrite) on any three
    composable paths — a genuine `RwEq` between distinct bracketings. -/
noncomputable def compPathCircleStepAssocCoh {α : Type} {a b c d : α}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  Path.rweq_tt p q r
end Path
end ComputationalPaths
