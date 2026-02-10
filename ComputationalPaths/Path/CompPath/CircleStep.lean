/-
# π₁(S¹) ≃ ℤ

This module packages the winding-number encode/decode data from
`CompPath/CircleCompPath.lean`
into a `SimpleEquiv` between `π₁(S¹)` and `ℤ`.
-/

import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.SimpleEquiv

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path
open CompPath

open SimpleEquiv

universe u

/-! ## Winding-number interface -/

/-- A discharge-friendly interface for `π₁(S¹) ≃ ℤ`. -/
class HasCirclePiOneEncode : Type u where
  /-- Winding-number map `π₁(S¹) → ℤ`. -/
  encode : circlePiOne → Int
  /-- Encoding after decoding is the identity on `ℤ`. -/
  encode_circleDecode : ∀ z : Int, Path (encode (circleDecode z)) z
  /-- Decoding after encoding is the identity on `π₁(S¹)`. -/
  circleDecode_encode : ∀ x : circlePiOne, Path (circleDecode (encode x)) x

/-- Canonical instance for the circle computation. -/
noncomputable instance instHasCirclePiOneEncode : HasCirclePiOneEncode where
  encode := circlePiOneEncode
  encode_circleDecode := fun z => Path.ofEq (circlePiOneEncode_circleDecode z)
  circleDecode_encode := fun x => Path.ofEq (circleDecode_circlePiOneEncode x)

/-- Winding-number map specialised to the computational circle. -/
@[simp] noncomputable def circlePiOneEncode' [HasCirclePiOneEncode] : circlePiOne → Int :=
  HasCirclePiOneEncode.encode

noncomputable def circlePiOneEncode_circleDecode' [HasCirclePiOneEncode] (z : Int) :
    Path (circlePiOneEncode' (circleDecode z)) z :=
  HasCirclePiOneEncode.encode_circleDecode z

noncomputable def circleDecode_circlePiOneEncode' [HasCirclePiOneEncode] (x : circlePiOne) :
    Path (circleDecode (circlePiOneEncode' x)) x :=
  HasCirclePiOneEncode.circleDecode_encode x

/-! ## π₁ equivalence -/

/-- Build the raw loop encode/decode interface from the quotient-level one.

This factors the raw winding number through the quotient `π₁(S¹)`, and then
uses `Quotient.exact` to recover an `RwEq` witness from the `decode ∘ encode`
equation in the quotient.  We keep this as an explicit constructor (rather than
an instance) to avoid typeclass loops between the two interfaces.
-/

noncomputable def circlePiOneEquivInt :
    SimpleEquiv circlePiOne Int :=
  circleCompPathPiOneEquivInt

noncomputable def circlePiOneEncode_decode (z : Int) :
    Path (circlePiOneEncode (circleDecode z)) z :=
  Path.ofEq (circlePiOneEncode_circleDecode z)

end Path
end ComputationalPaths
