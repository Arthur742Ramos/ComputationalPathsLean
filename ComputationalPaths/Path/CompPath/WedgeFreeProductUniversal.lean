/-
# Wedge Sum Universal Property via Free Products

This module packages the universal property of the free product at the π₁ level
for wedge sums, using the SVK wedge equivalence.

## Key Results

- `wedgePiOneWordLift`: universal map from π₁(A ∨ B) to any H
- `wedgePiOneWordLift_decode`: agrees with wordLift on decoded words

## References

- HoTT Book, Chapter 8.6
- Favonia & Shulman, "The Seifert-van Kampen Theorem in HoTT"
-/

import ComputationalPaths.Path.CompPath.PushoutPaths
import ComputationalPaths.Path.Rewrite.SimpleEquiv

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path

open CompPath

/-! ## Wedge Sum Universal Map -/

namespace WedgeFreeProductUniversal

universe u

variable {A : Type u} {B : Type u} {H : Type u}
variable (a₀ : A) (b₀ : B)

/-- Universal map from π₁(A ∨ B) induced by functions on the factors. -/
noncomputable def wedgePiOneWordLift
    [HasWedgeSVKDecodeBijective A B a₀ b₀] [One H] [Mul H]
    (φ₁ : π₁(A, a₀) → H) (φ₂ : π₁(B, b₀) → H) :
    π₁(Wedge A B a₀ b₀, Wedge.basepoint) → H :=
  fun α =>
    FreeProductUniversal.wordLift
      (G₁ := π₁(A, a₀)) (G₂ := π₁(B, b₀)) (H := H) φ₁ φ₂
      ((wedgeFundamentalGroupEquiv_of_decode_bijective
        (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)).toFun α)

/-- The universal map agrees with wordLift on decoded free-product words. -/
theorem wedgePiOneWordLift_decode
    [HasWedgeSVKDecodeBijective A B a₀ b₀] [One H] [Mul H]
    (φ₁ : π₁(A, a₀) → H) (φ₂ : π₁(B, b₀) → H)
    (w : WedgeFreeProductCode (A := A) (B := B) a₀ b₀) :
    wedgePiOneWordLift (A := A) (B := B) (H := H) a₀ b₀ φ₁ φ₂
      (wedgeFreeProductDecode (A := A) (B := B) a₀ b₀ w) =
    FreeProductUniversal.wordLift
      (G₁ := π₁(A, a₀)) (G₂ := π₁(B, b₀)) (H := H) φ₁ φ₂ w := by
  have h :=
    (wedgeFundamentalGroupEquiv_of_decode_bijective
      (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)).right_inv w
  simpa [wedgePiOneWordLift] using
    _root_.congrArg (FreeProductUniversal.wordLift φ₁ φ₂) h

end WedgeFreeProductUniversal

/-! ## Summary

This module provides a universal map from π₁(A ∨ B) by composing the SVK wedge
equivalence with the free-product word lift, and proves that it agrees with
`wordLift` on decoded words.
-/

end Path
end ComputationalPaths
