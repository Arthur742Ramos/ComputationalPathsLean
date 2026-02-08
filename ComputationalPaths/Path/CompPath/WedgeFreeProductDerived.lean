/-
# Derived Algebra for Wedge-Sum Fundamental Groups

This module derives algebraic properties of the wedge-sum fundamental group
from the SVK wedge equivalence and free-product word operations.

## Key Results
- `wedgeFundamentalGroupEquiv_mul`: the wedge equivalence respects multiplication.
- `wedgePiOneWordLift_mul`: the universal wedge map preserves multiplication.

## References
- HoTT Book, Chapter 8
- Favonia & Shulman, "The Seifert-van Kampen Theorem in HoTT"
-/

import ComputationalPaths.Path.CompPath.PushoutPaths
import ComputationalPaths.Path.CompPath.WedgeFreeProductUniversal

namespace ComputationalPaths
namespace Path

open CompPath
open WedgeFreeProductUniversal

universe u

set_option maxHeartbeats 1000000

/-! ## Multiplicativity of the wedge equivalence -/

/-- The wedge free-product equivalence sends multiplication to word concatenation. -/
theorem wedgeFundamentalGroupEquiv_mul {A : Type u} {B : Type u}
    (a₀ : A) (b₀ : B) [HasWedgeSVKDecodeBijective A B a₀ b₀]
    (α β : π₁(Wedge A B a₀ b₀, Wedge.basepoint)) :
    (wedgeFundamentalGroupEquiv_of_decode_bijective
        (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)).toFun (piOneMul α β) =
      FreeProductWord.concat
        ((wedgeFundamentalGroupEquiv_of_decode_bijective
            (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)).toFun α)
        ((wedgeFundamentalGroupEquiv_of_decode_bijective
            (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)).toFun β) := by
  let e :=
    wedgeFundamentalGroupEquiv_of_decode_bijective
      (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)
  have hinj :
      Function.Injective (wedgeFreeProductDecode (A := A) (B := B) a₀ b₀) :=
    (HasWedgeSVKDecodeBijective.bijective
      (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)).1
  apply hinj
  have hleft :
      wedgeFreeProductDecode (A := A) (B := B) a₀ b₀ (e.toFun (piOneMul α β)) =
        piOneMul α β := by
    simpa [e] using e.left_inv (piOneMul α β)
  have hright :
      wedgeFreeProductDecode (A := A) (B := B) a₀ b₀
          (FreeProductWord.concat (e.toFun α) (e.toFun β)) =
        piOneMul α β := by
    calc
      wedgeFreeProductDecode (A := A) (B := B) a₀ b₀
          (FreeProductWord.concat (e.toFun α) (e.toFun β)) =
        piOneMul
          (wedgeFreeProductDecode (A := A) (B := B) a₀ b₀ (e.toFun α))
          (wedgeFreeProductDecode (A := A) (B := B) a₀ b₀ (e.toFun β)) := by
            simpa using
              (wedgeFreeProductDecode_concat (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)
                (e.toFun α) (e.toFun β))
      _ = piOneMul α
          (wedgeFreeProductDecode (A := A) (B := B) a₀ b₀ (e.toFun β)) := by
            simpa [e] using
              _root_.congrArg
                (fun x =>
                  piOneMul x (wedgeFreeProductDecode (A := A) (B := B) a₀ b₀ (e.toFun β)))
                (e.left_inv α)
      _ = piOneMul α β := by
            simpa [e] using
              _root_.congrArg (fun x => piOneMul α x) (e.left_inv β)
  exact hleft.trans hright.symm

/-! ## Multiplicativity of the universal wedge map -/

/-- The wedge universal map preserves multiplication. -/
theorem wedgePiOneWordLift_mul {A : Type u} {B : Type u} {H : Type u}
    (a₀ : A) (b₀ : B) [HasWedgeSVKDecodeBijective A B a₀ b₀] [One H] [Mul H]
    (hone_mul : ∀ x : H, 1 * x = x)
    (hmul_assoc : ∀ x y z : H, (x * y) * z = x * (y * z))
    (φ₁ : π₁(A, a₀) → H) (φ₂ : π₁(B, b₀) → H)
    (α β : π₁(Wedge A B a₀ b₀, Wedge.basepoint)) :
    wedgePiOneWordLift (A := A) (B := B) (H := H) a₀ b₀ φ₁ φ₂ (piOneMul α β) =
      wedgePiOneWordLift (A := A) (B := B) (H := H) a₀ b₀ φ₁ φ₂ α *
        wedgePiOneWordLift (A := A) (B := B) (H := H) a₀ b₀ φ₁ φ₂ β := by
  let e :=
    wedgeFundamentalGroupEquiv_of_decode_bijective
      (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)
  change FreeProductUniversal.wordLift φ₁ φ₂ (e.toFun (piOneMul α β)) =
      FreeProductUniversal.wordLift φ₁ φ₂ (e.toFun α) *
        FreeProductUniversal.wordLift φ₁ φ₂ (e.toFun β)
  rw [wedgeFundamentalGroupEquiv_mul (A := A) (B := B) (a₀ := a₀) (b₀ := b₀) α β]
  simpa using
    (FreeProductUniversal.wordLift_concat (G₁ := π₁(A, a₀)) (G₂ := π₁(B, b₀)) (H := H)
      hone_mul hmul_assoc φ₁ φ₂ (e.toFun α) (e.toFun β))

/-! ## Summary

We show the SVK wedge equivalence is multiplicative and that the induced
universal map from π₁(A ∨ B) respects multiplication.
-/

end Path
end ComputationalPaths
