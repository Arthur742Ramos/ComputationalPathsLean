/-
# Wedge SVK Circle Instances

Instances of SVK theorem for wedge of circles.
-/

import ComputationalPaths.Path.CompPath.WedgeFreeProductUniversal

namespace ComputationalPaths.Path.CompPath.WedgeSVKCircleInstances

universe u

section

variable {A : Type u} {B : Type u} {H : Type u}
variable (a₀ : A) (b₀ : B)

noncomputable def wedge_circle_wordLift
    [HasWedgeSVKDecodeBijective A B a₀ b₀] [One H] [Mul H]
    (φ₁ : π₁(A, a₀) → H) (φ₂ : π₁(B, b₀) → H) :
    π₁(Wedge A B a₀ b₀, Wedge.basepoint) → H :=
  WedgeFreeProductUniversal.wedgePiOneWordLift
    (A := A) (B := B) (H := H) a₀ b₀ φ₁ φ₂

theorem wedge_circle_wordLift_decode
    [HasWedgeSVKDecodeBijective A B a₀ b₀] [One H] [Mul H]
    (φ₁ : π₁(A, a₀) → H) (φ₂ : π₁(B, b₀) → H)
    (w : WedgeFreeProductCode (A := A) (B := B) a₀ b₀) :
    wedge_circle_wordLift (A := A) (B := B) (H := H) a₀ b₀ φ₁ φ₂
      (wedgeFreeProductDecode (A := A) (B := B) a₀ b₀ w) =
    FreeProductUniversal.wordLift
      (G₁ := π₁(A, a₀)) (G₂ := π₁(B, b₀)) (H := H) φ₁ φ₂ w := by
  simpa [wedge_circle_wordLift] using
    (WedgeFreeProductUniversal.wedgePiOneWordLift_decode
      (A := A) (B := B) (H := H) (a₀ := a₀) (b₀ := b₀) φ₁ φ₂ w)

noncomputable def wedge_circle_inl :
    π₁(A, a₀) → π₁(Wedge A B a₀ b₀, Wedge.basepoint) :=
  pushoutPiOneInl (A := A) (B := B) (C := PUnit')
    (f := fun _ : PUnit' => a₀) (g := fun _ : PUnit' => b₀) PUnit'.unit

noncomputable def wedge_circle_inr :
    π₁(B, b₀) → π₁(Wedge A B a₀ b₀, Wedge.basepoint) :=
  pushoutPiOneInr (A := A) (B := B) (C := PUnit')
    (f := fun _ : PUnit' => a₀) (g := fun _ : PUnit' => b₀) PUnit'.unit

@[simp] theorem wedge_circle_inl_mul (α β : π₁(A, a₀)) :
    wedge_circle_inl (A := A) (B := B) a₀ b₀ (piOneMul α β) =
      piOneMul
        (wedge_circle_inl (A := A) (B := B) a₀ b₀ α)
        (wedge_circle_inl (A := A) (B := B) a₀ b₀ β) := by
  simpa [wedge_circle_inl] using
    (pushoutPiOneInl_mul (A := A) (B := B) (C := PUnit')
      (f := fun _ : PUnit' => a₀) (g := fun _ : PUnit' => b₀) PUnit'.unit α β)

@[simp] theorem wedge_circle_inr_mul (β₁ β₂ : π₁(B, b₀)) :
    wedge_circle_inr (A := A) (B := B) a₀ b₀ (piOneMul β₁ β₂) =
      piOneMul
        (wedge_circle_inr (A := A) (B := B) a₀ b₀ β₁)
        (wedge_circle_inr (A := A) (B := B) a₀ b₀ β₂) := by
  simpa [wedge_circle_inr] using
    (pushoutPiOneInr_mul (A := A) (B := B) (C := PUnit')
      (f := fun _ : PUnit' => a₀) (g := fun _ : PUnit' => b₀) PUnit'.unit β₁ β₂)

end

end ComputationalPaths.Path.CompPath.WedgeSVKCircleInstances
