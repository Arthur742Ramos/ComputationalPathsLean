/-
# Universal Property of Free Products of Fundamental Groups

This module packages the universal property of the free product of fundamental
groups using the FreeProductWord/FreeGroupEq machinery from `PushoutPaths.lean`.

## Key Results
- `piOneFreeProductLift`: induced homomorphism from the free product
- `piOneFreeProductLift_unique`: uniqueness of the induced homomorphism

## References
- HoTT Book, Chapter 8.6
- Favonia & Shulman, "The Seifert-van Kampen Theorem in HoTT"
-/

import ComputationalPaths.Path.CompPath.PushoutPaths

namespace ComputationalPaths
namespace Path
namespace CompPath
namespace FreeProductUniversal

universe u

/-! ## Free Product of Fundamental Groups -/

section PiOneFreeProduct

variable {A : Type u} {B : Type u} (a₀ : A) (b₀ : B)

-- Local additive structure used by FreeGroupEq (addition = loop composition).
noncomputable local instance : Add (π₁(A, a₀)) := ⟨piOneMul⟩
noncomputable local instance : Zero (π₁(A, a₀)) := ⟨Quot.mk _ (Path.refl a₀)⟩
noncomputable local instance : Add (π₁(B, b₀)) := ⟨piOneMul⟩
noncomputable local instance : Zero (π₁(B, b₀)) := ⟨Quot.mk _ (Path.refl b₀)⟩

/-- The free product of π₁(A, a₀) and π₁(B, b₀), quotiented by FreeGroupEq. -/
abbrev PiOneFreeProduct : Type u :=
  Quot (FreeProductWord.FreeGroupEq (G₁ := π₁(A, a₀)) (G₂ := π₁(B, b₀)))

/-- Embed a word into the free product quotient. -/
noncomputable def piOneFreeProductOfWord
    (w : FreeProductWord (π₁(A, a₀)) (π₁(B, b₀))) :
    PiOneFreeProduct a₀ b₀ :=
  Quot.mk _ w

/-- Identity element (empty word). -/
noncomputable def piOneFreeProductOne : PiOneFreeProduct a₀ b₀ :=
  piOneFreeProductOfWord a₀ b₀ .nil

/-- Left injection of π₁(A, a₀) into the free product. -/
noncomputable def piOneFreeProductInl (x : π₁(A, a₀)) : PiOneFreeProduct a₀ b₀ :=
  piOneFreeProductOfWord a₀ b₀ (FreeProductWord.singleLeft x)

/-- Right injection of π₁(B, b₀) into the free product. -/
noncomputable def piOneFreeProductInr (y : π₁(B, b₀)) : PiOneFreeProduct a₀ b₀ :=
  piOneFreeProductOfWord a₀ b₀ (FreeProductWord.singleRight y)

/-- Multiply by a fixed word on the right. -/
noncomputable def piOneFreeProductMulWordRight
    (w₂ : FreeProductWord (π₁(A, a₀)) (π₁(B, b₀))) :
    PiOneFreeProduct a₀ b₀ → PiOneFreeProduct a₀ b₀ :=
  Quot.lift
    (fun w₁ => Quot.mk _ (FreeProductWord.concat w₁ w₂))
    (fun _ _ h => Quot.sound (FreeProductWord.concat_freeGroupEq_left w₂ h))

/-- Multiplication in the free product (concatenation of words). -/
noncomputable def piOneFreeProductMul
    (x y : PiOneFreeProduct a₀ b₀) : PiOneFreeProduct a₀ b₀ :=
  Quot.lift
    (fun w₂ => piOneFreeProductMulWordRight a₀ b₀ w₂ x)
    (fun w₂ w₂' h => by
      induction x using Quot.ind with
      | _ w₁ =>
          unfold piOneFreeProductMulWordRight
          apply Quot.sound
          exact FreeProductWord.concat_freeGroupEq_right w₁ h)
    y

noncomputable instance : Mul (PiOneFreeProduct a₀ b₀) := ⟨piOneFreeProductMul a₀ b₀⟩
noncomputable instance : One (PiOneFreeProduct a₀ b₀) := ⟨piOneFreeProductOne a₀ b₀⟩

/-- Multiplication on representatives. -/
@[simp] theorem piOneFreeProductMul_mk_mk
    (w₁ w₂ : FreeProductWord (π₁(A, a₀)) (π₁(B, b₀))) :
    piOneFreeProductMul a₀ b₀ (Quot.mk _ w₁) (Quot.mk _ w₂) =
      Quot.mk _ (FreeProductWord.concat w₁ w₂) := rfl

/-! ## Universal Lift -/

variable {H : Type u} [One H] [Mul H]

/-- The universal homomorphism induced by maps on π₁(A) and π₁(B). -/
noncomputable def piOneFreeProductLift
    (hone_mul : ∀ x : H, 1 * x = x)
    (hmul_assoc : ∀ x y z : H, (x * y) * z = x * (y * z))
    (φ₁ : π₁(A, a₀) → H) (φ₂ : π₁(B, b₀) → H)
    (hφ₁_add : ∀ x y, φ₁ (x + y) = φ₁ x * φ₁ y)
    (hφ₂_add : ∀ x y, φ₂ (x + y) = φ₂ x * φ₂ y)
    (hφ₁_zero : φ₁ 0 = 1)
    (hφ₂_zero : φ₂ 0 = 1) :
    PiOneFreeProduct a₀ b₀ → H :=
  Quot.lift
    (wordLift (G₁ := π₁(A, a₀)) (G₂ := π₁(B, b₀)) (H := H) φ₁ φ₂)
    (fun _ _ h =>
      wordLift_respects_freeGroupEq hone_mul hmul_assoc φ₁ φ₂
        hφ₁_add hφ₂_add hφ₁_zero hφ₂_zero h)

/-- Computation rule for `piOneFreeProductLift` on representatives. -/
@[simp] theorem piOneFreeProductLift_mk
    (hone_mul : ∀ x : H, 1 * x = x)
    (hmul_assoc : ∀ x y z : H, (x * y) * z = x * (y * z))
    (φ₁ : π₁(A, a₀) → H) (φ₂ : π₁(B, b₀) → H)
    (hφ₁_add : ∀ x y, φ₁ (x + y) = φ₁ x * φ₁ y)
    (hφ₂_add : ∀ x y, φ₂ (x + y) = φ₂ x * φ₂ y)
    (hφ₁_zero : φ₁ 0 = 1)
    (hφ₂_zero : φ₂ 0 = 1)
    (w : FreeProductWord (π₁(A, a₀)) (π₁(B, b₀))) :
    piOneFreeProductLift (A := A) (B := B) a₀ b₀
        (H := H) hone_mul hmul_assoc φ₁ φ₂
        hφ₁_add hφ₂_add hφ₁_zero hφ₂_zero (Quot.mk _ w) =
      wordLift φ₁ φ₂ w := rfl

/-- The lift agrees with φ₁ on left injections. -/
theorem piOneFreeProductLift_inl
    (hone_mul : ∀ x : H, 1 * x = x)
    (hmul_assoc : ∀ x y z : H, (x * y) * z = x * (y * z))
    (hmul_one : ∀ x : H, x * 1 = x)
    (φ₁ : π₁(A, a₀) → H) (φ₂ : π₁(B, b₀) → H)
    (hφ₁_add : ∀ x y, φ₁ (x + y) = φ₁ x * φ₁ y)
    (hφ₂_add : ∀ x y, φ₂ (x + y) = φ₂ x * φ₂ y)
    (hφ₁_zero : φ₁ 0 = 1)
    (hφ₂_zero : φ₂ 0 = 1)
    (x : π₁(A, a₀)) :
    piOneFreeProductLift (A := A) (B := B) a₀ b₀
        (H := H) hone_mul hmul_assoc φ₁ φ₂
        hφ₁_add hφ₂_add hφ₁_zero hφ₂_zero
        (piOneFreeProductInl a₀ b₀ x) = φ₁ x := by
  simp [piOneFreeProductInl, piOneFreeProductOfWord, wordLift_singleLeft, hmul_one]

/-- The lift agrees with φ₂ on right injections. -/
theorem piOneFreeProductLift_inr
    (hone_mul : ∀ x : H, 1 * x = x)
    (hmul_assoc : ∀ x y z : H, (x * y) * z = x * (y * z))
    (hmul_one : ∀ x : H, x * 1 = x)
    (φ₁ : π₁(A, a₀) → H) (φ₂ : π₁(B, b₀) → H)
    (hφ₁_add : ∀ x y, φ₁ (x + y) = φ₁ x * φ₁ y)
    (hφ₂_add : ∀ x y, φ₂ (x + y) = φ₂ x * φ₂ y)
    (hφ₁_zero : φ₁ 0 = 1)
    (hφ₂_zero : φ₂ 0 = 1)
    (y : π₁(B, b₀)) :
    piOneFreeProductLift (A := A) (B := B) a₀ b₀
        (H := H) hone_mul hmul_assoc φ₁ φ₂
        hφ₁_add hφ₂_add hφ₁_zero hφ₂_zero
        (piOneFreeProductInr a₀ b₀ y) = φ₂ y := by
  simp [piOneFreeProductInr, piOneFreeProductOfWord, wordLift_singleRight, hmul_one]

/-- The lift sends the free product identity to 1. -/
theorem piOneFreeProductLift_one
    (hone_mul : ∀ x : H, 1 * x = x)
    (hmul_assoc : ∀ x y z : H, (x * y) * z = x * (y * z))
    (φ₁ : π₁(A, a₀) → H) (φ₂ : π₁(B, b₀) → H)
    (hφ₁_add : ∀ x y, φ₁ (x + y) = φ₁ x * φ₁ y)
    (hφ₂_add : ∀ x y, φ₂ (x + y) = φ₂ x * φ₂ y)
    (hφ₁_zero : φ₁ 0 = 1)
    (hφ₂_zero : φ₂ 0 = 1) :
    piOneFreeProductLift (A := A) (B := B) a₀ b₀
        (H := H) hone_mul hmul_assoc φ₁ φ₂
        hφ₁_add hφ₂_add hφ₁_zero hφ₂_zero
        (piOneFreeProductOne a₀ b₀) = 1 := by
  simp [piOneFreeProductOne, piOneFreeProductOfWord]

/-- The lift preserves multiplication. -/
theorem piOneFreeProductLift_mul
    (hone_mul : ∀ x : H, 1 * x = x)
    (hmul_assoc : ∀ x y z : H, (x * y) * z = x * (y * z))
    (φ₁ : π₁(A, a₀) → H) (φ₂ : π₁(B, b₀) → H)
    (hφ₁_add : ∀ x y, φ₁ (x + y) = φ₁ x * φ₁ y)
    (hφ₂_add : ∀ x y, φ₂ (x + y) = φ₂ x * φ₂ y)
    (hφ₁_zero : φ₁ 0 = 1)
    (hφ₂_zero : φ₂ 0 = 1)
    (x y : PiOneFreeProduct a₀ b₀) :
    piOneFreeProductLift (A := A) (B := B) a₀ b₀
        (H := H) hone_mul hmul_assoc φ₁ φ₂
        hφ₁_add hφ₂_add hφ₁_zero hφ₂_zero
        (piOneFreeProductMul a₀ b₀ x y) =
      piOneFreeProductLift (A := A) (B := B) a₀ b₀
          (H := H) hone_mul hmul_assoc φ₁ φ₂
          hφ₁_add hφ₂_add hφ₁_zero hφ₂_zero x *
      piOneFreeProductLift (A := A) (B := B) a₀ b₀
          (H := H) hone_mul hmul_assoc φ₁ φ₂
          hφ₁_add hφ₂_add hφ₁_zero hφ₂_zero y := by
  induction x using Quot.ind with
  | _ w₁ =>
    induction y using Quot.ind with
    | _ w₂ =>
      simp [piOneFreeProductMul, piOneFreeProductMulWordRight, wordLift_concat,
        hone_mul, hmul_assoc]

/-- Uniqueness: any homomorphism agreeing with φ₁/φ₂ equals the lift. -/
theorem piOneFreeProductLift_unique
    (hone_mul : ∀ x : H, 1 * x = x)
    (hmul_assoc : ∀ x y z : H, (x * y) * z = x * (y * z))
    (φ₁ : π₁(A, a₀) → H) (φ₂ : π₁(B, b₀) → H)
    (hφ₁_add : ∀ x y, φ₁ (x + y) = φ₁ x * φ₁ y)
    (hφ₂_add : ∀ x y, φ₂ (x + y) = φ₂ x * φ₂ y)
    (hφ₁_zero : φ₁ 0 = 1)
    (hφ₂_zero : φ₂ 0 = 1)
    (ψ : PiOneFreeProduct a₀ b₀ → H)
    (ψ_mul : ∀ x y, ψ (piOneFreeProductMul a₀ b₀ x y) = ψ x * ψ y)
    (ψ_one : ψ (piOneFreeProductOne a₀ b₀) = 1)
    (ψ_inl : ∀ x, ψ (piOneFreeProductInl a₀ b₀ x) = φ₁ x)
    (ψ_inr : ∀ y, ψ (piOneFreeProductInr a₀ b₀ y) = φ₂ y) :
    ψ =
      piOneFreeProductLift (A := A) (B := B) a₀ b₀
        (H := H) hone_mul hmul_assoc φ₁ φ₂
        hφ₁_add hφ₂_add hφ₁_zero hφ₂_zero := by
  funext x
  induction x using Quot.ind with
  | _ w =>
      have hword : ψ (Quot.mk _ w) = wordLift φ₁ φ₂ w := by
        induction w with
        | nil =>
            simpa [piOneFreeProductOne, piOneFreeProductOfWord, wordLift_nil] using ψ_one
        | consLeft x rest ih =>
            have hmul :
                piOneFreeProductMul a₀ b₀ (piOneFreeProductInl a₀ b₀ x) (Quot.mk _ rest) =
                  Quot.mk _ (FreeProductWord.consLeft x rest) := by
              simp [piOneFreeProductInl, piOneFreeProductOfWord]
            calc
              ψ (Quot.mk _ (FreeProductWord.consLeft x rest)) =
                  ψ (piOneFreeProductMul a₀ b₀ (piOneFreeProductInl a₀ b₀ x) (Quot.mk _ rest)) := by
                    simp [hmul]
              _ = ψ (piOneFreeProductInl a₀ b₀ x) * ψ (Quot.mk _ rest) := ψ_mul _ _
              _ = φ₁ x * wordLift φ₁ φ₂ rest := by simp [ψ_inl, ih]
              _ = wordLift φ₁ φ₂ (FreeProductWord.consLeft x rest) := by rfl
        | consRight y rest ih =>
            have hmul :
                piOneFreeProductMul a₀ b₀ (piOneFreeProductInr a₀ b₀ y) (Quot.mk _ rest) =
                  Quot.mk _ (FreeProductWord.consRight y rest) := by
              simp [piOneFreeProductInr, piOneFreeProductOfWord]
            calc
              ψ (Quot.mk _ (FreeProductWord.consRight y rest)) =
                  ψ (piOneFreeProductMul a₀ b₀ (piOneFreeProductInr a₀ b₀ y) (Quot.mk _ rest)) := by
                    simp [hmul]
              _ = ψ (piOneFreeProductInr a₀ b₀ y) * ψ (Quot.mk _ rest) := ψ_mul _ _
              _ = φ₂ y * wordLift φ₁ φ₂ rest := by simp [ψ_inr, ih]
              _ = wordLift φ₁ φ₂ (FreeProductWord.consRight y rest) := by rfl
      simpa [piOneFreeProductLift] using hword

end PiOneFreeProduct

/-! ## Summary

We define the free product of fundamental groups as a FreeGroupEq quotient and
show that any pair of homomorphisms from π₁(A) and π₁(B) induces a unique map
out of the free product, characterized by the word-lift construction.
-/

end FreeProductUniversal
end CompPath
end Path
end ComputationalPaths
