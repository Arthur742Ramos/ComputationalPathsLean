/-
# Universal Property for Wedge Free Products

This module packages the free-product word machinery needed for wedge sums.
We equip free-product words with a strict monoid structure, build the
`wordLift`-based monoid homomorphism, and show that the wedge decode map is the
unique monoid homomorphism extending the canonical injections on π₁.

## Key Results

- `FreeProductWord.strictMonoid`: strict monoid structure via concatenation
- `FreeProductUniversal.wordLiftMonoidHom`: monoid hom induced by `wordLift`
- `FreeProductUniversal.wordLiftMonoidHom_unique`: uniqueness of word lifts
- `wedgeFreeProductDecodeMonoidHom`: wedge decode as a monoid homomorphism

## References

- `PushoutPaths.lean` (free product words and wedge decode)
- HoTT Book, Chapter 8 (free products of fundamental groups)
-/

import ComputationalPaths.Path.CompPath.PushoutPaths
import ComputationalPaths.Path.Algebra.GroupStructures

namespace ComputationalPaths
namespace Path
namespace CompPath

open Algebra
open FreeProductWord
open FreeProductUniversal

universe u v w

/-! ## Free product words as a strict monoid -/

namespace FreeProductWord

/-- Strict monoid structure on free product words via concatenation. -/
@[simp] noncomputable def strictMonoid (G₁ : Type u) (G₂ : Type v) :
    StrictMonoid (FreeProductWord G₁ G₂) := by
  refine
    { mul := FreeProductWord.concat
      one := FreeProductWord.nil
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_ }
  · intro x y z
    exact FreeProductWord.concat_assoc x y z
  · intro x
    rfl
  · intro x
    exact FreeProductWord.concat_nil_right x

end FreeProductWord

/-! ## Monoid homomorphisms from free product words -/

namespace FreeProductUniversal

variable {G₁ : Type u} {G₂ : Type v} {H : Type w}

local instance (S : StrictMonoid H) : One H := ⟨S.one⟩
local instance (S : StrictMonoid H) : Mul H := ⟨S.mul⟩

/-- Monoid hom induced by `wordLift`. -/
noncomputable def wordLiftMonoidHom (S : StrictMonoid H) (φ₁ : G₁ → H) (φ₂ : G₂ → H) :
    MonoidHom (FreeProductWord G₁ G₂) H
      (FreeProductWord.strictMonoid G₁ G₂) S := by
  refine
    { toFun := wordLift φ₁ φ₂
      map_mul := ?_
      map_one := ?_ }
  · intro w₁ w₂
    simpa using
      (wordLift_concat (hone_mul := S.one_mul) (hmul_assoc := S.mul_assoc)
        (φ₁ := φ₁) (φ₂ := φ₂) w₁ w₂)
  · rfl

/-- `wordLiftMonoidHom` sends singleton left words to `φ₁`. -/
@[simp] theorem wordLiftMonoidHom_singleLeft (S : StrictMonoid H) (φ₁ : G₁ → H) (φ₂ : G₂ → H)
    (x : G₁) :
    wordLiftMonoidHom (G₁ := G₁) (G₂ := G₂) S φ₁ φ₂ (FreeProductWord.singleLeft x) = φ₁ x := by
  simpa using
    (wordLift_singleLeft (hmul_one := S.mul_one) (φ₁ := φ₁) (φ₂ := φ₂) x)

/-- `wordLiftMonoidHom` sends singleton right words to `φ₂`. -/
@[simp] theorem wordLiftMonoidHom_singleRight (S : StrictMonoid H) (φ₁ : G₁ → H) (φ₂ : G₂ → H)
    (y : G₂) :
    wordLiftMonoidHom (G₁ := G₁) (G₂ := G₂) S φ₁ φ₂ (FreeProductWord.singleRight y) = φ₂ y := by
  simpa using
    (wordLift_singleRight (hmul_one := S.mul_one) (φ₁ := φ₁) (φ₂ := φ₂) y)

/-- Uniqueness: a monoid hom from free product words is determined by its values on singletons. -/
theorem wordLiftMonoidHom_unique (S : StrictMonoid H) (φ₁ : G₁ → H) (φ₂ : G₂ → H)
    (f : MonoidHom (FreeProductWord G₁ G₂) H
      (FreeProductWord.strictMonoid G₁ G₂) S)
    (hleft : ∀ x, f (FreeProductWord.singleLeft x) = φ₁ x)
    (hright : ∀ y, f (FreeProductWord.singleRight y) = φ₂ y) :
    ∀ w, f w = wordLift φ₁ φ₂ w := by
  intro w
  induction w with
  | nil =>
      simpa using f.map_one
  | consLeft x rest ih =>
      calc
        f (FreeProductWord.consLeft x rest)
            = f (FreeProductWord.concat (FreeProductWord.singleLeft x) rest) := by
                simp [FreeProductWord.singleLeft, FreeProductWord.concat]
        _ = S.mul (f (FreeProductWord.singleLeft x)) (f rest) := by
                simpa using f.map_mul (FreeProductWord.singleLeft x) rest
        _ = S.mul (φ₁ x) (wordLift φ₁ φ₂ rest) := by
                simp [hleft, ih]
        _ = wordLift φ₁ φ₂ (FreeProductWord.consLeft x rest) := by
                rfl
  | consRight y rest ih =>
      calc
        f (FreeProductWord.consRight y rest)
            = f (FreeProductWord.concat (FreeProductWord.singleRight y) rest) := by
                simp [FreeProductWord.singleRight, FreeProductWord.concat]
        _ = S.mul (f (FreeProductWord.singleRight y)) (f rest) := by
                simpa using f.map_mul (FreeProductWord.singleRight y) rest
        _ = S.mul (φ₂ y) (wordLift φ₁ φ₂ rest) := by
                simp [hright, ih]
        _ = wordLift φ₁ φ₂ (FreeProductWord.consRight y rest) := by
                rfl

end FreeProductUniversal

/-! ## Wedge free product decode as a monoid homomorphism -/

section WedgeFreeProduct

variable {A : Type u} {B : Type v} (a₀ : A) (b₀ : B)

/-- Strict monoid structure on `π₁` using `piOneMul`. -/
noncomputable def piOneStrictMonoid (X : Type u) (x₀ : X) :
    StrictMonoid (π₁(X, x₀)) := by
  refine
    { mul := piOneMul
      one := Quot.mk _ (Path.refl x₀)
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_ }
  · intro x y z
    exact piOneMul_assoc x y z
  · intro x
    exact piOneMul_refl_left x
  · intro x
    exact piOneMul_refl_right x

/-- Left injection of `π₁(A)` into `π₁(A ∨ B)`. -/
noncomputable def wedgePiOneInl :
    π₁(A, a₀) → π₁(Wedge A B a₀ b₀, Wedge.basepoint) :=
  Quot.lift
    (fun p => Quot.mk _ (Pushout.inlPath p))
    (fun _ _ hp => Quot.sound (rweq_congrArg_of_rweq Pushout.inl hp))

/-- Right injection of `π₁(B)` into `π₁(A ∨ B)` (conjugated by the glue path). -/
noncomputable def wedgePiOneInr :
    π₁(B, b₀) → π₁(Wedge A B a₀ b₀, Wedge.basepoint) :=
  Quot.lift
    (fun p => Quot.mk _ (Path.trans
      (Wedge.glue (A := A) (B := B) (a₀ := a₀) (b₀ := b₀))
      (Path.trans (Pushout.inrPath p)
        (Path.symm (Wedge.glue (A := A) (B := B) (a₀ := a₀) (b₀ := b₀))))))
    (fun _ _ hp => Quot.sound (
      rweq_trans_congr_right _ (rweq_trans_congr_left _
        (rweq_congrArg_of_rweq Pushout.inr hp))))

/-- `wedgeFreeProductDecode` packaged as a monoid homomorphism. -/
noncomputable def wedgeFreeProductDecodeMonoidHom :
    MonoidHom (WedgeFreeProductCode (A := A) (B := B) a₀ b₀)
      (π₁(Wedge A B a₀ b₀, Wedge.basepoint))
      (FreeProductWord.strictMonoid (π₁(A, a₀)) (π₁(B, b₀)))
      (piOneStrictMonoid (X := Wedge A B a₀ b₀) Wedge.basepoint) := by
  refine
    { toFun := wedgeFreeProductDecode a₀ b₀
      map_mul := ?_
      map_one := ?_ }
  · intro w₁ w₂
    exact wedgeFreeProductDecode_concat (a₀ := a₀) (b₀ := b₀) w₁ w₂
  · rfl

/-- `wedgeFreeProductDecode` is the word-lift of the wedge injections. -/
theorem wedgeFreeProductDecode_eq_wordLift :
    wedgeFreeProductDecode a₀ b₀ =
      FreeProductUniversal.wordLift
        (wedgePiOneInl (A := A) (B := B) a₀ b₀)
        (wedgePiOneInr (A := A) (B := B) a₀ b₀) := by
  let S := piOneStrictMonoid (X := Wedge A B a₀ b₀) (x₀ := Wedge.basepoint)
  let _ : One (π₁(Wedge A B a₀ b₀, Wedge.basepoint)) := ⟨S.one⟩
  let _ : Mul (π₁(Wedge A B a₀ b₀, Wedge.basepoint)) := ⟨S.mul⟩
  funext w
  induction w with
  | nil =>
      rfl
  | consLeft α rest ih =>
      simp [wedgeFreeProductDecode, FreeProductUniversal.wordLift, ih]
  | consRight β rest ih =>
      simp [wedgeFreeProductDecode, FreeProductUniversal.wordLift, ih]

/-- Uniqueness: monoid homs extending the wedge injections agree with `wedgeFreeProductDecode`. -/
theorem wedgeFreeProductDecode_unique
    (f : MonoidHom (WedgeFreeProductCode (A := A) (B := B) a₀ b₀)
      (π₁(Wedge A B a₀ b₀, Wedge.basepoint))
      (FreeProductWord.strictMonoid (π₁(A, a₀)) (π₁(B, b₀)))
      (piOneStrictMonoid (X := Wedge A B a₀ b₀) Wedge.basepoint))
    (hleft :
      ∀ α, f (FreeProductWord.singleLeft α) =
        wedgePiOneInl (A := A) (B := B) a₀ b₀ α)
    (hright :
      ∀ β, f (FreeProductWord.singleRight β) =
        wedgePiOneInr (A := A) (B := B) a₀ b₀ β) :
    ∀ w, f w = wedgeFreeProductDecode a₀ b₀ w := by
  have h :=
    FreeProductUniversal.wordLiftMonoidHom_unique
      (S := piOneStrictMonoid (X := Wedge A B a₀ b₀) (x₀ := Wedge.basepoint))
      (φ₁ := wedgePiOneInl (A := A) (B := B) a₀ b₀)
      (φ₂ := wedgePiOneInr (A := A) (B := B) a₀ b₀)
      f hleft hright
  intro w
  simpa [wedgeFreeProductDecode_eq_wordLift (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)] using h w

end WedgeFreeProduct

/-! ## Summary

This module packages the universal property of free product words and records
that wedge-sum decoding is a strict-monoid homomorphism uniquely determined by
the wedge injections on fundamental groups.
-/

end CompPath
end Path
end ComputationalPaths
