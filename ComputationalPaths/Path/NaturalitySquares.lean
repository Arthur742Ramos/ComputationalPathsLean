/-
# Naturality Squares for Fundamental Group Constructions

This module records functoriality and naturality statements for
`SimpleEquiv`, the fundamental group assignment, and the SVK construction.

## Key Results

- `simpleEquiv_comp_id` / `simpleEquiv_id_comp`: identity laws for `SimpleEquiv` composition.
- `simpleEquiv_comp_assoc`: associativity of `SimpleEquiv` composition.
- `inducedPiOneMap_comp`: functoriality of the induced map on π₁.
- `svk_decode_inl` / `svk_decode_inr`: SVK decode commutes with inclusions.
- `svk_amalgamation_square`: the amalgamation square in π₁(Pushout).

## References

- Mac Lane, "Categories for the Working Mathematician"
- Favonia & Shulman, "The Seifert-van Kampen Theorem in HoTT"
-/

import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Homotopy.FundamentalGroupoid
import ComputationalPaths.Path.Homotopy.FundamentalGroupoidFunctor
import ComputationalPaths.Path.CompPath.PushoutPaths

namespace ComputationalPaths
namespace Path
namespace NaturalitySquares

open CompPath

universe u v w x

/-! ## SimpleEquiv Functoriality -/

/-- Right identity for `SimpleEquiv` composition. -/
@[simp] theorem simpleEquiv_comp_id {α : Sort u} {β : Sort v}
    (e : SimpleEquiv α β) :
    SimpleEquiv.comp e (SimpleEquiv.refl β) = e :=
  SimpleEquiv.comp_refl e

/-- Left identity for `SimpleEquiv` composition. -/
@[simp] theorem simpleEquiv_id_comp {α : Sort u} {β : Sort v}
    (e : SimpleEquiv α β) :
    SimpleEquiv.comp (SimpleEquiv.refl α) e = e :=
  SimpleEquiv.refl_comp e

/-- Associativity for `SimpleEquiv` composition. -/
@[simp] theorem simpleEquiv_comp_assoc {α : Sort u} {β : Sort v}
    {γ : Sort w} {δ : Sort x}
    (e : SimpleEquiv α β) (f : SimpleEquiv β γ) (g : SimpleEquiv γ δ) :
    SimpleEquiv.comp (SimpleEquiv.comp e f) g =
      SimpleEquiv.comp e (SimpleEquiv.comp f g) :=
  SimpleEquiv.comp_assoc e f g

/-! ## Functoriality of π₁ -/

/-- Identity induces the identity map on π₁. -/
theorem inducedPiOneMap_id {A : Type u} (a : A) (α : π₁(A, a)) :
    inducedPiOneMap (A := A) (B := A) id a α = α :=
  inducedPiOneMap_idFun (A := A) a α

/-- Composition of functions induces composition on π₁. -/
theorem inducedPiOneMap_comp {A : Type u} {B : Type u} {C : Type u}
    (f : A → B) (g : B → C) (a : A) (α : π₁(A, a)) :
    inducedPiOneMap g (f a) (inducedPiOneMap f a α) =
      inducedPiOneMap (fun x => g (f x)) a α := by
  simpa [inducedPiOneMap] using
    (fundamentalGroupoidMap_compFun (A := A) (B := B) (C := C) f g (p := α))

/-! ## SVK Naturality Squares -/

section SVK

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B} (c₀ : C)
variable [Pushout.HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]

/-- SVK decode commutes with the left inclusion into the amalgamated product. -/
theorem svk_decode_inl (α : π₁(A, f c₀)) :
    pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (AmalgamatedFreeProduct.inl
          (G₁ := π₁(A, f c₀)) (G₂ := π₁(B, g c₀)) (H := π₁(C, c₀))
          (i₁ := piOneFmap c₀) (i₂ := piOneGmap c₀) α) =
      pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α := by
  simp [AmalgamatedFreeProduct.inl, AmalgamatedFreeProduct.ofWord,
    pushoutDecodeAmalg, FreeProductWord.singleLeft, pushoutDecode_consLeft]
  simp [pushoutDecode]
  exact
    (piOneMul_refl_right (X := Pushout A B C f g)
      (x₀ := Pushout.inl (f c₀))
      (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α))

/-- SVK decode commutes with the right inclusion into the amalgamated product. -/
theorem svk_decode_inr (β : π₁(B, g c₀)) :
    pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (AmalgamatedFreeProduct.inr
          (G₁ := π₁(A, f c₀)) (G₂ := π₁(B, g c₀)) (H := π₁(C, c₀))
          (i₁ := piOneFmap c₀) (i₂ := piOneGmap c₀) β) =
      pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β := by
  simp [AmalgamatedFreeProduct.inr, AmalgamatedFreeProduct.ofWord,
    pushoutDecodeAmalg, FreeProductWord.singleRight, pushoutDecode_consRight]
  simp [pushoutDecode]
  exact
    (piOneMul_refl_right (X := Pushout A B C f g)
      (x₀ := Pushout.inl (f c₀))
      (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β))

/-- The amalgamation square in π₁(Pushout) commutes. -/
theorem svk_amalgamation_square (γ : π₁(C, c₀)) :
    pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (piOneFmap c₀ γ) =
      pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (piOneGmap c₀ γ) := by
  have h := pushoutDecode_respects_amalg (A := A) (B := B) (C := C)
    (f := f) (g := g) c₀ γ (FreeProductWord.nil)
  have h' :
      piOneMul (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀
          (piOneFmap c₀ γ))
        (pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ FreeProductWord.nil) =
      piOneMul (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀
          (piOneGmap c₀ γ))
        (pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ FreeProductWord.nil) := by
    simpa [pushoutDecode_consLeft, pushoutDecode_consRight] using h
  have h'' :
      piOneMul (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀
          (piOneFmap c₀ γ))
        (Quot.mk _ (Path.refl (Pushout.inl (f c₀)))) =
      piOneMul (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀
          (piOneGmap c₀ γ))
        (Quot.mk _ (Path.refl (Pushout.inl (f c₀)))) := by
    simpa [pushoutDecode] using h'
  calc
    pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (piOneFmap c₀ γ) =
        piOneMul
          (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀
            (piOneFmap c₀ γ))
          (Quot.mk _ (Path.refl (Pushout.inl (f c₀)))) := by
      exact
        (piOneMul_refl_right (X := Pushout A B C f g)
          (x₀ := Pushout.inl (f c₀))
          (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀
            (piOneFmap c₀ γ))).symm
    _ =
        piOneMul
          (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀
            (piOneGmap c₀ γ))
          (Quot.mk _ (Path.refl (Pushout.inl (f c₀)))) := h''
    _ =
        pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀
          (piOneGmap c₀ γ) := by
      exact
        (piOneMul_refl_right (X := Pushout A B C f g)
          (x₀ := Pushout.inl (f c₀))
          (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀
            (piOneGmap c₀ γ)))

end SVK

private def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

/-! ## Summary

We show that `SimpleEquiv` composition is functorial, the induced map on π₁
respects composition, and the SVK decode map satisfies the expected naturality
and amalgamation squares.
-/

end NaturalitySquares
end Path
end ComputationalPaths
