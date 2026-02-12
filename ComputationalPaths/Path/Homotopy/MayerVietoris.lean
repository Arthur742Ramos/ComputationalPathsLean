/- 
# Mayer-Vietoris Sequence for Fundamental Groups

This module packages a Mayer-Vietoris style sequence for a pushout cover:

  C --g--> B
  |        |
  f        inr
  v        v
  A --inl-> Pushout A B C f g

We define the connecting map π₁(C) → π₁(A) × π₁(B), the folding map to
π₁(Pushout), and show that the composite is trivial (image ⊆ kernel).

## Key Results

- `mvConnecting`: the diagonal map induced by f and g
- `mvFold`: the map to π₁(Pushout) using the two inclusions
- `mvExactAtPieces`: exactness at the middle term (composite is trivial)

## References

- HoTT Book, Chapter 8.7 (Seifert-van Kampen and Mayer-Vietoris)
-/

import ComputationalPaths.Path.CompPath.PushoutPaths
import ComputationalPaths.Path.Homotopy.FundamentalGroup

namespace ComputationalPaths
namespace Path
namespace Homotopy

open CompPath

universe u

/-! ## Mayer-Vietoris maps -/

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B}

/-- The induced map π₁(C) → π₁(A) from the left leg of the cover. -/
noncomputable abbrev mvLeft (c₀ : C) : π₁(C, c₀) → π₁(A, f c₀) :=
  CompPath.piOneFmap (f := f) (c₀ := c₀)

/-- The induced map π₁(C) → π₁(B) from the right leg of the cover. -/
noncomputable abbrev mvRight (c₀ : C) : π₁(C, c₀) → π₁(B, g c₀) :=
  CompPath.piOneGmap (g := g) (c₀ := c₀)

/-- Connecting map π₁(C) → π₁(A) × π₁(B). -/
noncomputable def mvConnecting (c₀ : C) :
    π₁(C, c₀) → π₁(A, f c₀) × π₁(B, g c₀) :=
  fun γ => (mvLeft (f := f) c₀ γ, mvRight (g := g) c₀ γ)

/-- Fold map π₁(A) × π₁(B) → π₁(Pushout). -/
noncomputable def mvFold (c₀ : C) :
    π₁(A, f c₀) × π₁(B, g c₀) →
      π₁(Pushout A B C f g, Pushout.inl (f c₀)) :=
  fun p =>
    PiOne.mul
      (CompPath.pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ p.1)
      (PiOne.inv
        (CompPath.pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ p.2))

/-! ## Amalgamation in π₁(Pushout) -/

/-- The two induced maps from π₁(C) agree in π₁(Pushout). -/
theorem mv_amalgamate
    (c₀ : C)
    [Pushout.HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    (γ : π₁(C, c₀)) :
    CompPath.pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (mvLeft (f := f) c₀ γ) =
      CompPath.pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (mvRight (g := g) c₀ γ) := by
  have h :=
    CompPath.pushoutDecode_respects_amalg (A := A) (B := B) (C := C)
      (f := f) (g := g) c₀ γ (FreeProductWord.nil)
  have h' :
      CompPath.piOneMul
          (CompPath.pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀
            (mvLeft (f := f) c₀ γ))
          (Quot.mk _ (Path.refl (Pushout.inl (f c₀)))) =
        CompPath.piOneMul
          (CompPath.pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀
            (mvRight (g := g) c₀ γ))
          (Quot.mk _ (Path.refl (Pushout.inl (f c₀)))) := by
    simpa [CompPath.pushoutDecode_consLeft, CompPath.pushoutDecode_consRight,
      CompPath.pushoutDecode] using h
  have hleft :
      CompPath.piOneMul
          (CompPath.pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀
            (mvLeft (f := f) c₀ γ))
          (Quot.mk _ (Path.refl (Pushout.inl (f c₀)))) =
        CompPath.pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀
          (mvLeft (f := f) c₀ γ) :=
    CompPath.piOneMul_refl_right
      (X := Pushout A B C f g)
      (x₀ := Pushout.inl (f c₀))
      (α := CompPath.pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (mvLeft (f := f) c₀ γ))
  have hright :
      CompPath.piOneMul
          (CompPath.pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀
            (mvRight (g := g) c₀ γ))
          (Quot.mk _ (Path.refl (Pushout.inl (f c₀)))) =
        CompPath.pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀
          (mvRight (g := g) c₀ γ) :=
    CompPath.piOneMul_refl_right
      (X := Pushout A B C f g)
      (x₀ := Pushout.inl (f c₀))
      (α := CompPath.pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (mvRight (g := g) c₀ γ))
  calc
    CompPath.pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (mvLeft (f := f) c₀ γ) =
      CompPath.piOneMul
          (CompPath.pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀
            (mvLeft (f := f) c₀ γ))
          (Quot.mk _ (Path.refl (Pushout.inl (f c₀)))) := hleft.symm
    _ =
      CompPath.piOneMul
          (CompPath.pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀
            (mvRight (g := g) c₀ γ))
          (Quot.mk _ (Path.refl (Pushout.inl (f c₀)))) := h'
    _ =
      CompPath.pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (mvRight (g := g) c₀ γ) := hright

/-! ## Exactness (image ⊆ kernel) -/

/-- Mayer-Vietoris exactness at the middle term: the composite is trivial. -/
theorem mvExactAtPieces
    (c₀ : C)
    [Pushout.HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    (γ : π₁(C, c₀)) :
    mvFold (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (mvConnecting (A := A) (B := B) (C := C) (f := f) (g := g) c₀ γ) =
      PiOne.id := by
  have h :=
    mv_amalgamate (A := A) (B := B) (C := C) (f := f) (g := g) c₀ γ
  simp [mvFold, mvConnecting, h]


private def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

/-! ## Summary

We define the Mayer-Vietoris connecting and folding maps for a pushout cover
and show the standard exactness property that the composite is trivial.
-/

end Homotopy
end Path
end ComputationalPaths
