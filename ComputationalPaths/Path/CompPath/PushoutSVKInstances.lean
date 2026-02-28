/-
# Pushout SVK Instances

Instances of the Seifert-van Kampen theorem for pushouts.
-/

import ComputationalPaths.Path.CompPath.PushoutPaths

namespace ComputationalPaths.Path.CompPath.PushoutSVKInstances

universe u

section

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B} (c₀ : C)

@[simp] theorem pushout_svk_inl_mul (α β : π₁(A, f c₀)) :
    pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (piOneMul α β) =
      piOneMul
        (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α)
        (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β) := by
  simpa using pushoutPiOneInl_mul (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α β

@[simp] theorem pushout_svk_inr_mul (β₁ β₂ : π₁(B, g c₀)) :
    pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (piOneMul β₁ β₂) =
      piOneMul
        (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β₁)
        (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β₂) := by
  simpa using pushoutPiOneInr_mul (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β₁ β₂

@[simp] theorem pushout_svk_decode_cons_left
    (α : π₁(A, f c₀)) (rest : PushoutCode A B C f g c₀) :
    pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (.consLeft α rest) =
      piOneMul
        (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α)
        (pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ rest) := by
  simpa using pushoutDecode_consLeft (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α rest

@[simp] theorem pushout_svk_decode_cons_right
    (β : π₁(B, g c₀)) (rest : PushoutCode A B C f g c₀) :
    pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (.consRight β rest) =
      piOneMul
        (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β)
        (pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ rest) := by
  simpa using pushoutDecode_consRight (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β rest

end

end ComputationalPaths.Path.CompPath.PushoutSVKInstances
