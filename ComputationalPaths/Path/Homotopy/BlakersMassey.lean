/-
# Blakers-Massey Theorem (Computational Paths)

This module records the path-level data needed for Blakers-Massey style
statements. The focus is on Path-valued commutativity witnesses and canonical
glue paths in the computational pushout.

## Key Results

- `PushoutSquare`: Path-valued commutative square data.
- `canonicalSquare`: the canonical pushout square for `PushoutCompPath`.
- `glue_cancel_right`, `glue_cancel_left`: glue cancellation via `RwEq`.

## References

- Blakers and Massey, "The Homotopy Groups of a Triad"
- HoTT Book, Chapter 8.5
-/

import ComputationalPaths.Path.CompPath.PushoutCompPath
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace BlakersMassey

universe u

/-! ## Pushout squares -/

/-- A pushout square specified by a Path-valued commutativity witness. -/
structure PushoutSquare (A B C P : Type u)
    (f : C → A) (g : C → B) (inl : A → P) (inr : B → P) : Type u where
  /-- The square commutes up to Path in the pushout corner. -/
  comm : (c : C) → Path (inl (f c)) (inr (g c))

/-- The canonical pushout square for the computational pushout type. -/
def canonicalSquare (A B C : Type u) (f : C → A) (g : C → B) :
    PushoutSquare A B C (CompPath.PushoutCompPath A B C f g) f g
      (CompPath.PushoutCompPath.inl (A := A) (B := B) (C := C) (f := f) (g := g))
      (CompPath.PushoutCompPath.inr (A := A) (B := B) (C := C) (f := f) (g := g)) where
  comm := fun c =>
    CompPath.PushoutCompPath.glue (A := A) (B := B) (C := C) (f := f) (g := g) c

/-! ## Glue cancellation -/

/-- Glue followed by its inverse is rewrite-equivalent to the identity path. -/
noncomputable def glue_cancel_right {A B C : Type u} {f : C → A} {g : C → B} (c : C) :
    RwEq
      (Path.trans
        (CompPath.PushoutCompPath.glue (A := A) (B := B) (C := C) (f := f) (g := g) c)
        (CompPath.PushoutCompPath.glueInv (A := A) (B := B) (C := C) (f := f) (g := g) c))
      (Path.refl
        (CompPath.PushoutCompPath.inl (A := A) (B := B) (C := C) (f := f) (g := g) (f c))) := by
  simpa [CompPath.PushoutCompPath.glueInv] using
    (rweq_cmpA_inv_right
      (p := CompPath.PushoutCompPath.glue (A := A) (B := B) (C := C) (f := f) (g := g) c))

/-- Inverse glue followed by glue is rewrite-equivalent to the identity path. -/
noncomputable def glue_cancel_left {A B C : Type u} {f : C → A} {g : C → B} (c : C) :
    RwEq
      (Path.trans
        (CompPath.PushoutCompPath.glueInv (A := A) (B := B) (C := C) (f := f) (g := g) c)
        (CompPath.PushoutCompPath.glue (A := A) (B := B) (C := C) (f := f) (g := g) c))
      (Path.refl
        (CompPath.PushoutCompPath.inr (A := A) (B := B) (C := C) (f := f) (g := g) (g c))) := by
  simpa [CompPath.PushoutCompPath.glueInv] using
    (rweq_cmpA_inv_left
      (p := CompPath.PushoutCompPath.glue (A := A) (B := B) (C := C) (f := f) (g := g) c))

/-! ## Summary -/

end BlakersMassey
end Path
end ComputationalPaths
