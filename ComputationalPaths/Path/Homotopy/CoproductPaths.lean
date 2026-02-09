/-
# Coproduct Paths (Sum and Wedge)

This module packages the coproduct (disjoint union) of path spaces for sum types
and restates the pointed coproduct (wedge) consequences on fundamental groups.

## Key Results
- `coproductPathCode`: coproduct path spaces for `Sum` (disjoint union).
- `coproductPathEncode`/`coproductPathDecode`: encode/decode maps with `toEq` round-trips.
- `coproductPiOneEquivFreeProduct`: π₁ of a pointed coproduct (wedge) is a free product.
- `coproductPiOneWordLift`: universal map out of π₁ of the coproduct.

## References
- HoTT Book, Chapter 2 (paths in sum types)
- HoTT Book, Chapter 8 (free products and van Kampen)
-/

import ComputationalPaths.Path.Homotopy.Coproduct
import ComputationalPaths.Path.CompPath.PushoutCompPath
import ComputationalPaths.Path.CompPath.PushoutPaths
import ComputationalPaths.Path.CompPath.WedgeFreeProductUniversal

namespace ComputationalPaths
namespace Path

open CompPath

universe u

/-! ## Coproduct (Sum) Paths -/

variable {A : Type u} {B : Type u}

/-- Coproduct (disjoint union) of types. -/
abbrev Coproduct (A : Type u) (B : Type u) : Type u := Sum A B

namespace Coproduct

/-- Left injection into the coproduct. -/
abbrev inl (a : A) : Coproduct A B := Sum.inl a

/-- Right injection into the coproduct. -/
abbrev inr (b : B) : Coproduct A B := Sum.inr b

end Coproduct

/-- Helper: Sum.inl a ≠ Sum.inr b. -/
private theorem sum_inl_ne_inr (a : A) (b : B) : Sum.inl a ≠ Sum.inr b := by
  intro h
  cases h

/-- Helper: Sum.inr b ≠ Sum.inl a. -/
private theorem sum_inr_ne_inl (b : B) (a : A) : Sum.inr b ≠ Sum.inl a := by
  intro h
  cases h

/-- Path code for coproducts: paths stay within each summand, otherwise empty. -/
def coproductPathCode : Coproduct A B → Coproduct A B → Type u
  | Sum.inl a, Sum.inl a' => Path a a'
  | Sum.inr b, Sum.inr b' => Path b b'
  | _, _ => PEmpty.{u+1}

/-- Encode a coproduct path into its summand path code. -/
def coproductPathEncode {x y : Coproduct A B} (p : Path x y) :
    coproductPathCode (A := A) (B := B) x y := by
  cases x with
  | inl a =>
      cases y with
      | inl a' =>
          exact Path.ofEq (Sum.inl.injEq a a' ▸ p.toEq)
      | inr b =>
          exact absurd p.toEq (sum_inl_ne_inr (A := A) (B := B) a b)
  | inr b =>
      cases y with
      | inl a =>
          exact absurd p.toEq (sum_inr_ne_inl (A := A) (B := B) b a)
      | inr b' =>
          exact Path.ofEq (Sum.inr.injEq b b' ▸ p.toEq)

/-- Decode a coproduct path code back to a path in the coproduct. -/
def coproductPathDecode {x y : Coproduct A B}
    (c : coproductPathCode (A := A) (B := B) x y) : Path x y := by
  cases x with
  | inl a =>
      cases y with
      | inl a' => exact inlCongr c
      | inr b => exact c.elim
  | inr b =>
      cases y with
      | inl a => exact c.elim
      | inr b' => exact inrCongr c

/-- Encoding then decoding preserves the underlying equality (`toEq`). -/
theorem coproductPathDecode_encode_toEq {x y : Coproduct A B} (p : Path x y) :
    (coproductPathDecode (A := A) (B := B)
        (coproductPathEncode (A := A) (B := B) p)).toEq = p.toEq := by
  cases x <;> cases y <;> cases p with
  | mk steps proof =>
      cases proof <;> rfl

/-- Encoding then decoding on left summand preserves `toEq`. -/
theorem coproductPathEncode_decode_inl_toEq (a₀ a : A) (p : Path a₀ a) :
    (coproductPathEncode (A := A) (B := B)
        (coproductPathDecode (A := A) (B := B)
          (x := Sum.inl a₀) (y := Sum.inl a) p)).toEq = p.toEq := by
  cases p with
  | mk steps proof =>
      cases proof <;> rfl

/-- Encoding then decoding on right summand preserves `toEq`. -/
theorem coproductPathEncode_decode_inr_toEq (b₀ b : B) (p : Path b₀ b) :
    (coproductPathEncode (A := A) (B := B)
        (coproductPathDecode (A := A) (B := B)
          (x := Sum.inr b₀) (y := Sum.inr b) p)).toEq = p.toEq := by
  cases p with
  | mk steps proof =>
      cases proof <;> rfl

/-- No paths between left and right injections. -/
theorem coproduct_inl_inr_path_empty (a : A) (b : B)
    (p : Path (Sum.inl a : Coproduct A B) (Sum.inr b)) : False :=
  absurd p.toEq (sum_inl_ne_inr (A := A) (B := B) a b)

/-- No paths between right and left injections. -/
theorem coproduct_inr_inl_path_empty (a : A) (b : B)
    (p : Path (Sum.inr b : Coproduct A B) (Sum.inl a)) : False :=
  absurd p.toEq (sum_inr_ne_inl (A := A) (B := B) b a)

/-! ## Pointed Coproduct (Wedge) and π₁ -/

section PointedCoproduct

variable {A : Type u} {B : Type u} (a₀ : A) (b₀ : B)

/-- Pointed coproduct (wedge sum) of `A` and `B`. -/
abbrev PointedCoproduct : Type u := Wedge A B a₀ b₀

/-- π₁ of a pointed coproduct is the free product (word level) under SVK. -/
noncomputable def coproductPiOneEquivFreeProduct
    [HasWedgeSVKDecodeBijective A B a₀ b₀] :
    SimpleEquiv
      (π₁(PointedCoproduct (A := A) (B := B) a₀ b₀, Wedge.basepoint))
      (WedgeFreeProductCode (A := A) (B := B) a₀ b₀) :=
  wedgeFundamentalGroupEquiv_of_decode_bijective (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)

variable {H : Type u}

/-- Universal map out of π₁ of the coproduct, induced by maps on the factors. -/
noncomputable def coproductPiOneWordLift
    [HasWedgeSVKDecodeBijective A B a₀ b₀] [One H] [Mul H]
    (φ₁ : π₁(A, a₀) → H) (φ₂ : π₁(B, b₀) → H) :
    π₁(PointedCoproduct (A := A) (B := B) a₀ b₀, Wedge.basepoint) → H :=
  WedgeFreeProductUniversal.wedgePiOneWordLift
    (A := A) (B := B) (H := H) a₀ b₀ φ₁ φ₂

/-- The coproduct lift agrees with `wordLift` on decoded words. -/
theorem coproductPiOneWordLift_decode
    [HasWedgeSVKDecodeBijective A B a₀ b₀] [One H] [Mul H]
    (φ₁ : π₁(A, a₀) → H) (φ₂ : π₁(B, b₀) → H)
    (w : WedgeFreeProductCode (A := A) (B := B) a₀ b₀) :
    coproductPiOneWordLift (A := A) (B := B) (H := H) a₀ b₀ φ₁ φ₂
        (wedgeFreeProductDecode (A := A) (B := B) a₀ b₀ w) =
      FreeProductUniversal.wordLift
        (G₁ := π₁(A, a₀)) (G₂ := π₁(B, b₀)) (H := H) φ₁ φ₂ w := by
  simpa [coproductPiOneWordLift] using
    (WedgeFreeProductUniversal.wedgePiOneWordLift_decode
      (A := A) (B := B) (H := H) a₀ b₀ φ₁ φ₂ w)

end PointedCoproduct

/-! ## Connected Coproducts -/

section ConnectedCoproduct

variable {A : Type u} {B : Type u}
variable [CompPath.IsPathConnected A] [CompPath.IsPathConnected B]

/-- Coproduct of connected types (wedge at chosen basepoints). -/
abbrev ConnectedCoproduct : Type u :=
  Wedge A B
    (CompPath.IsPathConnected.base (A := A))
    (CompPath.IsPathConnected.base (A := B))

/-- Basepoint for the connected coproduct. -/
@[simp] def connectedCoproductBasepoint : ConnectedCoproduct (A := A) (B := B) :=
  Wedge.basepoint (A := A) (B := B)
    (a₀ := CompPath.IsPathConnected.base (A := A))
    (b₀ := CompPath.IsPathConnected.base (A := B))

/-- π₁ of a connected coproduct is the free product (word level) under SVK. -/
noncomputable def connectedCoproductPiOneEquivFreeProduct
    [HasWedgeSVKDecodeBijective A B
      (CompPath.IsPathConnected.base (A := A))
      (CompPath.IsPathConnected.base (A := B))] :
    SimpleEquiv
      (π₁(ConnectedCoproduct (A := A) (B := B),
        connectedCoproductBasepoint (A := A) (B := B)))
      (WedgeFreeProductCode (A := A) (B := B)
        (CompPath.IsPathConnected.base (A := A))
        (CompPath.IsPathConnected.base (A := B))) :=
  coproductPiOneEquivFreeProduct
    (A := A) (B := B)
    (a₀ := CompPath.IsPathConnected.base (A := A))
    (b₀ := CompPath.IsPathConnected.base (A := B))

end ConnectedCoproduct

/-! ## Summary

We package coproduct (sum) path codes with encode/decode maps, restate the wedge
π₁ free-product equivalence, and provide the universal map out of the coproduct
fundamental group.
-/

end Path
end ComputationalPaths
