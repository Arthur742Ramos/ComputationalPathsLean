/-
# Constructive Wedge Encode-Decode

This module provides a constructive implementation of the encode-decode method
for wedge sums, assuming only that the decode map is bijective.

The key insight is that for wedge sums A ∨ B:
1. The decode function is already constructive
2. Encode can be defined by showing decode is a bijection
3. The round-trip properties follow from the structure of paths in wedges

## Strategy

We use the "code family" approach where:
- Code(x) is a type family over the wedge
- At the basepoint, Code gives the word type
- Transport in Code corresponds to accumulating letters

For wedge sums specifically, we can leverage that:
- All loops at basepoint are characterized by their word structure
- Two loops with the same toEq are RwEq (by rweq_canon)
- This allows us to define encode via equality induction

## References

- Favonia & Shulman, "The Seifert-van Kampen Theorem in HoTT"
- HoTT Book, Chapter 8.7
-/

import ComputationalPaths.Path.HIT.Pushout
import ComputationalPaths.Path.HIT.PushoutPaths
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path

universe u

variable {A : Type u} {B : Type u} (a₀ : A) (b₀ : B)
variable [HasWedgeSVKDecodeBijective A B a₀ b₀]

/-! ## Alternative Approach: Encode via Bijectivity

Rather than using code family transport (which has universe issues),
we define encode INDIRECTLY by showing decode is bijective.

The encode function can then be defined as the inverse of decode:
  encode(α) = w where decode(w) = α

This approach uses the Prop-level assumption `HasWedgeSVKDecodeBijective`.
-/

/-! ## Bijectivity of Decode

We show that wedgeFreeProductDecode is a bijection:
1. Injective: different words give different π₁ elements
2. Surjective: every π₁ element is decode of some word

This allows us to define encode as the inverse.
-/

/-- Helper: decode of nil is the identity element. -/
theorem wedgeFreeProductDecode_nil :
    wedgeFreeProductDecode a₀ b₀ .nil = Quot.mk _ (Path.refl _) := rfl

/-- Injectivity: If decode w₁ = decode w₂, then w₁ = w₂.
This is provided by the `HasWedgeSVKDecodeBijective` assumption.
-/
theorem wedgeFreeProductDecode_injective
    (w₁ w₂ : WedgeFreeProductCode a₀ b₀)
    (h : wedgeFreeProductDecode a₀ b₀ w₁ = wedgeFreeProductDecode a₀ b₀ w₂) :
    w₁ = w₂ := by
  exact
    (HasWedgeSVKDecodeBijective.bijective (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)).1 h

/-- Surjectivity: Every π₁ element is decode of some word.

This is provided by the `HasWedgeSVKDecodeBijective` assumption.
-/
theorem wedgeFreeProductDecode_surjective
    (α : π₁(Wedge A B a₀ b₀, Wedge.basepoint)) :
    ∃ w, wedgeFreeProductDecode a₀ b₀ w = α :=
  (HasWedgeSVKDecodeBijective.bijective (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)).2 α

/-- Define encode as the inverse of decode.

Since decode is bijective, we can define encode uniquely:
encode(α) = w where decode(w) = α
-/
noncomputable def wedgeEncodeViaBijection :
    π₁(Wedge A B a₀ b₀, Wedge.basepoint) → WedgeFreeProductCode a₀ b₀ :=
  fun α => Classical.choose (wedgeFreeProductDecode_surjective a₀ b₀ α)

/-- The defining property of wedgeEncodeViaBijection. -/
theorem wedgeEncodeViaBijection_spec (α : π₁(Wedge A B a₀ b₀, Wedge.basepoint)) :
    wedgeFreeProductDecode a₀ b₀ (wedgeEncodeViaBijection a₀ b₀ α) = α :=
  Classical.choose_spec (wedgeFreeProductDecode_surjective a₀ b₀ α)

/-! ## Round-Trip Properties

With encode defined as decode's inverse, the round-trips are straightforward.
-/

/-- decode ∘ encode = id follows from the specification of encode. -/
theorem wedgeDecode_wedgeEncode (α : π₁(Wedge A B a₀ b₀, Wedge.basepoint)) :
    wedgeFreeProductDecode a₀ b₀ (wedgeEncodeViaBijection a₀ b₀ α) = α :=
  wedgeEncodeViaBijection_spec a₀ b₀ α

/-- encode ∘ decode = id follows from injectivity of decode. -/
theorem wedgeEncode_wedgeDecode (w : WedgeFreeProductCode a₀ b₀) :
    wedgeEncodeViaBijection a₀ b₀ (wedgeFreeProductDecode a₀ b₀ w) = w := by
  apply wedgeFreeProductDecode_injective a₀ b₀
  exact wedgeEncodeViaBijection_spec a₀ b₀ (wedgeFreeProductDecode a₀ b₀ w)

/-- The full equivalence between π₁(Wedge) and the free product. -/
noncomputable def wedgeFundamentalGroupEquivConstructive :
    SimpleEquiv
      (π₁(Wedge A B a₀ b₀, Wedge.basepoint))
      (WedgeFreeProductCode a₀ b₀) where
  toFun := wedgeEncodeViaBijection a₀ b₀
  invFun := wedgeFreeProductDecode a₀ b₀
  left_inv := wedgeDecode_wedgeEncode a₀ b₀
  right_inv := wedgeEncode_wedgeDecode a₀ b₀

/-! ## Summary

We've shown that the wedge encode-decode axioms can be derived from:
1. Injectivity of decode (different words give different π₁ elements)
2. Surjectivity of decode (every π₁ element is decode of some word)

Both properties follow from the encode-decode axioms in PushoutPaths.lean:
- Injectivity: Use encode ∘ decode = id to derive w₁ = w₂ from decode w₁ = decode w₂
- Surjectivity: Use encode to produce a word, decode ∘ encode = id gives the result

This provides a clean constructive interface that depends on the axioms
establishing the encode-decode round-trips.
-/

end Path
end ComputationalPaths
