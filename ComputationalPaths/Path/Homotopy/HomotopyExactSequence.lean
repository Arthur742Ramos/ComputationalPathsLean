/-
# Long Exact Sequence of Homotopy Groups for Fibrations

This module packages the long exact sequence on homotopy groups (at the π₁ level)
for a type-family fibration, reusing the constructions already available in
`Fibration` and `LongExactSequence` inside the computational-paths framework.

## Key Results

- `longExactSequencePi1`: the π₁ long exact sequence for a fibration
- `connectingHomomorphism`: the boundary map in the sequence
- `exact_at_totalSpace`, `exact_at_base`: Path witnesses of exactness at the middle terms

## References

- HoTT Book, Chapter 8.4
- May, "A Concise Course in Algebraic Topology"
-/

import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Homotopy.LongExactSequence

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace HomotopyExactSequence

open Fibration LongExactSequence

universe u

/-! ## Long exact sequence -/

/-- The π₁ long exact sequence associated to a type-family fibration. -/
noncomputable def longExactSequencePi1 {B : Type u} {P : B → Type u} (b : B) (x₀ : P b) :
    Fibration.LongExactSequencePi1 (P := P) b x₀ :=
  Fibration.longExactSequence (P := P) b x₀

/-- The boundary map in the π₁ long exact sequence for a fibration. -/
noncomputable def connectingHomomorphism {B : Type u} {P : B → Type u} (b : B) (x₀ : P b) :
    π₁(B, b) → P b :=
  LongExactSequence.connectingHomomorphism (P := P) b x₀

/-- Exactness at the total space term of the π₁ long exact sequence. -/
noncomputable def exact_at_totalSpace {B : Type u} {P : B → Type u} (b : B) (x₀ : P b) :
    ∀ α : π₁(P b, x₀),
      Path
        ((longExactSequencePi1 (P := P) b x₀).proj_star
          ((longExactSequencePi1 (P := P) b x₀).incl_star α))
        (Quot.mk _ (Path.refl b)) := by
  intro α
  exact Path.ofEq ((longExactSequencePi1 (P := P) b x₀).exact_at_E α)

/-- Exactness at the base term of the π₁ long exact sequence. -/
noncomputable def exact_at_base {B : Type u} {P : B → Type u} (b : B) (x₀ : P b) :
    ∀ β : π₁(Total (P := P), ⟨b, x₀⟩),
      Path
        ((longExactSequencePi1 (P := P) b x₀).boundary
          ((longExactSequencePi1 (P := P) b x₀).proj_star β))
        x₀ := by
  intro β
  exact Path.ofEq ((longExactSequencePi1 (P := P) b x₀).exact_at_B β)

/-! ## Summary

This module re-exports the π₁ segment of the long exact sequence for a
type-family fibration, together with the boundary map and exactness at the
total-space and base terms.
-/
end HomotopyExactSequence
end Homotopy
end Path
end ComputationalPaths
