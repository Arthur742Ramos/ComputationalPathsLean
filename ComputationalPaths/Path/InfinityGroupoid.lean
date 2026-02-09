/-
# Infinity-Groupoid Approximation of Computational Paths

This module packages the omega-groupoid tower from `OmegaGroupoid` as an
explicit infinity-groupoid approximation and defines the tower of
n-groupoid truncations.

## Key Results

- `InfinityGroupoid`: tower of cells with coherence witnesses in every dimension
- `cellType`: alias to `OmegaGroupoid.CellType`
- `CoherenceAt` and `coherenceAt`: coherence witnesses per level
- `NGroupoidTruncation` and `truncationTower`: truncated towers of cells

## References

- Lumsdaine, "Weak omega-categories from intensional type theory" (2010)
- van den Berg & Garner, "Types are weak omega-groupoids" (2011)
-/

import ComputationalPaths.Path.OmegaGroupoid

namespace ComputationalPaths
namespace Path
namespace InfinityGroupoid

open OmegaGroupoid

universe u

variable {A : Type u}

/-! ## Cell tower and coherence -/

/-- The cell tower for the infinity-groupoid approximation. -/
abbrev cellType (A : Type u) : Nat → Type u :=
  OmegaGroupoid.CellType A

/-- Coherence at level `n`: any two parallel `n`-cells are connected by an
    `(n+1)`-cell in the tower. -/
def CoherenceAt (A : Type u) : Nat → Type u
  | 0 => PUnit
  | 1 => PUnit
  | 2 =>
      ∀ {a b : A} {p q : Path a b} (d1 d2 : Derivation₂ p q), Derivation₃ d1 d2
  | 3 =>
      ∀ {a b : A} {p q : Path a b} {d1 d2 : Derivation₂ p q}
        (m1 m2 : Derivation₃ d1 d2), Derivation₄ m1 m2
  | n + 4 =>
      ∀ {a b : A} {p q : Path a b} {d1 d2 : Derivation₂ p q}
        {m1 m2 : Derivation₃ d1 d2} (c1 c2 : Derivation₄ m1 m2),
        DerivationHigh n c1 c2

/-- Canonical coherence witnesses for the computational path tower. -/
def coherenceAt (A : Type u) : (n : Nat) → CoherenceAt (A := A) n
  | 0 => PUnit.unit
  | 1 => PUnit.unit
  | 2 => fun d1 d2 => contractibility₃ d1 d2
  | 3 => fun m1 m2 => contractibility₄ m1 m2
  | n + 4 => fun c1 c2 => contractibilityHigh n c1 c2

/-- An infinity-groupoid approximation on a type `A`. -/
structure InfinityGroupoid (A : Type u) where
  /-- Cells in each dimension. -/
  cells : Nat → Type u := cellType A
  /-- Coherence witnesses at each level. -/
  coherence : (n : Nat) → CoherenceAt (A := A) n

/-- The canonical infinity-groupoid approximation for computational paths. -/
def compPathInfinityGroupoid (A : Type u) : InfinityGroupoid A where
  cells := cellType A
  coherence := coherenceAt (A := A)

/-! ## n-groupoid truncations -/

/-- Cell tower truncated at level `n` (higher cells are collapsed to `PUnit`). -/
def truncCell (A : Type u) (n : Nat) : Nat → Type u
  | k => if k ≤ n then cellType A k else PUnit

/-- The `n`-groupoid truncation of the infinity-groupoid tower. -/
structure NGroupoidTruncation (A : Type u) (n : Nat) where
  /-- Cells in each dimension for the truncation. -/
  cells : Nat → Type u := truncCell A n
  /-- Coherence witness at the top level. -/
  coherence : CoherenceAt (A := A) n

/-- The canonical `n`-groupoid truncation for computational paths. -/
def compPathTruncation (A : Type u) (n : Nat) : NGroupoidTruncation A n where
  cells := truncCell A n
  coherence := coherenceAt (A := A) n

/-- The full tower of `n`-groupoid truncations. -/
def truncationTower (A : Type u) : (n : Nat) → NGroupoidTruncation A n :=
  fun n => compPathTruncation A n

/-! ## Summary -/

/-!
We expose the omega-groupoid tower from `OmegaGroupoid` as an explicit
infinity-groupoid approximation, define a tower of `n`-groupoid truncations,
and package canonical coherence witnesses at each level.
-/

end InfinityGroupoid
end Path
end ComputationalPaths
