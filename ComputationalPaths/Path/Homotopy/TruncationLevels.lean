/-
# Truncation Levels for Computational Paths

This module packages HoTT-style truncation levels for computational paths.
We anchor the (-1) and 0 levels to the existing `IsProp` and `IsSet`
definitions (paths and rewrite equivalence), then define higher levels by
iterating path spaces.

## Key Results

- `TruncLevel`: truncation indices (-1 and nonnegative levels)
- `IsTrunc`: n-truncated types
- `prop_is_trunc_minus_one`: propositions are (-1)-truncated
- `set_is_trunc_zero`: sets are 0-truncated
- `truncation_paths`: positive truncation levels are inherited by path spaces

## Mathematical Background

In HoTT, `isTrunc (n+1) A` is defined by truncation of identity types.
We mirror this for nonnegative levels while keeping the base cases aligned
with computational-path notions of propositions and sets.

## References

- HoTT Book, Chapter 7 (Truncation levels and n-types)
- de Queiroz et al., SAJL 2016 (computational paths)
- Lumsdaine, "Weak omega-categories from intensional type theory"
-/

import ComputationalPaths.Path.Homotopy.Truncation

namespace ComputationalPaths
namespace Path
namespace Truncation

universe u

variable {A : Type u}

/-! ## Truncation levels -/

/-- Truncation indices: (-1) and nonnegative levels. -/
inductive TruncLevel : Type
| negOne : TruncLevel
| nonneg : Nat → TruncLevel

namespace TruncLevel

/-- (-1)-level. -/
abbrev minusOne : TruncLevel := negOne

/-- 0-level. -/
abbrev zero : TruncLevel := nonneg 0

/-- 1-level. -/
abbrev one : TruncLevel := nonneg 1

/-- Successor on truncation levels (HoTT: n maps to n+1). -/
def succ : TruncLevel → TruncLevel
  | negOne => nonneg 0
  | nonneg n => nonneg (n + 1)

@[simp] theorem succ_negOne : succ negOne = nonneg 0 := rfl
@[simp] theorem succ_nonneg (n : Nat) : succ (nonneg n) = nonneg (n + 1) := rfl

end TruncLevel

/-! ## n-truncated types -/

/-- Type-level wrapper for `IsSet`, keeping truncation levels in `Type`. -/
structure IsSetType (A : Type u) : Type u where
  /-- Evidence that `A` is a set. -/
  isSet : IsSet A

/-- `IsTrunc n A` means that `A` is n-truncated in the computational-paths sense. -/
abbrev IsTrunc (n : TruncLevel) (A : Type u) : Type u :=
  match n with
  | TruncLevel.negOne => IsProp A
  | TruncLevel.nonneg 0 => IsSetType A
  | TruncLevel.nonneg (Nat.succ n) =>
      ∀ a b : A, IsTrunc (TruncLevel.nonneg n) (Path a b)

/-! ## Base truncation levels -/

/-- Propositions are (-1)-truncated. -/
abbrev prop_is_trunc_minus_one (h : IsProp A) :
    IsTrunc TruncLevel.negOne A := h

/-- Sets are 0-truncated. -/
abbrev set_is_trunc_zero (h : IsSet A) :
    IsTrunc TruncLevel.zero A := ⟨h⟩

/-! ## Path-space stability -/

/-- For n >= 0, (n+1)-truncation implies n-truncation of path spaces. -/
abbrev truncation_paths {n : Nat} (h : IsTrunc (TruncLevel.nonneg (Nat.succ n)) A)
    (a b : A) : IsTrunc (TruncLevel.nonneg n) (Path a b) :=
  h a b

/-! ## Summary

We package truncation levels for computational paths by:
1. Indexing levels with `TruncLevel` (negative one and nonnegative levels).
2. Defining `IsTrunc` with base cases `IsProp` and `IsSet`, and iterating
   path spaces for higher levels.
3. Recording the standard HoTT-style facts: propositions are (-1)-truncated,
   sets are 0-truncated, and truncation levels are inherited by path types.
-/

end Truncation
end Path
end ComputationalPaths
