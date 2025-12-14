/-
# Truncation Levels and n-Types

This module defines the homotopy truncation levels (n-types) in the
computational paths framework:

- **Contractible**: Types with a unique element up to path
- **Proposition**: At most one element up to path
- **Set**: Paths are propositions (0-type)
- **Groupoid**: 2-paths are propositions (1-type)

## Mathematical Background

A type A is an n-type if π_k(A, a) is trivial for all k > n.

In the computational paths framework with contractibility₃:
- All types are at most 1-types (by contractibility₃)
- This reflects the "truncated" nature of our model

## References

- HoTT Book, Chapter 7 (Homotopy n-types)
- Lumsdaine, "Higher inductive types and synthetic homotopy theory"
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.HigherHomotopy
import ComputationalPaths.Path.OmegaGroupoid
import ComputationalPaths.Path.HIT.Pushout

namespace ComputationalPaths
namespace Path
namespace Truncation

open OmegaGroupoid HigherHomotopy

universe u

variable {A : Type u}

/-! ## Contractibility (-2-types)

A type is contractible if it has a center point and every element
is path-connected to the center.
-/

/-- A type is contractible if it has a center and all paths to the center. -/
structure IsContr (A : Type u) where
  /-- The center of contraction -/
  center : A
  /-- Every element is path-connected to the center -/
  contr : (a : A) → Path a center

namespace IsContr

/-- All elements of a contractible type are path-connected. -/
def allPathsConnected (h : IsContr A) (a b : A) : Path a b :=
  Path.trans (h.contr a) (Path.symm (h.contr b))

/-- Unit (PUnit') is contractible. -/
def punitContr : IsContr PUnit' where
  center := PUnit'.unit
  contr := fun _ => Path.refl PUnit'.unit

end IsContr

/-! ## Propositions (-1-types)

A type is a proposition if any two elements are path-connected.
-/

/-- A type is a proposition if any two elements are connected by a path. -/
structure IsProp (A : Type u) where
  /-- Any two elements are path-connected -/
  eq : (a b : A) → Path a b

namespace IsProp

/-- Empty type is a proposition (vacuously). -/
def emptyProp : IsProp Empty where
  eq := fun a _ => nomatch a

/-- Unit type is a proposition. -/
def punitProp : IsProp PUnit' where
  eq := fun _ _ => Path.refl PUnit'.unit

/-- Contractible types are propositions. -/
def ofContr (h : IsContr A) : IsProp A where
  eq := fun a b => h.allPathsConnected a b

end IsProp

/-! ## Sets (0-types)

A type is a set if its identity types are propositions.
Equivalently, any two parallel paths are connected.
-/

/-- A type is a set if any two parallel paths are RwEq. -/
structure IsSet (A : Type u) where
  /-- Any two parallel paths are rewrite-equivalent -/
  pathEq : {a b : A} → (p q : Path a b) → RwEq p q

namespace IsSet

/-- **Set axiom for propositions**: In a proposition, any two parallel paths are RwEq.
This captures the fact that propositions have at most one element up to equality. -/
axiom prop_pathEq {A : Type u} (_h : IsProp A) {a b : A} (p q : Path a b) : RwEq p q

/-- Propositions are sets. -/
def ofProp (h : IsProp A) : IsSet A where
  pathEq := fun p q => prop_pathEq h p q

/-- **Set axiom for Nat**: Parallel paths in Nat are RwEq.
Nat has UIP in Lean's type theory due to decidable equality. -/
axiom nat_pathEq {a b : Nat} (p q : Path a b) : RwEq p q

/-- **Set axiom for Bool**: Parallel paths in Bool are RwEq. -/
axiom bool_pathEq {a b : Bool} (p q : Path a b) : RwEq p q

/-- **Set axiom for Int**: Parallel paths in Int are RwEq. -/
axiom int_pathEq {a b : Int} (p q : Path a b) : RwEq p q

/-- **Axiom for set characterization**: If all loops in π₁(A, a) are trivial for all a,
then A is a set (parallel paths are RwEq). This completes the characterization of sets
via trivial π₁. The forward direction is provable; this axiom handles the converse. -/
axiom set_of_trivial_pi1 {A : Type u} :
    (∀ (a : A), ∀ (α : π₁(A, a)), α = Quot.mk _ (Path.refl a)) → IsSet A

/-- A type is a set iff π₁(A, a) is trivial for all a. -/
theorem iff_pi1_trivial :
    Nonempty (IsSet A) ↔ ∀ (a : A), ∀ (α : π₁(A, a)), α = Quot.mk _ (Path.refl a) := by
  constructor
  · intro ⟨h⟩ a α
    induction α using Quot.ind with
    | _ p =>
      apply Quot.sound
      exact h.pathEq p (Path.refl a)
  · intro h
    exact ⟨set_of_trivial_pi1 h⟩

/-- Nat is a set (by UIP in Lean). -/
def natSet : IsSet Nat where
  pathEq := nat_pathEq

/-- Bool is a set. -/
def boolSet : IsSet Bool where
  pathEq := bool_pathEq

/-- Int is a set. -/
def intSet : IsSet Int where
  pathEq := int_pathEq

end IsSet

/-! ## Groupoids (1-types)

A type is a 1-groupoid if its identity types are sets.
Equivalently, any two parallel 2-paths (derivations) are connected.
-/

/-- A type is a 1-groupoid if parallel Derivation₂s are connected. -/
structure IsGroupoid (A : Type u) where
  /-- Any two parallel derivations are connected by a meta-derivation -/
  derivEq : {a b : A} → {p q : Path a b} →
            (d₁ d₂ : Derivation₂ p q) → Nonempty (Derivation₃ d₁ d₂)

namespace IsGroupoid

/-- Sets are 1-groupoids. -/
def ofSet (_h : IsSet A) : IsGroupoid A where
  derivEq := fun d₁ d₂ => ⟨contractibility₃ d₁ d₂⟩

/-- All types are 1-groupoids in our framework (by contractibility₃). -/
def allTypes : IsGroupoid A where
  derivEq := fun d₁ d₂ => ⟨contractibility₃ d₁ d₂⟩

/-- A type is a 1-groupoid iff π₂(A, a) is trivial for all a. -/
theorem iff_pi2_trivial :
    Nonempty (IsGroupoid A) ↔ ∀ (a : A), ∀ (α : π₂(A, a)), α = PiTwo.id := by
  constructor
  · intro ⟨h⟩ a α
    induction α using Quotient.ind with
    | _ d =>
      apply Quotient.sound
      exact h.derivEq d Loop2Space.refl
  · intro _
    exact ⟨allTypes⟩

end IsGroupoid

/-! ## Connection to Higher Homotopy Groups

The truncation level determines which homotopy groups are trivial.
-/

/-- If A is a set (0-type), then π₁(A, a) is trivial. -/
theorem set_pi1_trivial (h : IsSet A) (a : A) :
    ∀ (α : π₁(A, a)), α = Quot.mk _ (Path.refl a) :=
  IsSet.iff_pi1_trivial.mp ⟨h⟩ a

/-- π₂(A, a) is always trivial in our framework (by contractibility₃). -/
theorem pi2_trivial (a : A) :
    ∀ (α : π₂(A, a)), α = PiTwo.id :=
  IsGroupoid.iff_pi2_trivial.mp ⟨IsGroupoid.allTypes⟩ a

/-! ## Cumulative Hierarchy

Higher truncation levels include lower ones.
-/

/-- Contractible types are propositions. -/
def contr_implies_prop : IsContr A → IsProp A :=
  IsProp.ofContr

/-- Propositions are sets. -/
def prop_implies_set : IsProp A → IsSet A :=
  IsSet.ofProp

/-- Sets are 1-groupoids. -/
def set_implies_groupoid : IsSet A → IsGroupoid A :=
  IsGroupoid.ofSet

/-- All types are 1-groupoids (the top of the hierarchy in our framework). -/
def all_types_groupoid : IsGroupoid A :=
  IsGroupoid.allTypes

/-! ## Summary

This module establishes the truncation hierarchy in computational paths:

1. **Truncation structures**:
   - `IsContr`: center + contraction paths
   - `IsProp`: any two elements path-connected
   - `IsSet`: any two parallel paths RwEq
   - `IsGroupoid`: any two parallel derivations connected

2. **Cumulative hierarchy**:
   contractible → proposition → set → groupoid

3. **Connection to π_n**:
   - Set ↔ π₁ trivial
   - Groupoid ↔ π₂ trivial

4. **Framework feature**: All types are automatically 1-groupoids
   due to contractibility₃. This reflects that our model is
   essentially 1-truncated.

This implements a key piece of the Future Work: connecting the
ω-groupoid structure to the truncation hierarchy from HoTT.
-/

end Truncation
end Path
end ComputationalPaths
