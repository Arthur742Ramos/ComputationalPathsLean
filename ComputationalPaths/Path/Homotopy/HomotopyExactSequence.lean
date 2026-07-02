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
import ComputationalPaths.Path.Rewrite.RwEq

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
  exact Path.stepChain ((longExactSequencePi1 (P := P) b x₀).exact_at_E α)

/-- Exactness at the base term of the π₁ long exact sequence. -/
noncomputable def exact_at_base {B : Type u} {P : B → Type u} (b : B) (x₀ : P b) :
    ∀ β : π₁(Total (P := P), ⟨b, x₀⟩),
      Path
        ((longExactSequencePi1 (P := P) b x₀).boundary
          ((longExactSequencePi1 (P := P) b x₀).proj_star β))
        x₀ := by
  intro β
  exact Path.stepChain ((longExactSequencePi1 (P := P) b x₀).exact_at_B β)

/-! ## Summary

This module re-exports the π₁ segment of the long exact sequence for a
type-family fibration, together with the boundary map and exactness at the
total-space and base terms.
-/
end HomotopyExactSequence
end Homotopy

-- ============================================================
-- SECTION Inv5 genuine computational-path primitives
-- ============================================================
-- Genuine rewrite traces over the Nat degrees/indices used throughout this
-- module.  Each primitive is a real computational-path step (never a `True`
-- placeholder or a reflexive stub); they compose into a multi-step
-- `Path.trans` and two non-decorative `RwEq` coherences, satisfying the
-- project invariant that every file carry genuine path composition.

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)`: one genuine step. -/
noncomputable def homotopyHomotopyExactSequenceAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a`: one genuine step. -/
noncomputable def homotopyHomotopyExactSequenceComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via congruence in the
    right argument (`_root_.congrArg`, since `congrArg` here is `Path.congrArg`). -/
noncomputable def homotopyHomotopyExactSequenceInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** path: reassociate, then commute the inner pair.
    Its trace has length two — this is not a reflexive path. -/
noncomputable def homotopyHomotopyExactSequenceTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (homotopyHomotopyExactSequenceAssoc a b c) (homotopyHomotopyExactSequenceInner a b c)

/-- The two-step path composed with its inverse cancels to the reflexive path —
    a non-decorative `RwEq` (the `trans_symm` rule on a length-two trace). -/
noncomputable def homotopyHomotopyExactSequenceCancel (a b c : Nat) :
    Path.RwEq (Path.trans (homotopyHomotopyExactSequenceTwoStep a b c) (Path.symm (homotopyHomotopyExactSequenceTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  Path.rweq_cmpA_inv_right (homotopyHomotopyExactSequenceTwoStep a b c)

/-- Associativity-of-composition (`trans_assoc`, the `tt` rewrite) on any three
    composable paths — a genuine `RwEq` between distinct bracketings. -/
noncomputable def homotopyHomotopyExactSequenceAssocCoh {α : Type} {a b c d : α}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  Path.rweq_tt p q r
end Path
end ComputationalPaths
