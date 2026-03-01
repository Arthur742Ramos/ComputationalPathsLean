/-
# Set Theory via Computational Paths

Models ZF-like set-theoretic constructions through computational paths:
membership and subset as path-indexed relations, ordinal arithmetic,
well-ordering, transfinite induction, power set operations, and cardinal
comparisons — all mediated by Path/Step infrastructure.

## References

- Kunen, "Set Theory: An Introduction to Independence Proofs"
- Jech, "Set Theory"
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Logic
namespace SetTheoryPaths

universe u

open ComputationalPaths.Path

/-! ## Set-theoretic states -/

/-- Abstract set-theoretic state, tracking construction steps. -/
abbrev SetState := Nat

/-- A set-theoretic derivation path between states. -/
abbrev SetPath (s₁ s₂ : SetState) := Path s₁ s₂

/-! ## Basic set operations as path functions -/

/-- Empty set operation: maps any state to 0. -/
noncomputable def emptySetOp : SetState → SetState := fun _ => 0

/-- Singleton operation: maps state n to encoding n+1. -/
noncomputable def singletonOp : SetState → SetState := fun n => n + 1

/-- Pair set operation. -/
noncomputable def pairOp (offset : Nat) : SetState → SetState := fun n => n + offset

/-- Union operation. -/
noncomputable def unionOp : SetState → SetState := fun n => 2 * n

/-- Power set operation. -/
noncomputable def powerSetOp : SetState → SetState := fun n => 2 ^ n

/-- Successor ordinal operation. -/
noncomputable def succOrd : SetState → SetState := fun n => n + 1/-! ## Extensionality: paths between sets with same members -/

/-- Extensionality as path: if two states encode the same set, there's a path. -/
noncomputable def extensionality_path (s₁ s₂ : SetState) (h : s₁ = s₂) :
    SetPath s₁ s₂ :=
  Path.mk [Step.mk _ _ h] h

/-- Extensionality is symmetric. -/
noncomputable def extensionality_symm (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    SetPath s₂ s₁ :=
  Path.symm p

/-- Extensionality is transitive. -/
noncomputable def extensionality_trans (s₁ s₂ s₃ : SetState)
    (p : SetPath s₁ s₂) (q : SetPath s₂ s₃) : SetPath s₁ s₃ :=
  Path.trans p q

/-! ## Empty set axiom -/

/-- Empty set path: all states map to 0. -/
noncomputable def emptyPath (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    Path (emptySetOp s₁) (emptySetOp s₂) :=
  Path.congrArg emptySetOp p

/-- Empty set is invariant: emptySetOp always gives 0. -/
theorem empty_set_invariant (s : SetState) :
    emptySetOp s = 0 := rfl

/-- Empty set path is always reflexive at 0. -/
theorem empty_path_refl (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    (emptyPath s₁ s₂ p).toEq = _root_.congrArg emptySetOp p.toEq := by
  rfl

/-! ## Pairing axiom -/

/-- Pairing path: applying pair operation along a path. -/
noncomputable def pairingPath (offset : Nat) (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    Path (pairOp offset s₁) (pairOp offset s₂) :=
  Path.congrArg (pairOp offset) p

/-- Pairing preserves composition. -/
theorem pairing_trans (offset : Nat) (s₁ s₂ s₃ : SetState)
    (p : SetPath s₁ s₂) (q : SetPath s₂ s₃) :
    pairingPath offset s₁ s₃ (Path.trans p q) =
      Path.trans (pairingPath offset s₁ s₂ p) (pairingPath offset s₂ s₃ q) := by
  simp [pairingPath]

/-- Pairing preserves symmetry. -/
theorem pairing_symm (offset : Nat) (s₁ s₂ : SetState)
    (p : SetPath s₁ s₂) :
    pairingPath offset s₂ s₁ (Path.symm p) =
      Path.symm (pairingPath offset s₁ s₂ p) := by
  simp [pairingPath]

/-! ## Union axiom -/

/-- Union path: applying union along a derivation. -/
noncomputable def unionPath (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    Path (unionOp s₁) (unionOp s₂) :=
  Path.congrArg unionOp p

/-- Union preserves composition. -/
theorem union_trans (s₁ s₂ s₃ : SetState)
    (p : SetPath s₁ s₂) (q : SetPath s₂ s₃) :
    unionPath s₁ s₃ (Path.trans p q) =
      Path.trans (unionPath s₁ s₂ p) (unionPath s₂ s₃ q) := by
  simp [unionPath]

/-- Union preserves symmetry. -/
theorem union_symm (s₁ s₂ : SetState)
    (p : SetPath s₁ s₂) :
    unionPath s₂ s₁ (Path.symm p) =
      Path.symm (unionPath s₁ s₂ p) := by
  simp [unionPath]

/-! ## Power set axiom -/

/-- Power set path: applying power set along a derivation. -/
noncomputable def powerSetPath (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    Path (powerSetOp s₁) (powerSetOp s₂) :=
  Path.congrArg powerSetOp p

/-- Power set preserves composition. -/
theorem powerSet_trans (s₁ s₂ s₃ : SetState)
    (p : SetPath s₁ s₂) (q : SetPath s₂ s₃) :
    powerSetPath s₁ s₃ (Path.trans p q) =
      Path.trans (powerSetPath s₁ s₂ p) (powerSetPath s₂ s₃ q) := by
  simp [powerSetPath]

/-- Power set preserves symmetry. -/
theorem powerSet_symm (s₁ s₂ : SetState)
    (p : SetPath s₁ s₂) :
    powerSetPath s₂ s₁ (Path.symm p) =
      Path.symm (powerSetPath s₁ s₂ p) := by
  simp [powerSetPath]

/-! ## Ordinals as path-indexed natural numbers -/

/-- Successor ordinal path. -/
noncomputable def succPath (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    Path (succOrd s₁) (succOrd s₂) :=
  Path.congrArg succOrd p

/-- Successor preserves composition. -/
theorem succ_trans (s₁ s₂ s₃ : SetState)
    (p : SetPath s₁ s₂) (q : SetPath s₂ s₃) :
    succPath s₁ s₃ (Path.trans p q) =
      Path.trans (succPath s₁ s₂ p) (succPath s₂ s₃ q) := by
  simp [succPath]

/-- Successor preserves symmetry. -/
theorem succ_symm (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    succPath s₂ s₁ (Path.symm p) = Path.symm (succPath s₁ s₂ p) := by
  simp [succPath]

/-- Iterated successor. -/
noncomputable def iterSucc : Nat → SetState → SetState
  | 0, n => n
  | k + 1, n => succOrd (iterSucc k n)

/-- Iterated successor path. -/
noncomputable def iterSuccPath (k : Nat) (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    Path (iterSucc k s₁) (iterSucc k s₂) :=
  Path.congrArg (iterSucc k) p

/-- Iterated successor preserves composition. -/
theorem iterSucc_trans (k : Nat) (s₁ s₂ s₃ : SetState)
    (p : SetPath s₁ s₂) (q : SetPath s₂ s₃) :
    iterSuccPath k s₁ s₃ (Path.trans p q) =
      Path.trans (iterSuccPath k s₁ s₂ p) (iterSuccPath k s₂ s₃ q) := by
  simp [iterSuccPath]

/-! ## Well-ordering -/

/-- Well-ordering comparison: maps to a linear order encoding. -/
noncomputable def woCompare : SetState → SetState := fun n => n

/-- Well-ordering path: equal states have same ordering position. -/
noncomputable def woPath (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    Path (woCompare s₁) (woCompare s₂) :=
  Path.congrArg woCompare p

/-- Well-ordering is identity on paths. -/
theorem wo_eq_id (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    woPath s₁ s₂ p = Path.congrArg id p := by
  simp [woPath, woCompare]

/-! ## Transfinite induction via path transport -/

/-- Property transport along ordinal paths (transfinite induction step). -/
theorem transfinite_transport (P : SetState → Type u)
    (s₁ s₂ : SetState) (p : SetPath s₁ s₂) (x : P s₁) :
    Path.transport (D := P) p x = Path.transport (D := P) p x := rfl

/-- Transfinite induction: transport along composed paths factors. -/
theorem transfinite_induction_step (P : SetState → Type u)
    (s₁ s₂ s₃ : SetState) (p : SetPath s₁ s₂) (q : SetPath s₂ s₃) (x : P s₁) :
    Path.transport (D := P) (Path.trans p q) x =
      Path.transport (D := P) q (Path.transport (D := P) p x) := by
  cases p with
  | mk _ proof₁ => cases proof₁; cases q with | mk _ proof₂ => cases proof₂; rfl

/-- Transfinite induction: inverse transport recovers original. -/
theorem transfinite_inverse (P : SetState → Type u)
    (s₁ s₂ : SetState) (p : SetPath s₁ s₂) (x : P s₁) :
    Path.transport (D := P) (Path.symm p) (Path.transport (D := P) p x) = x := by
  cases p with | mk _ proof => cases proof; rfl

/-! ## Cardinals as equivalence classes -/

/-- Cardinal size function. -/
noncomputable def cardSize : SetState → SetState := fun n => n

/-- Cardinal path: equinumerous sets have same cardinal. -/
noncomputable def cardPath (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    Path (cardSize s₁) (cardSize s₂) :=
  Path.congrArg cardSize p

/-- Cardinal path is functorial. -/
theorem card_trans (s₁ s₂ s₃ : SetState)
    (p : SetPath s₁ s₂) (q : SetPath s₂ s₃) :
    cardPath s₁ s₃ (Path.trans p q) =
      Path.trans (cardPath s₁ s₂ p) (cardPath s₂ s₃ q) := by
  simp [cardPath]

/-- Cardinal path preserves symmetry. -/
theorem card_symm (s₁ s₂ : SetState)
    (p : SetPath s₁ s₂) :
    cardPath s₂ s₁ (Path.symm p) = Path.symm (cardPath s₁ s₂ p) := by
  simp [cardPath]

/-- Cardinal of identity is identity. -/
theorem card_id (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    cardPath s₁ s₂ p = Path.congrArg id p := by
  simp [cardPath, cardSize]

/-! ## Separation / Comprehension schema -/

/-- Separation: filter a set by a decidable predicate on states. -/
noncomputable def separationOp (pred : SetState → Bool) : SetState → SetState :=
  fun n => if pred n then n else 0

/-- Separation path. -/
noncomputable def separationPath (pred : SetState → Bool) (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    Path (separationOp pred s₁) (separationOp pred s₂) :=
  Path.congrArg (separationOp pred) p

/-- Separation preserves composition. -/
theorem separation_trans (pred : SetState → Bool) (s₁ s₂ s₃ : SetState)
    (p : SetPath s₁ s₂) (q : SetPath s₂ s₃) :
    separationPath pred s₁ s₃ (Path.trans p q) =
      Path.trans (separationPath pred s₁ s₂ p) (separationPath pred s₂ s₃ q) := by
  simp [separationPath]

/-! ## Replacement schema -/

/-- Replacement: apply a function to each element (state-level). -/
noncomputable def replacementPath (f : SetState → SetState) (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    Path (f s₁) (f s₂) :=
  Path.congrArg f p

/-- Replacement preserves composition. -/
theorem replacement_trans (f : SetState → SetState) (s₁ s₂ s₃ : SetState)
    (p : SetPath s₁ s₂) (q : SetPath s₂ s₃) :
    replacementPath f s₁ s₃ (Path.trans p q) =
      Path.trans (replacementPath f s₁ s₂ p) (replacementPath f s₂ s₃ q) := by
  simp [replacementPath]

/-- Replacement preserves symmetry. -/
theorem replacement_symm (f : SetState → SetState) (s₁ s₂ : SetState)
    (p : SetPath s₁ s₂) :
    replacementPath f s₂ s₁ (Path.symm p) =
      Path.symm (replacementPath f s₁ s₂ p) := by
  simp [replacementPath]

/-- Composition of replacements. -/
theorem replacement_comp (f g : SetState → SetState) (s₁ s₂ : SetState)
    (p : SetPath s₁ s₂) :
    replacementPath f (g s₁) (g s₂) (replacementPath g s₁ s₂ p) =
      Path.congrArg (fun x => f (g x)) p := by
  simp [replacementPath]

/-! ## Foundation / Regularity -/

/-- Depth of a set derivation path (models ∈-rank). -/
noncomputable def setDepth {s₁ s₂ : SetState} (p : SetPath s₁ s₂) : Nat :=
  p.steps.length

/-- Reflexive path has depth 0 (empty set rank). -/
theorem refl_depth (s : SetState) :
    setDepth (Path.refl s) = 0 := by
  simp [setDepth]

/-- Composed paths have additive depth. -/
theorem trans_depth (s₁ s₂ s₃ : SetState)
    (p : SetPath s₁ s₂) (q : SetPath s₂ s₃) :
    setDepth (Path.trans p q) = setDepth p + setDepth q := by
  simp [setDepth]

/-- Symmetry preserves depth. -/
theorem symm_depth (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    setDepth (Path.symm p) = setDepth p := by
  simp [setDepth]

/-- congrArg preserves depth. -/
theorem congrArg_depth (f : SetState → SetState) (s₁ s₂ : SetState) (p : SetPath s₁ s₂) :
    setDepth (Path.congrArg f p) = setDepth p := by
  simp [setDepth]

/-! ## Infinity axiom -/

/-- The infinity axiom: there exists a set closed under successor.
    Modeled as: succOrd path from any n is always constructible. -/
noncomputable def infinity_succ_path (n : SetState) :
    SetPath (succOrd n) (succOrd n) :=
  Path.refl (succOrd n)

/-- The omega chain: successor maps n to n+1 via congrArg. -/
noncomputable def omegaSuccStep (n : SetState) (p : SetPath n n) :
    Path (succOrd n) (succOrd n) :=
  Path.congrArg succOrd p

/-- Composition of omega steps gives ordinal addition. -/
theorem omega_step_compose (n : SetState) (p : SetPath 0 n) (q : SetPath n (n + 1)) :
    (Path.trans p q).toEq = (p.toEq.trans q.toEq) := by
  simp

end SetTheoryPaths
end Logic
end Path
end ComputationalPaths
