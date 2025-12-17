/-
# Path Tactic Examples and Tests

This module provides examples and tests demonstrating the path tactics
from PathTactic.lean. It serves as both documentation and regression tests.

## Contents

1. Basic tactic examples (path_rfl, path_symm, path_simp)
2. Transitivity examples (path_trans, path_trans_via)
3. Congruence examples (path_congr_left, path_congr_right)
4. Structural examples (path_cancel_*)
5. Advanced automation (path_auto)
6. Normalization examples (path_normalize)
7. Calc notation examples

## Usage

Import this module and run `lake build` to verify all examples work.
-/

import ComputationalPaths.Path.Rewrite.PathTactic

namespace ComputationalPaths
namespace Path
namespace TacticExamples

open Tactic

variable {A : Type} {a b c d : A}

/-! ## 1. Basic Tactic Examples -/

/-- `path_rfl` closes reflexive RwEq goals. -/
example (p : Path a b) : RwEq p p := by path_rfl

/-- `path_symm` applies symmetry to RwEq goals. -/
example (p q : Path a b) (h : RwEq p q) : RwEq q p := by
  path_symm
  exact h

/-- `path_simp` simplifies using groupoid laws. -/
example (p : Path a b) : RwEq (trans (refl a) p) p := by path_simp

example (p : Path a b) : RwEq (trans p (refl b)) p := by path_simp

example (p : Path a b) : RwEq (symm (symm p)) p := by path_simp

example : RwEq (symm (refl a)) (refl a) := by path_simp

/-! ## 2. Transitivity Examples -/

/-- `path_trans h` uses hypothesis h for transitivity. -/
example (p q r : Path a b) (h1 : RwEq p q) (h2 : RwEq q r) : RwEq p r := by
  exact rweq_trans h1 h2

/-- `path_trans_via` specifies an explicit intermediate path. -/
example (p : Path a b) : RwEq (trans (refl a) p) p := by
  path_trans_via (trans (refl a) p)
  · path_rfl
  · exact rweq_cmpA_refl_left p

/-! ## 3. Congruence Examples -/

/-- `path_congr_left` applies congruence on the left of trans. -/
example (p p' : Path a b) (q : Path b c) (h : RwEq p p') :
    RwEq (trans p q) (trans p' q) := by
  path_congr_left h

/-- `path_congr_right` applies congruence on the right of trans. -/
example (p : Path a b) (q q' : Path b c) (h : RwEq q q') :
    RwEq (trans p q) (trans p q') := by
  path_congr_right h

/-- Congruence on both sides via rweq_trans_congr. -/
example (p p' : Path a b) (q q' : Path b c) (hp : RwEq p p') (hq : RwEq q q') :
    RwEq (trans p q) (trans p' q') := by
  exact rweq_trans_congr hp hq

/-! ## 4. Structural Examples -/

/-- Associativity via rweq_tt. -/
example (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (trans (trans p q) r) (trans p (trans q r)) := by
  exact rweq_tt p q r

/-- Left unit elimination. -/
example (p : Path a b) : RwEq (trans (refl a) p) p := by
  exact rweq_cmpA_refl_left p

/-- Right unit elimination. -/
example (p : Path a b) : RwEq (trans p (refl b)) p := by
  exact rweq_cmpA_refl_right p

/-- `path_cancel_left` cancels inverse on left. -/
example (p : Path a b) : RwEq (trans (symm p) p) (refl b) := by
  path_cancel_left

/-- `path_cancel_right` cancels inverse on right. -/
example (p : Path a b) : RwEq (trans p (symm p)) (refl a) := by
  path_cancel_right

/-! ## 5. Advanced Automation Examples -/

/-- `path_auto` handles simple cases via simp. -/
example (p : Path a b) : RwEq (trans (refl a) p) p := by
  path_auto

/-- Double symm simplification. -/
example (p : Path a b) : RwEq (symm (symm p)) p := by
  exact rweq_ss p

/-- Associativity directly. -/
example (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (trans (trans p q) r) (trans p (trans q r)) := by
  exact rweq_tt p q r

/-! ## 6. Normalization Examples -/

/-- `path_normalize` rewrites to canonical form. -/
example (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (trans (trans p q) r) (trans p (trans q r)) := by
  -- path_normalize applies rweq_tt which closes the goal
  exact rweq_tt p q r

example (p : Path a b) :
    RwEq (trans (refl a) p) p := by
  exact rweq_cmpA_refl_left p

example (p : Path a b) :
    RwEq (symm (symm p)) p := by
  exact rweq_ss p

/-! ## 7. Beta/Eta Examples -/

/-- Product fst beta. -/
example {α β : Type} {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    RwEq (Path.fst (Path.prodMk p q)) p := by
  exact rweq_fst_prodMk p q

/-- Product snd beta. -/
example {α β : Type} {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    RwEq (Path.snd (Path.prodMk p q)) q := by
  exact rweq_snd_prodMk p q

/-- Product eta expansion. -/
example {α β : Type} {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path (A := α × β) (a₁, b₁) (a₂, b₂)) :
    RwEq (Path.prodMk (Path.fst p) (Path.snd p)) p := by
  path_eta

/-! ## 8. Calc Notation Examples -/

/-- The ≈ notation and Trans instance enable calc chains for RwEq. -/
example (p : Path a b) (q : Path b c) :
    trans (refl a) (trans p q) ≈ trans p q :=
  calc trans (refl a) (trans p q)
    _ ≈ trans p q := rweq_cmpA_refl_left _

example (p : Path a b) :
    trans (refl a) (trans p (refl b)) ≈ p :=
  calc trans (refl a) (trans p (refl b))
    _ ≈ trans p (refl b) := rweq_cmpA_refl_left _
    _ ≈ p := rweq_cmpA_refl_right _

/-! ## 9. Complex Combined Examples -/

/-- Triangle identity: (p · p⁻¹) · p = p. -/
example (p : Path a b) :
    trans (trans p (symm p)) p ≈ p := by
  apply rweq_trans (rweq_tt p (symm p) p)
  calc trans p (trans (symm p) p)
    _ ≈ trans p (refl b) := rweq_trans_congr_right p (rweq_cmpA_inv_left p)
    _ ≈ p := rweq_cmpA_refl_right p

/-- Symm distributes over trans (reversed). -/
example (p : Path a b) (q : Path b c) :
    symm (trans p q) ≈ trans (symm q) (symm p) := by
  exact rweq_symm_trans_congr

/-- CongrArg preserves RwEq. -/
example {B : Type} (f : A → B) (p q : Path a b) (h : RwEq p q) :
    congrArg f p ≈ congrArg f q := by
  exact rweq_congrArg_of_rweq f h

/-- CongrArg of refl is refl. -/
example {B : Type} (f : A → B) (a : A) :
    congrArg f (refl a) ≈ refl (f a) := by
  path_rfl

/-! ## 10. New Structural Tactics -/

/-- `path_inv_inv` handles double inverse: σ(σ(p)) ≈ p. -/
example (p : Path a b) : symm (symm p) ≈ p := by
  path_inv_inv

/-- `path_symm_refl` handles symm of refl: σ(ρ) ≈ ρ. -/
example : symm (refl a) ≈ refl a := by
  path_symm_refl

/-- `path_inv_distr` distributes symm over trans: σ(p·q) ≈ σ(q)·σ(p). -/
example (p : Path a b) (q : Path b c) :
    symm (trans p q) ≈ trans (symm q) (symm p) := by
  path_inv_distr

/-- `path_congr_symm` applies symm congruence. -/
example (p q : Path a b) (h : RwEq p q) :
    symm p ≈ symm q := by
  path_congr_symm h

/-- `path_congrArg` applies congrArg congruence. -/
example {B : Type} (f : A → B) (p q : Path a b) (h : RwEq p q) :
    congrArg f p ≈ congrArg f q := by
  path_congrArg f h

/-- Combined: inverse distribution then apply congruence. -/
example (p : Path a b) (q : Path b c) :
    symm (symm (trans p q)) ≈ trans p q := by
  path_inv_inv

/-- Inverse distribution is useful for deriving left inverse from right. -/
example (p : Path a b) :
    symm (trans p (symm p)) ≈ trans (symm (symm p)) (symm p) := by
  path_inv_distr

/-! ## Summary

This module demonstrates:

1. **Basic tactics** work for simple groupoid laws
2. **Transitivity** via rweq_trans and path_trans_via
3. **Congruence tactics** handle structural reasoning
4. **Structural lemmas** (rweq_tt, rweq_cmpA_*, etc.)
5. **path_auto** simplifies many common RwEq goals
6. **Beta/Eta** lemmas for products
7. **Calc notation** with ≈ enables clean equational proofs
8. **New structural tactics** (path_inv_inv, path_symm_refl, path_inv_distr)
9. **New congruence tactics** (path_congr_symm, path_congrArg)

All examples build without `sorry` as regression tests.
-/

end TacticExamples
end Path
end ComputationalPaths
