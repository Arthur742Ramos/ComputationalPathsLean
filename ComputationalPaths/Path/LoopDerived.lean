/-
# Loop Algebra Derived Theorems

Axiom-free, sorry-free theorems about loop algebra operations,
derived from primitive Step rules via `rweq_of_step`.

These theorems are important for fundamental group calculations.

## Key Results

- Loop concatenation and inversion laws
- Loop power laws (iteration)
- Conjugation identities
- Eckmann-Hilton preparation
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.GroupoidDerived
import ComputationalPaths.Path.PathAlgebraDerived
import ComputationalPaths.Path.CoherenceDerived

namespace ComputationalPaths
namespace Path
namespace LoopDerived

open Step

universe u

variable {A : Type u} {a : A}

/-! ## Loop Algebra Basics

A loop is a path from a to a. The loop space Ω(A, a) forms a group. -/

/-- Loop unit: refl is the identity loop -/
theorem rweq_loop_unit (p : Path a a) :
    RwEq (trans (refl a) p) p :=
  rweq_of_step (Step.trans_refl_left p)

/-- Loop unit on right -/
theorem rweq_loop_unit_right (p : Path a a) :
    RwEq (trans p (refl a)) p :=
  rweq_of_step (Step.trans_refl_right p)

/-- Loop inverse: p · p⁻¹ ≈ refl -/
theorem rweq_loop_inv_right (p : Path a a) :
    RwEq (trans p (symm p)) (refl a) :=
  rweq_cmpA_inv_right p

/-- Loop inverse: p⁻¹ · p ≈ refl -/
theorem rweq_loop_inv_left (p : Path a a) :
    RwEq (trans (symm p) p) (refl a) :=
  rweq_cmpA_inv_left p

/-- Loop associativity -/
theorem rweq_loop_assoc (p q r : Path a a) :
    RwEq (trans (trans p q) r) (trans p (trans q r)) :=
  rweq_of_step (Step.trans_assoc p q r)

/-! ## Double/Triple Loop Composition -/

/-- Double loop: (p · q)⁻¹ ≈ q⁻¹ · p⁻¹ -/
theorem rweq_loop_symm_trans (p q : Path a a) :
    RwEq (symm (trans p q)) (trans (symm q) (symm p)) :=
  rweq_of_step (Step.symm_trans_congr p q)

/-- Triple loop: ((p · q) · r)⁻¹ ≈ r⁻¹ · q⁻¹ · p⁻¹ (left assoc) -/
theorem rweq_loop_symm_trans3 (p q r : Path a a) :
    RwEq (symm (trans (trans p q) r))
         (trans (symm r) (trans (symm q) (symm p))) := by
  have h1 : RwEq (symm (trans (trans p q) r))
                 (trans (symm r) (symm (trans p q))) :=
    rweq_of_step (Step.symm_trans_congr (trans p q) r)
  have h2 := rweq_loop_symm_trans p q
  exact RwEq.trans h1 (rweq_trans_congr_right (symm r) h2)

/-! ## Loop Powers (Informal)

For a loop p, we can compose p with itself n times. -/

/-- Two-fold loop: p · p -/
theorem rweq_loop_pow2_assoc (p : Path a a) :
    RwEq (trans (trans p p) p) (trans p (trans p p)) :=
  rweq_of_step (Step.trans_assoc p p p)

/-- Four-fold loop associativity -/
theorem rweq_loop_pow4_assoc (p : Path a a) :
    RwEq (trans (trans (trans p p) p) p)
         (trans p (trans p (trans p p))) :=
  PathAlgebraDerived.rweq_trans_four_assoc

/-! ## Loop Conjugation

Conjugation by p: q ↦ p · q · p⁻¹ -/

/-- Conjugation by refl is identity -/
theorem rweq_loop_conj_refl (q : Path a a) :
    RwEq (trans (trans (refl a) q) (symm (refl a)))
         q := by
  have h1 : RwEq (trans (trans (refl a) q) (symm (refl a)))
                 (trans q (symm (refl a))) :=
    rweq_trans_congr_left (symm (refl a)) (rweq_of_step (Step.trans_refl_left q))
  have h2 : RwEq (symm (refl a)) (refl a) :=
    rweq_of_step (Step.symm_refl a)
  have h3 : RwEq (trans q (symm (refl a))) (trans q (refl a)) :=
    rweq_trans_congr_right q h2
  have h4 : RwEq (trans q (refl a)) q :=
    rweq_of_step (Step.trans_refl_right q)
  exact RwEq.trans h1 (RwEq.trans h3 h4)

/-! ## Commutator Identities

For loops p, q, the commutator is [p,q] = p·q·p⁻¹·q⁻¹ -/

/-- Commutator with self is trivial: [p, p] ≈ refl -/
theorem rweq_loop_self_commutator (p : Path a a) :
    RwEq (trans (trans (trans p p) (symm p)) (symm p))
         (refl a) := by
  -- p · p · p⁻¹ · p⁻¹
  -- First: p · p · p⁻¹ ≈ p
  have h1 : RwEq (trans (trans p p) (symm p))
                 (trans p (trans p (symm p))) :=
    rweq_of_step (Step.trans_assoc p p (symm p))
  have h2 : RwEq (trans p (symm p)) (refl a) :=
    rweq_loop_inv_right p
  have h3 : RwEq (trans p (trans p (symm p)))
                 (trans p (refl a)) :=
    rweq_trans_congr_right p h2
  have h4 : RwEq (trans p (refl a)) p :=
    rweq_of_step (Step.trans_refl_right p)
  have h5 := RwEq.trans h1 (RwEq.trans h3 h4)
  -- So (p · p · p⁻¹) · p⁻¹ ≈ p · p⁻¹ ≈ refl
  have h6 : RwEq (trans (trans (trans p p) (symm p)) (symm p))
                 (trans p (symm p)) :=
    rweq_trans_congr_left (symm p) h5
  exact RwEq.trans h6 (rweq_loop_inv_right p)

/-! ## Whiskering for Loops -/

/-- Left whiskering preserves refl: refl · p ≈ p -/
theorem rweq_loop_whisker_left_refl (p : Path a a) :
    RwEq (trans (refl a) p) p :=
  rweq_of_step (Step.trans_refl_left p)

/-- Right whiskering preserves refl: p · refl ≈ p -/
theorem rweq_loop_whisker_right_refl (p : Path a a) :
    RwEq (trans p (refl a)) p :=
  rweq_of_step (Step.trans_refl_right p)

end LoopDerived
end Path
end ComputationalPaths
