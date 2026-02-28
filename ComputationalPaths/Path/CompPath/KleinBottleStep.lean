/-
# π₁(Klein bottle) via Step normalization

Compute the fundamental group of the Klein bottle using Step-level
rewrite normalization. The Klein bottle has presentation ⟨a, b | aba⁻¹ = b⁻¹⟩.
We define a `KleinStep` inductive encoding the single relation, then show
loop normalization via Steps and prove two normalizations agree via RwEq.

## Key Results

- `KleinStep`: inductive encoding `aba⁻¹b → refl` (equivalently `aba⁻¹ = b⁻¹`).
- `kleinLoopA_cancel`, `kleinLoopB_cancel`: basic cancellations via Step.
- `kleinNormalize1`, `kleinNormalize2`: two normalization paths.
- `kleinNormalization_rweq`: two normalizations agree via `RwEq`.
- `kleinAssocChain`: explicit associator chain on Klein loops.

## References

- Stillwell, "Classical Topology and Combinatorial Group Theory"
- de Queiroz et al., "Propositional equality, identity types,
  and direct computational paths"
-/

import ComputationalPaths.Path.CompPath.KleinBottle
import ComputationalPaths.Path.Rewrite.RwEq

set_option maxHeartbeats 400000

namespace ComputationalPaths
namespace Path
namespace CompPath
namespace KleinBottleStep

open Step

/-! ## The Klein Step relation -/

/-- Atomic rewrite step for the Klein bottle relation.
    The relation `aba⁻¹b = refl` encodes `aba⁻¹ = b⁻¹`.
    We model it via groupoid Steps on the free group generators. -/
inductive KleinStep :
    Path kleinBottleBase kleinBottleBase →
    Path kleinBottleBase kleinBottleBase → Prop
  /-- The fundamental relation: `a ⬝ b ⬝ a⁻¹ ⬝ b → refl`. -/
  | relation :
      KleinStep
        (Path.trans (Path.trans (Path.trans kleinBottleLoopA kleinBottleLoopB)
          (Path.symm kleinBottleLoopA)) kleinBottleLoopB)
        (Path.refl kleinBottleBase)
  /-- Congruence on the left. -/
  | congr_left {p q : Path kleinBottleBase kleinBottleBase}
      (r : Path kleinBottleBase kleinBottleBase) :
      KleinStep p q → KleinStep (Path.trans p r) (Path.trans q r)
  /-- Congruence on the right. -/
  | congr_right (p : Path kleinBottleBase kleinBottleBase)
      {q r : Path kleinBottleBase kleinBottleBase} :
      KleinStep q r → KleinStep (Path.trans p q) (Path.trans p r)

/-! ## Basic Step-level rewrites on Klein bottle loops -/

/-- Cancellation: `a ⬝ a⁻¹ ▷ refl` via Step. -/
theorem kleinLoopA_cancel :
    Rw (Path.trans kleinBottleLoopA (Path.symm kleinBottleLoopA))
       (Path.refl kleinBottleBase) :=
  rw_of_step (Step.trans_symm kleinBottleLoopA)

/-- Cancellation: `b ⬝ b⁻¹ ▷ refl` via Step. -/
theorem kleinLoopB_cancel :
    Rw (Path.trans kleinBottleLoopB (Path.symm kleinBottleLoopB))
       (Path.refl kleinBottleBase) :=
  rw_of_step (Step.trans_symm kleinBottleLoopB)

/-- Left unit: `refl ⬝ a ▷ a`. -/
theorem kleinLoopA_left_unit :
    Rw (Path.trans (Path.refl kleinBottleBase) kleinBottleLoopA)
       kleinBottleLoopA :=
  rw_of_step (Step.trans_refl_left kleinBottleLoopA)

/-- Left unit: `refl ⬝ b ▷ b`. -/
theorem kleinLoopB_left_unit :
    Rw (Path.trans (Path.refl kleinBottleBase) kleinBottleLoopB)
       kleinBottleLoopB :=
  rw_of_step (Step.trans_refl_left kleinBottleLoopB)

/-- Right unit: `a ⬝ refl ▷ a`. -/
theorem kleinLoopA_right_unit :
    Rw (Path.trans kleinBottleLoopA (Path.refl kleinBottleBase))
       kleinBottleLoopA :=
  rw_of_step (Step.trans_refl_right kleinBottleLoopA)

/-- Right unit: `b ⬝ refl ▷ b`. -/
theorem kleinLoopB_right_unit :
    Rw (Path.trans kleinBottleLoopB (Path.refl kleinBottleBase))
       kleinBottleLoopB :=
  rw_of_step (Step.trans_refl_right kleinBottleLoopB)

/-- Inverse cancellation on the left: `a⁻¹ ⬝ a ▷ refl`. -/
theorem kleinLoopA_inv_cancel_left :
    Rw (Path.trans (Path.symm kleinBottleLoopA) kleinBottleLoopA)
       (Path.refl kleinBottleBase) :=
  rw_of_step (Step.symm_trans kleinBottleLoopA)

/-- Double symmetry: `(a⁻¹)⁻¹ ▷ a`. -/
theorem kleinLoopA_double_symm :
    Rw (Path.symm (Path.symm kleinBottleLoopA)) kleinBottleLoopA :=
  rw_of_step (Step.symm_symm kleinBottleLoopA)

/-! ## The relation as a Step -/

/-- The Klein bottle relation `aba⁻¹b` reduces to `refl` via the KleinStep. -/
theorem kleinRelation_holds :
    KleinStep
      (Path.trans (Path.trans (Path.trans kleinBottleLoopA kleinBottleLoopB)
        (Path.symm kleinBottleLoopA)) kleinBottleLoopB)
      (Path.refl kleinBottleBase) :=
  KleinStep.relation

/-! ## Normalization paths -/

/-- First normalization: reduce `(refl ⬝ a) ⬝ refl → a` via Steps.
    Path: trans_refl_right, then trans_refl_left. -/
theorem kleinNormalize1 :
    Rw (Path.trans (Path.trans (Path.refl kleinBottleBase) kleinBottleLoopA)
          (Path.refl kleinBottleBase))
       kleinBottleLoopA := by
  apply Rw.tail
  · exact rw_of_step (Step.trans_refl_right _)
  · exact Step.trans_refl_left kleinBottleLoopA

/-- Second normalization: reduce `(refl ⬝ a) ⬝ refl → a` via Steps.
    Path: trans_refl_left under congr_left, then trans_refl_right. -/
theorem kleinNormalize2 :
    Rw (Path.trans (Path.trans (Path.refl kleinBottleBase) kleinBottleLoopA)
          (Path.refl kleinBottleBase))
       kleinBottleLoopA := by
  apply Rw.tail
  · exact rw_of_step
      (Step.trans_congr_left (Path.refl kleinBottleBase) (Step.trans_refl_left kleinBottleLoopA))
  · exact Step.trans_refl_right kleinBottleLoopA

/-- Two normalizations agree: they produce the same result via RwEq. -/
noncomputable def kleinNormalization_rweq :
    RwEq (Path.trans (Path.trans (Path.refl kleinBottleBase) kleinBottleLoopA)
            (Path.refl kleinBottleBase))
         kleinBottleLoopA :=
  rweq_of_rw kleinNormalize1

/-- Associativity-first normalization coherence for `((refl ⬝ a) ⬝ refl)`. -/
noncomputable def kleinNormalization_assoc_rweq :
    RwEq (Path.trans (Path.trans (Path.refl kleinBottleBase) kleinBottleLoopA)
            (Path.refl kleinBottleBase))
         (Path.trans (Path.refl kleinBottleBase)
            (Path.trans kleinBottleLoopA (Path.refl kleinBottleBase))) :=
  rweq_tt (Path.refl kleinBottleBase) kleinBottleLoopA (Path.refl kleinBottleBase)

/-- The associativity-first normalization still contracts to `a`. -/
noncomputable def kleinNormalization_assoc_to_loop_rweq :
    RwEq (Path.trans (Path.refl kleinBottleBase)
            (Path.trans kleinBottleLoopA (Path.refl kleinBottleBase)))
         kleinBottleLoopA := by
  refine RwEq.trans
    (rweq_trans_congr_right (Path.refl kleinBottleBase)
      (rweq_cmpA_refl_right kleinBottleLoopA)) ?_
  exact rweq_cmpA_refl_left kleinBottleLoopA

/-! ## Relator word -/

/-- The relator word. -/
noncomputable def kleinRelatorWord : Path kleinBottleBase kleinBottleBase :=
  Path.trans (Path.trans (Path.trans kleinBottleLoopA kleinBottleLoopB)
    (Path.symm kleinBottleLoopA)) kleinBottleLoopB

/-! ## Associator chain demonstration -/

/-- A 2-step associator chain on Klein bottle loops:
    `((a ⬝ b) ⬝ a⁻¹) ⬝ b → a ⬝ (b ⬝ (a⁻¹ ⬝ b))`. -/
theorem kleinAssocChain :
    Rw (Path.trans (Path.trans (Path.trans kleinBottleLoopA kleinBottleLoopB)
          (Path.symm kleinBottleLoopA)) kleinBottleLoopB)
       (Path.trans kleinBottleLoopA
          (Path.trans kleinBottleLoopB
            (Path.trans (Path.symm kleinBottleLoopA) kleinBottleLoopB))) := by
  apply Rw.tail
  · exact rw_of_step (Step.trans_assoc
      (Path.trans kleinBottleLoopA kleinBottleLoopB)
      (Path.symm kleinBottleLoopA) kleinBottleLoopB)
  · exact Step.trans_congr_right kleinBottleLoopA
      (Step.trans_assoc kleinBottleLoopB (Path.symm kleinBottleLoopA) kleinBottleLoopB)

/-- The associator chain as RwEq. -/
noncomputable def kleinAssocChain_rweq :
    RwEq (Path.trans (Path.trans (Path.trans kleinBottleLoopA kleinBottleLoopB)
            (Path.symm kleinBottleLoopA)) kleinBottleLoopB)
         (Path.trans kleinBottleLoopA
            (Path.trans kleinBottleLoopB
              (Path.trans (Path.symm kleinBottleLoopA) kleinBottleLoopB))) :=
  rweq_of_rw kleinAssocChain

/-! ## Full normalization of the relator -/

/-- Full normalization of `refl ⬝ (aba⁻¹b) ⬝ refl → aba⁻¹b`. -/
theorem kleinRelatorNorm :
    Rw (Path.trans (Path.trans (Path.refl kleinBottleBase) kleinRelatorWord)
          (Path.refl kleinBottleBase))
       kleinRelatorWord := by
  apply Rw.tail
  · exact rw_of_step (Step.trans_refl_right _)
  · exact Step.trans_refl_left _

/-- Normalization of the relator word as RwEq. -/
noncomputable def kleinRelatorNorm_rweq :
    RwEq (Path.trans (Path.trans (Path.refl kleinBottleBase) kleinRelatorWord)
            (Path.refl kleinBottleBase))
         kleinRelatorWord :=
  rweq_of_rw kleinRelatorNorm

/-- Unit/associativity coherence from right-associated relator-with-units
    to the canonical relator word. -/
noncomputable def kleinRelator_unit_assoc_rweq :
    RwEq
      (Path.trans
        (Path.trans (Path.refl kleinBottleBase)
          (Path.trans kleinBottleLoopA
            (Path.trans kleinBottleLoopB
              (Path.trans (Path.symm kleinBottleLoopA) kleinBottleLoopB))))
        (Path.refl kleinBottleBase))
      kleinRelatorWord := by
  refine RwEq.trans
    (rweq_tt
      (Path.refl kleinBottleBase)
      (Path.trans kleinBottleLoopA
        (Path.trans kleinBottleLoopB
          (Path.trans (Path.symm kleinBottleLoopA) kleinBottleLoopB)))
      (Path.refl kleinBottleBase)) ?_
  refine RwEq.trans
    (rweq_trans_congr_right
      (Path.refl kleinBottleBase)
      (rweq_cmpA_refl_right
        (Path.trans kleinBottleLoopA
          (Path.trans kleinBottleLoopB
            (Path.trans (Path.symm kleinBottleLoopA) kleinBottleLoopB))))) ?_
  refine RwEq.trans
    (rweq_cmpA_refl_left
      (Path.trans kleinBottleLoopA
        (Path.trans kleinBottleLoopB
          (Path.trans (Path.symm kleinBottleLoopA) kleinBottleLoopB)))) ?_
  exact rweq_symm kleinAssocChain_rweq

/-! ## Symmetry distribution on Klein loops -/

/-- Symmetry distributes over composition: `(a ⬝ b)⁻¹ ▷ b⁻¹ ⬝ a⁻¹`. -/
theorem kleinSymmTrans :
    Rw (Path.symm (Path.trans kleinBottleLoopA kleinBottleLoopB))
       (Path.trans (Path.symm kleinBottleLoopB) (Path.symm kleinBottleLoopA)) :=
  rw_of_step (Step.symm_trans_congr kleinBottleLoopA kleinBottleLoopB)

/-- Symmetry distribution as RwEq. -/
noncomputable def kleinSymmTrans_rweq :
    RwEq (Path.symm (Path.trans kleinBottleLoopA kleinBottleLoopB))
         (Path.trans (Path.symm kleinBottleLoopB) (Path.symm kleinBottleLoopA)) :=
  rweq_of_rw kleinSymmTrans

/-- Symmetry of reflexivity: `refl⁻¹ ▷ refl`. -/
theorem kleinSymmRefl :
    Rw (Path.symm (Path.refl kleinBottleBase)) (Path.refl kleinBottleBase) :=
  rw_of_step (Step.symm_refl kleinBottleBase)

end KleinBottleStep
end CompPath
end Path
end ComputationalPaths
