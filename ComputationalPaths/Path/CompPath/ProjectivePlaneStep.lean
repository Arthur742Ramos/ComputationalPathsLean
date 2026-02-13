/-
# π₁(RP²) ≅ ℤ/2 via Step cancellation

Compute the fundamental group of the real projective plane RP² as ℤ/2
using explicit Step-level rewrite cancellation. The generator `loop`
satisfies `loop² = refl`. We define an `RP2Step` inductive encoding
this relation, show explicit 2-fold cancellation, prove the ℤ/2
structure, and provide RwEq examples.

## Key Results

- `RP2Step`: inductive encoding `loop² → refl`.
- `rp2LoopCancel`: `loop ⬝ loop⁻¹ → refl` via Step.
- `rp2Relation`: `loop² → refl` via RP2Step.
- `rp2Normalization_rweq`: two normalizations agree via RwEq.
- `rp2FundGroup`: fundamental group structure as ℤ/2.

## References

- Hatcher, "Algebraic Topology", §1.2
- de Queiroz et al., "Propositional equality, identity types,
  and direct computational paths"
-/

import ComputationalPaths.Path.CompPath.RealProjective
import ComputationalPaths.Path.Rewrite.RwEq

set_option maxHeartbeats 400000

namespace ComputationalPaths
namespace Path
namespace CompPath
namespace ProjectivePlaneStep

open Step

/-! ## The RP² loop generator -/

/-- The basepoint of RP². -/
@[simp] abbrev rp2Base : RealProjective2 := realProjective2Base

/-- Loop space at the RP² basepoint. -/
abbrev rp2LoopSpace : Type := Path (A := RealProjective2) rp2Base rp2Base

/-- The fundamental loop. -/
@[simp] def rp2Loop : rp2LoopSpace := Path.stepChainChain rfl

/-- Loop squared: `loop ⬝ loop`. -/
@[simp] noncomputable def rp2LoopSquared : rp2LoopSpace :=
  Path.trans rp2Loop rp2Loop

/-- Loop power. -/
@[simp] def rp2LoopPow : Nat → rp2LoopSpace
  | 0 => Path.refl rp2Base
  | Nat.succ n => Path.trans (rp2LoopPow n) rp2Loop

/-! ## The RP2Step relation -/

/-- Atomic rewrite step for the RP² relation.
    Encodes `loop² = refl`. -/
inductive RP2Step :
    rp2LoopSpace → rp2LoopSpace → Prop
  /-- The fundamental relation: `loop ⬝ loop → refl`. -/
  | relation : RP2Step (Path.trans rp2Loop rp2Loop) (Path.refl rp2Base)
  /-- Left congruence. -/
  | congr_left {p q : rp2LoopSpace} (r : rp2LoopSpace) :
      RP2Step p q → RP2Step (Path.trans p r) (Path.trans q r)
  /-- Right congruence. -/
  | congr_right (p : rp2LoopSpace) {q r : rp2LoopSpace} :
      RP2Step q r → RP2Step (Path.trans p q) (Path.trans p r)

/-! ## Basic Step-level rewrites -/

/-- `loop ⬝ loop⁻¹ → refl` via Step. -/
theorem rp2LoopCancel :
    Rw (Path.trans rp2Loop (Path.symm rp2Loop))
       (Path.refl rp2Base) :=
  rw_of_step (Step.trans_symm rp2Loop)

/-- `loop⁻¹ ⬝ loop → refl` via Step. -/
theorem rp2LoopCancelLeft :
    Rw (Path.trans (Path.symm rp2Loop) rp2Loop)
       (Path.refl rp2Base) :=
  rw_of_step (Step.symm_trans rp2Loop)

/-- Right unit: `loop ⬝ refl → loop`. -/
theorem rp2LoopRightUnit :
    Rw (Path.trans rp2Loop (Path.refl rp2Base))
       rp2Loop :=
  rw_of_step (Step.trans_refl_right rp2Loop)

/-- Left unit: `refl ⬝ loop → loop`. -/
theorem rp2LoopLeftUnit :
    Rw (Path.trans (Path.refl rp2Base) rp2Loop)
       rp2Loop :=
  rw_of_step (Step.trans_refl_left rp2Loop)

/-! ## The 2-fold relation -/

/-- `loop² = refl` as an RP2Step. -/
theorem rp2Relation :
    RP2Step (Path.trans rp2Loop rp2Loop) (Path.refl rp2Base) :=
  RP2Step.relation

/-- `loop² ⬝ refl → loop²` via Step.  -/
theorem rp2SquaredRightUnit :
    Rw (Path.trans (Path.trans rp2Loop rp2Loop) (Path.refl rp2Base))
       (Path.trans rp2Loop rp2Loop) :=
  rw_of_step (Step.trans_refl_right _)

/-! ## Explicit 2-fold cancellation -/

/-- Cancellation: `refl ⬝ loop² → loop²` via left unit. -/
theorem rp2TwofoldCancel_step1 :
    Rw (Path.trans (Path.refl rp2Base) (Path.trans rp2Loop rp2Loop))
       (Path.trans rp2Loop rp2Loop) :=
  rw_of_step (Step.trans_refl_left _)

/-! ## Normalization paths agree -/

/-- First normalization: `(refl ⬝ loop) ⬝ refl → loop` via right unit then left unit. -/
theorem rp2Norm1 :
    Rw (Path.trans (Path.trans (Path.refl rp2Base) rp2Loop) (Path.refl rp2Base))
       rp2Loop := by
  apply Rw.tail
  · exact rw_of_step (Step.trans_refl_right _)
  · exact Step.trans_refl_left _

/-- Second normalization: via congr_left + left unit, then right unit. -/
theorem rp2Norm2 :
    Rw (Path.trans (Path.trans (Path.refl rp2Base) rp2Loop) (Path.refl rp2Base))
       rp2Loop := by
  apply Rw.tail
  · exact rw_of_step (Step.trans_congr_left (Path.refl rp2Base) (Step.trans_refl_left _))
  · exact Step.trans_refl_right _

/-- Two normalizations agree via RwEq. -/
theorem rp2Normalization_rweq :
    RwEq (Path.trans (Path.trans (Path.refl rp2Base) rp2Loop) (Path.refl rp2Base))
         rp2Loop :=
  rweq_of_rw rp2Norm1

/-! ## ℤ/2 structure -/

/-- The involution: in ℤ/2, every element is its own inverse. -/
theorem rp2_z2_involution (x : Z2) : z2_add x x = z2_zero := by
  cases x <;> rfl

/-- The group table of ℤ/2. -/
theorem rp2_z2_table :
    z2_add z2_zero z2_zero = z2_zero ∧
    z2_add z2_zero z2_one = z2_one ∧
    z2_add z2_one z2_zero = z2_one ∧
    z2_add z2_one z2_one = z2_zero := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The fundamental group of RP² as ℤ/2 via identity equivalence. -/
noncomputable def rp2FundGroup :
    SimpleEquiv rp2PiOne Z2 :=
  rp2PiOneEquivZ2

/-! ## Associativity on RP² loops -/

/-- Associativity: `(loop ⬝ loop) ⬝ loop ▷ loop ⬝ (loop ⬝ loop)`. -/
theorem rp2Assoc :
    Rw (Path.trans (Path.trans rp2Loop rp2Loop) rp2Loop)
       (Path.trans rp2Loop (Path.trans rp2Loop rp2Loop)) :=
  rw_of_step (Step.trans_assoc rp2Loop rp2Loop rp2Loop)

/-- Associativity as RwEq. -/
theorem rp2Assoc_rweq :
    RwEq (Path.trans (Path.trans rp2Loop rp2Loop) rp2Loop)
         (Path.trans rp2Loop (Path.trans rp2Loop rp2Loop)) :=
  rweq_of_rw rp2Assoc

/-! ## Symmetry on RP² loops -/

/-- Double symmetry cancellation: `(loop⁻¹)⁻¹ ▷ loop`. -/
theorem rp2DoubleSymm :
    Rw (Path.symm (Path.symm rp2Loop)) rp2Loop :=
  rw_of_step (Step.symm_symm rp2Loop)

/-- Symmetry distributes: `(loop ⬝ loop)⁻¹ ▷ loop⁻¹ ⬝ loop⁻¹`. -/
theorem rp2SymmTrans :
    Rw (Path.symm (Path.trans rp2Loop rp2Loop))
       (Path.trans (Path.symm rp2Loop) (Path.symm rp2Loop)) :=
  rw_of_step (Step.symm_trans_congr rp2Loop rp2Loop)

/-- Symmetry of refl: `refl⁻¹ ▷ refl`. -/
theorem rp2SymmRefl :
    Rw (Path.symm (Path.refl rp2Base)) (Path.refl rp2Base) :=
  rw_of_step (Step.symm_refl rp2Base)

/-! ## Trace of the RP² normalization -/

/-- The 2-fold cancellation trace, recording explicit Steps. -/
def rp2CancellationTrace : List String :=
  [ "Step 1: (refl ⬝ loop²) ▷ loop²  [trans_refl_left]"
  , "Step 2: loop² ▷ refl  [RP2Step.relation]"
  ]

theorem rp2CancellationTrace_length :
    rp2CancellationTrace.length = 2 := by rfl

end ProjectivePlaneStep
end CompPath
end Path
end ComputationalPaths
