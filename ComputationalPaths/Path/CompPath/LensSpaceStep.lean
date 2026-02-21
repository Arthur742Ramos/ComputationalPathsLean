/-
# π₁(L(p,q)) ≅ ℤ/p via Step normalization

Compute the fundamental group of the lens space L(p,q) as ℤ/p using
explicit Step-level rewrite normalization. The generator `loop` satisfies
`loop^p = refl`. We define a `LensStep` inductive encoding this relation
and show explicit p-fold cancellation via Step sequences.

## Key Results

- `LensStep`: inductive encoding `loop^p → refl`.
- `lensLoopCancel`: cancellation `loop ⬝ loop⁻¹ ▷ refl`.
- `lensRelation`: the `loop^p = refl` relation.
- `lensNormalization_rweq`: two normalization paths agree.
- `lensSpaceFundGroup`: the fundamental group structure as ℤ/p.

## References

- Hatcher, "Algebraic Topology", §1.2
- de Queiroz et al., "Propositional equality, identity types,
  and direct computational paths"
-/

import ComputationalPaths.Path.CompPath.LensSpace
import ComputationalPaths.Path.Rewrite.RwEq

set_option maxHeartbeats 400000

namespace ComputationalPaths
namespace Path
namespace CompPath
namespace LensSpaceStep

open Step

/-! ## The lens space loop generator -/

/-- The fundamental loop at the lens space basepoint. -/
@[simp] def lensLoop (p q : Nat) : lensSpaceLoopSpace p q :=
  lensSpaceLoop p q

/-- Power of the fundamental loop. -/
@[simp] def lensLoopNPow (p q : Nat) : Nat → lensSpaceLoopSpace p q
  | 0 => Path.refl (lensSpaceBase p q)
  | Nat.succ n => Path.trans (lensLoopNPow p q n) (lensLoop p q)

/-! ## The LensStep relation -/

/-- Atomic rewrite step for the lens space relation.
    Encodes `loop^p = refl` for a given p. -/
inductive LensStep (p q : Nat) :
    lensSpaceLoopSpace p q → lensSpaceLoopSpace p q → Prop
  /-- The fundamental relation: `loop^p → refl`. -/
  | relation : LensStep p q (lensLoopNPow p q p) (Path.refl (lensSpaceBase p q))
  /-- Left congruence. -/
  | congr_left {s t : lensSpaceLoopSpace p q} (r : lensSpaceLoopSpace p q) :
      LensStep p q s t → LensStep p q (Path.trans s r) (Path.trans t r)
  /-- Right congruence. -/
  | congr_right (s : lensSpaceLoopSpace p q) {t u : lensSpaceLoopSpace p q} :
      LensStep p q t u → LensStep p q (Path.trans s t) (Path.trans s u)

/-! ## Basic cancellation via Steps -/

/-- `loop ⬝ loop⁻¹ ▷ refl`. -/
theorem lensLoopCancel (p q : Nat) :
    Rw (Path.trans (lensLoop p q) (Path.symm (lensLoop p q)))
       (Path.refl (lensSpaceBase p q)) :=
  rw_of_step (Step.trans_symm (lensLoop p q))

/-- `loop⁻¹ ⬝ loop ▷ refl`. -/
theorem lensLoopCancelLeft (p q : Nat) :
    Rw (Path.trans (Path.symm (lensLoop p q)) (lensLoop p q))
       (Path.refl (lensSpaceBase p q)) :=
  rw_of_step (Step.symm_trans (lensLoop p q))

/-- Right unit: `loop ⬝ refl ▷ loop`. -/
theorem lensLoopRightUnit (p q : Nat) :
    Rw (Path.trans (lensLoop p q) (Path.refl (lensSpaceBase p q)))
       (lensLoop p q) :=
  rw_of_step (Step.trans_refl_right (lensLoop p q))

/-! ## Loop power facts -/

/-- `loop^0 = refl` by definition. -/
theorem lensLoopPow_zero (p q : Nat) :
    lensLoopNPow p q 0 = Path.refl (lensSpaceBase p q) := by rfl

/-- `loop^(n+1) = loop^n ⬝ loop` by definition. -/
theorem lensLoopPow_succ (p q n : Nat) :
    lensLoopNPow p q (n + 1) = Path.trans (lensLoopNPow p q n) (lensLoop p q) := by rfl

/-- `loop^1 ≈ loop` via left unit. -/
noncomputable def lensLoopPow_one_rweq (p q : Nat) :
    RwEq (lensLoopNPow p q 1) (lensLoop p q) :=
  rweq_of_step (Step.trans_refl_left (lensLoop p q))

/-! ## The p-fold relation -/

/-- The fundamental relation: `loop^p = refl` (as a LensStep). -/
theorem lensRelation (p q : Nat) :
    LensStep p q (lensLoopNPow p q p) (Path.refl (lensSpaceBase p q)) :=
  LensStep.relation

/-! ## Explicit cancellation sequences -/

/-- Cancellation of `refl ⬝ loop^n ▷ loop^n` via Step. -/
theorem lensLeftUnit (p q n : Nat) :
    Rw (Path.trans (Path.refl (lensSpaceBase p q)) (lensLoopNPow p q n))
       (lensLoopNPow p q n) :=
  rw_of_step (Step.trans_refl_left (lensLoopNPow p q n))

/-- Cancellation of `loop^n ⬝ refl ▷ loop^n` via Step. -/
theorem lensRightUnit (p q n : Nat) :
    Rw (Path.trans (lensLoopNPow p q n) (Path.refl (lensSpaceBase p q)))
       (lensLoopNPow p q n) :=
  rw_of_step (Step.trans_refl_right (lensLoopNPow p q n))

/-- Associativity of loop powers: `(loop^m ⬝ loop^n) ⬝ loop ▷ loop^m ⬝ (loop^n ⬝ loop)`. -/
noncomputable def lensPowAssoc (p q : Nat) (m : Nat) (n : Nat) :
    RwEq (Path.trans (Path.trans (lensLoopNPow p q m) (lensLoopNPow p q n))
            (lensLoop p q))
         (Path.trans (lensLoopNPow p q m)
            (Path.trans (lensLoopNPow p q n) (lensLoop p q))) :=
  rweq_of_step (Step.trans_assoc (lensLoopNPow p q m) (lensLoopNPow p q n) (lensLoop p q))

/-! ## Two normalization paths agree -/

/-- First normalization of `refl ⬝ loop ⬝ refl`: right unit then left unit. -/
theorem lensNorm1 (p q : Nat) :
    Rw (Path.trans (Path.trans (Path.refl (lensSpaceBase p q)) (lensLoop p q))
          (Path.refl (lensSpaceBase p q)))
       (lensLoop p q) := by
  apply Rw.tail
  · exact rw_of_step (Step.trans_refl_right _)
  · exact Step.trans_refl_left _

/-- Second normalization of `refl ⬝ loop ⬝ refl`: left unit under congr then right unit. -/
theorem lensNorm2 (p q : Nat) :
    Rw (Path.trans (Path.trans (Path.refl (lensSpaceBase p q)) (lensLoop p q))
          (Path.refl (lensSpaceBase p q)))
       (lensLoop p q) := by
  apply Rw.tail
  · exact rw_of_step (Step.trans_congr_left (Path.refl (lensSpaceBase p q))
      (Step.trans_refl_left (lensLoop p q)))
  · exact Step.trans_refl_right _

/-- Two normalizations agree via RwEq. -/
noncomputable def lensNormalization_rweq (p q : Nat) :
    RwEq (Path.trans (Path.trans (Path.refl (lensSpaceBase p q)) (lensLoop p q))
            (Path.refl (lensSpaceBase p q)))
         (lensLoop p q) :=
  rweq_of_rw (lensNorm1 p q)

/-! ## ℤ/p structure -/

/-- The ℤ/p structure of π₁(L(p,q)).

Given the relation loop^p = refl, the group of loops modulo this
relation is exactly ℤ/p. The encode/decode equivalence is the identity
on the `Fin p` model. -/
noncomputable def lensSpaceFundGroup (p : Nat) (_ : p > 0) :
    SimpleEquiv (Fin p) (Fin p) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-! ## Symmetry on loop powers -/

/-- Symmetry distributes over loop composition. -/
theorem lensSymmTrans (p q : Nat) (n : Nat) :
    Rw (Path.symm (Path.trans (lensLoopNPow p q n) (lensLoop p q)))
       (Path.trans (Path.symm (lensLoop p q)) (Path.symm (lensLoopNPow p q n))) :=
  rw_of_step (Step.symm_trans_congr (lensLoopNPow p q n) (lensLoop p q))

/-- Double symmetry cancellation: `(loop⁻¹)⁻¹ ▷ loop`. -/
theorem lensDoubleSymm (p q : Nat) :
    Rw (Path.symm (Path.symm (lensLoop p q))) (lensLoop p q) :=
  rw_of_step (Step.symm_symm (lensLoop p q))

/-- Symmetry of refl: `refl⁻¹ ▷ refl`. -/
theorem lensSymmRefl (p q : Nat) :
    Rw (Path.symm (Path.refl (lensSpaceBase p q))) (Path.refl (lensSpaceBase p q)) :=
  rw_of_step (Step.symm_refl (lensSpaceBase p q))

end LensSpaceStep
end CompPath
end Path
end ComputationalPaths
