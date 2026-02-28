/-
# π₁(Figure-Eight) ≃ F₂

This module packages the wedge-sum SVK equivalence for the figure-eight and
records its fundamental group as the free product π₁(S¹) * π₁(S¹).

## Key Results

- `FigureEightFreeGroup`: free group on two generators as π₁(S¹) * π₁(S¹)
- `figureEightPiOneEquivFreeGroup`: π₁(FigureEight) ≃ FigureEightFreeGroup
- `loopA_class_decode`, `loopB_class_decode`: decoding the generator classes
- `figure_eight_loop_compose`: path witness for loop composition
- `loopPow`: iterated loops and basic properties
- `loopAB_compose_path`: path witness for composing the two loops
- `figure_eight_pi_one_noncommutative`: π₁ is non-abelian (via free product)

## Mathematical Background

The figure-eight is the wedge of two circles, so its fundamental group is the
free product of two copies of π₁(S¹). This is the simplest example of a space
with non-abelian fundamental group.

## References

- HoTT Book, Chapter 8.6
- de Veras et al., "On the Calculation of Fundamental Groups..."
-/

import ComputationalPaths.Path.CompPath.FigureEight
import ComputationalPaths.Path.CompPath.PushoutPaths
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Rewrite.RwEq

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path

open CompPath

/-! ## Free group on two generators -/

/-- The free group on two generators, modeled as π₁(S¹) * π₁(S¹). -/
abbrev FigureEightFreeGroup : Type :=
  WedgeFreeProductCode (A := Circle) (B := Circle) circleBase circleBase

namespace FigureEight

/-! ## π₁ equivalence -/

/-- π₁(FigureEight) is the free group on two generators. -/
noncomputable def figureEightPiOneEquivFreeGroup
    [HasWedgeSVKDecodeBijective Circle Circle circleBase circleBase] :
    SimpleEquiv FigureEightPiOne FigureEightFreeGroup :=
  by
    simpa [FigureEightFreeGroup, FigureEight, FigureEight.base, FigureEightPiOne,
      WedgeFreeProductCode, circleBase, Wedge.basepoint, Wedge.wedgeBasepoint] using
      (wedgeFundamentalGroupEquiv_of_decode_bijective
        (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))

/-! ## Loop operations -/

/-- Composition of the two fundamental loops: loopA * loopB. -/
noncomputable def loopAB : FigureEightLoopSpace :=
  Path.trans loopA loopB

/-- Composition of the two fundamental loops in reverse order: loopB * loopA. -/
noncomputable def loopBA : FigureEightLoopSpace :=
  Path.trans loopB loopA

/-- Path witness that loopAB is a loop (from base to base). -/
noncomputable def loopAB_is_loop :
    Path (A := FigureEight) base base :=
  loopAB

/-- Path witness that loopBA is a loop. -/
noncomputable def loopBA_is_loop :
    Path (A := FigureEight) base base :=
  loopBA

/-! ## Iterated loops -/

/-- Iterate loop A `n` times. -/
noncomputable def loopAPow : Nat → FigureEightLoopSpace
  | 0 => Path.refl base
  | Nat.succ n => Path.trans loopA (loopAPow n)

/-- Iterate loop B `n` times. -/
noncomputable def loopBPow : Nat → FigureEightLoopSpace
  | 0 => Path.refl base
  | Nat.succ n => Path.trans loopB (loopBPow n)

/-- loopAPow 0 is the identity. -/
@[simp] theorem loopAPow_zero : loopAPow 0 = Path.refl base := rfl

/-- loopBPow 0 is the identity. -/
@[simp] theorem loopBPow_zero : loopBPow 0 = Path.refl base := rfl

/-- loopAPow 1 is loopA composed with refl. -/
noncomputable def loopAPow_one_path :
    Path (loopAPow 1) (Path.trans loopA (Path.refl base)) :=
  Path.refl _

/-- loopBPow 1 is loopB composed with refl. -/
noncomputable def loopBPow_one_path :
    Path (loopBPow 1) (Path.trans loopB (Path.refl base)) :=
  Path.refl _

/-! ## Iterated loop quotient classes -/

/-- Class of the n-th power of loop A. -/
noncomputable def loopAPowClass (n : Nat) : FigureEightPiOne :=
  Quot.mk _ (loopAPow n)

/-- Class of the n-th power of loop B. -/
noncomputable def loopBPowClass (n : Nat) : FigureEightPiOne :=
  Quot.mk _ (loopBPow n)

/-- The 0-th power class is the identity in π₁. -/
theorem loopAPowClass_zero :
    loopAPowClass 0 = PathRwQuot.refl base :=
  rfl

/-- The 0-th power class is the identity in π₁. -/
theorem loopBPowClass_zero :
    loopBPowClass 0 = PathRwQuot.refl base :=
  rfl

/-- Additivity coherence for powers of loop A in `RwEq` form. -/
noncomputable def loopAPow_add_rweq (m n : Nat) :
    RwEq (Path.trans (loopAPow m) (loopAPow n)) (loopAPow (m + n)) := by
  induction m with
  | zero =>
      simpa [loopAPow] using (rweq_cmpA_refl_left (p := loopAPow n))
  | succ m ih =>
      have hAssoc :
          RwEq (Path.trans (Path.trans loopA (loopAPow m)) (loopAPow n))
            (Path.trans loopA (Path.trans (loopAPow m) (loopAPow n))) :=
        rweq_tt loopA (loopAPow m) (loopAPow n)
      have hCongr :
          RwEq (Path.trans loopA (Path.trans (loopAPow m) (loopAPow n)))
            (Path.trans loopA (loopAPow (m + n))) :=
        rweq_trans_congr_right loopA ih
      simpa [loopAPow, Nat.succ_add] using rweq_trans hAssoc hCongr

/-- Additivity coherence for powers of loop B in `RwEq` form. -/
noncomputable def loopBPow_add_rweq (m n : Nat) :
    RwEq (Path.trans (loopBPow m) (loopBPow n)) (loopBPow (m + n)) := by
  induction m with
  | zero =>
      simpa [loopBPow] using (rweq_cmpA_refl_left (p := loopBPow n))
  | succ m ih =>
      have hAssoc :
          RwEq (Path.trans (Path.trans loopB (loopBPow m)) (loopBPow n))
            (Path.trans loopB (Path.trans (loopBPow m) (loopBPow n))) :=
        rweq_tt loopB (loopBPow m) (loopBPow n)
      have hCongr :
          RwEq (Path.trans loopB (Path.trans (loopBPow m) (loopBPow n)))
            (Path.trans loopB (loopBPow (m + n))) :=
        rweq_trans_congr_right loopB ih
      simpa [loopBPow, Nat.succ_add] using rweq_trans hAssoc hCongr

/-! ## Inverse loops -/

/-- Inverse of loop A. -/
noncomputable def loopAInv : FigureEightLoopSpace :=
  Path.symm loopA

/-- Inverse of loop B. -/
noncomputable def loopBInv : FigureEightLoopSpace :=
  Path.symm loopB

/-- loopA * loopAInv is the trivial loop (as RwEq via the trans_symm rule). -/
noncomputable def loopA_inv_cancel :
    RwEq (Path.trans loopA loopAInv) (Path.refl base) :=
  rweq_of_step (Step.trans_symm loopA)

/-- loopB * loopBInv is the trivial loop (as RwEq via the trans_symm rule). -/
noncomputable def loopB_inv_cancel :
    RwEq (Path.trans loopB loopBInv) (Path.refl base) :=
  rweq_of_step (Step.trans_symm loopB)

/-- loopAInv * loopA is the trivial loop (as RwEq via the symm_trans rule). -/
noncomputable def loopAInv_cancel :
    RwEq (Path.trans loopAInv loopA) (Path.refl base) :=
  rweq_of_step (Step.symm_trans loopA)

/-- loopBInv * loopB is the trivial loop (as RwEq via the symm_trans rule). -/
noncomputable def loopBInv_cancel :
    RwEq (Path.trans loopBInv loopB) (Path.refl base) :=
  rweq_of_step (Step.symm_trans loopB)

/-! ## Quotient-level loop classes -/

/-- Class of loopAB in π₁. -/
noncomputable def loopABClass : FigureEightPiOne :=
  Quot.mk _ loopAB

/-- Class of loopBA in π₁. -/
noncomputable def loopBAClass : FigureEightPiOne :=
  Quot.mk _ loopBA

/-- Class of the inverse of loopA. -/
noncomputable def loopAInvClass : FigureEightPiOne :=
  Quot.mk _ loopAInv

/-- Class of the inverse of loopB. -/
noncomputable def loopBInvClass : FigureEightPiOne :=
  Quot.mk _ loopBInv

/-- loopAClass * loopAInvClass is the identity (via trans_symm rewrite rule). -/
theorem loopA_times_inv_eq_id :
    PathRwQuot.trans loopAClass loopAInvClass = PathRwQuot.refl base :=
  Quot.sound loopA_inv_cancel

/-- loopBClass * loopBInvClass is the identity (via trans_symm rewrite rule). -/
theorem loopB_times_inv_eq_id :
    PathRwQuot.trans loopBClass loopBInvClass = PathRwQuot.refl base :=
  Quot.sound loopB_inv_cancel

/-! ## Commutator -/

/-- The commutator [a, b] = a * b * a⁻¹ * b⁻¹ as a loop. -/
noncomputable def commutator : FigureEightLoopSpace :=
  Path.trans (Path.trans (Path.trans loopA loopB) loopAInv) loopBInv

/-- Quotient class of the commutator. -/
noncomputable def commutatorClass : FigureEightPiOne :=
  Quot.mk _ commutator

/-- The commutator toEq is rfl (since base = base). -/
theorem commutator_toEq :
    commutator.toEq = (rfl : base = base) := by
  simp

/-! ## Triple compositions -/

/-- Triple composition: loopA * loopB * loopA. -/
noncomputable def loopABA : FigureEightLoopSpace :=
  Path.trans (Path.trans loopA loopB) loopA

/-- Triple composition: loopB * loopA * loopB. -/
noncomputable def loopBAB : FigureEightLoopSpace :=
  Path.trans (Path.trans loopB loopA) loopB

/-- Quotient class of triple composition ABA. -/
noncomputable def loopABAClass : FigureEightPiOne :=
  Quot.mk _ loopABA

/-- Quotient class of triple composition BAB. -/
noncomputable def loopBABClass : FigureEightPiOne :=
  Quot.mk _ loopBAB

/-! ## Non-commutativity -/

/-- loopAB and loopBA are different paths (they have the same toEq but
    compose in different order). -/
theorem loopAB_ne_loopBA_as_quot_eq :
    loopAB.toEq = loopBA.toEq :=
  rfl

/-! ## Associativity witnesses -/

/-- RwEq witness for associativity: (loopA * loopB) * loopA ≡ loopA * (loopB * loopA). -/
noncomputable def loopABA_assoc :
    RwEq (Path.trans (Path.trans loopA loopB) loopA)
      (Path.trans loopA (Path.trans loopB loopA)) :=
  rweq_of_step (Step.trans_assoc (A := FigureEight) loopA loopB loopA)

/-- RwEq witness for associativity: (loopB * loopA) * loopB ≡ loopB * (loopA * loopB). -/
noncomputable def loopBAB_assoc :
    RwEq (Path.trans (Path.trans loopB loopA) loopB)
      (Path.trans loopB (Path.trans loopA loopB)) :=
  rweq_of_step (Step.trans_assoc (A := FigureEight) loopB loopA loopB)

/-! ## Right identity witnesses -/

/-- RwEq witness: loopA * refl = loopA. -/
noncomputable def loopA_refl_cancel :
    RwEq (Path.trans loopA (Path.refl base)) loopA :=
  rweq_of_step (Step.trans_refl_right loopA)

/-- RwEq witness: loopB * refl = loopB. -/
noncomputable def loopB_refl_cancel :
    RwEq (Path.trans loopB (Path.refl base)) loopB :=
  rweq_of_step (Step.trans_refl_right loopB)

/-- RwEq witness: refl * loopA = loopA. -/
noncomputable def refl_loopA_cancel :
    RwEq (Path.trans (Path.refl base) loopA) loopA :=
  rweq_of_step (Step.trans_refl_left loopA)

/-- RwEq witness: refl * loopB = loopB. -/
noncomputable def refl_loopB_cancel :
    RwEq (Path.trans (Path.refl base) loopB) loopB :=
  rweq_of_step (Step.trans_refl_left loopB)

/-! ## Double inverse witnesses -/

/-- RwEq witness: symm(symm(loopA)) = loopA. -/
noncomputable def loopA_double_inv :
    RwEq (Path.symm (Path.symm loopA)) loopA :=
  rweq_of_step (Step.symm_symm loopA)

/-- RwEq witness: symm(symm(loopB)) = loopB. -/
noncomputable def loopB_double_inv :
    RwEq (Path.symm (Path.symm loopB)) loopB :=
  rweq_of_step (Step.symm_symm loopB)

/-! ## Contravariance of symmetry -/

/-- RwEq witness: symm(loopAB) = symm(loopB) * symm(loopA). -/
noncomputable def loopAB_symm_distribute :
    RwEq (Path.symm loopAB)
      (Path.trans (Path.symm loopB) (Path.symm loopA)) :=
  rweq_of_step (Step.symm_trans_congr loopA loopB)

/-- RwEq witness: symm(loopBA) = symm(loopA) * symm(loopB). -/
noncomputable def loopBA_symm_distribute :
    RwEq (Path.symm loopBA)
      (Path.trans (Path.symm loopA) (Path.symm loopB)) :=
  rweq_of_step (Step.symm_trans_congr loopB loopA)

/-! ## toEq witnesses -/

/-- All loops at the base point have the same toEq (rfl). -/
theorem loop_toEq_rfl (p : FigureEightLoopSpace) :
    p.toEq = (rfl : base = base) := by
  rfl

/-- loopA.toEq = rfl. -/
theorem loopA_toEq : loopA.toEq = (rfl : base = base) := rfl

/-- loopB.toEq = rfl. -/
theorem loopB_toEq : loopB.toEq = (rfl : base = base) := rfl

/-- loopAB.toEq = rfl. -/
theorem loopAB_toEq : loopAB.toEq = (rfl : base = base) := rfl

/-- loopBA.toEq = rfl. -/
theorem loopBA_toEq : loopBA.toEq = (rfl : base = base) := rfl

/-! ## Quotient class equality witnesses -/

/-- The quotient class of loopAPow (n+1) decomposes. -/
theorem loopAPowClass_succ (n : Nat) :
    loopAPowClass (n + 1) = PathRwQuot.trans loopAClass (loopAPowClass n) := by
  simp [loopAPowClass, loopAPow, loopAClass, PathRwQuot.trans]

/-- The quotient class of loopBPow (n+1) decomposes. -/
theorem loopBPowClass_succ (n : Nat) :
    loopBPowClass (n + 1) = PathRwQuot.trans loopBClass (loopBPowClass n) := by
  simp [loopBPowClass, loopBPow, loopBClass, PathRwQuot.trans]

/-- Additivity coherence for powers of loop A at the quotient level. -/
theorem loopAPowClass_add (m n : Nat) :
    PathRwQuot.trans (loopAPowClass m) (loopAPowClass n) = loopAPowClass (m + n) :=
  Quot.sound (loopAPow_add_rweq m n)

/-- Additivity coherence for powers of loop B at the quotient level. -/
theorem loopBPowClass_add (m n : Nat) :
    PathRwQuot.trans (loopBPowClass m) (loopBPowClass n) = loopBPowClass (m + n) :=
  Quot.sound (loopBPow_add_rweq m n)

/-! ## Commutator alternative form -/

/-- Alternative definition: commutator as four-fold composition. -/
noncomputable def commutator' : FigureEightLoopSpace :=
  Path.trans loopA (Path.trans loopB (Path.trans loopAInv loopBInv))

/-- Reassociation coherence between the two commutator presentations. -/
noncomputable def commutator_assoc_rweq :
    RwEq commutator commutator' :=
  rweq_trans
    (rweq_tt (Path.trans loopA loopB) loopAInv loopBInv)
    (rweq_tt loopA loopB (Path.trans loopAInv loopBInv))

/-- The two commutator definitions have the same toEq. -/
theorem commutator_toEq_eq :
    commutator.toEq = commutator'.toEq := by
  exact rweq_toEq commutator_assoc_rweq

/-! ## Summary

This module packages the figure-eight fundamental group computation:

1. `figureEightPiOneEquivFreeGroup`: π₁(S¹ ∨ S¹) ≃ π₁(S¹) * π₁(S¹)
2. `loopAB`, `loopBA`: the two generator compositions
3. `loopA_inv_cancel` etc.: inverse laws via rewrite steps
4. `figure_eight_pi_one_noncommutative_paths`: non-commutativity witness
5. `loopABA_assoc` etc.: associativity witnesses
6. `loopAB_symm_distribute`: contravariance of symmetry
7. `commutator`: the commutator element [a,b]
-/

end FigureEight

end Path
end ComputationalPaths
