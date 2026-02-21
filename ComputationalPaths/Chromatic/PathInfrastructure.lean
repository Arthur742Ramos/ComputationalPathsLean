/-
# Chromatic path infrastructure

This module packages chromatic filtration and Morava K-theory periodicity data
with explicit computational-path witnesses (`Path.Step`) and derived rewrite
equivalences (`RwEq`).
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Chromatic

open Path

universe u

/-- Chromatic filtration data with explicit path-level coherence for two-step
transition maps in the chromatic tower. -/
structure ChromaticFiltrationPaths (X : Type u) where
  /-- Stage `n` of the chromatic filtration. -/
  stage : Nat → Type u
  /-- Localization map `X → L_n X`. -/
  localization : (n : Nat) → X → stage n
  /-- Tower map `L_{n+1} X → L_n X`. -/
  transition : (n : Nat) → stage (n + 1) → stage n
  /-- Chosen two-step transition map `L_{n+2} X → L_n X`. -/
  twoStep : (n : Nat) → stage (n + 2) → stage n
  /-- Coherence witness between the chosen two-step map and iterated transition. -/
  twoStepPath :
    ∀ (n : Nat) (x : stage (n + 2)),
      Path (twoStep n x) (transition n (transition (n + 1) x))
  /-- Primitive rewrite witness: appending reflexivity to the coherence path
  contracts by a single computational step. -/
  twoStepStep :
    ∀ (n : Nat) (x : stage (n + 2)),
      Path.Step
        (Path.trans (twoStepPath n x)
          (Path.refl (transition n (transition (n + 1) x))))
        (twoStepPath n x)

namespace ChromaticFiltrationPaths

variable {X : Type u} (F : ChromaticFiltrationPaths X)

noncomputable def twoStep_rweq (n : Nat) (x : F.stage (n + 2)) :
    RwEq
      (Path.trans (F.twoStepPath n x)
        (Path.refl (F.transition n (F.transition (n + 1) x))))
      (F.twoStepPath n x) :=
  rweq_of_step (F.twoStepStep n x)

noncomputable def twoStep_cancel_rweq (n : Nat) (x : F.stage (n + 2)) :
    RwEq
      (Path.trans (Path.symm (F.twoStepPath n x)) (F.twoStepPath n x))
      (Path.refl (F.transition n (F.transition (n + 1) x))) :=
  rweq_cmpA_inv_left (F.twoStepPath n x)

end ChromaticFiltrationPaths

/-- Morava K-theory path package with explicit periodicity witness. -/
structure MoravaKPathData where
  /-- Prime `p` for `K(n)`. -/
  prime : Nat
  /-- Primality side condition (lightweight, computational form). -/
  prime_gt_one : prime > 1
  /-- Height `n` of Morava K-theory. -/
  height : Nat
  /-- Coefficient object for periodicity bookkeeping. -/
  coeff : Type u
  /-- Multiplication on coefficients. -/
  mul : coeff → coeff → coeff
  /-- Periodicity generator `v_n`. -/
  vn : coeff
  /-- Formal inverse `v_n^{-1}`. -/
  vnInv : coeff
  /-- Computational witness for periodicity commutation. -/
  periodicityPath : Path (mul vn vnInv) (mul vnInv vn)
  /-- Primitive rewrite witness for right unit normalization. -/
  periodicityStep :
    Path.Step
      (Path.trans periodicityPath (Path.refl (mul vnInv vn)))
      periodicityPath

namespace MoravaKPathData

variable (K : MoravaKPathData)

noncomputable def periodicity_rweq :
    RwEq
      (Path.trans K.periodicityPath (Path.refl (K.mul K.vnInv K.vn)))
      K.periodicityPath :=
  rweq_of_step K.periodicityStep

noncomputable def periodicity_cancel_left_rweq :
    RwEq
      (Path.trans (Path.symm K.periodicityPath) K.periodicityPath)
      (Path.refl (K.mul K.vnInv K.vn)) :=
  rweq_cmpA_inv_left K.periodicityPath

noncomputable def periodicity_cancel_right_rweq :
    RwEq
      (Path.trans K.periodicityPath (Path.symm K.periodicityPath))
      (Path.refl (K.mul K.vn K.vnInv)) :=
  rweq_cmpA_inv_right K.periodicityPath

end MoravaKPathData

/-- Constant chromatic filtration with identity transitions. -/
def constantFiltration (X : Type u) : ChromaticFiltrationPaths X where
  stage := fun _ => X
  localization := fun _ x => x
  transition := fun _ x => x
  twoStep := fun _ x => x
  twoStepPath := fun _ x => Path.refl x
  twoStepStep := fun _ x => Path.Step.trans_refl_right (Path.refl x)

/-- Canonical Morava K-path package on `PUnit`. -/
def trivialMoravaKPathData (p n : Nat) (hp : p > 1) : MoravaKPathData where
  prime := p
  prime_gt_one := hp
  height := n
  coeff := PUnit
  mul := fun _ _ => PUnit.unit
  vn := PUnit.unit
  vnInv := PUnit.unit
  periodicityPath := Path.refl PUnit.unit
  periodicityStep := Path.Step.trans_refl_right (Path.refl PUnit.unit)

end Chromatic
end ComputationalPaths
