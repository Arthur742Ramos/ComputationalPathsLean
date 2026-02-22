/-
# Bousfield localization and nilpotence paths

This module packages Bousfield localization, the nilpotence theorem,
and periodicity theorem data within the computational-path framework.
These are the core structural results of chromatic homotopy theory,
and their coherence is tracked by `Path`, `Step`, and `RwEq`.
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Chromatic.PathInfrastructure

namespace ComputationalPaths
namespace Chromatic
namespace BousfieldNilpotence

open Path

universe u

/-- Bousfield localization data with explicit path witnesses for
the localization adjunction and acyclicity. -/
structure BousfieldLocalizationData (Sp : Type u) where
  /-- The homology theory used for localization. -/
  homology : Sp → Type u
  /-- The localized spectrum L_E X. -/
  localize : Sp → Sp
  /-- The localization map η : X → L_E X. -/
  unit : (X : Sp) → Sp
  /-- The unit is a homology equivalence. -/
  unitPath : (X : Sp) → Path (unit X) (localize X)
  /-- E-acyclic spectra: E_* X = 0. -/
  acyclic : Sp → Prop
  /-- Localized spectra are E-local. -/
  localIsLocal : (X : Sp) → Path (localize (localize X)) (localize X)
  /-- Idempotency of localization. -/
  idempotent : (X : Sp) → Path (localize (localize X)) (localize X)

namespace BousfieldLocalizationData

variable {Sp : Type u} (B : BousfieldLocalizationData Sp)

/-- unitPath right-cancels. -/
noncomputable def unitPath_cancel_right (X : Sp) :
    RwEq (Path.trans (B.unitPath X) (Path.symm (B.unitPath X)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (B.unitPath X)

/-- unitPath left-cancels. -/
noncomputable def unitPath_cancel_left (X : Sp) :
    RwEq (Path.trans (Path.symm (B.unitPath X)) (B.unitPath X))
         (Path.refl _) :=
  rweq_cmpA_inv_left (B.unitPath X)

/-- unitPath symm-symm. -/
noncomputable def unitPath_symm_symm (X : Sp) :
    RwEq (Path.symm (Path.symm (B.unitPath X)))
         (B.unitPath X) :=
  rweq_of_step (Step.symm_symm (B.unitPath X))

/-- unitPath right-unit. -/
noncomputable def unitPath_refl_right (X : Sp) :
    RwEq (Path.trans (B.unitPath X) (Path.refl _))
         (B.unitPath X) :=
  rweq_cmpA_refl_right (B.unitPath X)

/-- unitPath left-unit. -/
noncomputable def unitPath_refl_left (X : Sp) :
    RwEq (Path.trans (Path.refl _) (B.unitPath X))
         (B.unitPath X) :=
  rweq_cmpA_refl_left (B.unitPath X)

/-- localIsLocal right-cancels. -/
noncomputable def localIsLocal_cancel_right (X : Sp) :
    RwEq (Path.trans (B.localIsLocal X) (Path.symm (B.localIsLocal X)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (B.localIsLocal X)

/-- localIsLocal symm-symm. -/
noncomputable def localIsLocal_symm_symm (X : Sp) :
    RwEq (Path.symm (Path.symm (B.localIsLocal X)))
         (B.localIsLocal X) :=
  rweq_of_step (Step.symm_symm (B.localIsLocal X))

/-- idempotent right-cancels. -/
noncomputable def idempotent_cancel_right (X : Sp) :
    RwEq (Path.trans (B.idempotent X) (Path.symm (B.idempotent X)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (B.idempotent X)

/-- idempotent symm-symm. -/
noncomputable def idempotent_symm_symm (X : Sp) :
    RwEq (Path.symm (Path.symm (B.idempotent X)))
         (B.idempotent X) :=
  rweq_of_step (Step.symm_symm (B.idempotent X))

/-- idempotent right-unit. -/
noncomputable def idempotent_refl_right (X : Sp) :
    RwEq (Path.trans (B.idempotent X) (Path.refl _))
         (B.idempotent X) :=
  rweq_cmpA_refl_right (B.idempotent X)

end BousfieldLocalizationData

/-- Nilpotence theorem data (Devinatz-Hopkins-Smith): a map f is
smash-nilpotent iff MU_*(f) = 0. -/
structure NilpotenceData (Sp : Type u) where
  /-- Smash product. -/
  smash : Sp → Sp → Sp
  /-- A self-map of finite type. -/
  selfMap : Sp → Sp
  /-- MU-homology detection. -/
  muHomology : Sp → Type u
  /-- Nilpotency path: if MU_*(f) = 0, then f^n = 0 for some n. -/
  nilpotencyWitness : (X : Sp) → (n : Nat) → Sp
  /-- The n-fold iterate vanishes. -/
  nilpotentPath : (X : Sp) → (n : Nat) →
    Path (nilpotencyWitness X n) (nilpotencyWitness X 0)
  /-- Smash commutativity. -/
  smash_comm : (X Y : Sp) → Path (smash X Y) (smash Y X)
  /-- Smash associativity. -/
  smash_assoc : (X Y Z : Sp) →
    Path (smash (smash X Y) Z) (smash X (smash Y Z))

namespace NilpotenceData

variable {Sp : Type u} (N : NilpotenceData Sp)

/-- nilpotentPath right-cancels. -/
noncomputable def nilpotentPath_cancel_right (X : Sp) (n : Nat) :
    RwEq (Path.trans (N.nilpotentPath X n)
                     (Path.symm (N.nilpotentPath X n)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (N.nilpotentPath X n)

/-- nilpotentPath symm-symm. -/
noncomputable def nilpotentPath_symm_symm (X : Sp) (n : Nat) :
    RwEq (Path.symm (Path.symm (N.nilpotentPath X n)))
         (N.nilpotentPath X n) :=
  rweq_of_step (Step.symm_symm (N.nilpotentPath X n))

/-- nilpotentPath right-unit. -/
noncomputable def nilpotentPath_refl_right (X : Sp) (n : Nat) :
    RwEq (Path.trans (N.nilpotentPath X n) (Path.refl _))
         (N.nilpotentPath X n) :=
  rweq_cmpA_refl_right (N.nilpotentPath X n)

/-- nilpotentPath left-unit. -/
noncomputable def nilpotentPath_refl_left (X : Sp) (n : Nat) :
    RwEq (Path.trans (Path.refl _) (N.nilpotentPath X n))
         (N.nilpotentPath X n) :=
  rweq_cmpA_refl_left (N.nilpotentPath X n)

/-- smash_comm right-cancels. -/
noncomputable def smash_comm_cancel_right (X Y : Sp) :
    RwEq (Path.trans (N.smash_comm X Y) (Path.symm (N.smash_comm X Y)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (N.smash_comm X Y)

/-- smash_comm symm-symm. -/
noncomputable def smash_comm_symm_symm (X Y : Sp) :
    RwEq (Path.symm (Path.symm (N.smash_comm X Y)))
         (N.smash_comm X Y) :=
  rweq_of_step (Step.symm_symm (N.smash_comm X Y))

/-- smash_assoc right-cancels. -/
noncomputable def smash_assoc_cancel_right (X Y Z : Sp) :
    RwEq (Path.trans (N.smash_assoc X Y Z)
                     (Path.symm (N.smash_assoc X Y Z)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (N.smash_assoc X Y Z)

/-- smash_assoc symm-symm. -/
noncomputable def smash_assoc_symm_symm (X Y Z : Sp) :
    RwEq (Path.symm (Path.symm (N.smash_assoc X Y Z)))
         (N.smash_assoc X Y Z) :=
  rweq_of_step (Step.symm_symm (N.smash_assoc X Y Z))

/-- smash_assoc right-unit. -/
noncomputable def smash_assoc_refl_right (X Y Z : Sp) :
    RwEq (Path.trans (N.smash_assoc X Y Z) (Path.refl _))
         (N.smash_assoc X Y Z) :=
  rweq_cmpA_refl_right (N.smash_assoc X Y Z)

/-- smash_assoc left-unit. -/
noncomputable def smash_assoc_refl_left (X Y Z : Sp) :
    RwEq (Path.trans (Path.refl _) (N.smash_assoc X Y Z))
         (N.smash_assoc X Y Z) :=
  rweq_cmpA_refl_left (N.smash_assoc X Y Z)

/-- Smash comm composed with its inverse gives refl. -/
noncomputable def smash_comm_cancel_left (X Y : Sp) :
    RwEq (Path.trans (Path.symm (N.smash_comm X Y)) (N.smash_comm X Y))
         (Path.refl _) :=
  rweq_cmpA_inv_left (N.smash_comm X Y)

end NilpotenceData

/-- Periodicity theorem data (Hopkins-Smith): v_n self-maps exist
on type n spectra. -/
structure PeriodicityData (Sp : Type u) where
  /-- Chromatic type assignment. -/
  chrType : Sp → Nat
  /-- The v_n self-map. -/
  vnMap : (X : Sp) → Sp → Sp
  /-- v_n self-map is periodic: v_n^k is non-nilpotent. -/
  periodicWitness : (X : Sp) → (k : Nat) → Sp
  /-- Periodicity path. -/
  periodicPath : (X : Sp) → (k : Nat) →
    Path (periodicWitness X (k + 1)) (vnMap X (periodicWitness X k))

namespace PeriodicityData

variable {Sp : Type u} (P : PeriodicityData Sp)

/-- periodicPath right-cancels. -/
noncomputable def periodicPath_cancel_right (X : Sp) (k : Nat) :
    RwEq (Path.trans (P.periodicPath X k)
                     (Path.symm (P.periodicPath X k)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (P.periodicPath X k)

/-- periodicPath symm-symm. -/
noncomputable def periodicPath_symm_symm (X : Sp) (k : Nat) :
    RwEq (Path.symm (Path.symm (P.periodicPath X k)))
         (P.periodicPath X k) :=
  rweq_of_step (Step.symm_symm (P.periodicPath X k))

/-- periodicPath right-unit. -/
noncomputable def periodicPath_refl_right (X : Sp) (k : Nat) :
    RwEq (Path.trans (P.periodicPath X k) (Path.refl _))
         (P.periodicPath X k) :=
  rweq_cmpA_refl_right (P.periodicPath X k)

/-- periodicPath left-unit. -/
noncomputable def periodicPath_refl_left (X : Sp) (k : Nat) :
    RwEq (Path.trans (Path.refl _) (P.periodicPath X k))
         (P.periodicPath X k) :=
  rweq_cmpA_refl_left (P.periodicPath X k)

/-- periodicPath left-cancels. -/
noncomputable def periodicPath_cancel_left (X : Sp) (k : Nat) :
    RwEq (Path.trans (Path.symm (P.periodicPath X k))
                     (P.periodicPath X k))
         (Path.refl _) :=
  rweq_cmpA_inv_left (P.periodicPath X k)

end PeriodicityData

end BousfieldNilpotence
end Chromatic
end ComputationalPaths
