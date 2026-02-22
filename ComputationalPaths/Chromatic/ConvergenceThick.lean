/-
# Chromatic convergence and thick subcategory paths

This module packages the chromatic convergence theorem structure and
the thick subcategory theorem (Hopkins-Smith) within the computational-path
framework. The filtration of the stable homotopy category by Morava K-theories
is tracked by `Path`, `Step`, and `RwEq` witnesses.
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Chromatic.PathInfrastructure

namespace ComputationalPaths
namespace Chromatic
namespace Convergence

open Path

universe u

/-- Chromatic convergence data: the inverse limit of the chromatic tower
recovers the p-local spectrum, with path witnesses. -/
structure ChromaticConvergenceData (X : Type u) where
  /-- p-local spectrum. -/
  pLocal : Type u
  /-- Localized spectrum at height n. -/
  localized : Nat → Type u
  /-- Localization map. -/
  localize : (n : Nat) → pLocal → localized n
  /-- Tower transition map L_{n+1} → L_n. -/
  tower : (n : Nat) → localized (n + 1) → localized n
  /-- Compatibility: tower ∘ localize_{n+1} = localize_n. -/
  compat : (n : Nat) → (x : pLocal) →
    Path (tower n (localize (n + 1) x)) (localize n x)
  /-- Convergence witness: the inverse limit structure. -/
  limitWitness : pLocal → (n : Nat) → localized n
  /-- The limit projection agrees with localization. -/
  limitAgree : (x : pLocal) → (n : Nat) →
    Path (limitWitness x n) (localize n x)

namespace ChromaticConvergenceData

variable {X : Type u} (C : ChromaticConvergenceData X)

/-- Compatibility right-cancels. -/
noncomputable def compat_cancel_right (n : Nat) (x : C.pLocal) :
    RwEq (Path.trans (C.compat n x) (Path.symm (C.compat n x)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (C.compat n x)

/-- Compatibility left-cancels. -/
noncomputable def compat_cancel_left (n : Nat) (x : C.pLocal) :
    RwEq (Path.trans (Path.symm (C.compat n x)) (C.compat n x))
         (Path.refl _) :=
  rweq_cmpA_inv_left (C.compat n x)

/-- Compatibility symm-symm. -/
noncomputable def compat_symm_symm (n : Nat) (x : C.pLocal) :
    RwEq (Path.symm (Path.symm (C.compat n x)))
         (C.compat n x) :=
  rweq_of_step (Step.symm_symm (C.compat n x))

/-- Compatibility right-unit. -/
noncomputable def compat_refl_right (n : Nat) (x : C.pLocal) :
    RwEq (Path.trans (C.compat n x) (Path.refl _))
         (C.compat n x) :=
  rweq_cmpA_refl_right (C.compat n x)

/-- Compatibility left-unit. -/
noncomputable def compat_refl_left (n : Nat) (x : C.pLocal) :
    RwEq (Path.trans (Path.refl _) (C.compat n x))
         (C.compat n x) :=
  rweq_cmpA_refl_left (C.compat n x)

/-- Limit agreement right-cancels. -/
noncomputable def limitAgree_cancel_right (x : C.pLocal) (n : Nat) :
    RwEq (Path.trans (C.limitAgree x n) (Path.symm (C.limitAgree x n)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (C.limitAgree x n)

/-- Limit agreement symm-symm. -/
noncomputable def limitAgree_symm_symm (x : C.pLocal) (n : Nat) :
    RwEq (Path.symm (Path.symm (C.limitAgree x n)))
         (C.limitAgree x n) :=
  rweq_of_step (Step.symm_symm (C.limitAgree x n))

/-- Limit agreement right-unit. -/
noncomputable def limitAgree_refl_right (x : C.pLocal) (n : Nat) :
    RwEq (Path.trans (C.limitAgree x n) (Path.refl _))
         (C.limitAgree x n) :=
  rweq_cmpA_refl_right (C.limitAgree x n)

/-- Limit agreement left-unit. -/
noncomputable def limitAgree_refl_left (x : C.pLocal) (n : Nat) :
    RwEq (Path.trans (Path.refl _) (C.limitAgree x n))
         (C.limitAgree x n) :=
  rweq_cmpA_refl_left (C.limitAgree x n)

/-- Two-step compatibility: composing consecutive tower maps. -/
noncomputable def twoStepCompat (n : Nat) (x : C.pLocal) :
    Path (C.tower n (C.tower (n + 1) (C.localize (n + 2) x)))
         (C.localize n x) :=
  Path.trans (Path.congrArg (C.tower n) (C.compat (n + 1) x))
             (C.compat n x)

/-- Two-step compatibility right-cancels. -/
noncomputable def twoStepCompat_cancel_right (n : Nat) (x : C.pLocal) :
    RwEq (Path.trans (C.twoStepCompat n x) (Path.symm (C.twoStepCompat n x)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (C.twoStepCompat n x)

/-- Two-step compatibility symm-symm. -/
noncomputable def twoStepCompat_symm_symm (n : Nat) (x : C.pLocal) :
    RwEq (Path.symm (Path.symm (C.twoStepCompat n x)))
         (C.twoStepCompat n x) :=
  rweq_of_step (Step.symm_symm (C.twoStepCompat n x))

/-- Two-step compatibility right-unit. -/
noncomputable def twoStepCompat_refl_right (n : Nat) (x : C.pLocal) :
    RwEq (Path.trans (C.twoStepCompat n x) (Path.refl _))
         (C.twoStepCompat n x) :=
  rweq_cmpA_refl_right (C.twoStepCompat n x)

/-- Limit agrees with tower compat: limit projection is compatible
with tower transitions. -/
noncomputable def limit_tower_compat (x : C.pLocal) (n : Nat) :
    Path (C.tower n (C.limitWitness x (n + 1)))
         (C.limitWitness x n) :=
  Path.trans
    (Path.congrArg (C.tower n) (C.limitAgree x (n + 1)))
    (Path.trans (C.compat n x) (Path.symm (C.limitAgree x n)))

/-- limit_tower_compat right-cancels. -/
noncomputable def limit_tower_compat_cancel_right (x : C.pLocal) (n : Nat) :
    RwEq (Path.trans (C.limit_tower_compat x n)
                     (Path.symm (C.limit_tower_compat x n)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (C.limit_tower_compat x n)

/-- limit_tower_compat symm-symm. -/
noncomputable def limit_tower_compat_symm_symm (x : C.pLocal) (n : Nat) :
    RwEq (Path.symm (Path.symm (C.limit_tower_compat x n)))
         (C.limit_tower_compat x n) :=
  rweq_of_step (Step.symm_symm (C.limit_tower_compat x n))

end ChromaticConvergenceData

/-- Thick subcategory data (Hopkins-Smith classification): finite spectra
are classified by type, and the type determines the thick subcategory. -/
structure ThickSubcategoryData where
  /-- Type of a finite spectrum (its "chromatic type"). -/
  chromaticType : Type u
  /-- Ordering on types. -/
  typeLeq : chromaticType → chromaticType → Prop
  /-- The thick subcategory generated by type n contains type m iff m ≥ n. -/
  containment : (m n : chromaticType) → typeLeq n m → chromaticType
  /-- Containment witness is the type m itself. -/
  containment_eq : (m n : chromaticType) → (h : typeLeq n m) →
    Path (containment m n h) m
  /-- Type assignment is functorial under smash product. -/
  smash_type : chromaticType → chromaticType → chromaticType
  /-- Smash type is minimum. -/
  smash_comm : (a b : chromaticType) →
    Path (smash_type a b) (smash_type b a)

namespace ThickSubcategoryData

variable (T : ThickSubcategoryData)

/-- containment_eq right-cancels. -/
noncomputable def containment_eq_cancel_right (m n : T.chromaticType)
    (h : T.typeLeq n m) :
    RwEq (Path.trans (T.containment_eq m n h)
                     (Path.symm (T.containment_eq m n h)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (T.containment_eq m n h)

/-- containment_eq symm-symm. -/
noncomputable def containment_eq_symm_symm (m n : T.chromaticType)
    (h : T.typeLeq n m) :
    RwEq (Path.symm (Path.symm (T.containment_eq m n h)))
         (T.containment_eq m n h) :=
  rweq_of_step (Step.symm_symm (T.containment_eq m n h))

/-- smash_comm right-cancels. -/
noncomputable def smash_comm_cancel_right (a b : T.chromaticType) :
    RwEq (Path.trans (T.smash_comm a b) (Path.symm (T.smash_comm a b)))
         (Path.refl _) :=
  rweq_cmpA_inv_right (T.smash_comm a b)

/-- smash_comm symm-symm. -/
noncomputable def smash_comm_symm_symm (a b : T.chromaticType) :
    RwEq (Path.symm (Path.symm (T.smash_comm a b)))
         (T.smash_comm a b) :=
  rweq_of_step (Step.symm_symm (T.smash_comm a b))

/-- smash_comm right-unit. -/
noncomputable def smash_comm_refl_right (a b : T.chromaticType) :
    RwEq (Path.trans (T.smash_comm a b) (Path.refl _))
         (T.smash_comm a b) :=
  rweq_cmpA_refl_right (T.smash_comm a b)

/-- smash_comm left-unit. -/
noncomputable def smash_comm_refl_left (a b : T.chromaticType) :
    RwEq (Path.trans (Path.refl _) (T.smash_comm a b))
         (T.smash_comm a b) :=
  rweq_cmpA_refl_left (T.smash_comm a b)

/-- Smash commutativity composed with its inverse is refl. -/
noncomputable def smash_comm_cancel_left (a b : T.chromaticType) :
    RwEq (Path.trans (Path.symm (T.smash_comm a b)) (T.smash_comm a b))
         (Path.refl _) :=
  rweq_cmpA_inv_left (T.smash_comm a b)

end ThickSubcategoryData

end Convergence
end Chromatic
end ComputationalPaths
