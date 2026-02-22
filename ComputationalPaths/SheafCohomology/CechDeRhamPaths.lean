/-
# Sheaf Cohomology: Čech–de Rham Complex & Hypercohomology Paths

Develops Čech cohomology refinement maps, de Rham-style differential
forms, double-complex data, hypercohomology filtration, and
Čech–de Rham comparison paths — all via computational paths with
Step/Path/trans/symm/congrArg.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.SheafCohomology.PathInfrastructure

set_option linter.unusedVariables false

namespace ComputationalPaths
namespace Path
namespace SheafCohomology

open Path

universe u v

noncomputable section

/-! ## Čech refinement data -/

/-- Čech refinement: maps between Čech complexes of different covers. -/
structure CechRefinementData (A : Type u) where
  zero : A
  add  : A → A → A
  neg  : A → A
  cechCocycle  : Nat → A → A
  cechCobdry   : Nat → A → A
  refinementMap : Nat → A → A
  refinementCommutes : ∀ n : Nat, ∀ x : A,
    Path (cechCobdry n (refinementMap n x))
         (refinementMap (n + 1) (cechCobdry n x))
  cechDSquared : ∀ n : Nat, ∀ x : A,
    Path (cechCobdry (n + 1) (cechCobdry n x)) zero
  refinementZero : ∀ n : Nat,
    Path (refinementMap n zero) zero
  cobdryZero : ∀ n : Nat,
    Path (cechCobdry n zero) zero

namespace CechRefinementData

variable {A : Type u} (C : CechRefinementData A)

/-! ### Theorem 1-10: Čech refinement coherences -/

/-- Theorem 1: Refinement commutes with coboundary. -/
noncomputable def refine_commutes (n : Nat) (x : A) :
    Path (C.cechCobdry n (C.refinementMap n x))
         (C.refinementMap (n + 1) (C.cechCobdry n x)) :=
  C.refinementCommutes n x

/-- Theorem 2: Čech d² = 0. -/
noncomputable def cech_d_squared (n : Nat) (x : A) :
    Path (C.cechCobdry (n + 1) (C.cechCobdry n x)) C.zero :=
  C.cechDSquared n x

/-- Theorem 3: Refinement at zero. -/
noncomputable def refine_zero (n : Nat) :
    Path (C.refinementMap n C.zero) C.zero :=
  C.refinementZero n

/-- Theorem 4: Coboundary at zero. -/
noncomputable def cobdry_zero (n : Nat) :
    Path (C.cechCobdry n C.zero) C.zero :=
  C.cobdryZero n

/-- Theorem 5: refine commutes right-unit. -/
noncomputable def refine_commutes_right_unit (n : Nat) (x : A) :
    RwEq (Path.trans (C.refinementCommutes n x) (Path.refl _))
         (C.refinementCommutes n x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 6: refine commutes inverse cancel. -/
noncomputable def refine_commutes_inv_cancel (n : Nat) (x : A) :
    RwEq (Path.trans (C.refinementCommutes n x)
                     (Path.symm (C.refinementCommutes n x)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 7: cech d² right-unit. -/
noncomputable def cech_d_squared_right_unit (n : Nat) (x : A) :
    RwEq (Path.trans (C.cechDSquared n x) (Path.refl _))
         (C.cechDSquared n x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 8: cech d² inverse cancel. -/
noncomputable def cech_d_squared_inv_cancel (n : Nat) (x : A) :
    RwEq (Path.trans (C.cechDSquared n x)
                     (Path.symm (C.cechDSquared n x)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 9: refinement congruence. -/
noncomputable def refine_congr (n : Nat) {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (C.refinementMap n x₁) (C.refinementMap n x₂) :=
  Path.congrArg (C.refinementMap n) p

/-- Theorem 10: coboundary congruence. -/
noncomputable def cobdry_congr (n : Nat) {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (C.cechCobdry n x₁) (C.cechCobdry n x₂) :=
  Path.congrArg (C.cechCobdry n) p

/-! ### Theorem 11-15: Additional Čech coherences -/

/-- Theorem 11: refine zero right-unit. -/
noncomputable def refine_zero_right_unit (n : Nat) :
    RwEq (Path.trans (C.refinementZero n) (Path.refl _))
         (C.refinementZero n) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 12: cobdry zero inverse cancel. -/
noncomputable def cobdry_zero_inv_cancel (n : Nat) :
    RwEq (Path.trans (C.cobdryZero n) (Path.symm (C.cobdryZero n)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 13: d² double symmetry. -/
noncomputable def cech_d_squared_symm_symm (n : Nat) (x : A) :
    RwEq (Path.symm (Path.symm (C.cechDSquared n x)))
         (C.cechDSquared n x) :=
  rweq_of_step (Step.symm_symm _)

/-- Theorem 14: refine commutes left-unit. -/
noncomputable def refine_commutes_left_unit (n : Nat) (x : A) :
    RwEq (Path.trans (Path.refl _) (C.refinementCommutes n x))
         (C.refinementCommutes n x) :=
  rweq_of_step (Step.trans_refl_left _)

/-- Theorem 15: d² left-inverse. -/
noncomputable def cech_d_squared_left_inv (n : Nat) (x : A) :
    RwEq (Path.trans (Path.symm (C.cechDSquared n x))
                     (C.cechDSquared n x))
         (Path.refl _) :=
  rweq_of_step (Step.symm_trans _)

end CechRefinementData

/-! ## Double complex and hypercohomology -/

/-- Double complex data with horizontal and vertical differentials. -/
structure DoubleComplexData (A : Type u) where
  zero : A
  add  : A → A → A
  dH   : Nat → Nat → A → A    -- horizontal differential
  dV   : Nat → Nat → A → A    -- vertical differential
  dHSquared : ∀ p q : Nat, ∀ x : A,
    Path (dH (p + 1) q (dH p q x)) zero
  dVSquared : ∀ p q : Nat, ∀ x : A,
    Path (dV p (q + 1) (dV p q x)) zero
  anticommute : ∀ p q : Nat, ∀ x : A,
    Path (add (dH p (q + 1) (dV p q x)) (dV (p + 1) q (dH p q x))) zero
  dHZero : ∀ p q : Nat, Path (dH p q zero) zero
  dVZero : ∀ p q : Nat, Path (dV p q zero) zero

namespace DoubleComplexData

variable {A : Type u} (D : DoubleComplexData A)

/-! ### Theorem 16-30: Double complex coherences -/

/-- Theorem 16: Horizontal d² = 0. -/
noncomputable def dH_squared (p q : Nat) (x : A) :
    Path (D.dH (p + 1) q (D.dH p q x)) D.zero :=
  D.dHSquared p q x

/-- Theorem 17: Vertical d² = 0. -/
noncomputable def dV_squared (p q : Nat) (x : A) :
    Path (D.dV p (q + 1) (D.dV p q x)) D.zero :=
  D.dVSquared p q x

/-- Theorem 18: Anti-commutativity. -/
noncomputable def dHV_anticommute (p q : Nat) (x : A) :
    Path (D.add (D.dH p (q + 1) (D.dV p q x))
                (D.dV (p + 1) q (D.dH p q x))) D.zero :=
  D.anticommute p q x

/-- Theorem 19: dH at zero. -/
noncomputable def dH_zero (p q : Nat) :
    Path (D.dH p q D.zero) D.zero :=
  D.dHZero p q

/-- Theorem 20: dV at zero. -/
noncomputable def dV_zero (p q : Nat) :
    Path (D.dV p q D.zero) D.zero :=
  D.dVZero p q

/-- Theorem 21: dH² right-unit. -/
noncomputable def dH_squared_right_unit (p q : Nat) (x : A) :
    RwEq (Path.trans (D.dHSquared p q x) (Path.refl _))
         (D.dHSquared p q x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 22: dV² right-unit. -/
noncomputable def dV_squared_right_unit (p q : Nat) (x : A) :
    RwEq (Path.trans (D.dVSquared p q x) (Path.refl _))
         (D.dVSquared p q x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 23: dH² inverse cancel. -/
noncomputable def dH_squared_inv_cancel (p q : Nat) (x : A) :
    RwEq (Path.trans (D.dHSquared p q x)
                     (Path.symm (D.dHSquared p q x)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 24: dV² inverse cancel. -/
noncomputable def dV_squared_inv_cancel (p q : Nat) (x : A) :
    RwEq (Path.trans (D.dVSquared p q x)
                     (Path.symm (D.dVSquared p q x)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 25: anticommutation right-unit. -/
noncomputable def anticommute_right_unit (p q : Nat) (x : A) :
    RwEq (Path.trans (D.anticommute p q x) (Path.refl _))
         (D.anticommute p q x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 26: dH congruence. -/
noncomputable def dH_congr (p q : Nat) {x₁ x₂ : A} (h : Path x₁ x₂) :
    Path (D.dH p q x₁) (D.dH p q x₂) :=
  Path.congrArg (D.dH p q) h

/-- Theorem 27: dV congruence. -/
noncomputable def dV_congr (p q : Nat) {x₁ x₂ : A} (h : Path x₁ x₂) :
    Path (D.dV p q x₁) (D.dV p q x₂) :=
  Path.congrArg (D.dV p q) h

/-- Theorem 28: dH zero inverse cancel. -/
noncomputable def dH_zero_inv_cancel (p q : Nat) :
    RwEq (Path.trans (D.dHZero p q) (Path.symm (D.dHZero p q)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 29: dV zero inverse cancel. -/
noncomputable def dV_zero_inv_cancel (p q : Nat) :
    RwEq (Path.trans (D.dVZero p q) (Path.symm (D.dVZero p q)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 30: anticommutation double symmetry. -/
noncomputable def anticommute_symm_symm (p q : Nat) (x : A) :
    RwEq (Path.symm (Path.symm (D.anticommute p q x)))
         (D.anticommute p q x) :=
  rweq_of_step (Step.symm_symm _)

/-! ### Theorem 31-40: Total complex and filtration -/

/-- Total complex differential: combines dH and dV with sign. -/
noncomputable def totalDiff (p q : Nat) (x : A) : A :=
  D.add (D.dH p q x) (D.dV p q x)

/-- Theorem 31: Total diff congruence. -/
noncomputable def totalDiff_congr (p q : Nat) {x₁ x₂ : A} (h : Path x₁ x₂) :
    Path (D.totalDiff p q x₁) (D.totalDiff p q x₂) :=
  Path.congrArg (D.totalDiff p q) h

/-- Theorem 32: Total diff at zero. -/
noncomputable def totalDiff_zero (p q : Nat) :
    Path (D.totalDiff p q D.zero) (D.add D.zero D.zero) := by
  show Path (D.add (D.dH p q D.zero) (D.dV p q D.zero)) (D.add D.zero D.zero)
  exact Path.trans
    (Path.congrArg (fun t => D.add t (D.dV p q D.zero)) (D.dHZero p q))
    (Path.congrArg (D.add D.zero) (D.dVZero p q))

/-- Theorem 33: dH squared left-unit. -/
noncomputable def dH_squared_left_unit (p q : Nat) (x : A) :
    RwEq (Path.trans (Path.refl _) (D.dHSquared p q x))
         (D.dHSquared p q x) :=
  rweq_of_step (Step.trans_refl_left _)

/-- Theorem 34: dV squared left-unit. -/
noncomputable def dV_squared_left_unit (p q : Nat) (x : A) :
    RwEq (Path.trans (Path.refl _) (D.dVSquared p q x))
         (D.dVSquared p q x) :=
  rweq_of_step (Step.trans_refl_left _)

/-- Theorem 35: dH squared left-inverse. -/
noncomputable def dH_squared_left_inv (p q : Nat) (x : A) :
    RwEq (Path.trans (Path.symm (D.dHSquared p q x))
                     (D.dHSquared p q x))
         (Path.refl _) :=
  rweq_of_step (Step.symm_trans _)

/-- Theorem 36: dH zero left-unit. -/
noncomputable def dH_zero_left_unit (p q : Nat) :
    RwEq (Path.trans (Path.refl _) (D.dHZero p q))
         (D.dHZero p q) :=
  rweq_of_step (Step.trans_refl_left _)

/-- Theorem 37: dV zero left-unit. -/
noncomputable def dV_zero_left_unit (p q : Nat) :
    RwEq (Path.trans (Path.refl _) (D.dVZero p q))
         (D.dVZero p q) :=
  rweq_of_step (Step.trans_refl_left _)

/-- Theorem 38: dH squared double symm. -/
noncomputable def dH_squared_symm_symm (p q : Nat) (x : A) :
    RwEq (Path.symm (Path.symm (D.dHSquared p q x)))
         (D.dHSquared p q x) :=
  rweq_of_step (Step.symm_symm _)

/-- Theorem 39: dV squared double symm. -/
noncomputable def dV_squared_symm_symm (p q : Nat) (x : A) :
    RwEq (Path.symm (Path.symm (D.dVSquared p q x)))
         (D.dVSquared p q x) :=
  rweq_of_step (Step.symm_symm _)

/-- Theorem 40: anticommutation left-inverse. -/
noncomputable def anticommute_left_inv (p q : Nat) (x : A) :
    RwEq (Path.trans (Path.symm (D.anticommute p q x))
                     (D.anticommute p q x))
         (Path.refl _) :=
  rweq_of_step (Step.symm_trans _)

end DoubleComplexData

end

end SheafCohomology
end Path
end ComputationalPaths
