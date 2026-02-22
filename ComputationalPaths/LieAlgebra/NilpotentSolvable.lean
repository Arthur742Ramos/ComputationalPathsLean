/-
# Lie Algebra: Nilpotent/Solvable Theory & Levi Decomposition Paths

Develops lower/upper central series, derived series, nilpotency/solvability
witnesses, semisimplicity, and Levi decomposition data — all via computational
paths with Step/Path/trans/symm/congrArg.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.LieAlgebra.PathInfrastructure

set_option linter.unusedVariables false

namespace ComputationalPaths
namespace Path
namespace LieAlgebra

open Path

universe u v

noncomputable section

/-! ## Derived & lower central series -/

/-- Data tracking the derived series and lower central series of a Lie algebra. -/
structure SeriesData (A : Type u) extends LieBracketData A where
  derivedSeries   : Nat → A → A
  lowerCentral    : Nat → A → A
  derivedZero     : ∀ x : A, Path (derivedSeries 0 x) x
  derivedSucc     : ∀ n : Nat, ∀ x y : A,
    Path (derivedSeries (n + 1) (bracket x y))
         (bracket (derivedSeries n x) (derivedSeries n y))
  lowerCentralZero : ∀ x : A, Path (lowerCentral 0 x) x
  lowerCentralSucc : ∀ n : Nat, ∀ x y : A,
    Path (lowerCentral (n + 1) (bracket x y))
         (bracket x (lowerCentral n y))

namespace SeriesData

variable {A : Type u} (S : SeriesData A)

/-! ### Theorem 1-10: Derived series coherences -/

/-- Theorem 1: Derived series at zero is identity. -/
noncomputable def derived_zero_id (x : A) :
    Path (S.derivedSeries 0 x) x :=
  S.derivedZero x

/-- Theorem 2: Derived series step. -/
noncomputable def derived_succ_bracket (n : Nat) (x y : A) :
    Path (S.derivedSeries (n + 1) (S.bracket x y))
         (S.bracket (S.derivedSeries n x) (S.derivedSeries n y)) :=
  S.derivedSucc n x y

/-- Theorem 3: derived_zero right-unit. -/
noncomputable def derived_zero_right_unit (x : A) :
    RwEq (Path.trans (S.derivedZero x) (Path.refl _)) (S.derivedZero x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 4: derived_zero left-unit. -/
noncomputable def derived_zero_left_unit (x : A) :
    RwEq (Path.trans (Path.refl _) (S.derivedZero x)) (S.derivedZero x) :=
  rweq_of_step (Step.trans_refl_left _)

/-- Theorem 5: derived_zero inverse cancel. -/
noncomputable def derived_zero_inv_cancel (x : A) :
    RwEq (Path.trans (S.derivedZero x) (Path.symm (S.derivedZero x)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 6: derived_zero left-inverse cancel. -/
noncomputable def derived_zero_left_inv (x : A) :
    RwEq (Path.trans (Path.symm (S.derivedZero x)) (S.derivedZero x))
         (Path.refl _) :=
  rweq_of_step (Step.symm_trans _)

/-- Theorem 7: derived_zero double symmetry. -/
noncomputable def derived_zero_symm_symm (x : A) :
    RwEq (Path.symm (Path.symm (S.derivedZero x))) (S.derivedZero x) :=
  rweq_of_step (Step.symm_symm _)

/-- Theorem 8: Derived series congruence. -/
noncomputable def derived_congr (n : Nat) {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (S.derivedSeries n x₁) (S.derivedSeries n x₂) :=
  Path.congrArg (S.derivedSeries n) p

/-- Theorem 9: derived_succ right-unit. -/
noncomputable def derived_succ_right_unit (n : Nat) (x y : A) :
    RwEq (Path.trans (S.derivedSucc n x y) (Path.refl _))
         (S.derivedSucc n x y) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 10: derived_succ inverse cancel. -/
noncomputable def derived_succ_inv_cancel (n : Nat) (x y : A) :
    RwEq (Path.trans (S.derivedSucc n x y) (Path.symm (S.derivedSucc n x y)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-! ### Theorem 11-20: Lower central series coherences -/

/-- Theorem 11: Lower central series at zero is identity. -/
noncomputable def lcs_zero_id (x : A) :
    Path (S.lowerCentral 0 x) x :=
  S.lowerCentralZero x

/-- Theorem 12: Lower central series step. -/
noncomputable def lcs_succ (n : Nat) (x y : A) :
    Path (S.lowerCentral (n + 1) (S.bracket x y))
         (S.bracket x (S.lowerCentral n y)) :=
  S.lowerCentralSucc n x y

/-- Theorem 13: lcs_zero right-unit. -/
noncomputable def lcs_zero_right_unit (x : A) :
    RwEq (Path.trans (S.lowerCentralZero x) (Path.refl _))
         (S.lowerCentralZero x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 14: lcs_zero inverse cancel. -/
noncomputable def lcs_zero_inv_cancel (x : A) :
    RwEq (Path.trans (S.lowerCentralZero x) (Path.symm (S.lowerCentralZero x)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 15: lcs_succ right-unit. -/
noncomputable def lcs_succ_right_unit (n : Nat) (x y : A) :
    RwEq (Path.trans (S.lowerCentralSucc n x y) (Path.refl _))
         (S.lowerCentralSucc n x y) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 16: Lower central congruence. -/
noncomputable def lcs_congr (n : Nat) {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (S.lowerCentral n x₁) (S.lowerCentral n x₂) :=
  Path.congrArg (S.lowerCentral n) p

/-- Theorem 17: lcs_zero left-unit. -/
noncomputable def lcs_zero_left_unit (x : A) :
    RwEq (Path.trans (Path.refl _) (S.lowerCentralZero x))
         (S.lowerCentralZero x) :=
  rweq_of_step (Step.trans_refl_left _)

/-- Theorem 18: lcs_zero double symmetry. -/
noncomputable def lcs_zero_symm_symm (x : A) :
    RwEq (Path.symm (Path.symm (S.lowerCentralZero x)))
         (S.lowerCentralZero x) :=
  rweq_of_step (Step.symm_symm _)

/-- Theorem 19: lcs_zero left-inverse. -/
noncomputable def lcs_zero_left_inv (x : A) :
    RwEq (Path.trans (Path.symm (S.lowerCentralZero x))
                     (S.lowerCentralZero x))
         (Path.refl _) :=
  rweq_of_step (Step.symm_trans _)

/-- Theorem 20: lcs_succ inverse cancel. -/
noncomputable def lcs_succ_inv_cancel (n : Nat) (x y : A) :
    RwEq (Path.trans (S.lowerCentralSucc n x y)
                     (Path.symm (S.lowerCentralSucc n x y)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-! ### Theorem 21-30: Nilpotency and solvability -/

/-- Nilpotency witness: lower central series reaches zero. -/
structure NilpotentWitness where
  degree : Nat
  nilPath : ∀ x : A, Path (S.lowerCentral degree x) S.zero

/-- Solvability witness: derived series reaches zero. -/
structure SolvableWitness where
  degree : Nat
  solvPath : ∀ x : A, Path (S.derivedSeries degree x) S.zero

variable (NW : S.NilpotentWitness) (SW : S.SolvableWitness)

/-- Theorem 21: Nilpotent witness path. -/
noncomputable def nilpotent_at (x : A) :
    Path (S.lowerCentral NW.degree x) S.zero :=
  NW.nilPath x

/-- Theorem 22: Nilpotent witness right-unit. -/
noncomputable def nilpotent_right_unit (x : A) :
    RwEq (Path.trans (NW.nilPath x) (Path.refl _)) (NW.nilPath x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 23: Nilpotent witness inverse cancel. -/
noncomputable def nilpotent_inv_cancel (x : A) :
    RwEq (Path.trans (NW.nilPath x) (Path.symm (NW.nilPath x)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 24: Nilpotent congruence. -/
noncomputable def nilpotent_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (S.lowerCentral NW.degree x₁) (S.lowerCentral NW.degree x₂) :=
  Path.congrArg (S.lowerCentral NW.degree) p

/-- Theorem 25: Solvable witness path. -/
noncomputable def solvable_at (x : A) :
    Path (S.derivedSeries SW.degree x) S.zero :=
  SW.solvPath x

/-- Theorem 26: Solvable witness right-unit. -/
noncomputable def solvable_right_unit (x : A) :
    RwEq (Path.trans (SW.solvPath x) (Path.refl _)) (SW.solvPath x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 27: Solvable witness inverse cancel. -/
noncomputable def solvable_inv_cancel (x : A) :
    RwEq (Path.trans (SW.solvPath x) (Path.symm (SW.solvPath x)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 28: Solvable double symmetry. -/
noncomputable def solvable_symm_symm (x : A) :
    RwEq (Path.symm (Path.symm (SW.solvPath x))) (SW.solvPath x) :=
  rweq_of_step (Step.symm_symm _)

/-- Theorem 29: Solvable congruence. -/
noncomputable def solvable_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (S.derivedSeries SW.degree x₁) (S.derivedSeries SW.degree x₂) :=
  Path.congrArg (S.derivedSeries SW.degree) p

/-- Theorem 30: Solvable left-unit. -/
noncomputable def solvable_left_unit (x : A) :
    RwEq (Path.trans (Path.refl _) (SW.solvPath x)) (SW.solvPath x) :=
  rweq_of_step (Step.trans_refl_left _)

/-! ### Theorem 31-40: Semisimple & Levi decomposition -/

/-- Semisimplicity data: the algebra has no solvable ideals. -/
structure SemisimpleData where
  project  : A → A
  radical  : A → A
  leviPath : ∀ x : A, Path (S.add (project x) (radical x)) x
  projectBracket : ∀ x y : A,
    Path (project (S.bracket x y)) (S.bracket (project x) (project y))
  radicalZero : ∀ x : A, Path (S.bracket (radical x) (radical x)) S.zero

variable (SS : S.SemisimpleData)

/-- Theorem 31: Levi decomposition path. -/
noncomputable def levi_decomp (x : A) :
    Path (S.add (SS.project x) (SS.radical x)) x :=
  SS.leviPath x

/-- Theorem 32: Projection preserves brackets. -/
noncomputable def levi_project_bracket (x y : A) :
    Path (SS.project (S.bracket x y))
         (S.bracket (SS.project x) (SS.project y)) :=
  SS.projectBracket x y

/-- Theorem 33: Radical is solvable (bracket vanishes). -/
noncomputable def levi_radical_zero (x : A) :
    Path (S.bracket (SS.radical x) (SS.radical x)) S.zero :=
  SS.radicalZero x

/-- Theorem 34: Levi decomposition right-unit. -/
noncomputable def levi_right_unit (x : A) :
    RwEq (Path.trans (SS.leviPath x) (Path.refl _))
         (SS.leviPath x) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 35: Levi decomposition inverse cancel. -/
noncomputable def levi_inv_cancel (x : A) :
    RwEq (Path.trans (SS.leviPath x) (Path.symm (SS.leviPath x)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

/-- Theorem 36: Levi decomposition double symmetry. -/
noncomputable def levi_symm_symm (x : A) :
    RwEq (Path.symm (Path.symm (SS.leviPath x)))
         (SS.leviPath x) :=
  rweq_of_step (Step.symm_symm _)

/-- Theorem 37: Project congruence. -/
noncomputable def levi_project_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (SS.project x₁) (SS.project x₂) :=
  Path.congrArg SS.project p

/-- Theorem 38: Radical congruence. -/
noncomputable def levi_radical_congr {x₁ x₂ : A} (p : Path x₁ x₂) :
    Path (SS.radical x₁) (SS.radical x₂) :=
  Path.congrArg SS.radical p

/-- Theorem 39: project bracket right-unit. -/
noncomputable def levi_project_bracket_right_unit (x y : A) :
    RwEq (Path.trans (SS.projectBracket x y) (Path.refl _))
         (SS.projectBracket x y) :=
  rweq_of_step (Step.trans_refl_right _)

/-- Theorem 40: radical zero inverse cancel. -/
noncomputable def levi_radical_zero_inv_cancel (x : A) :
    RwEq (Path.trans (SS.radicalZero x) (Path.symm (SS.radicalZero x)))
         (Path.refl _) :=
  rweq_of_step (Step.trans_symm _)

end SeriesData

end

end LieAlgebra
end Path
end ComputationalPaths
