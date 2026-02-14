/- 
# Solid module path infrastructure

This module packages computational witnesses for solidification maps in
condensed algebra.  Coherences are carried by `Path`, with explicit
`Path.Step` witnesses showing rewrite-normalization behavior.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Condensed
namespace SolidModules

open Path

universe u

/-- Path-level solid module data:
`solidify` with unit and idempotence witnesses, plus step-level normalization. -/
structure SolidModulePathData (M : Type u) where
  solidify : M → M
  unitPath : ∀ x : M, Path (solidify x) x
  unitStep :
    ∀ x : M,
      Path.Step (Path.trans (unitPath x) (Path.refl x)) (unitPath x)
  idempotentPath : ∀ x : M, Path (solidify (solidify x)) (solidify x)
  idempotentStep :
    ∀ x : M,
      Path.Step
        (Path.trans (idempotentPath x) (Path.refl (solidify x)))
        (idempotentPath x)

namespace SolidModulePathData

variable {M : Type u} (S : SolidModulePathData M)

@[simp] theorem unit_rweq (x : M) :
    RwEq (Path.trans (S.unitPath x) (Path.refl x)) (S.unitPath x) :=
  rweq_of_step (S.unitStep x)

@[simp] theorem idempotent_rweq (x : M) :
    RwEq
      (Path.trans (S.idempotentPath x) (Path.refl (S.solidify x)))
      (S.idempotentPath x) :=
  rweq_of_step (S.idempotentStep x)

@[simp] theorem unit_cancel_left (x : M) :
    RwEq
      (Path.trans (Path.symm (S.unitPath x)) (S.unitPath x))
      (Path.refl x) :=
  rweq_cmpA_inv_left (S.unitPath x)

@[simp] theorem unit_cancel_right (x : M) :
    RwEq
      (Path.trans (S.unitPath x) (Path.symm (S.unitPath x)))
      (Path.refl (S.solidify x)) :=
  rweq_cmpA_inv_right (S.unitPath x)

/-- Two-step normalization for idempotence paths, using associativity and unit
rewrite rules. -/
theorem idempotent_two_step_rweq (x : M) :
    RwEq
      (Path.trans
        (Path.trans (S.idempotentPath x) (Path.refl (S.solidify x)))
        (Path.refl (S.solidify x)))
      (S.idempotentPath x) := by
  exact rweq_trans
    (rweq_of_step
      (Path.Step.trans_assoc
        (S.idempotentPath x)
        (Path.refl (S.solidify x))
        (Path.refl (S.solidify x))))
    (rweq_trans
      (rweq_trans_congr_right
        (S.idempotentPath x)
        (rweq_cmpA_refl_left (Path.refl (S.solidify x))))
      (rweq_cmpA_refl_right (S.idempotentPath x)))

theorem solidify_unit_assoc_exact (x : M) :
    RwEq
      (Path.trans
        (Path.trans (S.idempotentPath x) (Path.refl (S.solidify x)))
        (S.unitPath x))
      (Path.trans (S.idempotentPath x) (S.unitPath x)) := by
  sorry

theorem solidify_unit_exact_right (x : M) :
    RwEq
      (Path.trans
        (Path.trans (S.idempotentPath x) (S.unitPath x))
        (Path.refl x))
      (Path.trans (S.idempotentPath x) (S.unitPath x)) := by
  sorry

theorem unit_split_exact_left (x : M) :
    RwEq
      (Path.trans
        (Path.trans (Path.symm (S.unitPath x)) (S.unitPath x))
        (Path.symm (S.unitPath x)))
      (Path.symm (S.unitPath x)) := by
  sorry

theorem solidification_exact_triangle (x : M) :
    RwEq
      (Path.trans
        (S.idempotentPath x)
        (Path.trans (S.unitPath x) (Path.symm (S.unitPath x))))
      (S.idempotentPath x) := by
  sorry

end SolidModulePathData

/-- Identity solidification package, giving concrete computational witnesses. -/
def identitySolidModulePathData (M : Type u) : SolidModulePathData M where
  solidify := fun x => x
  unitPath := fun x => Path.refl x
  unitStep := fun x => Path.Step.trans_refl_right (Path.refl x)
  idempotentPath := fun x => Path.refl x
  idempotentStep := fun x => Path.Step.trans_refl_right (Path.refl x)

/-- The canonical identity solidification satisfies two-step normalization. -/
theorem identity_idempotent_two_step_rweq (M : Type u) (x : M) :
    RwEq
      (Path.trans (Path.trans (Path.refl x) (Path.refl x)) (Path.refl x))
      (Path.refl x) :=
  (identitySolidModulePathData M).idempotent_two_step_rweq x

end SolidModules
end Condensed
end ComputationalPaths
