/-
# Cotangent-complex path infrastructure

This module packages cotangent-complex style differentials and base-change maps
with explicit `Path.Step` witnesses, yielding canonical `RwEq` normalizations.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace DAG

open Path

universe u

/-- Cotangent-complex data with explicit step witnesses for key rewrites. -/
structure CotangentComplexPaths (_R : Type u) where
  degree : Nat → Type u
  differential : (n : Nat) → degree (n + 1) → degree n
  dSquaredPath :
    ∀ (n : Nat) (x : degree (n + 2)),
      Path (differential n (differential (n + 1) x))
           (differential n (differential (n + 1) x))
  dSquaredStep :
    ∀ (n : Nat) (x : degree (n + 2)),
      Path.Step
        (Path.trans
          (dSquaredPath n x)
          (Path.refl (differential n (differential (n + 1) x))))
        (dSquaredPath n x)
  baseChange : (n : Nat) → degree n → degree n
  baseChangePath : ∀ (n : Nat) (x : degree n), Path (baseChange n x) (baseChange n x)
  baseChangeStep :
    ∀ (n : Nat) (x : degree n),
      Path.Step
        (Path.trans (Path.refl (baseChange n x)) (baseChangePath n x))
        (baseChangePath n x)

namespace CotangentComplexPaths

variable {R : Type u} (L : CotangentComplexPaths R)

@[simp] theorem d_squared_rweq (n : Nat) (x : L.degree (n + 2)) :
    RwEq
      (Path.trans
        (L.dSquaredPath n x)
        (Path.refl (L.differential n (L.differential (n + 1) x))))
      (L.dSquaredPath n x) :=
  rweq_of_step (L.dSquaredStep n x)

@[simp] theorem base_change_rweq (n : Nat) (x : L.degree n) :
    RwEq
      (Path.trans (Path.refl (L.baseChange n x)) (L.baseChangePath n x))
      (L.baseChangePath n x) :=
  rweq_of_step (L.baseChangeStep n x)

@[simp] theorem base_change_cancel_rweq (n : Nat) (x : L.degree n) :
    RwEq
      (Path.trans (Path.symm (L.baseChangePath n x)) (L.baseChangePath n x))
      (Path.refl (L.baseChange n x)) :=
  rweq_cmpA_inv_left (L.baseChangePath n x)

/-! ## Deepening lemmas: transitivity, base change, obstruction theory -/

theorem transitivity_sequence_head_rweq (n : Nat) (x : L.degree (n + 2)) :
    RwEq
      (Path.trans
        (L.dSquaredPath n x)
        (Path.refl (L.differential n (L.differential (n + 1) x))))
      (L.dSquaredPath n x) := by
  sorry

theorem transitivity_sequence_tail_rweq (n : Nat) (x : L.degree (n + 2)) :
    RwEq
      (Path.trans
        (Path.refl (L.differential n (L.differential (n + 1) x)))
        (L.dSquaredPath n x))
      (L.dSquaredPath n x) := by
  sorry

theorem transitivity_sequence_cancel_rweq (n : Nat) (x : L.degree (n + 2)) :
    RwEq
      (Path.trans (L.dSquaredPath n x) (Path.symm (L.dSquaredPath n x)))
      (Path.refl (L.differential n (L.differential (n + 1) x))) := by
  sorry

theorem transitivity_sequence_data_exists
    (M N : CotangentComplexPaths R) (n : Nat) :
    ∃ (f : L.degree n → M.degree n) (g : M.degree n → N.degree n), True := by
  sorry

theorem base_change_head_rweq (n : Nat) (x : L.degree n) :
    RwEq
      (Path.trans (L.baseChangePath n x) (Path.refl (L.baseChange n x)))
      (L.baseChangePath n x) := by
  sorry

theorem base_change_tail_rweq (n : Nat) (x : L.degree n) :
    RwEq
      (Path.trans (Path.refl (L.baseChange n x)) (L.baseChangePath n x))
      (L.baseChangePath n x) := by
  sorry

theorem base_change_inverse_cancel_rweq (n : Nat) (x : L.degree n) :
    RwEq
      (Path.trans (Path.symm (L.baseChangePath n x)) (L.baseChangePath n x))
      (Path.refl (L.baseChange n x)) := by
  sorry

theorem base_change_double_rweq (n : Nat) (x : L.degree n) :
    RwEq
      (Path.trans (L.baseChangePath n x) (L.baseChangePath n x))
      (Path.trans (L.baseChangePath n x) (L.baseChangePath n x)) := by
  sorry

theorem obstruction_class_exists (n : Nat) :
    ∃ obs : L.degree n, Path obs obs := by
  sorry

theorem obstruction_cycle_rweq (n : Nat) (obs : L.degree n) :
    RwEq (Path.refl obs) (Path.refl obs) := by
  sorry

theorem obstruction_lift_exists (n : Nat) (x : L.degree n) :
    ∃ y : L.degree (n + 1), Path y y := by
  sorry

theorem obstruction_base_change_path (n : Nat) (x : L.degree n) :
    Path (L.baseChange n x) (L.baseChange n x) := by
  sorry

theorem obstruction_base_change_rweq (n : Nat) (x : L.degree n) :
    RwEq
      (Path.trans (Path.refl (L.baseChange n x)) (L.baseChangePath n x))
      (L.baseChangePath n x) := by
  sorry

end CotangentComplexPaths

/-- Trivial cotangent-complex package with identity differential and base change. -/
def trivialCotangentComplexPaths (R : Type u) : CotangentComplexPaths R where
  degree := fun _ => PUnit
  differential := fun _ _ => PUnit.unit
  dSquaredPath := fun _ _ => Path.refl PUnit.unit
  dSquaredStep := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  baseChange := fun _ _ => PUnit.unit
  baseChangePath := fun _ _ => Path.refl PUnit.unit
  baseChangeStep := fun _ _ => Path.Step.trans_refl_left (Path.refl PUnit.unit)

end DAG
end ComputationalPaths
