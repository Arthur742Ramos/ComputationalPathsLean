/- 
# Liquid tensor path infrastructure

This module encodes liquid tensor coherence with explicit computational
rewrite data (`Path.Step`) and derived rewrite equivalences (`RwEq`).
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Condensed
namespace LiquidTensor

open Path

universe u

/-- Path-level data for liquid tensor behavior. -/
structure LiquidTensorPathData (X : Type u) where
  tensor : X → X → X
  liquidize : X → X
  liquidizePath : ∀ x : X, Path (liquidize x) x
  liquidizeStep :
    ∀ x : X,
      Path.Step (Path.trans (liquidizePath x) (Path.refl x)) (liquidizePath x)
  leftPath :
    ∀ x y : X,
      Path (tensor (liquidize x) y) (liquidize (tensor x y))
  rightPath :
    ∀ x y : X,
      Path (liquidize (tensor x y)) (tensor x (liquidize y))
  compositeStep :
    ∀ x y : X,
      Path.Step
        (Path.trans
          (Path.trans (leftPath x y) (rightPath x y))
          (Path.refl (tensor x (liquidize y))))
        (Path.trans (leftPath x y) (rightPath x y))

namespace LiquidTensorPathData

variable {X : Type u} (L : LiquidTensorPathData X)

@[simp] theorem liquidize_rweq (x : X) :
    RwEq (Path.trans (L.liquidizePath x) (Path.refl x)) (L.liquidizePath x) :=
  rweq_of_step (L.liquidizeStep x)

@[simp] theorem composite_rweq (x y : X) :
    RwEq
      (Path.trans
        (Path.trans (L.leftPath x y) (L.rightPath x y))
        (Path.refl (L.tensor x (L.liquidize y))))
      (Path.trans (L.leftPath x y) (L.rightPath x y)) :=
  rweq_of_step (L.compositeStep x y)

/-- Normalization of a composite liquid tensor path with two trailing units. -/
theorem composite_two_refl_rweq (x y : X) :
    RwEq
      (Path.trans
        (Path.trans
          (Path.trans (L.leftPath x y) (L.rightPath x y))
          (Path.refl (L.tensor x (L.liquidize y))))
        (Path.refl (L.tensor x (L.liquidize y))))
      (Path.trans (L.leftPath x y) (L.rightPath x y)) := by
  exact rweq_trans
    (rweq_of_step
      (Path.Step.trans_assoc
        (Path.trans (L.leftPath x y) (L.rightPath x y))
        (Path.refl (L.tensor x (L.liquidize y)))
        (Path.refl (L.tensor x (L.liquidize y)))))
    (rweq_trans
      (rweq_trans_congr_right
        (Path.trans (L.leftPath x y) (L.rightPath x y))
        (rweq_cmpA_refl_left (Path.refl (L.tensor x (L.liquidize y)))))
      (L.composite_rweq x y))

@[simp] theorem composite_cancel_right (x y : X) :
    RwEq
      (Path.trans
        (Path.trans (L.leftPath x y) (L.rightPath x y))
        (Path.symm (Path.trans (L.leftPath x y) (L.rightPath x y))))
      (Path.refl (L.tensor (L.liquidize x) y)) :=
  rweq_cmpA_inv_right (Path.trans (L.leftPath x y) (L.rightPath x y))

@[simp] theorem composite_cancel_left (x y : X) :
    RwEq
      (Path.trans
        (Path.symm (Path.trans (L.leftPath x y) (L.rightPath x y)))
        (Path.trans (L.leftPath x y) (L.rightPath x y)))
      (Path.refl (L.tensor x (L.liquidize y))) :=
  rweq_cmpA_inv_left (Path.trans (L.leftPath x y) (L.rightPath x y))

theorem liquidize_two_unit_exact (x : X) :
    RwEq
      (Path.trans
        (L.liquidizePath x)
        (Path.trans (Path.refl x) (Path.refl x)))
      (L.liquidizePath x) := by
  sorry

theorem tensor_composite_assoc_exact (x y : X) :
    RwEq
      (Path.trans
        (L.leftPath x y)
        (Path.trans (L.rightPath x y) (Path.refl (L.tensor x (L.liquidize y)))))
      (Path.trans (L.leftPath x y) (L.rightPath x y)) := by
  sorry

theorem tensor_left_cancel_exact (x y : X) :
    RwEq
      (Path.trans
        (Path.symm (L.leftPath x y))
        (Path.trans (L.leftPath x y) (L.rightPath x y)))
      (L.rightPath x y) := by
  sorry

theorem tensor_right_cancel_exact (x y : X) :
    RwEq
      (Path.trans
        (Path.trans (L.leftPath x y) (L.rightPath x y))
        (Path.symm (L.rightPath x y)))
      (L.leftPath x y) := by
  sorry

end LiquidTensorPathData

/-- Canonical liquid tensor package: left projection tensor with identity
liquidization, carrying explicit step witnesses. -/
def leftProjectionLiquidTensorPathData (X : Type u) : LiquidTensorPathData X where
  tensor := fun x _ => x
  liquidize := fun x => x
  liquidizePath := fun x => Path.refl x
  liquidizeStep := fun x => Path.Step.trans_refl_right (Path.refl x)
  leftPath := fun x _ => Path.refl x
  rightPath := fun x _ => Path.refl x
  compositeStep := fun x _ =>
    Path.Step.trans_refl_right (Path.trans (Path.refl x) (Path.refl x))

/-- In the canonical model, the composite liquid tensor path cancels with its
inverse by rewrite normalization. -/
theorem leftProjection_composite_cancel (X : Type u) (x y : X) :
    RwEq
      (Path.trans
        (Path.trans (Path.refl x) (Path.refl x))
        (Path.symm (Path.trans (Path.refl x) (Path.refl x))))
      (Path.refl x) :=
  (leftProjectionLiquidTensorPathData X).composite_cancel_right x y

end LiquidTensor
end Condensed
end ComputationalPaths
