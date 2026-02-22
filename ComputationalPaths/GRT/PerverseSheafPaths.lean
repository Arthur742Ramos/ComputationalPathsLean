import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Perverse sheaf path infrastructure

This module packages perverse-sheaf style operations with explicit
computational-step witnesses (`Path.Step`) and derived rewrite equivalences
(`RwEq`).
-/

namespace ComputationalPaths
namespace GRT

open Path

universe u

/-- Perverse-sheaf operations with explicit `Path.Step` witnesses. -/
structure PerverseSheafPathData (Obj : Type u) where
  /-- Cohomological shift. -/
  shift : Obj → Int → Obj
  /-- Nearby-cycles functor. -/
  nearbyCycles : Obj → Obj
  /-- Vanishing-cycles functor. -/
  vanishingCycles : Obj → Obj
  /-- `t`-exactness witness at shift `0` for nearby cycles. -/
  tExactPath : ∀ F : Obj, Path (shift (nearbyCycles F) 0) (nearbyCycles F)
  /-- Primitive rewrite witness for right-unit normalization of `t`-exactness. -/
  tExactStep :
    ∀ F : Obj,
      Path.Step
        (Path.trans (tExactPath F) (Path.refl (nearbyCycles F)))
        (tExactPath F)
  /-- Gluing witness between vanishing and nearby cycles. -/
  gluingPath : ∀ F : Obj, Path (vanishingCycles F) (nearbyCycles F)
  /-- Primitive rewrite witness for left-unit normalization of gluing. -/
  gluingStep :
    ∀ F : Obj,
      Path.Step
        (Path.trans (Path.refl (vanishingCycles F)) (gluingPath F))
        (gluingPath F)

namespace PerverseSheafPathData

variable {Obj : Type u} (P : PerverseSheafPathData Obj)

noncomputable def tExact_rweq (F : Obj) :
    RwEq
      (Path.trans (P.tExactPath F) (Path.refl (P.nearbyCycles F)))
      (P.tExactPath F) :=
  rweq_of_step (P.tExactStep F)

@[simp] theorem tExact_left_unit_step (F : Obj) :
    Path.Step
      (Path.trans (Path.refl (P.shift (P.nearbyCycles F) 0)) (P.tExactPath F))
      (P.tExactPath F) :=
  Path.Step.trans_refl_left (P.tExactPath F)

noncomputable def tExact_left_unit_rweq (F : Obj) :
    RwEq
      (Path.trans (Path.refl (P.shift (P.nearbyCycles F) 0)) (P.tExactPath F))
      (P.tExactPath F) :=
  rweq_of_step (P.tExact_left_unit_step F)

noncomputable def gluing_rweq (F : Obj) :
    RwEq
      (Path.trans (Path.refl (P.vanishingCycles F)) (P.gluingPath F))
      (P.gluingPath F) :=
  rweq_of_step (P.gluingStep F)

@[simp] theorem gluing_right_unit_step (F : Obj) :
    Path.Step
      (Path.trans (P.gluingPath F) (Path.refl (P.nearbyCycles F)))
      (P.gluingPath F) :=
  Path.Step.trans_refl_right (P.gluingPath F)

noncomputable def gluing_right_unit_rweq (F : Obj) :
    RwEq
      (Path.trans (P.gluingPath F) (Path.refl (P.nearbyCycles F)))
      (P.gluingPath F) :=
  rweq_of_step (P.gluing_right_unit_step F)

@[simp] theorem gluing_cancel_left_step (F : Obj) :
    Path.Step
      (Path.trans (Path.symm (P.gluingPath F)) (P.gluingPath F))
      (Path.refl (P.nearbyCycles F)) :=
  Path.Step.symm_trans (P.gluingPath F)

noncomputable def gluing_cancel_left_rweq (F : Obj) :
    RwEq
      (Path.trans (Path.symm (P.gluingPath F)) (P.gluingPath F))
      (Path.refl (P.nearbyCycles F)) :=
  rweq_of_step (P.gluing_cancel_left_step F)

@[simp] theorem gluing_cancel_right_step (F : Obj) :
    Path.Step
      (Path.trans (P.gluingPath F) (Path.symm (P.gluingPath F)))
      (Path.refl (P.vanishingCycles F)) :=
  Path.Step.trans_symm (P.gluingPath F)

noncomputable def gluing_cancel_right_rweq (F : Obj) :
    RwEq
      (Path.trans (P.gluingPath F) (Path.symm (P.gluingPath F)))
      (Path.refl (P.vanishingCycles F)) :=
  rweq_of_step (P.gluing_cancel_right_step F)

end PerverseSheafPathData

/-- Build perverse-sheaf path data from path-level witnesses. -/
noncomputable def mkPerverseSheafPathData
    {Obj : Type u}
    (shift : Obj → Int → Obj)
    (nearbyCycles : Obj → Obj)
    (vanishingCycles : Obj → Obj)
    (tExactPath : ∀ F : Obj, Path (shift (nearbyCycles F) 0) (nearbyCycles F))
    (gluingPath : ∀ F : Obj, Path (vanishingCycles F) (nearbyCycles F)) :
    PerverseSheafPathData Obj where
  shift := shift
  nearbyCycles := nearbyCycles
  vanishingCycles := vanishingCycles
  tExactPath := tExactPath
  tExactStep := fun F => Path.Step.trans_refl_right (tExactPath F)
  gluingPath := gluingPath
  gluingStep := fun F => Path.Step.trans_refl_left (gluingPath F)

end GRT
end ComputationalPaths
