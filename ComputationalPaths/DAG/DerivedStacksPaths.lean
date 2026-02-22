/-
# Derived stack path infrastructure

This module packages derived-stack style descent and atlas gluing data with
explicit `Path.Step` witnesses so normalization is available as `RwEq`.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace DAG

open Path

universe u v

/-- Derived-stack descent data tracked by explicit computational steps. -/
structure DerivedStackPaths (Obj : Type u) where
  atlas : Obj → Type v
  prestack : Obj → Type v
  pullback : {X Y : Obj} → Path X Y → prestack Y → prestack X
  descentPath :
    ∀ {X Y : Obj} (p : Path X Y) (s : prestack Y),
      Path (pullback p s) (pullback p s)
  descentStep :
    ∀ {X Y : Obj} (p : Path X Y) (s : prestack Y),
      Path.Step
        (Path.trans (descentPath p s) (Path.refl (pullback p s)))
        (descentPath p s)
  atlasGluePath : ∀ (X : Obj) (a : atlas X), Path a a
  atlasGlueStep :
    ∀ (X : Obj) (a : atlas X),
      Path.Step
        (Path.trans (Path.refl a) (atlasGluePath X a))
        (atlasGluePath X a)

namespace DerivedStackPaths

variable {Obj : Type u} (D : DerivedStackPaths Obj)

noncomputable def descent_rweq {X Y : Obj} (p : Path X Y) (s : D.prestack Y) :
    RwEq
      (Path.trans (D.descentPath p s) (Path.refl (D.pullback p s)))
      (D.descentPath p s) :=
  rweq_of_step (D.descentStep p s)

noncomputable def atlas_glue_rweq (X : Obj) (a : D.atlas X) :
    RwEq
      (Path.trans (Path.refl a) (D.atlasGluePath X a))
      (D.atlasGluePath X a) :=
  rweq_of_step (D.atlasGlueStep X a)

noncomputable def descent_cancel_rweq {X Y : Obj}
    (p : Path X Y) (s : D.prestack Y) :
    RwEq
      (Path.trans (D.descentPath p s) (Path.symm (D.descentPath p s)))
      (Path.refl (D.pullback p s)) :=
  rweq_cmpA_inv_right (D.descentPath p s)

end DerivedStackPaths

/-- Trivial derived-stack package with identity pullback and canonical steps. -/
noncomputable def trivialDerivedStackPaths (Obj : Type u) : DerivedStackPaths Obj where
  atlas := fun _ => PUnit
  prestack := fun _ => PUnit
  pullback := fun _ _ => PUnit.unit
  descentPath := fun _ _ => Path.refl PUnit.unit
  descentStep := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  atlasGluePath := fun _ _ => Path.refl PUnit.unit
  atlasGlueStep := fun _ _ => Path.Step.trans_refl_left (Path.refl PUnit.unit)

end DAG
end ComputationalPaths
