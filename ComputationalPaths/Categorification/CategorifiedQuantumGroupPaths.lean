import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Categorification paths: categorified quantum groups

This module packages a lightweight computational-path interface for categorified
quantum groups. Coherence laws are tracked by explicit `Path` witnesses and
normalization witnesses in `Path.Step`, then compared via `RwEq`.
-/

namespace ComputationalPaths
namespace Categorification
namespace CategorifiedQuantumGroupPaths

open Path

universe u

/-- Domain-specific rewrite tags for categorified quantum-group coherence moves. -/
inductive CatQGroupStep : Type
  | crossing
  | nilHecke
  | biadjunctionUnit
  | biadjunctionCounit
  | bubble

/-- Minimal computational-path interface for categorified quantum groups. -/
structure CatQuantumGroupPathData (Obj : Type u) where
  tensor : Obj → Obj → Obj
  shift : Obj → Obj
  e1 : Obj → Obj
  f1 : Obj → Obj
  crossingPath :
    (X Y : Obj) →
      Path (tensor (e1 X) (f1 Y))
        (tensor (f1 Y) (e1 X))
  nilHeckePath :
    (X : Obj) →
      Path (tensor (e1 (e1 X)) (shift X))
        (tensor (e1 (e1 X)) (shift X))
  unitPath :
    (X : Obj) →
      Path (tensor (f1 (e1 X)) (shift X))
        (shift X)
  counitPath :
    (X : Obj) →
      Path (shift X)
        (tensor (e1 (f1 X)) (shift X))
  braidHexagonPath :
    (X Y Z : Obj) →
      Path (tensor (tensor (e1 X) (f1 Y)) (shift Z))
        (tensor (e1 X) (tensor (f1 Y) (shift Z)))

namespace CatQuantumGroupPathData

variable {Obj : Type u}
variable (Q : CatQuantumGroupPathData Obj)

/-- Step witness: right-unit normalization for crossings. -/
noncomputable def crossing_step (X Y : Obj) :
    Path.Step
      (Path.trans
        (Q.crossingPath X Y)
        (Path.refl (Q.tensor (Q.f1 Y) (Q.e1 X))))
      (Q.crossingPath X Y) :=
  Path.Step.trans_refl_right (Q.crossingPath X Y)

noncomputable def crossing_rweq (X Y : Obj) :
    RwEq
      (Path.trans
        (Q.crossingPath X Y)
        (Path.refl (Q.tensor (Q.f1 Y) (Q.e1 X))))
      (Q.crossingPath X Y) :=
  rweq_of_step (Q.crossing_step X Y)

/-- Step witness: left-unit normalization for nil-Hecke paths. -/
noncomputable def nilHecke_step (X : Obj) :
    Path.Step
      (Path.trans
        (Path.refl (Q.tensor (Q.e1 (Q.e1 X)) (Q.shift X)))
        (Q.nilHeckePath X))
      (Q.nilHeckePath X) :=
  Path.Step.trans_refl_left (Q.nilHeckePath X)

noncomputable def nilHecke_rweq (X : Obj) :
    RwEq
      (Path.trans
        (Path.refl (Q.tensor (Q.e1 (Q.e1 X)) (Q.shift X)))
        (Q.nilHeckePath X))
      (Q.nilHeckePath X) :=
  rweq_of_step (Q.nilHecke_step X)

/-- Unit followed by counit, modeling a biadjunction triangle leg. -/
noncomputable def unitCounitTrianglePath (X : Obj) :
    Path (Q.tensor (Q.f1 (Q.e1 X)) (Q.shift X))
      (Q.tensor (Q.e1 (Q.f1 X)) (Q.shift X)) :=
  Path.trans (Q.unitPath X) (Q.counitPath X)

noncomputable def unitCounitTriangle_rweq (X : Obj) :
    RwEq
      (Path.trans
        (Q.unitCounitTrianglePath X)
        (Path.refl (Q.tensor (Q.e1 (Q.f1 X)) (Q.shift X))))
      (Q.unitCounitTrianglePath X) :=
  rweq_cmpA_refl_right (Q.unitCounitTrianglePath X)

noncomputable def crossing_cancel_left (X Y : Obj) :
    RwEq
      (Path.trans (Path.symm (Q.crossingPath X Y)) (Q.crossingPath X Y))
      (Path.refl (Q.tensor (Q.f1 Y) (Q.e1 X))) :=
  rweq_cmpA_inv_left (Q.crossingPath X Y)

noncomputable def crossing_cancel_right (X Y : Obj) :
    RwEq
      (Path.trans (Q.crossingPath X Y) (Path.symm (Q.crossingPath X Y)))
      (Path.refl (Q.tensor (Q.e1 X) (Q.f1 Y))) :=
  rweq_cmpA_inv_right (Q.crossingPath X Y)

/-- Step witness: right-unit normalization for braid-hexagon coherence. -/
noncomputable def braidHexagon_step (X Y Z : Obj) :
    Path.Step
      (Path.trans
        (Q.braidHexagonPath X Y Z)
        (Path.refl (Q.tensor (Q.e1 X) (Q.tensor (Q.f1 Y) (Q.shift Z)))))
      (Q.braidHexagonPath X Y Z) :=
  Path.Step.trans_refl_right (Q.braidHexagonPath X Y Z)

noncomputable def braidHexagon_rweq (X Y Z : Obj) :
    RwEq
      (Path.trans
        (Q.braidHexagonPath X Y Z)
        (Path.refl (Q.tensor (Q.e1 X) (Q.tensor (Q.f1 Y) (Q.shift Z)))))
      (Q.braidHexagonPath X Y Z) :=
  rweq_of_step (Q.braidHexagon_step X Y Z)

noncomputable def unitCounit_cancel_rweq (X : Obj) :
    RwEq
      (Path.trans
        (Path.symm (Q.unitCounitTrianglePath X))
        (Q.unitCounitTrianglePath X))
      (Path.refl (Q.tensor (Q.e1 (Q.f1 X)) (Q.shift X))) :=
  rweq_cmpA_inv_left (Q.unitCounitTrianglePath X)

end CatQuantumGroupPathData

/-- Trivial model instantiating categorified quantum-group path data. -/
noncomputable def trivialCatQuantumGroupPathData : CatQuantumGroupPathData PUnit where
  tensor := fun _ _ => PUnit.unit
  shift := fun _ => PUnit.unit
  e1 := fun _ => PUnit.unit
  f1 := fun _ => PUnit.unit
  crossingPath := fun _ _ => Path.refl PUnit.unit
  nilHeckePath := fun _ => Path.refl PUnit.unit
  unitPath := fun _ => Path.refl PUnit.unit
  counitPath := fun _ => Path.refl PUnit.unit
  braidHexagonPath := fun _ _ _ => Path.refl PUnit.unit

end CategorifiedQuantumGroupPaths
end Categorification
end ComputationalPaths
