import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Log geometry paths: logarithmic structures

This module packages a minimal logarithmic-geometry interface with explicit
computational paths. Chart compatibility, unit transport, and path-preserving
functoriality are represented via `Path`, `Path.Step`, and `RwEq`.
-/

namespace ComputationalPaths
namespace Log
namespace LogStructuresPaths

open Path

universe u

/-- Domain-specific rewrite tags for logarithmic-structure coherence moves. -/
inductive LogStructureStep : Type
  | chartMul
  | chartUnit
  | transport

/-- Minimal logarithmic-structure data with chart and path-preserving transport. -/
structure LogStructurePathData (Obj Monoid : Type u) where
  chart : Obj → Monoid
  strataMul : Obj → Obj → Obj
  monoidMul : Monoid → Monoid → Monoid
  unitObj : Obj
  unitMonoid : Monoid
  chartMulPath :
    ∀ x y : Obj,
      Path (chart (strataMul x y)) (monoidMul (chart x) (chart y))
  chartUnitPath :
    Path (chart unitObj) unitMonoid
  transportChart :
    {x y : Obj} → Path x y → Path (chart x) (chart y)

namespace LogStructurePathData

variable {Obj Monoid : Type u} (L : LogStructurePathData Obj Monoid)

/-- Step witness: right-unit normalization for chart multiplicativity. -/
def chartMul_step (x y : Obj) :
    Path.Step
      (Path.trans (L.chartMulPath x y)
        (Path.refl (L.monoidMul (L.chart x) (L.chart y))))
      (L.chartMulPath x y) :=
  Path.Step.trans_refl_right (L.chartMulPath x y)

noncomputable def chartMul_rweq (x y : Obj) :
    RwEq
      (Path.trans (L.chartMulPath x y)
        (Path.refl (L.monoidMul (L.chart x) (L.chart y))))
      (L.chartMulPath x y) :=
  rweq_of_step (L.chartMul_step x y)

/-- Step witness: right-unit normalization for the chart-unit comparison. -/
def chartUnit_step :
    Path.Step
      (Path.trans L.chartUnitPath (Path.refl L.unitMonoid))
      L.chartUnitPath :=
  Path.Step.trans_refl_right L.chartUnitPath

noncomputable def chartUnit_rweq :
    RwEq
      (Path.trans L.chartUnitPath (Path.refl L.unitMonoid))
      L.chartUnitPath :=
  rweq_of_step (L.chartUnit_step)

/-- Step witness: right-unit normalization for chart transport along paths. -/
def transportChart_step {x y : Obj} (p : Path x y) :
    Path.Step
      (Path.trans (L.transportChart p) (Path.refl (L.chart y)))
      (L.transportChart p) :=
  Path.Step.trans_refl_right (L.transportChart p)

noncomputable def transportChart_rweq {x y : Obj} (p : Path x y) :
    RwEq
      (Path.trans (L.transportChart p) (Path.refl (L.chart y)))
      (L.transportChart p) :=
  rweq_of_step (L.transportChart_step p)

noncomputable def chartUnit_cancel_rweq :
    RwEq
      (Path.trans (Path.symm L.chartUnitPath) L.chartUnitPath)
      (Path.refl L.unitMonoid) :=
  rweq_cmpA_inv_left L.chartUnitPath

end LogStructurePathData

/-- Trivial instance instantiating the logarithmic-structure path interface. -/
def trivialLogStructurePathData : LogStructurePathData PUnit Nat where
  chart := fun _ => 0
  strataMul := fun _ _ => PUnit.unit
  monoidMul := Nat.add
  unitObj := PUnit.unit
  unitMonoid := 0
  chartMulPath := fun _ _ => Path.refl 0
  chartUnitPath := Path.refl 0
  transportChart := fun _ => Path.refl 0

end LogStructuresPaths
end Log
end ComputationalPaths
