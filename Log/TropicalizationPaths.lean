import ComputationalPaths.Path.Rewrite.RwEq
import Log.LogStructuresPaths

/-!
# Log geometry paths: tropicalization

This module links logarithmic structures to tropicalized data using
path-preserving constructions. Tropicalization compatibility is encoded with
explicit `Path` composites, normalized by `Path.Step`, and compared by `RwEq`.
-/

namespace ComputationalPaths
namespace Log
namespace TropicalizationPaths

open Path
open LogStructuresPaths

universe u v

/-- Tropicalization package over a logarithmic-structure path model. -/
structure LogTropicalizationPathData {Obj Monoid : Type u}
    (L : LogStructurePathData Obj Monoid) (Γ : Type v) where
  tropicalize : Monoid → Γ
  tropMul : Γ → Γ → Γ
  tropicalizeMulPath :
    ∀ x y : Obj,
      Path
        (tropicalize (L.monoidMul (L.chart x) (L.chart y)))
        (tropMul (tropicalize (L.chart x)) (tropicalize (L.chart y)))
  tropicalizeUnitPath :
    Path (tropicalize L.unitMonoid)
      (tropMul (tropicalize L.unitMonoid) (tropicalize L.unitMonoid))
  tropicalizeMap :
    {a b : Monoid} → Path a b → Path (tropicalize a) (tropicalize b)

namespace LogTropicalizationPathData

variable {Obj Monoid : Type u} {Γ : Type v}
variable {L : LogStructurePathData Obj Monoid}
variable (T : LogTropicalizationPathData L Γ)

/-- Tropicalization preserves the chart-unit comparison path. -/
def tropicalizeChartUnit :
    Path (T.tropicalize (L.chart L.unitObj)) (T.tropicalize L.unitMonoid) :=
  T.tropicalizeMap L.chartUnitPath

/-- Composite path: tropicalizing chart multiplication agrees with tropical sum. -/
def tropicalizeChartMul (x y : Obj) :
    Path
      (T.tropicalize (L.chart (L.strataMul x y)))
      (T.tropMul (T.tropicalize (L.chart x)) (T.tropicalize (L.chart y))) :=
  Path.trans (T.tropicalizeMap (L.chartMulPath x y)) (T.tropicalizeMulPath x y)

/-- Step witness: right-unit normalization for mapped tropicalization paths. -/
def tropicalizeMap_step {a b : Monoid} (p : Path a b) :
    Path.Step
      (Path.trans (T.tropicalizeMap p) (Path.refl (T.tropicalize b)))
      (T.tropicalizeMap p) :=
  Path.Step.trans_refl_right (T.tropicalizeMap p)

@[simp] theorem tropicalizeMap_rweq {a b : Monoid} (p : Path a b) :
    RwEq
      (Path.trans (T.tropicalizeMap p) (Path.refl (T.tropicalize b)))
      (T.tropicalizeMap p) :=
  rweq_of_step (T.tropicalizeMap_step p)

/-- Step witness: right-unit normalization for tropicalized multiplication. -/
def tropicalizeMul_step (x y : Obj) :
    Path.Step
      (Path.trans (T.tropicalizeMulPath x y)
        (Path.refl (T.tropMul (T.tropicalize (L.chart x)) (T.tropicalize (L.chart y)))))
      (T.tropicalizeMulPath x y) :=
  Path.Step.trans_refl_right (T.tropicalizeMulPath x y)

@[simp] theorem tropicalizeMul_rweq (x y : Obj) :
    RwEq
      (Path.trans (T.tropicalizeMulPath x y)
        (Path.refl (T.tropMul (T.tropicalize (L.chart x)) (T.tropicalize (L.chart y)))))
      (T.tropicalizeMulPath x y) :=
  rweq_of_step (T.tropicalizeMul_step x y)

/-- Step witness: right-unit normalization for the tropicalized unit path. -/
def tropicalizeUnit_step :
    Path.Step
      (Path.trans T.tropicalizeUnitPath
        (Path.refl (T.tropMul (T.tropicalize L.unitMonoid) (T.tropicalize L.unitMonoid))))
      T.tropicalizeUnitPath :=
  Path.Step.trans_refl_right T.tropicalizeUnitPath

@[simp] theorem tropicalizeUnit_rweq :
    RwEq
      (Path.trans T.tropicalizeUnitPath
        (Path.refl (T.tropMul (T.tropicalize L.unitMonoid) (T.tropicalize L.unitMonoid))))
      T.tropicalizeUnitPath :=
  rweq_of_step (T.tropicalizeUnit_step)

/-- Step witness: right-unit normalization for tropicalized chart multiplication. -/
def tropicalizeChartMul_step (x y : Obj) :
    Path.Step
      (Path.trans (T.tropicalizeChartMul x y)
        (Path.refl (T.tropMul (T.tropicalize (L.chart x)) (T.tropicalize (L.chart y)))))
      (T.tropicalizeChartMul x y) :=
  Path.Step.trans_refl_right (T.tropicalizeChartMul x y)

@[simp] theorem tropicalizeChartMul_rweq (x y : Obj) :
    RwEq
      (Path.trans (T.tropicalizeChartMul x y)
        (Path.refl (T.tropMul (T.tropicalize (L.chart x)) (T.tropicalize (L.chart y)))))
      (T.tropicalizeChartMul x y) :=
  rweq_of_step (T.tropicalizeChartMul_step x y)

@[simp] theorem tropicalizeChartMul_cancel_rweq (x y : Obj) :
    RwEq
      (Path.trans (Path.symm (T.tropicalizeChartMul x y)) (T.tropicalizeChartMul x y))
      (Path.refl (T.tropMul (T.tropicalize (L.chart x)) (T.tropicalize (L.chart y)))) :=
  rweq_cmpA_inv_left (T.tropicalizeChartMul x y)

end LogTropicalizationPathData

/-- Trivial instance instantiating logarithmic tropicalization path data. -/
def trivialLogTropicalizationPathData :
    LogTropicalizationPathData LogStructuresPaths.trivialLogStructurePathData Nat where
  tropicalize := fun n => n
  tropMul := Nat.add
  tropicalizeMulPath := fun _ _ => Path.refl 0
  tropicalizeUnitPath := Path.refl 0
  tropicalizeMap := fun p => p

end TropicalizationPaths
end Log
end ComputationalPaths
