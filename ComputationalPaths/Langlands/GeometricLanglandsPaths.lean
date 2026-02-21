import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Geometric Langlands path infrastructure

This module packages geometric Langlands coherence data with explicit
computational-step witnesses (`Path.Step`) and derived rewrite equivalences
(`RwEq`).
-/

namespace ComputationalPaths
namespace Langlands

open Path

universe u v

/-- Geometric Langlands package with explicit `Path.Step` witnesses. -/
structure GeometricLanglandsPathData (BunObj : Type u) (SpecObj : Type v) where
  /-- Hecke modification on `Bun_G` objects. -/
  heckeModify : BunObj → BunObj
  /-- Candidate Hecke eigensheaf assignment. -/
  eigensheaf : BunObj → BunObj
  /-- Spectral transform toward the dual local-system side. -/
  spectralTransform : BunObj → SpecObj
  /-- Hecke eigensheaf compatibility path. -/
  heckeEigenPath :
    ∀ F : BunObj, Path (eigensheaf (heckeModify F)) (heckeModify (eigensheaf F))
  /-- Primitive right-unit normalization witness for Hecke compatibility. -/
  heckeEigenStep :
    ∀ F : BunObj,
      Path.Step
        (Path.trans (heckeEigenPath F) (Path.refl (heckeModify (eigensheaf F))))
        (heckeEigenPath F)
  /-- Spectral compatibility path for Hecke modification. -/
  spectralCompatPath :
    ∀ F : BunObj, Path (spectralTransform (heckeModify F)) (spectralTransform F)
  /-- Primitive left-unit normalization witness for spectral compatibility. -/
  spectralCompatStep :
    ∀ F : BunObj,
      Path.Step
        (Path.trans (Path.refl (spectralTransform (heckeModify F))) (spectralCompatPath F))
        (spectralCompatPath F)

namespace GeometricLanglandsPathData

variable {BunObj : Type u} {SpecObj : Type v}
variable (G : GeometricLanglandsPathData BunObj SpecObj)

noncomputable def heckeEigen_rweq (F : BunObj) :
    RwEq
      (Path.trans (G.heckeEigenPath F) (Path.refl (G.heckeModify (G.eigensheaf F))))
      (G.heckeEigenPath F) :=
  rweq_of_step (G.heckeEigenStep F)

noncomputable def spectralCompat_rweq (F : BunObj) :
    RwEq
      (Path.trans (Path.refl (G.spectralTransform (G.heckeModify F))) (G.spectralCompatPath F))
      (G.spectralCompatPath F) :=
  rweq_of_step (G.spectralCompatStep F)

noncomputable def heckeEigen_cancel_rweq (F : BunObj) :
    RwEq
      (Path.trans (Path.symm (G.heckeEigenPath F)) (G.heckeEigenPath F))
      (Path.refl (G.heckeModify (G.eigensheaf F))) :=
  rweq_cmpA_inv_left (G.heckeEigenPath F)

noncomputable def spectralCompat_cancel_rweq (F : BunObj) :
    RwEq
      (Path.trans (G.spectralCompatPath F) (Path.symm (G.spectralCompatPath F)))
      (Path.refl (G.spectralTransform (G.heckeModify F))) :=
  rweq_cmpA_inv_right (G.spectralCompatPath F)

end GeometricLanglandsPathData

/-- Build geometric Langlands path data from primary path-level witnesses. -/
def mkGeometricLanglandsPathData
    {BunObj : Type u} {SpecObj : Type v}
    (heckeModify : BunObj → BunObj)
    (eigensheaf : BunObj → BunObj)
    (spectralTransform : BunObj → SpecObj)
    (heckeEigenPath :
      ∀ F : BunObj, Path (eigensheaf (heckeModify F)) (heckeModify (eigensheaf F)))
    (spectralCompatPath :
      ∀ F : BunObj, Path (spectralTransform (heckeModify F)) (spectralTransform F)) :
    GeometricLanglandsPathData BunObj SpecObj where
  heckeModify := heckeModify
  eigensheaf := eigensheaf
  spectralTransform := spectralTransform
  heckeEigenPath := heckeEigenPath
  heckeEigenStep := fun F => Path.Step.trans_refl_right (heckeEigenPath F)
  spectralCompatPath := spectralCompatPath
  spectralCompatStep := fun F => Path.Step.trans_refl_left (spectralCompatPath F)

end Langlands
end ComputationalPaths
