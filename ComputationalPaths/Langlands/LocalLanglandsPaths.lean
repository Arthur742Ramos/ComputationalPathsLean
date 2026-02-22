import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Local Langlands path infrastructure

This module packages local Langlands compatibility data with explicit
computational-step witnesses (`Path.Step`) and derived rewrite equivalences
(`RwEq`).
-/

namespace ComputationalPaths
namespace Langlands

open Path

universe u v

/-- Local Langlands correspondence data with explicit `Path.Step` witnesses. -/
structure LocalLanglandsPathData (Rep : Type u) (Param : Type v) where
  /-- Local parameter map from representations to Langlands parameters. -/
  toParameter : Rep → Param
  /-- Frobenius twist on local representations. -/
  frobeniusTwist : Rep → Rep
  /-- Inertia restriction on local representations. -/
  inertiaRestriction : Rep → Rep
  /-- Compatibility of parameters with Frobenius twisting. -/
  frobeniusCompatPath :
    ∀ ρ : Rep, Path (toParameter (frobeniusTwist ρ)) (toParameter ρ)
  /-- Primitive right-unit normalization witness for Frobenius compatibility. -/
  frobeniusCompatStep :
    ∀ ρ : Rep,
      Path.Step
        (Path.trans (frobeniusCompatPath ρ) (Path.refl (toParameter ρ)))
        (frobeniusCompatPath ρ)
  /-- Compatibility of parameters with inertia restriction. -/
  inertiaCompatPath :
    ∀ ρ : Rep, Path (toParameter (inertiaRestriction ρ)) (toParameter ρ)
  /-- Primitive left-unit normalization witness for inertia compatibility. -/
  inertiaCompatStep :
    ∀ ρ : Rep,
      Path.Step
        (Path.trans (Path.refl (toParameter (inertiaRestriction ρ))) (inertiaCompatPath ρ))
        (inertiaCompatPath ρ)

namespace LocalLanglandsPathData

variable {Rep : Type u} {Param : Type v} (L : LocalLanglandsPathData Rep Param)

noncomputable def frobeniusCompat_rweq (ρ : Rep) :
    RwEq
      (Path.trans (L.frobeniusCompatPath ρ) (Path.refl (L.toParameter ρ)))
      (L.frobeniusCompatPath ρ) :=
  rweq_of_step (L.frobeniusCompatStep ρ)

noncomputable def inertiaCompat_rweq (ρ : Rep) :
    RwEq
      (Path.trans (Path.refl (L.toParameter (L.inertiaRestriction ρ))) (L.inertiaCompatPath ρ))
      (L.inertiaCompatPath ρ) :=
  rweq_of_step (L.inertiaCompatStep ρ)

noncomputable def frobeniusCompat_cancel_rweq (ρ : Rep) :
    RwEq
      (Path.trans (Path.symm (L.frobeniusCompatPath ρ)) (L.frobeniusCompatPath ρ))
      (Path.refl (L.toParameter ρ)) :=
  rweq_cmpA_inv_left (L.frobeniusCompatPath ρ)

noncomputable def inertiaCompat_cancel_rweq (ρ : Rep) :
    RwEq
      (Path.trans (L.inertiaCompatPath ρ) (Path.symm (L.inertiaCompatPath ρ)))
      (Path.refl (L.toParameter (L.inertiaRestriction ρ))) :=
  rweq_cmpA_inv_right (L.inertiaCompatPath ρ)

end LocalLanglandsPathData

/-- Build local Langlands path data from primary path-level witnesses. -/
noncomputable def mkLocalLanglandsPathData
    {Rep : Type u} {Param : Type v}
    (toParameter : Rep → Param)
    (frobeniusTwist : Rep → Rep)
    (inertiaRestriction : Rep → Rep)
    (frobeniusCompatPath :
      ∀ ρ : Rep, Path (toParameter (frobeniusTwist ρ)) (toParameter ρ))
    (inertiaCompatPath :
      ∀ ρ : Rep, Path (toParameter (inertiaRestriction ρ)) (toParameter ρ)) :
    LocalLanglandsPathData Rep Param where
  toParameter := toParameter
  frobeniusTwist := frobeniusTwist
  inertiaRestriction := inertiaRestriction
  frobeniusCompatPath := frobeniusCompatPath
  frobeniusCompatStep := fun ρ => Path.Step.trans_refl_right (frobeniusCompatPath ρ)
  inertiaCompatPath := inertiaCompatPath
  inertiaCompatStep := fun ρ => Path.Step.trans_refl_left (inertiaCompatPath ρ)

end Langlands
end ComputationalPaths
