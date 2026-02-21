import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Localization path infrastructure

This module packages localization endofunctors that act on computational paths.
The action on paths is accompanied by explicit `Step` witnesses showing:

1. path preservation (`mapPath p ▷ congrArg obj p`), and
2. path reflection (`mapPath (reflectPath q) ▷* q`).
-/

namespace ComputationalPaths
namespace Localization

open Path
open Path.Step

universe u

/-- Localization endofunctor with explicit reflection witness on paths. -/
structure LocalizationFunctor (A : Type u) where
  /-- Action on objects. -/
  obj : A → A
  /-- Reflection of localized paths back to source paths. -/
  reflectPath : {a b : A} → Path (obj a) (obj b) → Path a b
  /-- Step witness that reflected paths map back to the original localized path. -/
  reflect_step :
    ∀ {a b : A} (q : Path (obj a) (obj b)),
      Path.Step (Path.congrArg obj (reflectPath q)) q

namespace LocalizationFunctor

variable {A : Type u} (L : LocalizationFunctor A)

/-- Localization action on paths with an explicit trailing identity segment. -/
def mapPath {a b : A} (p : Path a b) : Path (L.obj a) (L.obj b) :=
  Path.trans (Path.congrArg L.obj p) (Path.refl (L.obj b))

/-- Localization preserves paths with a direct `Step` witness. -/
theorem mapPath_preserves_step {a b : A} (p : Path a b) :
    Path.Step (L.mapPath p) (Path.congrArg L.obj p) := by
  simpa [mapPath] using
    (Path.Step.trans_refl_right (Path.congrArg L.obj p))

/-- Preservation witness lifted to the reflexive-transitive closure. -/
theorem mapPath_preserves_rw {a b : A} (p : Path a b) :
    Rw (L.mapPath p) (Path.congrArg L.obj p) :=
  rw_of_step (L.mapPath_preserves_step p)

/-- Preservation witness lifted to rewrite equivalence. -/
noncomputable def mapPath_preserves_rweq {a b : A} (p : Path a b) :
    RwEq (L.mapPath p) (Path.congrArg L.obj p) :=
  rweq_of_step (L.mapPath_preserves_step p)

/-- Localization reflects localized paths back to themselves via explicit steps. -/
theorem map_reflect_rw {a b : A} (q : Path (L.obj a) (L.obj b)) :
    Rw (L.mapPath (L.reflectPath q)) q := by
  apply Rw.tail
  · exact rw_of_step
      (Path.Step.trans_congr_left (Path.refl (L.obj b)) (L.reflect_step q))
  · exact Path.Step.trans_refl_right q

/-- Reflection witness as rewrite equivalence. -/
noncomputable def map_reflect_rweq {a b : A} (q : Path (L.obj a) (L.obj b)) :
    RwEq (L.mapPath (L.reflectPath q)) q :=
  rweq_of_rw (L.map_reflect_rw q)

/-- Raw reflection witness exposed directly in `Step` form. -/
theorem reflects_path_step {a b : A} (q : Path (L.obj a) (L.obj b)) :
    Path.Step (Path.congrArg L.obj (L.reflectPath q)) q :=
  L.reflect_step q

end LocalizationFunctor
end Localization
end ComputationalPaths
