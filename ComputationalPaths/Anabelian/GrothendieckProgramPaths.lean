import ComputationalPaths.Anabelian.ConjecturesPaths
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Grothendieck program paths for anabelian geometry

This module packages Grothendieck's anabelian reconstruction program with
explicit computational-step witnesses (`Path.Step`) and rewrite equivalences
(`RwEq`).
-/

namespace ComputationalPaths
namespace Anabelian

open Path

universe u

/-! ## Grothendieck's program -/

/-- Step-based infrastructure for Grothendieck's anabelian program. -/
structure GrothendieckProgramPaths (Obj : Type u) where
  /-- Conjectural section/Hom interfaces. -/
  conjectures : AnabelianConjecturePaths Obj
  /-- Reconstruction map from étale data. -/
  reconstruction : Obj → Obj
  /-- Reconstruction path witness. -/
  reconstructionPath :
    ∀ X : Obj, Path (reconstruction (conjectures.etalePi1 X)) X
  /-- Primitive right-unit normalization for reconstruction witnesses. -/
  reconstructionStep :
    ∀ X : Obj,
      Path.Step
        (Path.trans (reconstructionPath X) (Path.refl X))
        (reconstructionPath X)
  /-- Functorial compatibility path in the program. -/
  functorialityPath :
    ∀ X : Obj,
      Path (conjectures.etalePi1 (reconstruction X)) (conjectures.etalePi1 X)
  /-- Primitive left-unit normalization for functoriality witnesses. -/
  functorialityStep :
    ∀ X : Obj,
      Path.Step
        (Path.trans (Path.refl (conjectures.etalePi1 (reconstruction X))) (functorialityPath X))
        (functorialityPath X)

namespace GrothendieckProgramPaths

variable {Obj : Type u} (G : GrothendieckProgramPaths Obj)

@[simp] theorem reconstruction_rweq (X : Obj) :
    RwEq
      (Path.trans (G.reconstructionPath X) (Path.refl X))
      (G.reconstructionPath X) :=
  rweq_of_step (G.reconstructionStep X)

@[simp] theorem functoriality_rweq (X : Obj) :
    RwEq
      (Path.trans (Path.refl (G.conjectures.etalePi1 (G.reconstruction X))) (G.functorialityPath X))
      (G.functorialityPath X) :=
  rweq_of_step (G.functorialityStep X)

@[simp] theorem reconstruction_cancel_rweq (X : Obj) :
    RwEq
      (Path.trans (Path.symm (G.reconstructionPath X)) (G.reconstructionPath X))
      (Path.refl X) :=
  rweq_cmpA_inv_left (G.reconstructionPath X)

@[simp] theorem functoriality_cancel_rweq (X : Obj) :
    RwEq
      (Path.trans (G.functorialityPath X) (Path.symm (G.functorialityPath X)))
      (Path.refl (G.conjectures.etalePi1 (G.reconstruction X))) :=
  rweq_cmpA_inv_right (G.functorialityPath X)

@[simp] theorem sectionConjecture_in_program_rweq (X : Obj) :
    RwEq
      (Path.trans (G.conjectures.sectionConjecturePath X) (Path.refl X))
      (G.conjectures.sectionConjecturePath X) :=
  (G.conjectures).sectionConjecture_rweq X

end GrothendieckProgramPaths

/-- Build Grothendieck-program data from path-level witnesses. -/
def mkGrothendieckProgramPaths
    {Obj : Type u}
    (conjectures : AnabelianConjecturePaths Obj)
    (reconstruction : Obj → Obj)
    (reconstructionPath :
      ∀ X : Obj, Path (reconstruction (conjectures.etalePi1 X)) X)
    (functorialityPath :
      ∀ X : Obj,
        Path (conjectures.etalePi1 (reconstruction X)) (conjectures.etalePi1 X)) :
    GrothendieckProgramPaths Obj where
  conjectures := conjectures
  reconstruction := reconstruction
  reconstructionPath := reconstructionPath
  reconstructionStep := fun X => Path.Step.trans_refl_right (reconstructionPath X)
  functorialityPath := functorialityPath
  functorialityStep := fun X => Path.Step.trans_refl_left (functorialityPath X)

/-- Canonical identity-model instance of Grothendieck's program paths. -/
def trivialGrothendieckProgramPaths (Obj : Type u) : GrothendieckProgramPaths Obj where
  conjectures := trivialAnabelianConjecturePaths Obj
  reconstruction := fun X => X
  reconstructionPath := fun X => Path.refl X
  reconstructionStep := fun X => Path.Step.trans_refl_right (Path.refl X)
  functorialityPath := fun X => Path.refl X
  functorialityStep := fun X => Path.Step.trans_refl_left (Path.refl X)

end Anabelian
end ComputationalPaths
