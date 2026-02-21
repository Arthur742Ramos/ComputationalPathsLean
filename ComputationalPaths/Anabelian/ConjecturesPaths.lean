import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Anabelian conjecture paths

This module packages anabelian-conjectural coherence data with explicit
computational-step witnesses (`Path.Step`) and derived rewrite equivalences
(`RwEq`).
-/

namespace ComputationalPaths
namespace Anabelian

open Path

universe u

/-! ## Conjectures -/

/-- Anabelian conjecture package with explicit `Path.Step` witnesses. -/
structure AnabelianConjecturePaths (Obj : Type u) where
  /-- Étale fundamental-group assignment. -/
  etalePi1 : Obj → Obj
  /-- Candidate section-lifting/reconstruction map. -/
  sectionLift : Obj → Obj
  /-- Section-conjecture style witness. -/
  sectionConjecturePath : ∀ X : Obj, Path (sectionLift X) X
  /-- Primitive right-unit normalization witness for the section conjecture. -/
  sectionConjectureStep :
    ∀ X : Obj,
      Path.Step
        (Path.trans (sectionConjecturePath X) (Path.refl X))
        (sectionConjecturePath X)
  /-- Hom-conjecture style compatibility witness on étale groups. -/
  homConjecturePath :
    ∀ X : Obj, Path (etalePi1 (sectionLift X)) (etalePi1 X)
  /-- Primitive left-unit normalization witness for the Hom conjecture. -/
  homConjectureStep :
    ∀ X : Obj,
      Path.Step
        (Path.trans (Path.refl (etalePi1 (sectionLift X))) (homConjecturePath X))
        (homConjecturePath X)

namespace AnabelianConjecturePaths

variable {Obj : Type u} (A : AnabelianConjecturePaths Obj)

noncomputable def sectionConjecture_rweq (X : Obj) :
    RwEq
      (Path.trans (A.sectionConjecturePath X) (Path.refl X))
      (A.sectionConjecturePath X) :=
  rweq_of_step (A.sectionConjectureStep X)

noncomputable def homConjecture_rweq (X : Obj) :
    RwEq
      (Path.trans (Path.refl (A.etalePi1 (A.sectionLift X))) (A.homConjecturePath X))
      (A.homConjecturePath X) :=
  rweq_of_step (A.homConjectureStep X)

noncomputable def sectionConjecture_cancel_rweq (X : Obj) :
    RwEq
      (Path.trans (Path.symm (A.sectionConjecturePath X)) (A.sectionConjecturePath X))
      (Path.refl X) :=
  rweq_cmpA_inv_left (A.sectionConjecturePath X)

noncomputable def homConjecture_cancel_rweq (X : Obj) :
    RwEq
      (Path.trans (A.homConjecturePath X) (Path.symm (A.homConjecturePath X)))
      (Path.refl (A.etalePi1 (A.sectionLift X))) :=
  rweq_cmpA_inv_right (A.homConjecturePath X)

end AnabelianConjecturePaths

/-- Build anabelian conjecture data from primary path-level witnesses. -/
def mkAnabelianConjecturePaths
    {Obj : Type u}
    (etalePi1 : Obj → Obj)
    (sectionLift : Obj → Obj)
    (sectionConjecturePath : ∀ X : Obj, Path (sectionLift X) X)
    (homConjecturePath : ∀ X : Obj, Path (etalePi1 (sectionLift X)) (etalePi1 X)) :
    AnabelianConjecturePaths Obj where
  etalePi1 := etalePi1
  sectionLift := sectionLift
  sectionConjecturePath := sectionConjecturePath
  sectionConjectureStep := fun X => Path.Step.trans_refl_right (sectionConjecturePath X)
  homConjecturePath := homConjecturePath
  homConjectureStep := fun X => Path.Step.trans_refl_left (homConjecturePath X)

/-- Canonical identity-model package for conjectural anabelian paths. -/
def trivialAnabelianConjecturePaths (Obj : Type u) : AnabelianConjecturePaths Obj where
  etalePi1 := fun X => X
  sectionLift := fun X => X
  sectionConjecturePath := fun X => Path.refl X
  sectionConjectureStep := fun X => Path.Step.trans_refl_right (Path.refl X)
  homConjecturePath := fun X => Path.refl X
  homConjectureStep := fun X => Path.Step.trans_refl_left (Path.refl X)

end Anabelian
end ComputationalPaths
