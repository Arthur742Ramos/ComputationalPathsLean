import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Mirror symmetry paths: Fukaya categories

This module packages a minimal A∞-flavored Fukaya interface with explicit
computational paths. Associativity, unit laws, and differential coherence are
encoded with `Path`, normalized via `Path.Step`, and compared by `RwEq`.
-/

namespace ComputationalPaths
namespace Mirror
namespace FukayaCategoryPaths

open Path

universe u

/-- Domain-specific rewrite tags for Fukaya-category coherence moves. -/
inductive FukayaStep : Type
  | assoc
  | unitLeft
  | unitRight
  | differentialSquare
  | leibniz

/-- Minimal computational-path data for a Fukaya-style A∞ category. -/
structure FukayaCategoryPathData (Obj Mor : Type u) where
  source : Mor → Obj
  target : Mor → Obj
  idMor : Obj → Mor
  compose : Mor → Mor → Mor
  mu1 : Mor → Mor
  assocPath :
    ∀ f g h : Mor,
      Path (compose (compose f g) h) (compose f (compose g h))
  unitLeftPath :
    ∀ f : Mor, Path (compose (idMor (source f)) f) f
  unitRightPath :
    ∀ f : Mor, Path (compose f (idMor (target f))) f
  differentialSquarePath :
    ∀ f : Mor, Path (mu1 (mu1 f)) (mu1 (mu1 f))
  leibnizPath :
    ∀ f g : Mor, Path (mu1 (compose f g)) (compose (mu1 f) g)

namespace FukayaCategoryPathData

variable {Obj Mor : Type u} (F : FukayaCategoryPathData Obj Mor)

/-- Compare the left and right unit forms by an explicit composite path. -/
noncomputable def leftToRightUnitPath (f : Mor) :
    Path (F.compose (F.idMor (F.source f)) f) (F.compose f (F.idMor (F.target f))) :=
  Path.trans (F.unitLeftPath f) (Path.symm (F.unitRightPath f))

/-- Step witness: right-unit normalization for associativity coherence. -/
noncomputable def assoc_step (f g h : Mor) :
    Path.Step
      (Path.trans (F.assocPath f g h) (Path.refl (F.compose f (F.compose g h))))
      (F.assocPath f g h) :=
  Path.Step.trans_refl_right (F.assocPath f g h)

noncomputable def assoc_rweq (f g h : Mor) :
    RwEq
      (Path.trans (F.assocPath f g h) (Path.refl (F.compose f (F.compose g h))))
      (F.assocPath f g h) :=
  rweq_of_step (F.assoc_step f g h)

/-- Step witness: right-unit normalization for left unit coherence. -/
noncomputable def unitLeft_step (f : Mor) :
    Path.Step
      (Path.trans (F.unitLeftPath f) (Path.refl f))
      (F.unitLeftPath f) :=
  Path.Step.trans_refl_right (F.unitLeftPath f)

noncomputable def unitLeft_rweq (f : Mor) :
    RwEq
      (Path.trans (F.unitLeftPath f) (Path.refl f))
      (F.unitLeftPath f) :=
  rweq_of_step (F.unitLeft_step f)

/-- Step witness: right-unit normalization for right unit coherence. -/
noncomputable def unitRight_step (f : Mor) :
    Path.Step
      (Path.trans (F.unitRightPath f) (Path.refl f))
      (F.unitRightPath f) :=
  Path.Step.trans_refl_right (F.unitRightPath f)

noncomputable def unitRight_rweq (f : Mor) :
    RwEq
      (Path.trans (F.unitRightPath f) (Path.refl f))
      (F.unitRightPath f) :=
  rweq_of_step (F.unitRight_step f)

/-- Step witness: left-unit normalization for the differential square path. -/
noncomputable def differentialSquare_step (f : Mor) :
    Path.Step
      (Path.trans (Path.refl (F.mu1 (F.mu1 f))) (F.differentialSquarePath f))
      (F.differentialSquarePath f) :=
  Path.Step.trans_refl_left (F.differentialSquarePath f)

noncomputable def differentialSquare_rweq (f : Mor) :
    RwEq
      (Path.trans (Path.refl (F.mu1 (F.mu1 f))) (F.differentialSquarePath f))
      (F.differentialSquarePath f) :=
  rweq_of_step (F.differentialSquare_step f)

/-- Step witness: right-unit normalization for Leibniz coherence. -/
noncomputable def leibniz_step (f g : Mor) :
    Path.Step
      (Path.trans (F.leibnizPath f g) (Path.refl (F.compose (F.mu1 f) g)))
      (F.leibnizPath f g) :=
  Path.Step.trans_refl_right (F.leibnizPath f g)

noncomputable def leibniz_rweq (f g : Mor) :
    RwEq
      (Path.trans (F.leibnizPath f g) (Path.refl (F.compose (F.mu1 f) g)))
      (F.leibnizPath f g) :=
  rweq_of_step (F.leibniz_step f g)

noncomputable def assoc_cancel_rweq (f g h : Mor) :
    RwEq
      (Path.trans (Path.symm (F.assocPath f g h)) (F.assocPath f g h))
      (Path.refl (F.compose f (F.compose g h))) :=
  rweq_cmpA_inv_left (F.assocPath f g h)

noncomputable def leftToRightUnit_cancel_rweq (f : Mor) :
    RwEq
      (Path.trans (Path.symm (F.leftToRightUnitPath f)) (F.leftToRightUnitPath f))
      (Path.refl (F.compose f (F.idMor (F.target f)))) :=
  rweq_cmpA_inv_left (F.leftToRightUnitPath f)

end FukayaCategoryPathData

/-- Trivial model instantiating the Fukaya computational-path interface. -/
noncomputable def trivialFukayaCategoryPathData : FukayaCategoryPathData PUnit PUnit where
  source := fun _ => PUnit.unit
  target := fun _ => PUnit.unit
  idMor := fun _ => PUnit.unit
  compose := fun _ _ => PUnit.unit
  mu1 := fun _ => PUnit.unit
  assocPath := fun _ _ _ => Path.refl PUnit.unit
  unitLeftPath := fun _ => Path.refl PUnit.unit
  unitRightPath := fun _ => Path.refl PUnit.unit
  differentialSquarePath := fun _ => Path.refl PUnit.unit
  leibnizPath := fun _ _ => Path.refl PUnit.unit

end FukayaCategoryPaths
end Mirror
end ComputationalPaths
