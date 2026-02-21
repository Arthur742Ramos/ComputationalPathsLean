import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Floer.FloerHomologyPaths

/-!
# Floer theory paths: Fukaya categories

This module packages a minimal A∞-flavored Fukaya interface with explicit
computational paths. Higher composition, unit laws, differential compatibility,
and a bridge to Floer homology are encoded with `Path`, normalized by
`Path.Step`, and compared by `RwEq`.
-/

namespace ComputationalPaths
namespace Floer
namespace FukayaCategoryPaths

open Path
open FloerHomologyPaths

universe u

/-- Domain-specific rewrite tags for Fukaya-category coherence moves. -/
inductive FukayaStep : Type
  | assoc
  | unitLeft
  | unitRight
  | differentialSquare
  | leibniz
  | bridge

/-- Minimal computational-path data for a Fukaya-style A∞ category. -/
structure FukayaCategoryPathData (Obj Mor : Type u) where
  source : Mor → Obj
  target : Mor → Obj
  idMor : Obj → Mor
  mu1 : Mor → Mor
  mu2 : Mor → Mor → Mor
  zeroMor : Mor
  assocPath :
    ∀ f g h : Mor, Path (mu2 (mu2 f g) h) (mu2 f (mu2 g h))
  unitLeftPath :
    ∀ f : Mor, Path (mu2 (idMor (source f)) f) f
  unitRightPath :
    ∀ f : Mor, Path (mu2 f (idMor (target f))) f
  differentialSquarePath :
    ∀ f : Mor, Path (mu1 (mu1 f)) zeroMor
  leibnizPath :
    ∀ f g : Mor, Path (mu1 (mu2 f g)) (mu2 (mu1 f) g)

namespace FukayaCategoryPathData

variable {Obj Mor : Type u} (F : FukayaCategoryPathData Obj Mor)

/-- Compare left and right unit forms by an explicit composite path. -/
def leftToRightUnitPath (f : Mor) :
    Path (F.mu2 (F.idMor (F.source f)) f) (F.mu2 f (F.idMor (F.target f))) :=
  Path.trans (F.unitLeftPath f) (Path.symm (F.unitRightPath f))

/-- Step witness: right-unit normalization for associativity coherence. -/
def assoc_step (f g h : Mor) :
    Path.Step
      (Path.trans (F.assocPath f g h) (Path.refl (F.mu2 f (F.mu2 g h))))
      (F.assocPath f g h) :=
  Path.Step.trans_refl_right (F.assocPath f g h)

@[simp] theorem assoc_rweq (f g h : Mor) :
    RwEq
      (Path.trans (F.assocPath f g h) (Path.refl (F.mu2 f (F.mu2 g h))))
      (F.assocPath f g h) :=
  rweq_of_step (F.assoc_step f g h)

/-- Step witness: right-unit normalization for left-unit coherence. -/
def unitLeft_step (f : Mor) :
    Path.Step
      (Path.trans (F.unitLeftPath f) (Path.refl f))
      (F.unitLeftPath f) :=
  Path.Step.trans_refl_right (F.unitLeftPath f)

@[simp] theorem unitLeft_rweq (f : Mor) :
    RwEq
      (Path.trans (F.unitLeftPath f) (Path.refl f))
      (F.unitLeftPath f) :=
  rweq_of_step (F.unitLeft_step f)

/-- Step witness: right-unit normalization for right-unit coherence. -/
def unitRight_step (f : Mor) :
    Path.Step
      (Path.trans (F.unitRightPath f) (Path.refl f))
      (F.unitRightPath f) :=
  Path.Step.trans_refl_right (F.unitRightPath f)

@[simp] theorem unitRight_rweq (f : Mor) :
    RwEq
      (Path.trans (F.unitRightPath f) (Path.refl f))
      (F.unitRightPath f) :=
  rweq_of_step (F.unitRight_step f)

/-- Step witness: right-unit normalization for differential-square coherence. -/
def differentialSquare_step (f : Mor) :
    Path.Step
      (Path.trans (F.differentialSquarePath f) (Path.refl F.zeroMor))
      (F.differentialSquarePath f) :=
  Path.Step.trans_refl_right (F.differentialSquarePath f)

@[simp] theorem differentialSquare_rweq (f : Mor) :
    RwEq
      (Path.trans (F.differentialSquarePath f) (Path.refl F.zeroMor))
      (F.differentialSquarePath f) :=
  rweq_of_step (F.differentialSquare_step f)

/-- Step witness: right-unit normalization for Leibniz coherence. -/
def leibniz_step (f g : Mor) :
    Path.Step
      (Path.trans (F.leibnizPath f g) (Path.refl (F.mu2 (F.mu1 f) g)))
      (F.leibnizPath f g) :=
  Path.Step.trans_refl_right (F.leibnizPath f g)

@[simp] theorem leibniz_rweq (f g : Mor) :
    RwEq
      (Path.trans (F.leibnizPath f g) (Path.refl (F.mu2 (F.mu1 f) g)))
      (F.leibnizPath f g) :=
  rweq_of_step (F.leibniz_step f g)

/-- Step witness: right-unit normalization for unit-comparison path. -/
def leftToRightUnit_step (f : Mor) :
    Path.Step
      (Path.trans (F.leftToRightUnitPath f) (Path.refl (F.mu2 f (F.idMor (F.target f)))))
      (F.leftToRightUnitPath f) :=
  Path.Step.trans_refl_right (F.leftToRightUnitPath f)

@[simp] theorem leftToRightUnit_rweq (f : Mor) :
    RwEq
      (Path.trans (F.leftToRightUnitPath f) (Path.refl (F.mu2 f (F.idMor (F.target f)))))
      (F.leftToRightUnitPath f) :=
  rweq_of_step (F.leftToRightUnit_step f)

@[simp] theorem assoc_cancel_rweq (f g h : Mor) :
    RwEq
      (Path.trans (Path.symm (F.assocPath f g h)) (F.assocPath f g h))
      (Path.refl (F.mu2 f (F.mu2 g h))) :=
  rweq_cmpA_inv_left (F.assocPath f g h)

@[simp] theorem leftToRightUnit_cancel_rweq (f : Mor) :
    RwEq
      (Path.trans (Path.symm (F.leftToRightUnitPath f)) (F.leftToRightUnitPath f))
      (Path.refl (F.mu2 f (F.idMor (F.target f)))) :=
  rweq_cmpA_inv_left (F.leftToRightUnitPath f)

end FukayaCategoryPathData

/--
Bridge data linking Fukaya-category morphisms to Floer-homology generators with
explicit computational paths.
-/
structure FukayaToFloerBridge {Obj Mor Gen : Type u}
    (F : FukayaCategoryPathData Obj Mor)
    (H : FloerHomologyPathData Gen) where
  morphismToGenerator : Mor → Gen
  mu1ToDifferentialPath :
    ∀ f : Mor,
      Path (morphismToGenerator (F.mu1 f)) (H.differential (morphismToGenerator f))
  idToCyclePath :
    ∀ X : Obj,
      Path (H.differential (morphismToGenerator (F.idMor X))) H.zero

namespace FukayaToFloerBridge

variable {Obj Mor Gen : Type u}
variable {F : FukayaCategoryPathData Obj Mor}
variable {H : FloerHomologyPathData Gen}
variable (B : FukayaToFloerBridge F H)

/-- Step witness: right-unit normalization for μ₁/differential compatibility. -/
def mu1ToDifferential_step (f : Mor) :
    Path.Step
      (Path.trans
        (B.mu1ToDifferentialPath f)
        (Path.refl (H.differential (B.morphismToGenerator f))))
      (B.mu1ToDifferentialPath f) :=
  Path.Step.trans_refl_right (B.mu1ToDifferentialPath f)

@[simp] theorem mu1ToDifferential_rweq (f : Mor) :
    RwEq
      (Path.trans
        (B.mu1ToDifferentialPath f)
        (Path.refl (H.differential (B.morphismToGenerator f))))
      (B.mu1ToDifferentialPath f) :=
  rweq_of_step (B.mu1ToDifferential_step f)

/-- Step witness: right-unit normalization for identity-to-cycle transport. -/
def idToCycle_step (X : Obj) :
    Path.Step
      (Path.trans (B.idToCyclePath X) (Path.refl H.zero))
      (B.idToCyclePath X) :=
  Path.Step.trans_refl_right (B.idToCyclePath X)

@[simp] theorem idToCycle_rweq (X : Obj) :
    RwEq
      (Path.trans (B.idToCyclePath X) (Path.refl H.zero))
      (B.idToCyclePath X) :=
  rweq_of_step (B.idToCycle_step X)

@[simp] theorem idToCycle_cancel_rweq (X : Obj) :
    RwEq
      (Path.trans (Path.symm (B.idToCyclePath X)) (B.idToCyclePath X))
      (Path.refl H.zero) :=
  rweq_cmpA_inv_left (B.idToCyclePath X)

end FukayaToFloerBridge

/-- Trivial model instantiating the Fukaya-category computational-path interface. -/
def trivialFukayaCategoryPathData : FukayaCategoryPathData PUnit PUnit where
  source := fun _ => PUnit.unit
  target := fun _ => PUnit.unit
  idMor := fun _ => PUnit.unit
  mu1 := fun _ => PUnit.unit
  mu2 := fun _ _ => PUnit.unit
  zeroMor := PUnit.unit
  assocPath := fun _ _ _ => Path.refl PUnit.unit
  unitLeftPath := fun _ => Path.refl PUnit.unit
  unitRightPath := fun _ => Path.refl PUnit.unit
  differentialSquarePath := fun _ => Path.refl PUnit.unit
  leibnizPath := fun _ _ => Path.refl PUnit.unit

/-- Trivial bridge instance between Fukaya and Floer path packages. -/
def trivialFukayaToFloerBridge :
    FukayaToFloerBridge trivialFukayaCategoryPathData
      FloerHomologyPaths.trivialFloerHomologyPathData where
  morphismToGenerator := fun _ => PUnit.unit
  mu1ToDifferentialPath := fun _ => Path.refl PUnit.unit
  idToCyclePath := fun _ => Path.refl PUnit.unit

end FukayaCategoryPaths
end Floer
end ComputationalPaths
