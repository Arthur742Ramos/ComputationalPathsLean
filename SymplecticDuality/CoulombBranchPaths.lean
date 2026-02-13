import ComputationalPaths.Path.Rewrite.RwEq
import SymplecticDuality.Mirror3DPaths

/-!
# Symplectic duality paths: Coulomb branches

This module packages a minimal Coulomb-branch interface with explicit
computational paths. Monopole involutions, wall-crossing compatibility, and
mirror-to-Coulomb comparisons are represented via `Path`, `Path.Step`, and `RwEq`.
-/

namespace ComputationalPaths
namespace SymplecticDuality
namespace CoulombBranchPaths

open Path
open Mirror3DPaths

universe u v

/-- Domain-specific rewrite tags for Coulomb-branch coherence moves. -/
inductive CoulombStep : Type
  | monopole
  | wallCrossing
  | quantumProduct
  | vacuum

/-- Minimal computational-path data for a Coulomb branch package. -/
structure CoulombBranchPathData (Branch : Type u) where
  monopole : Branch → Branch
  wallCrossing : Branch → Branch
  quantumProduct : Branch → Branch → Branch
  vacuum : Branch
  monopoleInvolutionPath :
    ∀ x : Branch, Path (monopole (monopole x)) x
  unitLeftPath :
    ∀ x : Branch, Path (quantumProduct vacuum x) x
  unitRightPath :
    ∀ x : Branch, Path (quantumProduct x vacuum) x
  wallMonopolePath :
    ∀ x : Branch, Path (wallCrossing (monopole x)) (monopole (wallCrossing x))
  monopoleInvolutionStep :
    ∀ x : Branch,
      Path.Step
        (Path.trans (monopoleInvolutionPath x) (Path.refl x))
        (monopoleInvolutionPath x)
  unitLeftStep :
    ∀ x : Branch,
      Path.Step
        (Path.trans (unitLeftPath x) (Path.refl x))
        (unitLeftPath x)
  unitRightStep :
    ∀ x : Branch,
      Path.Step
        (Path.trans (unitRightPath x) (Path.refl x))
        (unitRightPath x)
  wallMonopoleStep :
    ∀ x : Branch,
      Path.Step
        (Path.trans (wallMonopolePath x) (Path.refl (monopole (wallCrossing x))))
        (wallMonopolePath x)
  monopoleMap :
    {a b : Branch} → Path a b → Path (monopole a) (monopole b)
  monopoleMapStep :
    {a b : Branch} → (p : Path a b) →
      Path.Step
        (Path.trans (monopoleMap p) (Path.refl (monopole b)))
        (monopoleMap p)

namespace CoulombBranchPathData

variable {Branch : Type u}
variable (C : CoulombBranchPathData Branch)

/-- Composite path from wall-crossed monopoles to a vacuum-extended product. -/
def wallToVacuumPath (x : Branch) :
    Path (C.wallCrossing (C.monopole x))
      (C.quantumProduct (C.monopole (C.wallCrossing x)) C.vacuum) :=
  Path.trans
    (C.wallMonopolePath x)
    (Path.symm (C.unitRightPath (C.monopole (C.wallCrossing x))))

/-- Step witness: right-unit normalization for monopole involution. -/
def monopoleInvolution_step (x : Branch) :
    Path.Step
      (Path.trans (C.monopoleInvolutionPath x) (Path.refl x))
      (C.monopoleInvolutionPath x) :=
  C.monopoleInvolutionStep x

@[simp] theorem monopoleInvolution_rweq (x : Branch) :
    RwEq
      (Path.trans (C.monopoleInvolutionPath x) (Path.refl x))
      (C.monopoleInvolutionPath x) :=
  rweq_of_step (C.monopoleInvolution_step x)

/-- Step witness: right-unit normalization for left-unit comparison. -/
def unitLeft_step (x : Branch) :
    Path.Step
      (Path.trans (C.unitLeftPath x) (Path.refl x))
      (C.unitLeftPath x) :=
  C.unitLeftStep x

@[simp] theorem unitLeft_rweq (x : Branch) :
    RwEq
      (Path.trans (C.unitLeftPath x) (Path.refl x))
      (C.unitLeftPath x) :=
  rweq_of_step (C.unitLeft_step x)

/-- Step witness: right-unit normalization for right-unit comparison. -/
def unitRight_step (x : Branch) :
    Path.Step
      (Path.trans (C.unitRightPath x) (Path.refl x))
      (C.unitRightPath x) :=
  C.unitRightStep x

@[simp] theorem unitRight_rweq (x : Branch) :
    RwEq
      (Path.trans (C.unitRightPath x) (Path.refl x))
      (C.unitRightPath x) :=
  rweq_of_step (C.unitRight_step x)

/-- Step witness: right-unit normalization for wall-monopole compatibility. -/
def wallMonopole_step (x : Branch) :
    Path.Step
      (Path.trans (C.wallMonopolePath x) (Path.refl (C.monopole (C.wallCrossing x))))
      (C.wallMonopolePath x) :=
  C.wallMonopoleStep x

@[simp] theorem wallMonopole_rweq (x : Branch) :
    RwEq
      (Path.trans (C.wallMonopolePath x) (Path.refl (C.monopole (C.wallCrossing x))))
      (C.wallMonopolePath x) :=
  rweq_of_step (C.wallMonopole_step x)

/-- Step witness: right-unit normalization for mapped Coulomb paths. -/
def monopoleMap_step {a b : Branch} (p : Path a b) :
    Path.Step
      (Path.trans (C.monopoleMap p) (Path.refl (C.monopole b)))
      (C.monopoleMap p) :=
  C.monopoleMapStep p

@[simp] theorem monopoleMap_rweq {a b : Branch} (p : Path a b) :
    RwEq
      (Path.trans (C.monopoleMap p) (Path.refl (C.monopole b)))
      (C.monopoleMap p) :=
  rweq_of_step (C.monopoleMap_step p)

/-- Step witness: right-unit normalization for the wall-to-vacuum composite. -/
def wallToVacuum_step (x : Branch) :
    Path.Step
      (Path.trans
        (C.wallToVacuumPath x)
        (Path.refl (C.quantumProduct (C.monopole (C.wallCrossing x)) C.vacuum)))
      (C.wallToVacuumPath x) :=
  Path.Step.trans_refl_right (C.wallToVacuumPath x)

@[simp] theorem wallToVacuum_rweq (x : Branch) :
    RwEq
      (Path.trans
        (C.wallToVacuumPath x)
        (Path.refl (C.quantumProduct (C.monopole (C.wallCrossing x)) C.vacuum)))
      (C.wallToVacuumPath x) :=
  rweq_of_step (C.wallToVacuum_step x)

@[simp] theorem wallToVacuum_cancel_rweq (x : Branch) :
    RwEq
      (Path.trans (Path.symm (C.wallToVacuumPath x)) (C.wallToVacuumPath x))
      (Path.refl (C.quantumProduct (C.monopole (C.wallCrossing x)) C.vacuum)) :=
  rweq_cmpA_inv_left (C.wallToVacuumPath x)

end CoulombBranchPathData

/--
Bridge data linking 3d mirror-symmetry parameters to Coulomb-branch monopole
normalization.
-/
structure MirrorCoulombBridge {Higgs : Type u} {Coulomb : Type v}
    (M : Mirror3DPathData Higgs Coulomb) (C : CoulombBranchPathData Coulomb) where
  fiMonopolePath :
    ∀ h : Higgs,
      Path (C.monopole (M.fiShift (M.mirrorToCoulomb h)))
        (M.fiShift (M.mirrorToCoulomb h))

namespace MirrorCoulombBridge

variable {Higgs : Type u} {Coulomb : Type v}
variable {M : Mirror3DPathData Higgs Coulomb}
variable {C : CoulombBranchPathData Coulomb}
variable (B : MirrorCoulombBridge M C)

/-- Monopole transport of mirror mass/FI compatibility. -/
def mirrorMonopoleComparison (h : Higgs) :
    Path (C.monopole (M.mirrorToCoulomb (M.massShift h)))
      (M.fiShift (M.mirrorToCoulomb h)) :=
  Path.trans (C.monopoleMap (M.massFIPath h)) (B.fiMonopolePath h)

/-- Step witness: right-unit normalization for mirror-monopole comparison. -/
def mirrorMonopole_step (h : Higgs) :
    Path.Step
      (Path.trans
        (B.mirrorMonopoleComparison h)
        (Path.refl (M.fiShift (M.mirrorToCoulomb h))))
      (B.mirrorMonopoleComparison h) :=
  Path.Step.trans_refl_right (B.mirrorMonopoleComparison h)

@[simp] theorem mirrorMonopole_rweq (h : Higgs) :
    RwEq
      (Path.trans
        (B.mirrorMonopoleComparison h)
        (Path.refl (M.fiShift (M.mirrorToCoulomb h))))
      (B.mirrorMonopoleComparison h) :=
  rweq_of_step (B.mirrorMonopole_step h)

@[simp] theorem mirrorMonopole_cancel_rweq (h : Higgs) :
    RwEq
      (Path.trans (Path.symm (B.mirrorMonopoleComparison h)) (B.mirrorMonopoleComparison h))
      (Path.refl (M.fiShift (M.mirrorToCoulomb h))) :=
  rweq_cmpA_inv_left (B.mirrorMonopoleComparison h)

end MirrorCoulombBridge

/-- Trivial model instantiating Coulomb-branch computational-path data. -/
def trivialCoulombBranchPathData : CoulombBranchPathData PUnit where
  monopole := fun _ => PUnit.unit
  wallCrossing := fun _ => PUnit.unit
  quantumProduct := fun _ _ => PUnit.unit
  vacuum := PUnit.unit
  monopoleInvolutionPath := fun _ => Path.refl PUnit.unit
  unitLeftPath := fun _ => Path.refl PUnit.unit
  unitRightPath := fun _ => Path.refl PUnit.unit
  wallMonopolePath := fun _ => Path.refl PUnit.unit
  monopoleInvolutionStep := fun _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  unitLeftStep := fun _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  unitRightStep := fun _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  wallMonopoleStep := fun _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  monopoleMap := fun p => p
  monopoleMapStep := fun p => Path.Step.trans_refl_right p

/-- Trivial bridge instance between mirror and Coulomb path packages. -/
def trivialMirrorCoulombBridge :
    MirrorCoulombBridge Mirror3DPaths.trivialMirror3DPathData
      trivialCoulombBranchPathData where
  fiMonopolePath := fun _ => Path.refl PUnit.unit

end CoulombBranchPaths
end SymplecticDuality
end ComputationalPaths
