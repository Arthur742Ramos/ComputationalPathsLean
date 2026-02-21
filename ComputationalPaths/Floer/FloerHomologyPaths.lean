import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Floer theory paths: Floer homology

This module packages a minimal Floer-homology interface with explicit
computational paths. Differential-square, continuation-map compatibility,
PSS transport, and filtration preservation are represented using `Path`,
normalized via `Path.Step`, and compared by `RwEq`.
-/

namespace ComputationalPaths
namespace Floer
namespace FloerHomologyPaths

open Path

universe u

/-- Domain-specific rewrite tags for Floer-homology coherence moves. -/
inductive FloerHomologyStep : Type
  | differentialSquare
  | continuation
  | pss
  | filtration
  | cancellation

/-- Minimal computational-path data for Floer homology packages. -/
structure FloerHomologyPathData (Gen : Type u) where
  zero : Gen
  differential : Gen → Gen
  continuation : Gen → Gen
  pss : Gen → Gen
  actionLevel : Gen → Nat
  differentialSquarePath :
    ∀ x : Gen, Path (differential (differential x)) zero
  continuationChainPath :
    ∀ x : Gen, Path (continuation (differential x)) (differential (continuation x))
  pssChainPath :
    ∀ x : Gen, Path (pss (differential x)) (differential (pss x))
  continuationPSSPath :
    ∀ x : Gen, Path (continuation x) (pss x)
  filtrationPath :
    ∀ x : Gen, Path (actionLevel (continuation x)) (actionLevel x)

namespace FloerHomologyPathData

variable {Gen : Type u} (F : FloerHomologyPathData Gen)

/-- Composite path comparing continuation transport against PSS transport. -/
def continuationToPSSPath (x : Gen) :
    Path (F.continuation (F.differential x)) (F.differential (F.pss x)) :=
  Path.trans
    (F.continuationChainPath x)
    (Path.congrArg F.differential (F.continuationPSSPath x))

/-- Step witness: right-unit normalization for differential-square coherence. -/
def differentialSquare_step (x : Gen) :
    Path.Step
      (Path.trans (F.differentialSquarePath x) (Path.refl F.zero))
      (F.differentialSquarePath x) :=
  Path.Step.trans_refl_right (F.differentialSquarePath x)

@[simp] theorem differentialSquare_rweq (x : Gen) :
    RwEq
      (Path.trans (F.differentialSquarePath x) (Path.refl F.zero))
      (F.differentialSquarePath x) :=
  rweq_of_step (F.differentialSquare_step x)

/-- Step witness: right-unit normalization for continuation chain compatibility. -/
def continuationChain_step (x : Gen) :
    Path.Step
      (Path.trans (F.continuationChainPath x) (Path.refl (F.differential (F.continuation x))))
      (F.continuationChainPath x) :=
  Path.Step.trans_refl_right (F.continuationChainPath x)

@[simp] theorem continuationChain_rweq (x : Gen) :
    RwEq
      (Path.trans (F.continuationChainPath x) (Path.refl (F.differential (F.continuation x))))
      (F.continuationChainPath x) :=
  rweq_of_step (F.continuationChain_step x)

/-- Step witness: right-unit normalization for PSS chain compatibility. -/
def pssChain_step (x : Gen) :
    Path.Step
      (Path.trans (F.pssChainPath x) (Path.refl (F.differential (F.pss x))))
      (F.pssChainPath x) :=
  Path.Step.trans_refl_right (F.pssChainPath x)

@[simp] theorem pssChain_rweq (x : Gen) :
    RwEq
      (Path.trans (F.pssChainPath x) (Path.refl (F.differential (F.pss x))))
      (F.pssChainPath x) :=
  rweq_of_step (F.pssChain_step x)

/-- Step witness: right-unit normalization for continuation-to-PSS transport. -/
def continuationToPSS_step (x : Gen) :
    Path.Step
      (Path.trans (F.continuationToPSSPath x) (Path.refl (F.differential (F.pss x))))
      (F.continuationToPSSPath x) :=
  Path.Step.trans_refl_right (F.continuationToPSSPath x)

@[simp] theorem continuationToPSS_rweq (x : Gen) :
    RwEq
      (Path.trans (F.continuationToPSSPath x) (Path.refl (F.differential (F.pss x))))
      (F.continuationToPSSPath x) :=
  rweq_of_step (F.continuationToPSS_step x)

/-- Step witness: right-unit normalization for continuation/PSS comparison. -/
def continuationPSS_step (x : Gen) :
    Path.Step
      (Path.trans (F.continuationPSSPath x) (Path.refl (F.pss x)))
      (F.continuationPSSPath x) :=
  Path.Step.trans_refl_right (F.continuationPSSPath x)

@[simp] theorem continuationPSS_rweq (x : Gen) :
    RwEq
      (Path.trans (F.continuationPSSPath x) (Path.refl (F.pss x)))
      (F.continuationPSSPath x) :=
  rweq_of_step (F.continuationPSS_step x)

/-- Step witness: left-unit normalization for filtration compatibility. -/
def filtration_step (x : Gen) :
    Path.Step
      (Path.trans (Path.refl (F.actionLevel (F.continuation x))) (F.filtrationPath x))
      (F.filtrationPath x) :=
  Path.Step.trans_refl_left (F.filtrationPath x)

@[simp] theorem filtration_rweq (x : Gen) :
    RwEq
      (Path.trans (Path.refl (F.actionLevel (F.continuation x))) (F.filtrationPath x))
      (F.filtrationPath x) :=
  rweq_of_step (F.filtration_step x)

@[simp] theorem continuationPSS_cancel_rweq (x : Gen) :
    RwEq
      (Path.trans (Path.symm (F.continuationPSSPath x)) (F.continuationPSSPath x))
      (Path.refl (F.pss x)) :=
  rweq_cmpA_inv_left (F.continuationPSSPath x)

@[simp] theorem continuationToPSS_cancel_rweq (x : Gen) :
    RwEq
      (Path.trans (Path.symm (F.continuationToPSSPath x)) (F.continuationToPSSPath x))
      (Path.refl (F.differential (F.pss x))) :=
  rweq_cmpA_inv_left (F.continuationToPSSPath x)

end FloerHomologyPathData

/-- Trivial model instantiating the Floer-homology computational-path interface. -/
def trivialFloerHomologyPathData : FloerHomologyPathData PUnit where
  zero := PUnit.unit
  differential := fun _ => PUnit.unit
  continuation := fun _ => PUnit.unit
  pss := fun _ => PUnit.unit
  actionLevel := fun _ => 0
  differentialSquarePath := fun _ => Path.refl PUnit.unit
  continuationChainPath := fun _ => Path.refl PUnit.unit
  pssChainPath := fun _ => Path.refl PUnit.unit
  continuationPSSPath := fun _ => Path.refl PUnit.unit
  filtrationPath := fun _ => Path.refl 0

end FloerHomologyPaths
end Floer
end ComputationalPaths
