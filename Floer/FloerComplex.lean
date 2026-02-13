import ComputationalPaths.Path.Rewrite.RwEq
import Floer.FloerHomologyPaths

/-!
# Floer theory paths: Floer complexes

This module packages a minimal chain-level Floer complex interface with explicit
computational paths. Differential-square, continuation compatibility, and action
filtration transport are represented with `Path`, normalized by `Path.Step`,
and compared by `RwEq`.
-/

namespace ComputationalPaths
namespace Floer
namespace FloerComplex

open Path
open FloerHomologyPaths

universe u

/-- Domain-specific rewrite tags for Floer-complex coherence moves. -/
inductive FloerComplexStep : Type
  | differentialSquare
  | continuationChain
  | actionFiltration
  | continuationOfSquare
  | cancellation

/-- Minimal computational-path data for Floer chain complexes. -/
structure FloerComplexPathData (Gen : Type u) where
  zero : Gen
  differential : Gen → Gen
  continuation : Gen → Gen
  actionLevel : Gen → Nat
  differentialSquarePath :
    ∀ x : Gen, Path (differential (differential x)) zero
  continuationChainPath :
    ∀ x : Gen, Path (continuation (differential x)) (differential (continuation x))
  actionFiltrationPath :
    ∀ x : Gen, Path (actionLevel (continuation x)) (actionLevel x)

namespace FloerComplexPathData

variable {Gen : Type u} (F : FloerComplexPathData Gen)

/-- Transport of differential-square along continuation. -/
def continuationOfSquarePath (x : Gen) :
    Path (F.continuation (F.differential (F.differential x))) (F.continuation F.zero) :=
  Path.congrArg F.continuation (F.differentialSquarePath x)

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

/-- Step witness: right-unit normalization for continuation-chain compatibility. -/
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

/-- Step witness: left-unit normalization for action filtration transport. -/
def actionFiltration_step (x : Gen) :
    Path.Step
      (Path.trans (Path.refl (F.actionLevel (F.continuation x))) (F.actionFiltrationPath x))
      (F.actionFiltrationPath x) :=
  Path.Step.trans_refl_left (F.actionFiltrationPath x)

@[simp] theorem actionFiltration_rweq (x : Gen) :
    RwEq
      (Path.trans (Path.refl (F.actionLevel (F.continuation x))) (F.actionFiltrationPath x))
      (F.actionFiltrationPath x) :=
  rweq_of_step (F.actionFiltration_step x)

/-- Step witness: right-unit normalization for continued differential-square paths. -/
def continuationOfSquare_step (x : Gen) :
    Path.Step
      (Path.trans (F.continuationOfSquarePath x) (Path.refl (F.continuation F.zero)))
      (F.continuationOfSquarePath x) :=
  Path.Step.trans_refl_right (F.continuationOfSquarePath x)

@[simp] theorem continuationOfSquare_rweq (x : Gen) :
    RwEq
      (Path.trans (F.continuationOfSquarePath x) (Path.refl (F.continuation F.zero)))
      (F.continuationOfSquarePath x) :=
  rweq_of_step (F.continuationOfSquare_step x)

@[simp] theorem continuationChain_cancel_rweq (x : Gen) :
    RwEq
      (Path.trans (Path.symm (F.continuationChainPath x)) (F.continuationChainPath x))
      (Path.refl (F.differential (F.continuation x))) :=
  rweq_cmpA_inv_left (F.continuationChainPath x)

/-- Bridge from chain-level data to the Floer-homology path package. -/
def toFloerHomologyPathData : FloerHomologyPathData Gen where
  zero := F.zero
  differential := F.differential
  continuation := F.continuation
  pss := F.continuation
  actionLevel := F.actionLevel
  differentialSquarePath := F.differentialSquarePath
  continuationChainPath := F.continuationChainPath
  pssChainPath := F.continuationChainPath
  continuationPSSPath := fun x => Path.refl (F.continuation x)
  filtrationPath := F.actionFiltrationPath

end FloerComplexPathData

/-- Trivial model instantiating the Floer-complex computational-path interface. -/
def trivialFloerComplexPathData : FloerComplexPathData PUnit where
  zero := PUnit.unit
  differential := fun _ => PUnit.unit
  continuation := fun _ => PUnit.unit
  actionLevel := fun _ => 0
  differentialSquarePath := fun _ => Path.refl PUnit.unit
  continuationChainPath := fun _ => Path.refl PUnit.unit
  actionFiltrationPath := fun _ => Path.refl 0

end FloerComplex
end Floer
end ComputationalPaths
