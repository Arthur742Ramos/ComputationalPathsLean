import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Prismatic cohomology paths: prisms

This module packages prism-style data with explicit computational paths.
Normalization and cancellation are tracked by domain-specific `PrismStep`
constructors and lifted to `RwEq`.
-/

namespace ComputationalPaths
namespace Prismatic

open Path

universe u

/-- Domain-specific rewrite steps for prism computations. -/
inductive PrismStep {A : Type u} :
    {a b : A} → Path a b → Path a b → Prop where
  | delta_right_unit {a b : A} (p : Path a b) :
      PrismStep (Path.trans p (Path.refl b)) p
  | frobenius_left_unit {a b : A} (p : Path a b) :
      PrismStep (Path.trans (Path.refl a) p) p
  | nygaard_cancel {a b : A} (p : Path a b) :
      PrismStep (Path.trans (Path.symm p) p) (Path.refl b)

/-- Interpret a prism step as a primitive `Path.Step`. -/
noncomputable def PrismStep.toStep {A : Type u} {a b : A} {p q : Path a b}
    (s : PrismStep p q) : Path.Step p q :=
  match s with
  | .delta_right_unit p => Path.Step.trans_refl_right p
  | .frobenius_left_unit p => Path.Step.trans_refl_left p
  | .nygaard_cancel p => Path.Step.symm_trans p

/-- Lift a prism step to rewrite equivalence. -/
noncomputable def rweq_of_prism_step {A : Type u} {a b : A}
    {p q : Path a b} (s : PrismStep p q) : RwEq p q :=
  rweq_of_step (PrismStep.toStep s)

/-- Prism data with explicit path witnesses for Frobenius, delta, and generator
compatibility. -/
structure PrismPathData (A : Type u) where
  frobenius : A → A
  delta : A → A
  idealGenerator : A
  phiDeltaPath : ∀ a : A, Path (frobenius a) (delta a)
  nygaardPath : ∀ a : A, Path (frobenius (delta a)) (delta (frobenius a))
  prismConditionPath : Path (frobenius idealGenerator) idealGenerator
  phiDeltaStep :
    ∀ a : A,
      PrismStep
        (Path.trans (phiDeltaPath a) (Path.refl (delta a)))
        (phiDeltaPath a)
  nygaardStep :
    ∀ a : A,
      PrismStep
        (Path.trans (Path.refl (frobenius (delta a))) (nygaardPath a))
        (nygaardPath a)
  prismConditionStep :
    PrismStep
      (Path.trans prismConditionPath (Path.refl idealGenerator))
      prismConditionPath

namespace PrismPathData

variable {A : Type u} (P : PrismPathData A)

noncomputable def phi_delta_rweq (a : A) :
    RwEq
      (Path.trans (P.phiDeltaPath a) (Path.refl (P.delta a)))
      (P.phiDeltaPath a) :=
  rweq_of_prism_step (P.phiDeltaStep a)

noncomputable def nygaard_rweq (a : A) :
    RwEq
      (Path.trans (Path.refl (P.frobenius (P.delta a))) (P.nygaardPath a))
      (P.nygaardPath a) :=
  rweq_of_prism_step (P.nygaardStep a)

noncomputable def prism_condition_rweq :
    RwEq
      (Path.trans P.prismConditionPath (Path.refl P.idealGenerator))
      P.prismConditionPath :=
  rweq_of_prism_step P.prismConditionStep

noncomputable def prism_condition_cancel_rweq :
    RwEq
      (Path.trans (Path.symm P.prismConditionPath) P.prismConditionPath)
      (Path.refl P.idealGenerator) :=
  rweq_of_prism_step (PrismStep.nygaard_cancel P.prismConditionPath)

/-- Transport of Frobenius along a base path. -/
noncomputable def frobeniusTransport {x y : A} (p : Path x y) :
    Path (P.frobenius x) (P.frobenius y) :=
  Path.congrArg P.frobenius p

/-- Round-trip path induced by the prism generator condition. -/
noncomputable def generatorRoundTrip : Path P.idealGenerator P.idealGenerator :=
  Path.trans (Path.symm P.prismConditionPath) P.prismConditionPath

noncomputable def generator_roundtrip_rweq :
    RwEq P.generatorRoundTrip (Path.refl P.idealGenerator) :=
  P.prism_condition_cancel_rweq

end PrismPathData

/-- Trivial prism package on `PUnit`. -/
noncomputable def trivialPrismPathData : PrismPathData PUnit where
  frobenius := fun _ => PUnit.unit
  delta := fun _ => PUnit.unit
  idealGenerator := PUnit.unit
  phiDeltaPath := fun _ => Path.refl PUnit.unit
  nygaardPath := fun _ => Path.refl PUnit.unit
  prismConditionPath := Path.refl PUnit.unit
  phiDeltaStep := fun _ => PrismStep.delta_right_unit (Path.refl PUnit.unit)
  nygaardStep := fun _ => PrismStep.frobenius_left_unit (Path.refl PUnit.unit)
  prismConditionStep := PrismStep.delta_right_unit (Path.refl PUnit.unit)

end Prismatic
end ComputationalPaths
