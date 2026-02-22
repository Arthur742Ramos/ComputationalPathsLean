import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Hodge.MixedHodgePaths

/-!
# Period maps as computational paths

This module models period maps for variations of mixed Hodge structures with
explicit domain-specific rewrite steps and derived `RwEq` witnesses.
-/

namespace ComputationalPaths
namespace Hodge

open Path

universe u v w

/-- Domain-specific rewrite steps for period-map calculations. -/
inductive PeriodMapStep {D : Type u} :
    {a b : D} → Path a b → Path a b → Prop where
  | horizontality_right_unit {a b : D} (p : Path a b) :
      PeriodMapStep (Path.trans p (Path.refl b)) p
  | functorial_left_unit {a b : D} (p : Path a b) :
      PeriodMapStep (Path.trans (Path.refl a) p) p
  | monodromy_cancel {a b : D} (p : Path a b) :
      PeriodMapStep (Path.trans (Path.symm p) p) (Path.refl b)

/-- Interpret a period-map step as a primitive `Path.Step`. -/
noncomputable def PeriodMapStep.toStep {D : Type u} {a b : D} {p q : Path a b}
    (s : PeriodMapStep p q) : Path.Step p q :=
  match s with
  | .horizontality_right_unit p => Path.Step.trans_refl_right p
  | .functorial_left_unit p => Path.Step.trans_refl_left p
  | .monodromy_cancel p => Path.Step.symm_trans p

/-- Lift a period-map step to rewrite equivalence. -/
noncomputable def rweq_of_period_step {D : Type u} {a b : D}
    {p q : Path a b} (s : PeriodMapStep p q) : RwEq p q :=
  rweq_of_step (PeriodMapStep.toStep s)

/-- Variation of mixed-Hodge structure with path-level transport. -/
structure VariationMixedHodgeData (X : Type u) (H : Type v) where
  filtration : MixedHodgeFiltrationData H
  fiber : X → H
  parallelTransport :
    ∀ {x y : X}, Path x y → Path (fiber x) (fiber y)
  weightTransport :
    ∀ i : Int, ∀ {x y : X} (_p : Path x y),
      Path (filtration.weightFiltration i (fiber x)) (filtration.weightFiltration i (fiber y))
  hodgeTransport :
    ∀ q : Nat, ∀ {x y : X} (_p : Path x y),
      Path (filtration.hodgeFiltration q (fiber x)) (filtration.hodgeFiltration q (fiber y))
  parallelTransportStep :
    ∀ {x y : X} (p : Path x y),
      PeriodMapStep
        (Path.trans (parallelTransport p) (Path.refl (fiber y)))
        (parallelTransport p)

/-- Period-map data with Griffiths-transversality style computational witnesses. -/
structure PeriodMapPathData (X : Type u) (H : Type v) (D : Type w) where
  variation : VariationMixedHodgeData X H
  periodMap : X → D
  periodTransport :
    ∀ {x y : X}, Path x y → Path (periodMap x) (periodMap y)
  horizontalityStep :
    ∀ {x y : X} (p : Path x y),
      PeriodMapStep
        (Path.trans (periodTransport p) (Path.refl (periodMap y)))
        (periodTransport p)
  functorialStep :
    ∀ {x y : X} (p : Path x y),
      PeriodMapStep
        (Path.trans (Path.refl (periodMap x)) (periodTransport p))
        (periodTransport p)
  localMonodromy : ∀ x : X, Path (periodMap x) (periodMap x)
  localMonodromyStep :
    ∀ x : X,
      PeriodMapStep
        (Path.trans (Path.symm (localMonodromy x)) (localMonodromy x))
        (Path.refl (periodMap x))

namespace PeriodMapPathData

variable {X : Type u} {H : Type v} {D : Type w}
variable (P : PeriodMapPathData X H D)

noncomputable def variation_transport_rweq {x y : X} (p : Path x y) :
    RwEq
      (Path.trans (P.variation.parallelTransport p) (Path.refl (P.variation.fiber y)))
      (P.variation.parallelTransport p) :=
  rweq_of_period_step (P.variation.parallelTransportStep p)

noncomputable def horizontality_rweq {x y : X} (p : Path x y) :
    RwEq
      (Path.trans (P.periodTransport p) (Path.refl (P.periodMap y)))
      (P.periodTransport p) :=
  rweq_of_period_step (P.horizontalityStep p)

noncomputable def functorial_rweq {x y : X} (p : Path x y) :
    RwEq
      (Path.trans (Path.refl (P.periodMap x)) (P.periodTransport p))
      (P.periodTransport p) :=
  rweq_of_period_step (P.functorialStep p)

noncomputable def local_monodromy_cancel_rweq (x : X) :
    RwEq
      (Path.trans (Path.symm (P.localMonodromy x)) (P.localMonodromy x))
      (Path.refl (P.periodMap x)) :=
  rweq_of_period_step (P.localMonodromyStep x)

/-- Round-trip period path around local monodromy. -/
noncomputable def periodRoundTrip (x : X) : Path (P.periodMap x) (P.periodMap x) :=
  Path.trans (P.localMonodromy x) (Path.symm (P.localMonodromy x))

noncomputable def period_roundtrip_rweq (x : X) :
    RwEq (P.periodRoundTrip x) (Path.refl (P.periodMap x)) :=
  rweq_of_step (Path.Step.trans_symm (P.localMonodromy x))

/-- Period-map action on weight-filtration transport. -/
noncomputable def weightPeriodTransport (i : Int) {x y : X} (p : Path x y) :
    Path
      (P.variation.filtration.weightFiltration i (P.variation.fiber x))
      (P.variation.filtration.weightFiltration i (P.variation.fiber y)) :=
  P.variation.weightTransport i p

end PeriodMapPathData

/-- Build variation data from a filtration and path transport witness. -/
noncomputable def mkVariationMixedHodgeData
    {X : Type u} {H : Type v}
    (filtration : MixedHodgeFiltrationData H)
    (fiber : X → H)
    (parallelTransport : ∀ {x y : X}, Path x y → Path (fiber x) (fiber y)) :
    VariationMixedHodgeData X H where
  filtration := filtration
  fiber := fiber
  parallelTransport := parallelTransport
  weightTransport := fun i {_} {_} p =>
    Path.congrArg (filtration.weightFiltration i) (parallelTransport p)
  hodgeTransport := fun q {_} {_} p =>
    Path.congrArg (filtration.hodgeFiltration q) (parallelTransport p)
  parallelTransportStep := fun p =>
    PeriodMapStep.horizontality_right_unit (parallelTransport p)

end Hodge
end ComputationalPaths
