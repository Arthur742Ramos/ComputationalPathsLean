import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Mixed Hodge structures as computational paths

This module packages mixed-Hodge filtration data with explicit domain-specific
rewrite steps and derived `RwEq` normalization lemmas.
-/

namespace ComputationalPaths
namespace Hodge

open Path

universe u v

/-- Domain-specific rewrite steps for mixed-Hodge filtration computations. -/
inductive MixedHodgeStep {H : Type u} :
    {a b : H} → Path a b → Path a b → Prop where
  | weight_right_unit {a b : H} (p : Path a b) :
      MixedHodgeStep (Path.trans p (Path.refl b)) p
  | hodge_left_unit {a b : H} (p : Path a b) :
      MixedHodgeStep (Path.trans (Path.refl a) p) p
  | polarization_cancel {a b : H} (p : Path a b) :
      MixedHodgeStep (Path.trans p (Path.symm p)) (Path.refl a)

/-- Interpret a mixed-Hodge domain step as a primitive `Path.Step`. -/
noncomputable def MixedHodgeStep.toStep {H : Type u} {a b : H} {p q : Path a b}
    (s : MixedHodgeStep p q) : Path.Step p q :=
  match s with
  | .weight_right_unit p => Path.Step.trans_refl_right p
  | .hodge_left_unit p => Path.Step.trans_refl_left p
  | .polarization_cancel p => Path.Step.trans_symm p

/-- Lift a mixed-Hodge step to rewrite equivalence. -/
noncomputable def rweq_of_mixed_hodge_step {H : Type u} {a b : H}
    {p q : Path a b} (s : MixedHodgeStep p q) : RwEq p q :=
  rweq_of_step (MixedHodgeStep.toStep s)

/-- Mixed-Hodge filtration package with explicit path-level coherence witnesses. -/
structure MixedHodgeFiltrationData (H : Type u) where
  weightFiltration : Int → H → H
  hodgeFiltration : Nat → H → H
  gradedPiece : Int → H → H
  weightComposePath :
    ∀ i j : Int, ∀ x : H,
      Path (weightFiltration i (weightFiltration j x)) (weightFiltration (i + j) x)
  hodgeComposePath :
    ∀ p q : Nat, ∀ x : H,
      Path (hodgeFiltration p (hodgeFiltration q x)) (hodgeFiltration (p + q) x)
  gradedWeightPath :
    ∀ n : Int, ∀ x : H,
      Path (gradedPiece n (weightFiltration 0 x)) (gradedPiece n x)
  weightComposeStep :
    ∀ i j : Int, ∀ x : H,
      MixedHodgeStep
        (Path.trans (weightComposePath i j x)
          (Path.refl (weightFiltration (i + j) x)))
        (weightComposePath i j x)
  hodgeComposeStep :
    ∀ p q : Nat, ∀ x : H,
      MixedHodgeStep
        (Path.trans
          (Path.refl (hodgeFiltration p (hodgeFiltration q x)))
          (hodgeComposePath p q x))
        (hodgeComposePath p q x)
  gradedWeightStep :
    ∀ n : Int, ∀ x : H,
      MixedHodgeStep
        (Path.trans (gradedWeightPath n x) (Path.refl (gradedPiece n x)))
        (gradedWeightPath n x)

namespace MixedHodgeFiltrationData

variable {H : Type u} (M : MixedHodgeFiltrationData H)

noncomputable def weight_compose_rweq (i j : Int) (x : H) :
    RwEq
      (Path.trans (M.weightComposePath i j x)
        (Path.refl (M.weightFiltration (i + j) x)))
      (M.weightComposePath i j x) :=
  rweq_of_mixed_hodge_step (M.weightComposeStep i j x)

noncomputable def hodge_compose_rweq (p q : Nat) (x : H) :
    RwEq
      (Path.trans
        (Path.refl (M.hodgeFiltration p (M.hodgeFiltration q x)))
        (M.hodgeComposePath p q x))
      (M.hodgeComposePath p q x) :=
  rweq_of_mixed_hodge_step (M.hodgeComposeStep p q x)

noncomputable def graded_weight_rweq (n : Int) (x : H) :
    RwEq
      (Path.trans (M.gradedWeightPath n x) (Path.refl (M.gradedPiece n x)))
      (M.gradedWeightPath n x) :=
  rweq_of_mixed_hodge_step (M.gradedWeightStep n x)

/-- Round-trip path used in polarization-style cancellation checks. -/
noncomputable def weightRoundTrip (i j : Int) (x : H) :
    Path
      (M.weightFiltration i (M.weightFiltration j x))
      (M.weightFiltration i (M.weightFiltration j x)) :=
  Path.trans (M.weightComposePath i j x) (Path.symm (M.weightComposePath i j x))

noncomputable def weight_roundtrip_rweq (i j : Int) (x : H) :
    RwEq (M.weightRoundTrip i j x)
      (Path.refl (M.weightFiltration i (M.weightFiltration j x))) := by
  unfold weightRoundTrip
  exact rweq_of_mixed_hodge_step
    (MixedHodgeStep.polarization_cancel (M.weightComposePath i j x))

/-- Hodge-filtration round-trip path and its cancellation witness. -/
noncomputable def hodgeRoundTrip (p q : Nat) (x : H) :
    Path
      (M.hodgeFiltration p (M.hodgeFiltration q x))
      (M.hodgeFiltration p (M.hodgeFiltration q x)) :=
  Path.trans (M.hodgeComposePath p q x) (Path.symm (M.hodgeComposePath p q x))

noncomputable def hodge_roundtrip_rweq (p q : Nat) (x : H) :
    RwEq (M.hodgeRoundTrip p q x)
      (Path.refl (M.hodgeFiltration p (M.hodgeFiltration q x))) := by
  unfold hodgeRoundTrip
  exact rweq_of_mixed_hodge_step
    (MixedHodgeStep.polarization_cancel (M.hodgeComposePath p q x))

/-- Weight filtration transport induced by a path in the base. -/
noncomputable def transportWeight
    {X : Type v} (fiber : X → H) {x y : X} (p : Path x y) (i : Int) :
    Path (M.weightFiltration i (fiber x)) (M.weightFiltration i (fiber y)) :=
  Path.congrArg (M.weightFiltration i) (Path.congrArg fiber p)

end MixedHodgeFiltrationData

/-- Build mixed-Hodge filtration data from path-level coherence witnesses. -/
noncomputable def mkMixedHodgeFiltrationData
    {H : Type u}
    (weightFiltration : Int → H → H)
    (hodgeFiltration : Nat → H → H)
    (gradedPiece : Int → H → H)
    (weightComposePath :
      ∀ i j : Int, ∀ x : H,
        Path (weightFiltration i (weightFiltration j x)) (weightFiltration (i + j) x))
    (hodgeComposePath :
      ∀ p q : Nat, ∀ x : H,
        Path (hodgeFiltration p (hodgeFiltration q x)) (hodgeFiltration (p + q) x))
    (gradedWeightPath :
      ∀ n : Int, ∀ x : H,
        Path (gradedPiece n (weightFiltration 0 x)) (gradedPiece n x)) :
    MixedHodgeFiltrationData H where
  weightFiltration := weightFiltration
  hodgeFiltration := hodgeFiltration
  gradedPiece := gradedPiece
  weightComposePath := weightComposePath
  hodgeComposePath := hodgeComposePath
  gradedWeightPath := gradedWeightPath
  weightComposeStep := fun i j x =>
    MixedHodgeStep.weight_right_unit (weightComposePath i j x)
  hodgeComposeStep := fun p q x =>
    MixedHodgeStep.hodge_left_unit (hodgeComposePath p q x)
  gradedWeightStep := fun n x =>
    MixedHodgeStep.weight_right_unit (gradedWeightPath n x)

end Hodge
end ComputationalPaths
