/-
# Control Theory via Computational Paths

This module models control theory concepts using computational paths:
controlled systems, reachability, controllability, observability,
feedback, stability under control, and optimal control.

## References

- Sontag, "Mathematical Control Theory"
- Khalil, "Nonlinear Systems"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace ControlPaths

universe u v

open ComputationalPaths.Path

/-! ## Controlled Systems -/

/-- A controlled system: state evolves under control input. -/
structure ControlSystem (S : Type u) where
  stateSpace : S
  controlSpace : S

/-- Control transition: state x goes to y under control u. -/
structure ControlTransition (S : Type u) where
  fromState : S
  toState : S
  controlInput : S
  transPath : Path fromState toState

/-- Control transition path trans refl. -/
theorem controlTrans_trans_refl {S : Type u} (d : ControlTransition S) :
    Path.trans d.transPath (Path.refl d.toState) = d.transPath := by
  simp

/-- Control transition path refl trans. -/
theorem controlTrans_refl_trans {S : Type u} (d : ControlTransition S) :
    Path.trans (Path.refl d.fromState) d.transPath = d.transPath := by
  simp

/-- RwEq: control transition trans refl. -/
theorem controlTrans_rweq_trans_refl {S : Type u} (d : ControlTransition S) :
    RwEq
      (Path.trans d.transPath (Path.refl d.toState))
      d.transPath :=
  rweq_of_step (Step.trans_refl_right d.transPath)

/-- RwEq: control transition refl trans. -/
theorem controlTrans_rweq_refl_trans {S : Type u} (d : ControlTransition S) :
    RwEq
      (Path.trans (Path.refl d.fromState) d.transPath)
      d.transPath :=
  rweq_of_step (Step.trans_refl_left d.transPath)

/-! ## Reachability -/

/-- Reachability data: state b is reachable from state a. -/
structure ReachData (S : Type u) where
  origin : S
  target : S
  reachPath : Path origin target

/-- Reachability is transitive via path composition. -/
def reach_trans {S : Type u} {a b c : S}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- Reachability composition is associative. -/
theorem reach_assoc {S : Type u} {a b c d : S}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    reach_trans (reach_trans p q) r = reach_trans p (reach_trans q r) := by
  simp [reach_trans]

/-- RwEq: reach path inv cancel right. -/
theorem reach_rweq_inv_right {S : Type u} (d : ReachData S) :
    RwEq
      (Path.trans d.reachPath (Path.symm d.reachPath))
      (Path.refl d.origin) :=
  rweq_cmpA_inv_right d.reachPath

/-- RwEq: reach path symm_symm. -/
theorem reach_rweq_symm_symm {S : Type u} (d : ReachData S) :
    RwEq
      (Path.symm (Path.symm d.reachPath))
      d.reachPath :=
  rweq_of_step (Step.symm_symm d.reachPath)

/-! ## Controllability -/

/-- Controllability data: any state is reachable from the origin. -/
structure ControllabilityData (S : Type u) where
  origin : S
  destination : S
  controlPath : Path origin destination

/-- Controllability path trans refl. -/
theorem controllability_trans_refl {S : Type u} (d : ControllabilityData S) :
    Path.trans d.controlPath (Path.refl d.destination) = d.controlPath := by
  simp

/-- RwEq: controllability trans refl. -/
theorem controllability_rweq_trans_refl {S : Type u} (d : ControllabilityData S) :
    RwEq
      (Path.trans d.controlPath (Path.refl d.destination))
      d.controlPath :=
  rweq_of_step (Step.trans_refl_right d.controlPath)

/-- RwEq: controllability inv cancel left. -/
theorem controllability_rweq_inv_left {S : Type u} (d : ControllabilityData S) :
    RwEq
      (Path.trans (Path.symm d.controlPath) d.controlPath)
      (Path.refl d.destination) :=
  rweq_cmpA_inv_left d.controlPath

/-! ## Observability -/

/-- Observability data: output determines state, witnessed as path. -/
structure ObservData (S : Type u) where
  stateVal : S
  outputVal : S
  observePath : Path stateVal outputVal

/-- Observability path trans refl. -/
theorem observe_trans_refl {S : Type u} (d : ObservData S) :
    Path.trans d.observePath (Path.refl d.outputVal) = d.observePath := by
  simp

/-- RwEq: observability symm_symm. -/
theorem observe_rweq_symm_symm {S : Type u} (d : ObservData S) :
    RwEq
      (Path.symm (Path.symm d.observePath))
      d.observePath :=
  rweq_of_step (Step.symm_symm d.observePath)

/-- RwEq: observability inv cancel right. -/
theorem observe_rweq_inv_right {S : Type u} (d : ObservData S) :
    RwEq
      (Path.trans d.observePath (Path.symm d.observePath))
      (Path.refl d.stateVal) :=
  rweq_cmpA_inv_right d.observePath

/-! ## Feedback Control -/

/-- Feedback data: closed-loop behavior equals reference, witnessed as path. -/
structure FeedbackData (S : Type u) where
  closedLoopVal : S
  referenceVal : S
  feedbackPath : Path closedLoopVal referenceVal

/-- Feedback path trans refl. -/
theorem feedback_trans_refl {S : Type u} (d : FeedbackData S) :
    Path.trans d.feedbackPath (Path.refl d.referenceVal) = d.feedbackPath := by
  simp

/-- RwEq: feedback trans refl. -/
theorem feedback_rweq_trans_refl {S : Type u} (d : FeedbackData S) :
    RwEq
      (Path.trans d.feedbackPath (Path.refl d.referenceVal))
      d.feedbackPath :=
  rweq_of_step (Step.trans_refl_right d.feedbackPath)

/-- RwEq: feedback inv cancel right. -/
theorem feedback_rweq_inv_right {S : Type u} (d : FeedbackData S) :
    RwEq
      (Path.trans d.feedbackPath (Path.symm d.feedbackPath))
      (Path.refl d.closedLoopVal) :=
  rweq_cmpA_inv_right d.feedbackPath

/-! ## Stability Under Control -/

/-- Stability data: controlled system stays near equilibrium. -/
structure StabilityData (S : Type u) where
  stateVal : S
  equilibrium : S
  stabilityPath : Path stateVal equilibrium

/-- Stability path refl trans. -/
theorem stability_refl_trans {S : Type u} (d : StabilityData S) :
    Path.trans (Path.refl d.stateVal) d.stabilityPath = d.stabilityPath := by
  simp

/-- RwEq: stability refl trans. -/
theorem stability_rweq_refl_trans {S : Type u} (d : StabilityData S) :
    RwEq
      (Path.trans (Path.refl d.stateVal) d.stabilityPath)
      d.stabilityPath :=
  rweq_of_step (Step.trans_refl_left d.stabilityPath)

/-- RwEq: stability symm_symm. -/
theorem stability_rweq_symm_symm {S : Type u} (d : StabilityData S) :
    RwEq
      (Path.symm (Path.symm d.stabilityPath))
      d.stabilityPath :=
  rweq_of_step (Step.symm_symm d.stabilityPath)

/-! ## Optimal Control -/

/-- Optimal control data: cost of optimal equals minimum. -/
structure OptimalControlData where
  actualCost : Nat
  optimalCost : Nat
  optimalPath : Path actualCost optimalCost

/-- Optimal control path trans refl. -/
theorem optimal_trans_refl (d : OptimalControlData) :
    Path.trans d.optimalPath (Path.refl d.optimalCost) = d.optimalPath := by
  simp

/-- RwEq: optimal control inv cancel right. -/
theorem optimal_rweq_inv_right (d : OptimalControlData) :
    RwEq
      (Path.trans d.optimalPath (Path.symm d.optimalPath))
      (Path.refl d.actualCost) :=
  rweq_cmpA_inv_right d.optimalPath

/-! ## congrArg for Control Maps -/

/-- Applying a control map to a reachability path via congrArg. -/
theorem congrArg_reach {A B : Type u} (f : A → B)
    {x y : A} (p : Path x y) :
    Path.congrArg f (Path.trans p (Path.refl y)) =
    Path.congrArg f p := by
  simp

/-- congrArg preserves control transition composition. -/
theorem congrArg_control_compose {A B : Type u} (f : A → B)
    {x y z : A} (p : Path x y) (q : Path y z) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) := by
  simp

/-- congrArg preserves symm of control paths. -/
theorem congrArg_control_symm {A B : Type u} (f : A → B)
    {x y : A} (p : Path x y) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) := by
  simp

end ControlPaths
end Computation
end Path
end ComputationalPaths
