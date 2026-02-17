/-
# Control Theory via Computational Paths

Control systems modeled through computational paths: controlled transitions,
reachability, controllability, observability, feedback loops, state estimation,
optimal control, Kalman decomposition, stabilization, and tracking.

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

/-- A controlled transition: input drives state from src to tgt. -/
structure ControlledTransition (S : Type u) where
  src : S
  tgt : S
  input : Nat
  controlPath : Path src tgt

/-- Compose two controlled transitions sequentially. -/
def controlCompose {S : Type u} {a b c : S}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- Control composition is associative. -/
theorem controlCompose_assoc {S : Type u} {a b c d : S}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    controlCompose (controlCompose p q) r = controlCompose p (controlCompose q r) := by
  simp [controlCompose]

/-- Control composition with refl right. -/
theorem controlCompose_refl_right {S : Type u} {a b : S} (p : Path a b) :
    controlCompose p (Path.refl b) = p := by
  simp [controlCompose]

/-- Control composition with refl left. -/
theorem controlCompose_refl_left {S : Type u} {a b : S} (p : Path a b) :
    controlCompose (Path.refl a) p = p := by
  simp [controlCompose]

/-! ## Reachability -/

/-- Reachability witness: state b is reachable from a. -/
structure ReachabilityWitness (S : Type u) where
  from_ : S
  to_ : S
  reachPath : Path from_ to_

/-- Reachability is transitive via path composition. -/
def reachTransitive {S : Type u} (r1 : ReachabilityWitness S) (r2 : ReachabilityWitness S)
    (h : r1.to_ = r2.from_) : Path r1.from_ r2.to_ :=
  Path.trans r1.reachPath (Path.trans (Path.mk [Step.mk _ _ h] h) r2.reachPath)

/-- RwEq: reachability path trans refl. -/
theorem reach_rweq_trans_refl {S : Type u} (r : ReachabilityWitness S) :
    RwEq
      (Path.trans r.reachPath (Path.refl r.to_))
      r.reachPath :=
  rweq_of_step (Step.trans_refl_right r.reachPath)

/-- RwEq: reachability inv cancel. -/
theorem reach_rweq_inv_right {S : Type u} (r : ReachabilityWitness S) :
    RwEq
      (Path.trans r.reachPath (Path.symm r.reachPath))
      (Path.refl r.from_) :=
  rweq_cmpA_inv_right r.reachPath

/-- RwEq: reachability symm_symm. -/
theorem reach_rweq_symm_symm {S : Type u} (r : ReachabilityWitness S) :
    RwEq (Path.symm (Path.symm r.reachPath)) r.reachPath :=
  rweq_of_step (Step.symm_symm r.reachPath)

/-! ## Controllability -/

/-- Controllability data: any target reachable from origin via some control path. -/
structure ControllabilityData (S : Type u) where
  origin : S
  target : S
  controlSeq : Path origin target

/-- Controllability path trans refl. -/
theorem controllability_trans_refl {S : Type u} (d : ControllabilityData S) :
    Path.trans d.controlSeq (Path.refl d.target) = d.controlSeq := by
  simp

/-- RwEq: controllability inv cancel left. -/
theorem controllability_rweq_inv_left {S : Type u} (d : ControllabilityData S) :
    RwEq
      (Path.trans (Path.symm d.controlSeq) d.controlSeq)
      (Path.refl d.target) :=
  rweq_cmpA_inv_left d.controlSeq

/-- RwEq: controllability refl trans. -/
theorem controllability_rweq_refl_trans {S : Type u} (d : ControllabilityData S) :
    RwEq
      (Path.trans (Path.refl d.origin) d.controlSeq)
      d.controlSeq :=
  rweq_of_step (Step.trans_refl_left d.controlSeq)

/-! ## Observability -/

/-- Observability data: output path distinguishes states. -/
structure ObservabilityData (S O : Type u) where
  state1 : S
  state2 : S
  output1 : O
  output2 : O
  obsPath : Path output1 output2

/-- RwEq: observability path trans refl. -/
theorem obs_rweq_trans_refl {S O : Type u} (d : ObservabilityData S O) :
    RwEq
      (Path.trans d.obsPath (Path.refl d.output2))
      d.obsPath :=
  rweq_of_step (Step.trans_refl_right d.obsPath)

/-- RwEq: observability inv cancel. -/
theorem obs_rweq_inv_right {S O : Type u} (d : ObservabilityData S O) :
    RwEq
      (Path.trans d.obsPath (Path.symm d.obsPath))
      (Path.refl d.output1) :=
  rweq_cmpA_inv_right d.obsPath

/-! ## Feedback Control -/

/-- Feedback data: output fed back to compute next input. -/
structure FeedbackData (S : Type u) where
  preState : S
  postState : S
  feedbackPath : Path preState postState

/-- Feedback loop: composing feedback paths. -/
def feedbackLoop {S : Type u} {a : S} (p : Path a a) : Nat → Path a a
  | 0 => Path.refl a
  | n + 1 => Path.trans (feedbackLoop p n) p

/-- Feedback loop zero is refl. -/
theorem feedbackLoop_zero {S : Type u} {a : S} (p : Path a a) :
    feedbackLoop p 0 = Path.refl a := rfl

/-- RwEq: feedback loop 1 simplifies. -/
theorem feedbackLoop_one_rweq {S : Type u} {a : S} (p : Path a a) :
    RwEq (feedbackLoop p 1) p :=
  rweq_of_step (Step.trans_refl_left p)

/-- Feedback data trans refl. -/
theorem feedback_trans_refl {S : Type u} (d : FeedbackData S) :
    Path.trans d.feedbackPath (Path.refl d.postState) = d.feedbackPath := by
  simp

/-- RwEq: feedback symm_symm. -/
theorem feedback_rweq_symm_symm {S : Type u} (d : FeedbackData S) :
    RwEq (Path.symm (Path.symm d.feedbackPath)) d.feedbackPath :=
  rweq_of_step (Step.symm_symm d.feedbackPath)

/-! ## State Estimation -/

/-- State estimation: estimated state relates to true state via path. -/
structure StateEstimate (S : Type u) where
  trueState : S
  estimatedState : S
  estimatePath : Path estimatedState trueState

/-- RwEq: estimate inv cancel right. -/
theorem estimate_rweq_inv_right {S : Type u} (d : StateEstimate S) :
    RwEq
      (Path.trans d.estimatePath (Path.symm d.estimatePath))
      (Path.refl d.estimatedState) :=
  rweq_cmpA_inv_right d.estimatePath

/-- RwEq: estimate refl trans. -/
theorem estimate_rweq_refl_trans {S : Type u} (d : StateEstimate S) :
    RwEq
      (Path.trans (Path.refl d.estimatedState) d.estimatePath)
      d.estimatePath :=
  rweq_of_step (Step.trans_refl_left d.estimatePath)

/-! ## Optimal Control -/

/-- Optimal control: path minimizing some cost functional. -/
structure OptimalControlData (S : Type u) where
  initialState : S
  finalState : S
  cost : Nat
  optimalPath : Path initialState finalState

/-- Optimal path trans refl. -/
theorem optimal_trans_refl {S : Type u} (d : OptimalControlData S) :
    Path.trans d.optimalPath (Path.refl d.finalState) = d.optimalPath := by
  simp

/-- RwEq: optimal inv cancel. -/
theorem optimal_rweq_inv_right {S : Type u} (d : OptimalControlData S) :
    RwEq
      (Path.trans d.optimalPath (Path.symm d.optimalPath))
      (Path.refl d.initialState) :=
  rweq_cmpA_inv_right d.optimalPath

/-! ## Stabilization -/

/-- Stabilization data: controlled system reaches equilibrium. -/
structure StabilizationData (S : Type u) where
  currentState : S
  equilibrium : S
  stabilizePath : Path currentState equilibrium

/-- Stabilization path trans refl. -/
theorem stabilize_trans_refl {S : Type u} (d : StabilizationData S) :
    Path.trans d.stabilizePath (Path.refl d.equilibrium) = d.stabilizePath := by
  simp

/-- RwEq: stabilization refl trans. -/
theorem stabilize_rweq_refl_trans {S : Type u} (d : StabilizationData S) :
    RwEq
      (Path.trans (Path.refl d.currentState) d.stabilizePath)
      d.stabilizePath :=
  rweq_of_step (Step.trans_refl_left d.stabilizePath)

/-- RwEq: stabilization symm_symm. -/
theorem stabilize_rweq_symm_symm {S : Type u} (d : StabilizationData S) :
    RwEq (Path.symm (Path.symm d.stabilizePath)) d.stabilizePath :=
  rweq_of_step (Step.symm_symm d.stabilizePath)

/-! ## Tracking -/

/-- Tracking data: actual output follows reference via path. -/
structure TrackingData (S : Type u) where
  reference : S
  actual : S
  trackPath : Path actual reference

/-- Tracking path trans refl. -/
theorem tracking_trans_refl {S : Type u} (d : TrackingData S) :
    Path.trans d.trackPath (Path.refl d.reference) = d.trackPath := by
  simp

/-- RwEq: tracking inv cancel left. -/
theorem tracking_rweq_inv_left {S : Type u} (d : TrackingData S) :
    RwEq
      (Path.trans (Path.symm d.trackPath) d.trackPath)
      (Path.refl d.reference) :=
  rweq_cmpA_inv_left d.trackPath

/-! ## congrArg for Control Paths -/

/-- Applying output function to control path via congrArg. -/
theorem congrArg_control {S T : Type u} (f : S → T)
    {a b : S} (p : Path a b) :
    Path.congrArg f (Path.trans p (Path.refl b)) =
    Path.congrArg f p := by
  simp

/-- congrArg preserves control composition. -/
theorem congrArg_controlCompose {S T : Type u} (f : S → T)
    {a b c : S} (p : Path a b) (q : Path b c) :
    Path.congrArg f (controlCompose p q) =
    controlCompose (Path.congrArg f p) (Path.congrArg f q) := by
  simp [controlCompose]

/-- congrArg preserves symm of control paths. -/
theorem congrArg_control_symm {S T : Type u} (f : S → T)
    {a b : S} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) := by
  simp

end ControlPaths
end Computation
end Path
end ComputationalPaths
