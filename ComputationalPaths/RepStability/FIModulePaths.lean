import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Representation stability paths: FI-modules

This module packages FI-module action data with explicit computational `Path`
witnesses for identity, composition, and stabilization naturality. Coherence
normalization is tracked by `Path.Step` and compared by `RwEq`.
-/

namespace ComputationalPaths
namespace RepStability
namespace FIModulePaths

open Path

universe u

/-- Domain-specific rewrite tags for FI-module coherence moves. -/
inductive FIModuleStep : Type
  | identity
  | composition
  | stabilization
  | central

/-- A lightweight morphism in FI from degree `n` to degree `m`. -/
structure FIHom (n m : Nat) where
  map : Nat → Nat

namespace FIHom

/-- Identity FI morphism. -/
def id (n : Nat) : FIHom n n where
  map := fun i => i

/-- Composition of FI morphisms. -/
def comp {n m k : Nat} (f : FIHom n m) (g : FIHom m k) : FIHom n k where
  map := fun i => g.map (f.map i)

@[simp] theorem comp_id_left {n m : Nat} (f : FIHom n m) :
    comp (id n) f = f := by
  cases f
  rfl

@[simp] theorem comp_id_right {n m : Nat} (f : FIHom n m) :
    comp f (id m) = f := by
  cases f
  rfl

@[simp] theorem comp_assoc {n m k l : Nat}
    (f : FIHom n m) (g : FIHom m k) (h : FIHom k l) :
    comp (comp f g) h = comp f (comp g h) := by
  cases f
  cases g
  cases h
  rfl

/-- Path witness for left identity in FI composition. -/
def comp_id_left_path {n m : Nat} (f : FIHom n m) :
    Path (comp (id n) f) f :=
  Path.stepChain (comp_id_left f)

/-- Path witness for right identity in FI composition. -/
def comp_id_right_path {n m : Nat} (f : FIHom n m) :
    Path (comp f (id m)) f :=
  Path.stepChain (comp_id_right f)

/-- Path witness for associativity in FI composition. -/
def comp_assoc_path {n m k l : Nat}
    (f : FIHom n m) (g : FIHom m k) (h : FIHom k l) :
    Path (comp (comp f g) h) (comp f (comp g h)) :=
  Path.stepChain (comp_assoc f g h)

noncomputable def comp_assoc_path_rweq {n m k l : Nat}
    (f : FIHom n m) (g : FIHom m k) (h : FIHom k l) :
    RwEq
      (Path.trans (comp_assoc_path f g h) (Path.refl (comp f (comp g h))))
      (comp_assoc_path f g h) :=
  rweq_cmpA_refl_right (comp_assoc_path f g h)

end FIHom

/-- Minimal computational-path interface for FI-modules. -/
structure FIModulePathData (Carrier : Type u) where
  action : {n m : Nat} → FIHom n m → Carrier → Carrier
  stabilize : Nat → Carrier → Carrier
  stableRange : Nat
  actionIdPath : ∀ (n : Nat) (x : Carrier), Path (action (FIHom.id n) x) x
  actionCompPath :
    ∀ {n m k : Nat} (f : FIHom n m) (g : FIHom m k) (x : Carrier),
      Path (action (FIHom.comp f g) x) (action g (action f x))
  stabilizationNaturalityPath :
    ∀ {n m : Nat} (f : FIHom n m) (x : Carrier),
      Path (stabilize m (action f x)) (action f (stabilize n x))
  eventualStabilityPath :
    ∀ (n : Nat), stableRange ≤ n → ∀ x : Carrier,
      Path (stabilize n x) (stabilize (n + 1) x)

namespace FIModulePathData

variable {Carrier : Type u}
variable (F : FIModulePathData Carrier)

/-- Composite FI-action comparison path. -/
def actionCompositePath {n m k : Nat} (f : FIHom n m) (g : FIHom m k) (x : Carrier) :
    Path (F.action (FIHom.comp f g) x) (F.action g (F.action f x)) :=
  F.actionCompPath f g x

/-- Step witness: right-unit normalization for identity action coherence. -/
def actionId_step (n : Nat) (x : Carrier) :
    Path.Step
      (Path.trans (F.actionIdPath n x) (Path.refl x))
      (F.actionIdPath n x) :=
  Path.Step.trans_refl_right (F.actionIdPath n x)

noncomputable def actionId_rweq (n : Nat) (x : Carrier) :
    RwEq
      (Path.trans (F.actionIdPath n x) (Path.refl x))
      (F.actionIdPath n x) :=
  rweq_of_step (F.actionId_step n x)

/-- Step witness: left-unit normalization for stabilization naturality. -/
def stabilizationNaturality_step {n m : Nat} (f : FIHom n m) (x : Carrier) :
    Path.Step
      (Path.trans (Path.refl (F.stabilize m (F.action f x))) (F.stabilizationNaturalityPath f x))
      (F.stabilizationNaturalityPath f x) :=
  Path.Step.trans_refl_left (F.stabilizationNaturalityPath f x)

noncomputable def stabilizationNaturality_rweq {n m : Nat} (f : FIHom n m) (x : Carrier) :
    RwEq
      (Path.trans (Path.refl (F.stabilize m (F.action f x))) (F.stabilizationNaturalityPath f x))
      (F.stabilizationNaturalityPath f x) :=
  rweq_of_step (F.stabilizationNaturality_step f x)

/-- Step witness: right-unit normalization for eventual stability paths. -/
def eventualStability_step (n : Nat) (hn : F.stableRange ≤ n) (x : Carrier) :
    Path.Step
      (Path.trans
        (F.eventualStabilityPath n hn x)
        (Path.refl (F.stabilize (n + 1) x)))
      (F.eventualStabilityPath n hn x) :=
  Path.Step.trans_refl_right (F.eventualStabilityPath n hn x)

noncomputable def eventualStability_rweq (n : Nat) (hn : F.stableRange ≤ n) (x : Carrier) :
    RwEq
      (Path.trans
        (F.eventualStabilityPath n hn x)
        (Path.refl (F.stabilize (n + 1) x)))
      (F.eventualStabilityPath n hn x) :=
  rweq_of_step (F.eventualStability_step n hn x)

/-- Two-step eventual stability path obtained by composing adjacent stages. -/
def eventualStability_twoStepPath (n : Nat) (hn : F.stableRange ≤ n) (x : Carrier) :
    Path (F.stabilize n x) (F.stabilize ((n + 1) + 1) x) :=
  Path.trans
    (F.eventualStabilityPath n hn x)
    (F.eventualStabilityPath (n + 1)
      (Nat.le_trans hn (Nat.le_succ n)) x)

noncomputable def eventualStability_twoStep_rweq (n : Nat)
    (hn : F.stableRange ≤ n) (x : Carrier) :
    RwEq
      (Path.trans
        (F.eventualStability_twoStepPath n hn x)
        (Path.refl (F.stabilize ((n + 1) + 1) x)))
      (F.eventualStability_twoStepPath n hn x) :=
  rweq_cmpA_refl_right (F.eventualStability_twoStepPath n hn x)

noncomputable def eventualStability_twoStep_cancel_rweq (n : Nat)
    (hn : F.stableRange ≤ n) (x : Carrier) :
    RwEq
      (Path.trans
        (Path.symm (F.eventualStability_twoStepPath n hn x))
        (F.eventualStability_twoStepPath n hn x))
      (Path.refl (F.stabilize ((n + 1) + 1) x)) :=
  rweq_cmpA_inv_left (F.eventualStability_twoStepPath n hn x)

/-- Bridge comparing stabilization naturality at identity with action-id laws. -/
def stabilizationIdBridgePath (n : Nat) (x : Carrier) :
    Path (F.stabilize n (F.action (FIHom.id n) x))
      (F.action (FIHom.id n) (F.stabilize n x)) :=
  Path.trans
    (Path.congrArg (F.stabilize n) (F.actionIdPath n x))
    (Path.symm (F.actionIdPath n (F.stabilize n x)))

noncomputable def stabilizationIdBridge_cancel_rweq (n : Nat) (x : Carrier) :
    RwEq
      (Path.trans
        (Path.symm (F.stabilizationIdBridgePath n x))
        (F.stabilizationIdBridgePath n x))
      (Path.refl (F.action (FIHom.id n) (F.stabilize n x))) :=
  rweq_cmpA_inv_left (F.stabilizationIdBridgePath n x)

noncomputable def actionComposite_cancel_rweq {n m k : Nat}
    (f : FIHom n m) (g : FIHom m k) (x : Carrier) :
    RwEq
      (Path.trans (Path.symm (F.actionCompPath f g x)) (F.actionCompPath f g x))
      (Path.refl (F.action g (F.action f x))) :=
  rweq_cmpA_inv_left (F.actionCompPath f g x)

end FIModulePathData

/-- Trivial model instantiating the FI-module computational-path interface. -/
def trivialFIModulePathData : FIModulePathData PUnit where
  action := fun {_ _} _ _ => PUnit.unit
  stabilize := fun _ _ => PUnit.unit
  stableRange := 0
  actionIdPath := fun _ _ => Path.refl PUnit.unit
  actionCompPath := fun _ _ _ => Path.refl PUnit.unit
  stabilizationNaturalityPath := fun _ _ => Path.refl PUnit.unit
  eventualStabilityPath := by
    intro _ _ x
    exact Path.refl x

end FIModulePaths
end RepStability
end ComputationalPaths
