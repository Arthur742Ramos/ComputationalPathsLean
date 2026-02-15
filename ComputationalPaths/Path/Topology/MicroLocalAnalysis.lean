/-
# Microlocal Analysis (Computational Paths Skeleton)

Skeleton declarations for wavefront sets, microsupport, microlocal sheaves,
Kashiwara-Schapira style bounds, Sato hyperfunctions, FBI transforms,
and propagation of singularities.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace MicroLocalAnalysis

structure CotangentPoint where
  base : Nat
  covector : Int

structure WavefrontSet where
  contains : CotangentPoint → Prop

structure Microsupport where
  contains : CotangentPoint → Prop

structure SheafModel where
  stalk : Nat → Nat

structure MicrolocalSheaf where
  sheaf : SheafModel
  support : Microsupport

structure HyperfunctionModel where
  boundaryValue : Nat → Int

structure FBITransformDatum where
  phase : Int → Int
  amplitude : Nat → Int

structure PropagationDatum where
  initialWF : WavefrontSet
  flow : CotangentPoint → CotangentPoint

structure KashiwaraSchapiraDatum where
  microsupportBound : Nat

structure CharacteristicCycle where
  multiplicity : Nat → Nat

def cotangentProjection (ξ : CotangentPoint) : Nat :=
  ξ.base

def cotangentFiberWeight (ξ : CotangentPoint) : Int :=
  ξ.covector

def wavefrontContains (W : WavefrontSet) (ξ : CotangentPoint) : Prop :=
  W.contains ξ

def wavefrontUnion (W₁ W₂ : WavefrontSet) : WavefrontSet :=
  ⟨fun ξ => W₁.contains ξ ∨ W₂.contains ξ⟩

def wavefrontIntersection (W₁ W₂ : WavefrontSet) : WavefrontSet :=
  ⟨fun ξ => W₁.contains ξ ∧ W₂.contains ξ⟩

def microsupportContains (M : Microsupport) (ξ : CotangentPoint) : Prop :=
  M.contains ξ

def microsupportOfSheaf (F : SheafModel) : Microsupport :=
  ⟨fun ξ => ξ.base ≤ F.stalk ξ.base⟩

def microsupportEnvelope (W : WavefrontSet) : Microsupport :=
  ⟨W.contains⟩

def characteristicVarietyModel (K : KashiwaraSchapiraDatum) : Nat :=
  K.microsupportBound + 1

def fbiTransformAmplitude (D : FBITransformDatum) (n : Nat) : Int :=
  D.amplitude n + D.phase (Int.ofNat n)

def satoBoundaryValue (H : HyperfunctionModel) (n : Nat) : Int :=
  H.boundaryValue n

def propagationCone (P : PropagationDatum) (ξ : CotangentPoint) : Nat :=
  (P.flow ξ).base

def bicharacteristicFlowStep (P : PropagationDatum) (ξ : CotangentPoint) : CotangentPoint :=
  P.flow ξ

def nonCharacteristicPullbackCondition (K : KashiwaraSchapiraDatum) (n : Nat) : Prop :=
  n ≤ characteristicVarietyModel K

def cleanIntersectionIndex (a b : Nat) : Nat :=
  a + b

def microsupportEstimate (K : KashiwaraSchapiraDatum) (n : Nat) : Nat :=
  characteristicVarietyModel K + n

def sheafQuantizationWeight (F : SheafModel) (n : Nat) : Nat :=
  F.stalk n + n

def microstalkRank (G : MicrolocalSheaf) (n : Nat) : Nat :=
  G.sheaf.stalk n

noncomputable def involutiveClosureMeasure (W : WavefrontSet) (n : Nat) : Nat :=
  by
    classical
    exact if W.contains ⟨n, 0⟩ then n + 1 else 0

noncomputable def singularSupportSize (W : WavefrontSet) (N : Nat) : Nat :=
  by
    classical
    exact (List.range N).foldl
      (fun acc n => acc + if W.contains ⟨n, 0⟩ then 1 else 0) 0

def microlocalCutoff (N n : Nat) : Nat :=
  n % (N + 1)

def propagationEnergy (P : PropagationDatum) (n : Nat) : Nat :=
  (P.flow ⟨n, 0⟩).base + n

def temperedGrowthIndex (D : FBITransformDatum) (n : Nat) : Nat :=
  Int.natAbs (fbiTransformAmplitude D n)

def characteristicCycleMass (C : CharacteristicCycle) (N : Nat) : Nat :=
  (List.range N).foldl (fun acc n => acc + C.multiplicity n) 0

def hyperfunctionOrder (H : HyperfunctionModel) (n : Nat) : Nat :=
  Int.natAbs (H.boundaryValue n)

theorem cotangentProjection_def (ξ : CotangentPoint) :
    cotangentProjection ξ = ξ.base := rfl

theorem cotangentFiberWeight_zero :
    cotangentFiberWeight ⟨0, 0⟩ = 0 := rfl

theorem wavefrontUnion_left (W₁ W₂ : WavefrontSet) (ξ : CotangentPoint)
    (h : W₁.contains ξ) :
    (wavefrontUnion W₁ W₂).contains ξ :=
  Or.inl h

theorem wavefrontUnion_right (W₁ W₂ : WavefrontSet) (ξ : CotangentPoint)
    (h : W₂.contains ξ) :
    (wavefrontUnion W₁ W₂).contains ξ :=
  Or.inr h

theorem wavefrontIntersection_intro (W₁ W₂ : WavefrontSet) (ξ : CotangentPoint)
    (h₁ : W₁.contains ξ) (h₂ : W₂.contains ξ) :
    (wavefrontIntersection W₁ W₂).contains ξ :=
  And.intro h₁ h₂

theorem microsupportContains_def (M : Microsupport) (ξ : CotangentPoint) :
    microsupportContains M ξ = M.contains ξ := rfl

theorem microsupportOfSheaf_contains (F : SheafModel) (ξ : CotangentPoint)
    (h : ξ.base ≤ F.stalk ξ.base) :
    (microsupportOfSheaf F).contains ξ := h

theorem characteristicVarietyModel_pos (K : KashiwaraSchapiraDatum) :
    0 < characteristicVarietyModel K := by
  simp [characteristicVarietyModel]

theorem fbiTransformAmplitude_zero (D : FBITransformDatum) :
    fbiTransformAmplitude D 0 = D.amplitude 0 + D.phase 0 := by
  simp [fbiTransformAmplitude]

theorem satoBoundaryValue_def (H : HyperfunctionModel) (n : Nat) :
    satoBoundaryValue H n = H.boundaryValue n := rfl

theorem propagationCone_nonneg (P : PropagationDatum) (ξ : CotangentPoint) :
    0 ≤ propagationCone P ξ := Nat.zero_le _

theorem bicharacteristicFlowStep_def (P : PropagationDatum) (ξ : CotangentPoint) :
    bicharacteristicFlowStep P ξ = P.flow ξ := rfl

theorem nonCharacteristicPullbackCondition_self (K : KashiwaraSchapiraDatum) :
    nonCharacteristicPullbackCondition K (characteristicVarietyModel K) := by
  simp [nonCharacteristicPullbackCondition]

theorem cleanIntersectionIndex_comm (a b : Nat) :
    cleanIntersectionIndex a b = cleanIntersectionIndex b a := by
  simp [cleanIntersectionIndex, Nat.add_comm]

theorem microsupportEstimate_nonneg (K : KashiwaraSchapiraDatum) (n : Nat) :
    0 ≤ microsupportEstimate K n := Nat.zero_le _

theorem sheafQuantizationWeight_nonneg (F : SheafModel) (n : Nat) :
    0 ≤ sheafQuantizationWeight F n := Nat.zero_le _

theorem microstalkRank_nonneg (G : MicrolocalSheaf) (n : Nat) :
    0 ≤ microstalkRank G n := Nat.zero_le _

theorem involutiveClosureMeasure_nonneg (W : WavefrontSet) (n : Nat) :
    0 ≤ involutiveClosureMeasure W n := Nat.zero_le _

theorem microlocalCutoff_lt (N n : Nat) :
    microlocalCutoff N n < N + 1 := by
  exact Nat.mod_lt _ (Nat.succ_pos N)

theorem propagationEnergy_nonneg (P : PropagationDatum) (n : Nat) :
    0 ≤ propagationEnergy P n := Nat.zero_le _

theorem temperedGrowthIndex_nonneg (D : FBITransformDatum) (n : Nat) :
    0 ≤ temperedGrowthIndex D n := Nat.zero_le _

theorem characteristicCycleMass_nonneg (C : CharacteristicCycle) (N : Nat) :
    0 ≤ characteristicCycleMass C N := Nat.zero_le _

theorem hyperfunctionOrder_nonneg (H : HyperfunctionModel) (n : Nat) :
    0 ≤ hyperfunctionOrder H n := Nat.zero_le _

def microlocal_path_refl (K : KashiwaraSchapiraDatum) :
    Path (characteristicVarietyModel K) (characteristicVarietyModel K) :=
  Path.refl _

def microlocal_path_trans (K : KashiwaraSchapiraDatum) :
    Path (characteristicVarietyModel K) (characteristicVarietyModel K) :=
  Path.trans (Path.refl _) (Path.refl _)

end MicroLocalAnalysis
end Topology
end Path
end ComputationalPaths
