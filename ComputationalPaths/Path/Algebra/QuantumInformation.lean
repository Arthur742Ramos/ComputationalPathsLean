import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace QuantumInformation

universe u

structure QuantumState where
  dim : Nat
  traceVal : Nat
  entropyVal : Nat

structure QuantumChannel where
  inputDim : Nat
  outputDim : Nat
  krausCount : Nat
  envDim : Nat
  depolarizing : Nat

structure StabilizerCode where
  length : Nat
  dimension : Nat
  distance : Nat
  syndrome : Nat

def quantumPathCompose {X : Type u} {a b c : X}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

def densityTrace (ρ : QuantumState) : Nat :=
  ρ.traceVal

def channelOutputEntropy (ρ : QuantumState) (Φ : QuantumChannel) : Nat :=
  ρ.entropyVal + Φ.outputDim

def stinespringEnvironmentDim (Φ : QuantumChannel) : Nat :=
  Φ.envDim

def krausRank (Φ : QuantumChannel) : Nat :=
  Φ.krausCount

def entanglementEntropy (ρ : QuantumState) : Nat :=
  ρ.entropyVal

def mutualInformation (ρ : QuantumState) (Φ : QuantumChannel) : Nat :=
  ρ.entropyVal + Φ.inputDim + Φ.outputDim

def coherentInformation (ρ : QuantumState) (Φ : QuantumChannel) : Nat :=
  Φ.outputDim + ρ.entropyVal

def quantumCapacityLowerBound (Φ : QuantumChannel) : Nat :=
  Φ.outputDim

def quantumCapacityUpperBound (Φ : QuantumChannel) : Nat :=
  Φ.inputDim + Φ.outputDim

def knillLaflammeSyndrome (C : StabilizerCode) : Nat :=
  C.syndrome

def stabilizerDistance (C : StabilizerCode) : Nat :=
  C.distance

def stabilizerRate (C : StabilizerCode) : Nat :=
  C.dimension + C.length

def errorCorrectionThreshold (C : StabilizerCode) : Nat :=
  C.distance + C.syndrome

def depolarizingParameter (Φ : QuantumChannel) : Nat :=
  Φ.depolarizing

def fidelityEstimate (ρ : QuantumState) (Φ : QuantumChannel) : Nat :=
  ρ.traceVal + Φ.outputDim

def traceDistanceEstimate (ρ σ : QuantumState) : Nat :=
  ρ.traceVal + σ.traceVal

def relativeEntropyEstimate (ρ σ : QuantumState) : Nat :=
  ρ.entropyVal + σ.entropyVal

def channelComplementaryRank (Φ : QuantumChannel) : Nat :=
  Φ.envDim + Φ.krausCount

def privateCapacityLowerBound (Φ : QuantumChannel) : Nat :=
  Φ.outputDim + Φ.depolarizing

def classicalCapacityLowerBound (Φ : QuantumChannel) : Nat :=
  Φ.inputDim

def entanglementAssistedCapacity (Φ : QuantumChannel) : Nat :=
  Φ.inputDim + Φ.outputDim + Φ.envDim

theorem quantumPathCompose_refl {X : Type u} (a : X) :
    quantumPathCompose (Path.refl a) (Path.refl a) =
      Path.trans (Path.refl a) (Path.refl a) := by
  sorry

theorem densityTrace_def (ρ : QuantumState) :
    densityTrace ρ = ρ.traceVal := by
  sorry

theorem channelOutputEntropy_def (ρ : QuantumState) (Φ : QuantumChannel) :
    channelOutputEntropy ρ Φ = ρ.entropyVal + Φ.outputDim := by
  sorry

theorem stinespringEnvironmentDim_def (Φ : QuantumChannel) :
    stinespringEnvironmentDim Φ = Φ.envDim := by
  sorry

theorem krausRank_def (Φ : QuantumChannel) :
    krausRank Φ = Φ.krausCount := by
  sorry

theorem entanglementEntropy_def (ρ : QuantumState) :
    entanglementEntropy ρ = ρ.entropyVal := by
  sorry

theorem mutualInformation_def (ρ : QuantumState) (Φ : QuantumChannel) :
    mutualInformation ρ Φ = ρ.entropyVal + Φ.inputDim + Φ.outputDim := by
  sorry

theorem coherentInformation_def (ρ : QuantumState) (Φ : QuantumChannel) :
    coherentInformation ρ Φ = Φ.outputDim + ρ.entropyVal := by
  sorry

theorem quantumCapacityLowerBound_def (Φ : QuantumChannel) :
    quantumCapacityLowerBound Φ = Φ.outputDim := by
  sorry

theorem quantumCapacityUpperBound_def (Φ : QuantumChannel) :
    quantumCapacityUpperBound Φ = Φ.inputDim + Φ.outputDim := by
  sorry

theorem knillLaflammeSyndrome_def (C : StabilizerCode) :
    knillLaflammeSyndrome C = C.syndrome := by
  sorry

theorem stabilizerDistance_def (C : StabilizerCode) :
    stabilizerDistance C = C.distance := by
  sorry

theorem stabilizerRate_def (C : StabilizerCode) :
    stabilizerRate C = C.dimension + C.length := by
  sorry

theorem errorCorrectionThreshold_def (C : StabilizerCode) :
    errorCorrectionThreshold C = C.distance + C.syndrome := by
  sorry

theorem depolarizingParameter_def (Φ : QuantumChannel) :
    depolarizingParameter Φ = Φ.depolarizing := by
  sorry

theorem fidelityEstimate_def (ρ : QuantumState) (Φ : QuantumChannel) :
    fidelityEstimate ρ Φ = ρ.traceVal + Φ.outputDim := by
  sorry

theorem traceDistanceEstimate_def (ρ σ : QuantumState) :
    traceDistanceEstimate ρ σ = ρ.traceVal + σ.traceVal := by
  sorry

theorem relativeEntropyEstimate_def (ρ σ : QuantumState) :
    relativeEntropyEstimate ρ σ = ρ.entropyVal + σ.entropyVal := by
  sorry

theorem channelComplementaryRank_def (Φ : QuantumChannel) :
    channelComplementaryRank Φ = Φ.envDim + Φ.krausCount := by
  sorry

theorem entanglementAssistedCapacity_def (Φ : QuantumChannel) :
    entanglementAssistedCapacity Φ = Φ.inputDim + Φ.outputDim + Φ.envDim := by
  sorry

end QuantumInformation
end Algebra
end Path
end ComputationalPaths
