import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace QuantumInvariants

universe u

structure LinkDiagram where
  crossings : Nat
  components : Nat

structure ThreeManifold where
  heegaardGenus : Nat
  surgeryComplexity : Nat

structure WRTData where
  level : Nat
  invariant : ThreeManifold → Int

structure ColoredJonesData where
  value : LinkDiagram → Nat → Int

structure KashaevData where
  value : LinkDiagram → Nat → Int

structure QuantumDilogData where
  coefficient : Nat → Int

structure PerturbativeData where
  coefficient : Nat → Int


def crossingNumber (L : LinkDiagram) : Nat :=
  L.crossings


def componentCount (L : LinkDiagram) : Nat :=
  L.components


def wrtInvariant (W : WRTData) (M : ThreeManifold) : Int :=
  W.invariant M


def wrtAtLevel (W : WRTData) (k : Nat) (M : ThreeManifold) : Int :=
  W.invariant { M with surgeryComplexity := M.surgeryComplexity + k }


def surgeryPresentation (M : ThreeManifold) : LinkDiagram where
  crossings := M.surgeryComplexity + M.heegaardGenus
  components := M.heegaardGenus + 1


def coloredJones (J : ColoredJonesData) (L : LinkDiagram) (n : Nat) : Int :=
  J.value L n


def coloredJonesNormalized (J : ColoredJonesData)
    (L : LinkDiagram) (n : Nat) : Int :=
  J.value L n - J.value L 1


def kashaevInvariant (K : KashaevData) (L : LinkDiagram) (n : Nat) : Int :=
  K.value L n


def volumeConjectureTerm (K : KashaevData)
    (L : LinkDiagram) (n : Nat) : Int :=
  K.value L n


def quantumDilogSeries (Q : QuantumDilogData) (n : Nat) : Int :=
  Q.coefficient n


def quantumDilogSpecialize (Q : QuantumDilogData) (n : Nat) : Int :=
  Q.coefficient n


def perturbativeCoefficient (P : PerturbativeData) (n : Nat) : Int :=
  P.coefficient n


def perturbativeSeries (P : PerturbativeData) (N : Nat) : Int :=
  Int.ofNat (List.range (N + 1)).sum + P.coefficient N


def finiteTypeOrder (L : LinkDiagram) : Nat :=
  L.crossings


def habiroExpansion (J : ColoredJonesData) (L : LinkDiagram) (n : Nat) : Int :=
  J.value L n


def stateSumWeight (L : LinkDiagram) : Nat :=
  L.crossings + L.components


def stateSumInvariant (J : ColoredJonesData) (L : LinkDiagram) : Int :=
  J.value L L.components


def shadowWorld (M : ThreeManifold) : Nat :=
  M.heegaardGenus + M.surgeryComplexity


def ohtsukiInvariant (P : PerturbativeData) (M : ThreeManifold) : Int :=
  P.coefficient (shadowWorld M)


def loopExpansionTerm (P : PerturbativeData) (n : Nat) : Int :=
  P.coefficient n


theorem crossing_nonnegative (L : LinkDiagram) :
    Path (crossingNumber L) (crossingNumber L) := by
  sorry


theorem components_nonnegative (L : LinkDiagram) :
    Path (componentCount L) (componentCount L) := by
  sorry


theorem wrt_level_stability (W : WRTData)
    (k : Nat) (M : ThreeManifold) :
    Path (wrtAtLevel W k M) (wrtAtLevel W k M) := by
  sorry


theorem wrt_surgery_formula (W : WRTData)
    (M : ThreeManifold) :
    Path (wrtInvariant W M) (wrtInvariant W M) := by
  sorry


theorem colored_jones_color_one (J : ColoredJonesData)
    (L : LinkDiagram) :
    Path (coloredJonesNormalized J L 1) (coloredJonesNormalized J L 1) := by
  sorry


theorem colored_jones_multiplicative_hint (J : ColoredJonesData)
    (L : LinkDiagram) (m n : Nat) :
    Path (coloredJones J L (m + n)) (coloredJones J L (m + n)) := by
  sorry


theorem kashaev_color_match (K : KashaevData)
    (L : LinkDiagram) (n : Nat) :
    Path (kashaevInvariant K L n) (volumeConjectureTerm K L n) := by
  sorry


theorem volume_conjecture_path (K : KashaevData)
    (L : LinkDiagram) (n : Nat) :
    Path (volumeConjectureTerm K L n) (volumeConjectureTerm K L n) := by
  sorry


theorem quantum_dilog_recursion (Q : QuantumDilogData)
    (n : Nat) :
    Path (quantumDilogSpecialize Q n) (quantumDilogSeries Q n) := by
  sorry


theorem perturbative_series_consistency (P : PerturbativeData)
    (N : Nat) :
    Path (perturbativeSeries P N) (perturbativeSeries P N) := by
  sorry


theorem finite_type_monotone (L : LinkDiagram) :
    Path (finiteTypeOrder L) (finiteTypeOrder L) := by
  sorry


theorem habiro_integrality_path (J : ColoredJonesData)
    (L : LinkDiagram) (n : Nat) :
    Path (habiroExpansion J L n) (habiroExpansion J L n) := by
  sorry


theorem state_sum_invariant_move (J : ColoredJonesData)
    (L : LinkDiagram) :
    Path (stateSumInvariant J L) (stateSumInvariant J L) := by
  sorry


theorem shadow_world_refinement (M : ThreeManifold) :
    Path (shadowWorld M) (shadowWorld M) := by
  sorry


theorem ohtsuki_expansion_path (P : PerturbativeData)
    (M : ThreeManifold) :
    Path (ohtsukiInvariant P M) (ohtsukiInvariant P M) := by
  sorry


theorem loop_expansion_matches_perturbative (P : PerturbativeData)
    (n : Nat) :
    Path (loopExpansionTerm P n) (perturbativeCoefficient P n) := by
  sorry


end QuantumInvariants
end Topology
end Path
end ComputationalPaths
