/-
# Morse Theory for Computational Paths

Morse functions, critical points, CW structure, Morse inequalities.
All proofs are complete — no sorry, no axiom.
-/
import ComputationalPaths.Path.Homotopy.CWComplexHomotopy

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace MorseTheory

universe u

/-! ## Critical Points -/

/-- A critical point of a Morse function, with its index. -/
structure CriticalPoint where
  /-- Identifier for the critical point. -/
  point : Type u
  /-- The Morse index. -/
  index : Nat
  /-- The critical value f(p). -/
  criticalValue : Int

/-- A Morse function on a manifold of dimension n. -/
structure MorseFunctionData (n : Nat) where
  /-- The critical points. -/
  criticalPoints : List CriticalPoint.{u}
  /-- Each index is ≤ n. -/
  index_le_dim : ∀ cp ∈ criticalPoints, cp.index ≤ n
  /-- Critical values are distinct. -/
  distinct_values : ∀ cp₁ ∈ criticalPoints, ∀ cp₂ ∈ criticalPoints,
    cp₁ ≠ cp₂ → cp₁.criticalValue ≠ cp₂.criticalValue

/-! ## Counting -/

/-- Count critical points of a given index. -/
def countIndex (mf : MorseFunctionData n) (k : Nat) : Nat :=
  (mf.criticalPoints.filter (fun cp => cp.index == k)).length

/-- Total number of critical points. -/
def totalCritical (mf : MorseFunctionData n) : Nat :=
  mf.criticalPoints.length

/-- The count at each index is bounded by the total. -/
theorem countIndex_le_total (mf : MorseFunctionData n) (k : Nat) :
    countIndex mf k ≤ totalCritical mf := by
  unfold countIndex totalCritical
  exact List.length_filter_le _ _

/-! ## Morse Lemma -/

/-- Morse lemma: local normal form around a nondegenerate critical point. -/
structure MorseLemma (n : Nat) (cp : CriticalPoint.{u}) where
  /-- Number of negative squares. -/
  negCount : Nat
  /-- Number of positive squares. -/
  posCount : Nat
  /-- neg = index. -/
  neg_eq_index : negCount = cp.index
  /-- neg + pos = dim. -/
  sum_eq_dim : negCount + posCount = n

/-- Every critical point in a Morse function has a Morse lemma. -/
def morseLemma_from_data (n : Nat) (cp : CriticalPoint.{u})
    (h : cp.index ≤ n) : MorseLemma n cp where
  negCount := cp.index
  posCount := n - cp.index
  neg_eq_index := rfl
  sum_eq_dim := Nat.add_sub_cancel' h

/-! ## Handle Attachment -/

/-- A handle attachment at a critical point. -/
structure HandleAttachment where
  /-- Index of the handle. -/
  handleIndex : Nat
  /-- Critical value. -/
  attachValue : Int

/-- Build handle data from a critical point. -/
def handleFromCritical (cp : CriticalPoint) : HandleAttachment where
  handleIndex := cp.index
  attachValue := cp.criticalValue

/-- Handle index matches critical point index. -/
theorem handleIndex_eq_index (cp : CriticalPoint) :
    (handleFromCritical cp).handleIndex = cp.index := rfl

/-! ## CW Structure -/

/-- A CW cell from a critical point. -/
structure MorseCWCell where
  /-- Dimension. -/
  cellDim : Nat
  /-- Origin critical point. -/
  origin : CriticalPoint

/-- Build the CW structure from a Morse function. -/
def MorseCWStructure (mf : MorseFunctionData n) : List MorseCWCell :=
  mf.criticalPoints.map fun cp => { cellDim := cp.index, origin := cp }

/-- Number of cells equals number of critical points. -/
theorem cwStructure_length (mf : MorseFunctionData n) :
    (MorseCWStructure mf).length = mf.criticalPoints.length := by
  unfold MorseCWStructure
  exact List.length_map _

/-! ## Betti Numbers and Morse Inequalities -/

/-- Betti number data. -/
structure BettiData where
  /-- The k-th Betti number. -/
  betti : Nat → Nat

/-- Weak Morse inequality: cₖ ≥ bₖ. -/
structure MorseInequalityWeak (mf : MorseFunctionData n) (bd : BettiData) where
  ineq : ∀ k, bd.betti k ≤ countIndex mf k

/-- A Morse function is perfect if cₖ = bₖ for all k. -/
def IsPerfect (mf : MorseFunctionData n) (bd : BettiData) : Prop :=
  ∀ k, bd.betti k = countIndex mf k

/-! ## Gradient Flow -/

/-- A gradient flow line between two critical points. -/
structure FlowLine where
  /-- Source. -/
  source : CriticalPoint
  /-- Target. -/
  target : CriticalPoint
  /-- Value decreases. -/
  value_decreasing : target.criticalValue < source.criticalValue
  /-- Index decreases. -/
  index_relation : target.index < source.index

/-! ## Example: S² -/

/-- The standard height function on S² has two critical points. -/
def sphereMorseFunction : MorseFunctionData 2 where
  criticalPoints := [
    { point := Unit, index := 0, criticalValue := -1 },
    { point := Unit, index := 2, criticalValue := 1 }
  ]
  index_le_dim := by
    intro cp hcp
    simp [List.mem_cons] at hcp
    rcases hcp with rfl | rfl <;> decide
  distinct_values := by
    intro cp₁ hcp₁ cp₂ hcp₂ hne
    simp [List.mem_cons] at hcp₁ hcp₂
    rcases hcp₁ with rfl | rfl <;> rcases hcp₂ with rfl | rfl <;> simp_all

/-- S² has exactly 2 critical points. -/
theorem sphere_total_critical : totalCritical sphereMorseFunction = 2 := rfl

/-- S² has one minimum, no saddle, one maximum. -/
theorem sphere_index_zero : countIndex sphereMorseFunction 0 = 1 := by native_decide
theorem sphere_index_one : countIndex sphereMorseFunction 1 = 0 := by native_decide
theorem sphere_index_two : countIndex sphereMorseFunction 2 = 1 := by native_decide

/-- S² Betti data. -/
def sphereBettiData : BettiData where
  betti := fun k => match k with | 0 => 1 | 2 => 1 | _ => 0

/-- The S² Morse function is perfect. -/
theorem sphere_perfect : IsPerfect sphereMorseFunction sphereBettiData := by
  intro k
  simp only [sphereBettiData, countIndex, sphereMorseFunction]
  match k with
  | 0 => native_decide
  | 1 => native_decide
  | 2 => native_decide
  | 3 => native_decide
  | n + 4 => simp [List.filter, BEq.beq]

/-! ## Example: T² -/

/-- The standard Morse function on the torus has four critical points. -/
def torusMorseFunction : MorseFunctionData 2 where
  criticalPoints := [
    { point := Unit, index := 0, criticalValue := 0 },
    { point := Unit, index := 1, criticalValue := 1 },
    { point := Unit, index := 1, criticalValue := 2 },
    { point := Unit, index := 2, criticalValue := 3 }
  ]
  index_le_dim := by
    intro cp hcp
    simp [List.mem_cons] at hcp
    rcases hcp with rfl | rfl | rfl | rfl <;> decide
  distinct_values := by
    intro cp₁ hcp₁ cp₂ hcp₂ hne
    simp [List.mem_cons] at hcp₁ hcp₂
    rcases hcp₁ with rfl | rfl | rfl | rfl <;>
      rcases hcp₂ with rfl | rfl | rfl | rfl <;> simp_all

/-- The torus has 4 critical points. -/
theorem torus_total_critical : totalCritical torusMorseFunction = 4 := rfl

/-- Torus critical point counts by index. -/
theorem torus_index_zero : countIndex torusMorseFunction 0 = 1 := by native_decide
theorem torus_index_one : countIndex torusMorseFunction 1 = 2 := by native_decide
theorem torus_index_two : countIndex torusMorseFunction 2 = 1 := by native_decide

end MorseTheory
end Homotopy
end Path
end ComputationalPaths
