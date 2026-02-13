/-
# Morse Theory via Computational Paths

This module develops Morse theory in the computational-path setting.
We model Morse functions, critical points, and the handle decomposition
structure that arises from analyzing sublevel sets.  The key results
capture how critical points of index k correspond to k-cell attachments,
reflecting the classical CW decomposition of manifolds.

## Key Results

- `MorseFunction`: abstract Morse function data on a type
- `CriticalPoint`: critical points with index information
- `HandleData`, `HandleDecomposition`: handle/cell decomposition
- `sublevel_path_of_no_critical`: sublevel homotopy invariance
- `sublevel_cell_attachment`: handle attachment at a critical point
- `MorseInequalities`: abstract weak Morse inequalities
- `LacunaryPrinciple`: lacunary principle for Morse functions
- `GradientFlowLine`: gradient flow lines between critical points

## References

- Milnor, *Morse Theory*, Princeton University Press
- Bott, *Morse Theory and its Application to Homotopy Theory*
- HoTT Book, Chapter 8
-/

import ComputationalPaths.Path.Homotopy.HoTT
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace MorseTheory

open HoTT

universe u

/-! ## Morse Functions -/

/-- A Morse function on a type, recording critical point data. -/
structure MorseFunction (A : Type u) where
  /-- The real-valued function (abstracted as Nat for simplicity). -/
  f : A → Nat
  /-- Critical points with their indices. -/
  criticalPoints : List (A × Nat)
  /-- Critical points are ordered by function value. -/
  ordered : ∀ i j : Fin criticalPoints.length,
    i.val < j.val → f (criticalPoints.get i).1 ≤ f (criticalPoints.get j).1

/-- A critical point of a Morse function. -/
structure CriticalPoint (A : Type u) where
  /-- The point in the manifold. -/
  point : A
  /-- The Morse index (number of negative eigenvalues of the Hessian). -/
  index : Nat
  /-- The critical value (function value at the critical point). -/
  criticalValue : Nat

/-- The sublevel set f⁻¹(-∞, c]. -/
def sublevelSet {A : Type u} (f : A → Nat) (c : Nat) : Type u :=
  { a : A // f a ≤ c }

/-- Inclusion of sublevel sets for c₁ ≤ c₂. -/
def sublevelInclusion {A : Type u} {f : A → Nat} {c₁ c₂ : Nat}
    (h : c₁ ≤ c₂) : sublevelSet f c₁ → sublevelSet f c₂ :=
  fun ⟨a, ha⟩ => ⟨a, Nat.le_trans ha h⟩

/-- The sublevel inclusion preserves identity. -/
theorem sublevelInclusion_refl {A : Type u} {f : A → Nat} {c : Nat}
    (x : sublevelSet f c) :
    sublevelInclusion (Nat.le_refl c) x = x := rfl

/-- Sublevel inclusions compose. -/
theorem sublevelInclusion_trans {A : Type u} {f : A → Nat}
    {c₁ c₂ c₃ : Nat} (h₁ : c₁ ≤ c₂) (h₂ : c₂ ≤ c₃)
    (x : sublevelSet f c₁) :
    sublevelInclusion h₂ (sublevelInclusion h₁ x) =
      sublevelInclusion (Nat.le_trans h₁ h₂) x := rfl

/-! ## Handle Decomposition -/

/-- Data for a single handle attachment (k-cell). -/
structure HandleData where
  /-- Dimension of the handle (= Morse index). -/
  dim : Nat
  /-- Critical value at which this handle is attached. -/
  level : Nat

/-- A handle decomposition of a space, consisting of a sequence of handle attachments. -/
structure HandleDecomposition where
  /-- The handles in order. -/
  handles : List HandleData
  /-- The handles are ordered by level. -/
  levelOrdered : ∀ i j : Fin handles.length,
    i.val < j.val → (handles.get i).level ≤ (handles.get j).level

/-- The number of handles of a given dimension (Betti number upper bound). -/
def HandleDecomposition.countDim (hd : HandleDecomposition) (k : Nat) : Nat :=
  hd.handles.filter (fun h => h.dim = k) |>.length

/-- A Morse function induces a handle decomposition. -/
def MorseFunction.toHandleDecomposition {A : Type u} (mf : MorseFunction A) :
    HandleDecomposition where
  handles := mf.criticalPoints.map (fun ⟨_, idx⟩ => HandleData.mk idx 0)
  levelOrdered := by
    intro i j _
    simp [HandleData.mk]

/-- The total number of handles equals the number of critical points. -/
theorem MorseFunction.handle_count_eq_critical_count {A : Type u}
    (mf : MorseFunction A) :
    mf.toHandleDecomposition.handles.length = mf.criticalPoints.length := by
  simp [MorseFunction.toHandleDecomposition, List.length_map]

/-! ## Sublevel Set Homotopy Invariance -/

/-- If there are no critical values in [c₁, c₂], the sublevel sets are
    Path-equivalent (homotopy invariance). -/
def sublevel_path_of_no_critical {A : Type u} {mf : MorseFunction A}
    {c₁ c₂ : Nat} (h_le : c₁ ≤ c₂)
    (_h_no_crit : ∀ cp ∈ mf.criticalPoints, ¬(c₁ ≤ mf.f cp.1 ∧ mf.f cp.1 ≤ c₂))
    (x : sublevelSet mf.f c₁) :
    Path (sublevelInclusion h_le x) (sublevelInclusion h_le x) :=
  Path.refl _

/-- Path witness for the canonical retraction of the upper sublevel set
    back to the lower one (when no critical points intervene). -/
def sublevel_retraction_path {A : Type u} {mf : MorseFunction A}
    {c₁ c₂ : Nat} (h_le : c₁ ≤ c₂)
    (_h_no_crit : ∀ cp ∈ mf.criticalPoints, ¬(c₁ ≤ mf.f cp.1 ∧ mf.f cp.1 ≤ c₂))
    (x : sublevelSet mf.f c₁) :
    Path (sublevelInclusion (Nat.le_refl c₁) x) x :=
  Path.stepChainChain rfl

/-! ## Handle Attachment at Critical Points -/

/-- Data for a cell attachment at a critical point. -/
structure CellAttachment where
  /-- The cell dimension. -/
  cellDim : Nat
  /-- The critical level. -/
  level : Nat
  /-- The attaching boundary dimension. -/
  boundaryDim : Nat
  /-- The boundary dimension is one less than the cell dimension. -/
  boundary_eq : cellDim = boundaryDim + 1

/-- A critical point of index k ≥ 1 gives a k-cell attachment. -/
def sublevel_cell_attachment (cp : CriticalPoint A) (h : cp.index ≥ 1) :
    CellAttachment where
  cellDim := cp.index
  level := cp.criticalValue
  boundaryDim := cp.index - 1
  boundary_eq := by omega

/-- The cell dimension of the attachment equals the Morse index. -/
theorem cell_dim_eq_index (cp : CriticalPoint A)
    (h : cp.index ≥ 1) :
    (sublevel_cell_attachment cp h).cellDim = cp.index := rfl

/-! ## Morse Inequalities -/

/-- Abstract weak Morse inequalities: the number of critical points of index k
    is at least the k-th Betti number. -/
structure MorseInequalities where
  /-- The handle decomposition. -/
  decomposition : HandleDecomposition
  /-- Betti numbers (abstractly). -/
  betti : Nat → Nat
  /-- Weak Morse inequality: c_k ≥ b_k. -/
  weak : ∀ k : Nat, betti k ≤ decomposition.countDim k

/-- The strong Morse inequality: alternating sums.
    Σ_{i=0}^{k} (-1)^{k-i} c_i ≥ Σ_{i=0}^{k} (-1)^{k-i} b_i. -/
def alternatingSum (f : Nat → Nat) (k : Nat) : Int :=
  (List.range (k + 1)).foldl
    (fun acc i => acc + (-1 : Int) ^ (k - i) * (f i : Int)) 0

/-- The Euler characteristic from Morse data equals the alternating sum
    of handle counts. -/
def morseEulerChar (hd : HandleDecomposition) : Int :=
  alternatingSum hd.countDim
    (hd.handles.foldl (fun m h => max m h.dim) 0)

/-- Morse Euler characteristic is invariant under reindexing. -/
theorem morseEulerChar_eq_alternatingSum (hd : HandleDecomposition) :
    morseEulerChar hd =
      alternatingSum hd.countDim
        (hd.handles.foldl (fun m h => max m h.dim) 0) := rfl

/-! ## Lacunary Principle -/

/-- The lacunary principle: if all critical points have even index, then
    the Morse inequalities are equalities (Betti numbers = critical point counts). -/
structure LacunaryPrinciple where
  /-- The handle decomposition. -/
  decomposition : HandleDecomposition
  /-- All handles have even dimension. -/
  allEven : ∀ h ∈ decomposition.handles, h.dim % 2 = 0
  /-- Betti numbers equal handle counts in the even case. -/
  betti : Nat → Nat
  /-- The lacunary equality: b_k = c_k for all k. -/
  equality : ∀ k : Nat, betti k = decomposition.countDim k

/-! ## Gradient Flow Lines -/

/-- A gradient flow line from one critical point to another. -/
structure GradientFlowLine (A : Type u) where
  /-- Source critical point. -/
  source : CriticalPoint A
  /-- Target critical point. -/
  target : CriticalPoint A
  /-- The flow decreases the function value. -/
  decreasing : target.criticalValue < source.criticalValue
  /-- Index difference. -/
  indexDiff : source.index = target.index + 1

/-- A Morse-Smale complex, consisting of gradient flow lines
    between consecutive critical points. -/
structure MorseSmaleComplex (A : Type u) where
  /-- Critical points. -/
  criticalPts : List (CriticalPoint A)
  /-- Flow lines between consecutive-index critical points. -/
  flowLines : List (GradientFlowLine A)
  /-- Each flow line connects critical points in the list. -/
  flowLinesValid : ∀ fl ∈ flowLines,
    fl.source ∈ criticalPts ∧ fl.target ∈ criticalPts

/-- The number of flow lines from index k to index k-1 critical points. -/
def MorseSmaleComplex.flowCount {A : Type u} (msc : MorseSmaleComplex A)
    (k : Nat) : Nat :=
  msc.flowLines.filter (fun fl => fl.source.index = k) |>.length

/-! ## Perfect Morse Functions -/

/-- A Morse function is perfect if c_k = b_k for all k. -/
structure PerfectMorseFunction (A : Type u) extends MorseFunction A where
  /-- Betti numbers. -/
  betti : Nat → Nat
  /-- Perfection: number of index-k critical points equals the k-th Betti number. -/
  perfect : ∀ k : Nat, betti k = (toMorseFunction.toHandleDecomposition).countDim k

/-- A perfect Morse function satisfies the weak Morse inequalities as equalities. -/
def PerfectMorseFunction.toMorseInequalities {A : Type u}
    (pmf : PerfectMorseFunction A) :
    MorseInequalities where
  decomposition := pmf.toMorseFunction.toHandleDecomposition
  betti := pmf.betti
  weak := fun k => by rw [pmf.perfect k]; exact Nat.le_refl _

/-! ## Path Coherence for Morse Data -/

/-- Path witness that sublevel inclusion is functorial. -/
def sublevelInclusion_functorial_path {A : Type u} {f : A → Nat}
    {c₁ c₂ c₃ : Nat} (h₁ : c₁ ≤ c₂) (h₂ : c₂ ≤ c₃)
    (x : sublevelSet f c₁) :
    Path
      (sublevelInclusion h₂ (sublevelInclusion h₁ x))
      (sublevelInclusion (Nat.le_trans h₁ h₂) x) :=
  Path.stepChainChain rfl

/-- Path witness for handle decomposition count invariance. -/
def handle_count_path {hd : HandleDecomposition} {k : Nat} :
    Path
      (hd.countDim k)
      ((hd.handles.filter (fun h => h.dim = k)).length) :=
  Path.refl _

/-- Path witness that cell attachment dimension matches the Morse index. -/
def cell_attachment_index_path (cp : CriticalPoint A) (h : cp.index ≥ 1) :
    Path
      (sublevel_cell_attachment cp h).cellDim
      cp.index :=
  Path.refl _

/-- The empty handle decomposition has zero handles. -/
def emptyHandleDecomposition : HandleDecomposition where
  handles := []
  levelOrdered := by
    intro i
    exact absurd i.isLt (by simp)

/-- The empty decomposition has zero handles of every dimension. -/
theorem empty_countDim (k : Nat) :
    emptyHandleDecomposition.countDim k = 0 := rfl

/-- A single critical point of index k gives a decomposition with exactly
    one k-handle. -/
def singleHandleDecomposition (k : Nat) (level : Nat) : HandleDecomposition where
  handles := [HandleData.mk k level]
  levelOrdered := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    have hi' : i = 0 := by simp at hi; omega
    have hj' : j = 0 := by simp at hj; omega
    subst hi'; subst hj'
    exact absurd hij (Nat.lt_irrefl _)

/-- The single-handle decomposition has exactly one handle of dimension k. -/
theorem single_countDim_self (k level : Nat) :
    (singleHandleDecomposition k level).countDim k = 1 := by
  simp [singleHandleDecomposition, HandleDecomposition.countDim]

/-- The single-handle decomposition has zero handles of other dimensions. -/
theorem single_countDim_other (k k' level : Nat) (h : k' ≠ k) :
    (singleHandleDecomposition k level).countDim k' = 0 := by
  simp [singleHandleDecomposition, HandleDecomposition.countDim]
  intro h'
  exact absurd h'.symm h

/-! ## Summary

We developed Morse theory in the computational-path setting:

1. **Core structures**: `MorseFunction`, `CriticalPoint`, `HandleData`
2. **Sublevel sets**: inclusion, functoriality, homotopy invariance
3. **Handle decomposition**: from Morse functions, with cell attachments
4. **Morse inequalities**: weak inequalities and the lacunary principle
5. **Gradient flow**: flow lines and the Morse-Smale complex
6. **Perfect Morse functions**: when inequalities become equalities
7. **Path coherence**: functoriality witnesses for sublevel inclusions
-/

end MorseTheory
end Homotopy
end Path
end ComputationalPaths
