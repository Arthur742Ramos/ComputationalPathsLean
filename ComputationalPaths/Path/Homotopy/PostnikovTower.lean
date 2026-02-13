/-
# Postnikov Towers for Computational Paths

This module formalizes Postnikov towers by truncating the computational-path
infinity-groupoid tower at each level. The resulting stages retain all cells
up to level `n` and collapse higher cells to `PUnit`.

## Key Results

- `nTruncation` : the `n`-th Postnikov stage (an `n`-groupoid truncation)
- `postnikovTower` : the full tower of stages
- `tower_converges` : stages stabilize on any fixed dimension
- `stage_kills_next` : the next homotopy group is trivial at each stage

## References

- HoTT Book, Chapter 8 (Postnikov towers)
- Lumsdaine, "Weak omega-categories from intensional type theory"
-/

import ComputationalPaths.Path.InfinityGroupoid

namespace ComputationalPaths
namespace Path
namespace PostnikovTower

open InfinityGroupoid

universe u

/-! ## Postnikov stages and n-truncations -/

/-- The `n`-truncation (Postnikov stage) of the computational-path tower. -/
def nTruncation (A : Type u) (n : Nat) : NGroupoidTruncation A n :=
  compPathTruncation A n

/-- The Postnikov tower of computational paths, indexed by truncation level. -/
def postnikovTower (A : Type u) : (n : Nat) → NGroupoidTruncation A n :=
  truncationTower A

/-- Cells in stage `n` at dimension `k`. -/
abbrev stageCells (A : Type u) (n k : Nat) : Type u :=
  (nTruncation A n).cells k

/-! ## Convergence of the tower -/

/-- If `k ≤ n`, the `k`-cells in stage `n` agree with the full tower. -/
def stageCells_eq_of_le {A : Type u} {n k : Nat} (h : k ≤ n) :
    Path (stageCells A n k) (cellType A k) := by
  refine Path.stepChain ?_
  simp [stageCells, nTruncation, compPathTruncation, truncCell, h]

/-- Tower convergence: once `k` is below the stage, all later stages agree on `k`-cells. -/
def tower_converges {A : Type u} {k n m : Nat} (hkn : k ≤ n) (hnm : n ≤ m) :
    Path (stageCells A n k) (stageCells A m k) := by
  have hkm : k ≤ m := Nat.le_trans hkn hnm
  refine Path.stepChain ?_
  simp [stageCells, nTruncation, compPathTruncation, truncCell, hkn, hkm]

/-! ## Killing homotopy groups -/

/-- Cells above the truncation level are collapsed to `PUnit`. -/
def stageCells_eq_punit_of_lt {A : Type u} {n k : Nat} (h : n < k) :
    Path (stageCells A n k) PUnit := by
  have hk : ¬ k ≤ n := Nat.not_le_of_gt h
  refine Path.stepChain ?_
  simp [stageCells, nTruncation, compPathTruncation, truncCell, hk]

/-- Each stage kills the next homotopy group: `(n+1)`-cells are `PUnit`. -/
def stage_kills_next {A : Type u} (n : Nat) :
    Path (stageCells A n (n + 1)) PUnit := by
  exact stageCells_eq_punit_of_lt (A := A) (n := n) (k := n + 1) (Nat.lt_succ_self n)

/-! ## Summary

We define Postnikov stages as the canonical `n`-groupoid truncations of the
computational-path infinity groupoid. The tower converges because each fixed
dimension stabilizes once the truncation level is high enough, and each stage
collapses the next layer of cells to `PUnit`, mirroring the classical statement
that the next homotopy group vanishes.
-/

end PostnikovTower
end Path
end ComputationalPaths
