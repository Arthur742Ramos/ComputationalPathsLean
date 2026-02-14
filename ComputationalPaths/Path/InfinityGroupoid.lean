/-
# Infinity-Groupoid Approximation of Computational Paths

This module packages the omega-groupoid tower from `OmegaGroupoid` as an
explicit infinity-groupoid approximation and defines the tower of
n-groupoid truncations.

## Key Results

- `InfinityGroupoid`: tower of cells with coherence witnesses in every dimension
- `cellType`: alias to `OmegaGroupoid.CellType`
- `CoherenceAt` and `coherenceAt`: coherence witnesses per level
- `NGroupoidTruncation` and `truncationTower`: truncated towers of cells

## References

- Lumsdaine, "Weak omega-categories from intensional type theory" (2010)
- van den Berg & Garner, "Types are weak omega-groupoids" (2011)
-/

import ComputationalPaths.Path.OmegaGroupoid

namespace ComputationalPaths
namespace Path
namespace InfinityGroupoid

open OmegaGroupoid

universe u

variable {A : Type u}

/-! ## Cell tower and coherence -/

/-- The cell tower for the infinity-groupoid approximation. -/
abbrev cellType (A : Type u) : Nat → Type u :=
  OmegaGroupoid.CellType A

/-- Coherence at level `n`: any two parallel `n`-cells are connected by an
    `(n+1)`-cell in the tower. -/
def CoherenceAt (A : Type u) : Nat → Type u
  | 0 => PUnit
  | 1 => PUnit
  | 2 =>
      ∀ {a b : A} {p q : Path a b} (d1 d2 : Derivation₂ p q), Derivation₃ d1 d2
  | 3 =>
      ∀ {a b : A} {p q : Path a b} {d1 d2 : Derivation₂ p q}
        (m1 m2 : Derivation₃ d1 d2), Derivation₄ m1 m2
  | n + 4 =>
      ∀ {a b : A} {p q : Path a b} {d1 d2 : Derivation₂ p q}
        {m1 m2 : Derivation₃ d1 d2} (c1 c2 : Derivation₄ m1 m2),
        DerivationHigh n c1 c2

/-- Canonical coherence witnesses for the computational path tower. -/
def coherenceAt (A : Type u) : (n : Nat) → CoherenceAt (A := A) n
  | 0 => PUnit.unit
  | 1 => PUnit.unit
  | 2 => fun d1 d2 => contractibility₃ d1 d2
  | 3 => fun m1 m2 => contractibility₄ m1 m2
  | n + 4 => fun c1 c2 => contractibilityHigh n c1 c2

/-- An infinity-groupoid approximation on a type `A`. -/
structure InfinityGroupoid (A : Type u) where
  /-- Cells in each dimension. -/
  cells : Nat → Type u := cellType A
  /-- Coherence witnesses at each level. -/
  coherence : (n : Nat) → CoherenceAt (A := A) n

/-- The canonical infinity-groupoid approximation for computational paths. -/
def compPathInfinityGroupoid (A : Type u) : InfinityGroupoid A where
  cells := cellType A
  coherence := coherenceAt (A := A)

/-! ## n-groupoid truncations -/

/-- Cell tower truncated at level `n` (higher cells are collapsed to `PUnit`). -/
def truncCell (A : Type u) (n : Nat) : Nat → Type u
  | k => if k ≤ n then cellType A k else PUnit

/-- The `n`-groupoid truncation of the infinity-groupoid tower. -/
structure NGroupoidTruncation (A : Type u) (n : Nat) where
  /-- Cells in each dimension for the truncation. -/
  cells : Nat → Type u := truncCell A n
  /-- Coherence witness at the top level. -/
  coherence : CoherenceAt (A := A) n

/-- The canonical `n`-groupoid truncation for computational paths. -/
def compPathTruncation (A : Type u) (n : Nat) : NGroupoidTruncation A n where
  cells := truncCell A n
  coherence := coherenceAt (A := A) n

/-- The full tower of `n`-groupoid truncations. -/
def truncationTower (A : Type u) : (n : Nat) → NGroupoidTruncation A n :=
  fun n => compPathTruncation A n

/-! ## Truncation functoriality -/

/-- Below the truncation cutoff, truncated cells agree with the original cell tower. -/
theorem truncCell_eq_cellType_of_le (n k : Nat) (hk : k ≤ n) :
    truncCell A n k = cellType A k := by
  simp [truncCell, hk]

/-- Above the truncation cutoff, cells collapse to `PUnit`. -/
theorem truncCell_eq_punit_of_gt (n k : Nat) (hk : n < k) :
    truncCell A n k = PUnit := by
  have hnot : ¬ k ≤ n := Nat.not_le_of_gt hk
  simp [truncCell, hnot]

/-- Identity law for truncation functoriality. -/
theorem truncation_functorial_refl (n k : Nat) :
    truncCell A n k = truncCell A n k := rfl

/-- Functoriality along a single truncation map `n ≤ m`, below level `n`. -/
theorem truncation_functorial_step {n m k : Nat} (h : n ≤ m) (hk : k ≤ n) :
    truncCell A m k = truncCell A n k := by
  have hkm : k ≤ m := Nat.le_trans hk h
  simp [truncCell, hk, hkm]

/-- Functoriality is compositional along `n ≤ m ≤ l`, below level `n`. -/
theorem truncation_functorial_comp {n m l k : Nat}
    (h₁ : n ≤ m) (h₂ : m ≤ l) (hk : k ≤ n) :
    truncCell A l k = truncCell A n k := by
  have hkm : k ≤ m := Nat.le_trans hk h₁
  have hkl : k ≤ l := Nat.le_trans hkm h₂
  simp [truncCell, hk, hkl]

/-- Functoriality identifies truncated cells with the original tower on stable dimensions. -/
theorem truncation_functorial_to_cellType {n m k : Nat}
    (h : n ≤ m) (hk : k ≤ n) :
    truncCell A m k = cellType A k := by
  have hkm : k ≤ m := Nat.le_trans hk h
  simp [truncCell, hkm]

/-- If `k` is above a larger cutoff `m`, then all lower truncations also collapse at `k`. -/
theorem truncation_functorial_punit_of_gt {n m k : Nat}
    (h : n ≤ m) (hk : m < k) :
    truncCell A n k = PUnit :=
  truncCell_eq_punit_of_gt (A := A) n k (Nat.lt_of_le_of_lt h hk)

/-- Truncation functoriality on cells in the canonical truncation tower. -/
theorem truncationTower_cells_eq_of_le {n m k : Nat} (h : n ≤ m) (hk : k ≤ n) :
    (truncationTower A m).cells k = (truncationTower A n).cells k := by
  simpa [truncationTower, compPathTruncation] using
    truncation_functorial_step (A := A) h hk

/-! ## Kan fillers for the truncation tower -/

/-- Canonical Kan filler at truncation level `n`. -/
def truncationTowerKanFiller (n : Nat) : CoherenceAt (A := A) n :=
  (truncationTower A n).coherence

/-- The truncation tower carries canonical Kan fillers at every level. -/
theorem truncationTower_kan_condition (n : Nat) :
    Nonempty (CoherenceAt (A := A) n) :=
  ⟨truncationTowerKanFiller (A := A) n⟩

/-- The tower Kan filler is definitionally the canonical coherence witness. -/
theorem truncationTowerKanFiller_eq_coherenceAt (n : Nat) :
    truncationTowerKanFiller (A := A) n = coherenceAt (A := A) n := by
  rfl

/-- The Kan condition is stable under successor levels in the truncation tower. -/
theorem truncationTower_kan_condition_succ (n : Nat) :
    Nonempty (CoherenceAt (A := A) (n + 1)) :=
  truncationTower_kan_condition (A := A) (n + 1)

/-- Level-2 Kan fillers in the truncation tower. -/
theorem truncationTower_kan₂ {a b : A} {p q : Path a b}
    (d₁ d₂ : Derivation₂ p q) :
    Nonempty (Derivation₃ d₁ d₂) :=
  ⟨truncationTowerKanFiller (A := A) 2 d₁ d₂⟩

/-- Level-3 Kan fillers in the truncation tower. -/
theorem truncationTower_kan₃ {a b : A} {p q : Path a b} {d₁ d₂ : Derivation₂ p q}
    (m₁ m₂ : Derivation₃ d₁ d₂) :
    Nonempty (Derivation₄ m₁ m₂) :=
  ⟨truncationTowerKanFiller (A := A) 3 m₁ m₂⟩

/-- Higher Kan fillers in the truncation tower. -/
theorem truncationTower_kan_high (n : Nat)
    {a b : A} {p q : Path a b} {d₁ d₂ : Derivation₂ p q} {m₁ m₂ : Derivation₃ d₁ d₂}
    (c₁ c₂ : Derivation₄ m₁ m₂) :
    Nonempty (DerivationHigh n c₁ c₂) :=
  ⟨truncationTowerKanFiller (A := A) (n + 4) c₁ c₂⟩

/-! ## Adjacent truncation levels -/

/-- Adjacent truncation levels agree on all cell dimensions `k ≤ n`. -/
theorem adjacent_truncCell_eq {n k : Nat} (hk : k ≤ n) :
    truncCell A n k = truncCell A (n + 1) k := by
  have hk' : k ≤ n + 1 := Nat.le_trans hk (Nat.le_succ n)
  simp [truncCell, hk, hk']

/-- Adjacent truncation levels are equivalent on all dimensions `k ≤ n`. -/
theorem adjacent_truncCell_equivalent {n k : Nat} (hk : k ≤ n) :
    truncCell A n k = truncCell A (n + 1) k :=
  adjacent_truncCell_eq (A := A) hk

/-- The canonical truncation tower agrees on adjacent levels below the lower cutoff. -/
theorem adjacent_truncations_agree_on_cells {n k : Nat} (hk : k ≤ n) :
    (truncationTower A n).cells k = (truncationTower A (n + 1)).cells k := by
  simpa [truncationTower, compPathTruncation] using adjacent_truncCell_eq (A := A) hk

/-- Adjacent truncation levels are equivalent as types below the lower cutoff. -/
theorem adjacent_truncCell_equiv {n k : Nat} (hk : k ≤ n) :
    Nonempty (truncCell A n k → truncCell A (n + 1) k) ∧
      Nonempty (truncCell A (n + 1) k → truncCell A n k) := by
  let e : truncCell A n k = truncCell A (n + 1) k :=
    adjacent_truncCell_eq (A := A) hk
  exact ⟨⟨Eq.mp e⟩, ⟨Eq.mp e.symm⟩⟩

/-- Adjacent tower levels are equivalent on stable cell dimensions. -/
theorem adjacent_truncations_cells_equiv {n k : Nat} (hk : k ≤ n) :
    Nonempty ((truncationTower A n).cells k → (truncationTower A (n + 1)).cells k) ∧
      Nonempty ((truncationTower A (n + 1)).cells k → (truncationTower A n).cells k) := by
  simpa [truncationTower, compPathTruncation] using adjacent_truncCell_equiv (A := A) hk

/-! ## Coherence interchange laws -/

/-- Canonical interchange witness. -/
def coherenceInterchange
    {a b c : A} {f f' : Path a b} {g g' : Path b c}
    (α : Derivation₂ f f') (β : Derivation₂ g g') :
    Derivation₃
      (Derivation₂.vcomp (whiskerRight α g) (whiskerLeft f' β))
      (Derivation₂.vcomp (whiskerLeft f β) (whiskerRight α g')) :=
  .step (.interchange α β)

/-- Interchange coherence between horizontal and vertical composition of 2-cells. -/
theorem coherence_interchange_law
    {a b c : A} {f f' : Path a b} {g g' : Path b c}
    (α : Derivation₂ f f') (β : Derivation₂ g g') :
    Nonempty
      (Derivation₃
        (Derivation₂.vcomp (whiskerRight α g) (whiskerLeft f' β))
        (Derivation₂.vcomp (whiskerLeft f β) (whiskerRight α g'))) :=
  ⟨coherenceInterchange (A := A) α β⟩

/-- Symmetric interchange coherence. -/
theorem coherence_interchange_law_symm
    {a b c : A} {f f' : Path a b} {g g' : Path b c}
    (α : Derivation₂ f f') (β : Derivation₂ g g') :
    Nonempty
      (Derivation₃
        (Derivation₂.vcomp (whiskerLeft f β) (whiskerRight α g'))
        (Derivation₂.vcomp (whiskerRight α g) (whiskerLeft f' β))) :=
  ⟨.inv (coherenceInterchange (A := A) α β)⟩

/-- Interchange in horizontal-composition form. -/
theorem coherence_interchange_hcomp
    {a b c : A} {f f' : Path a b} {g g' : Path b c}
    (α : Derivation₂ f f') (β : Derivation₂ g g') :
    Nonempty
      (Derivation₃
        (hcomp α β)
        (Derivation₂.vcomp (whiskerLeft f β) (whiskerRight α g'))) := by
  simpa [hcomp] using coherence_interchange_law (A := A) α β

/-- Symmetric interchange in horizontal-composition form. -/
theorem coherence_interchange_hcomp_symm
    {a b c : A} {f f' : Path a b} {g g' : Path b c}
    (α : Derivation₂ f f') (β : Derivation₂ g g') :
    Nonempty
      (Derivation₃
        (Derivation₂.vcomp (whiskerLeft f β) (whiskerRight α g'))
        (hcomp α β)) := by
  simpa [hcomp] using coherence_interchange_law_symm (A := A) α β

/-- Any interchange witness is coherently connected to the canonical one. -/
theorem coherence_interchange_contractible
    {a b c : A} {f f' : Path a b} {g g' : Path b c}
    (α : Derivation₂ f f') (β : Derivation₂ g g')
    (m :
      Derivation₃
        (Derivation₂.vcomp (whiskerRight α g) (whiskerLeft f' β))
        (Derivation₂.vcomp (whiskerLeft f β) (whiskerRight α g'))) :
    Nonempty (Derivation₄ m (coherenceInterchange (A := A) α β)) :=
  ⟨contractibility₄ m (coherenceInterchange (A := A) α β)⟩

/-- Any two interchange witnesses are connected by a canonical 4-cell. -/
theorem coherence_interchange_connected
    {a b c : A} {f f' : Path a b} {g g' : Path b c}
    (α : Derivation₂ f f') (β : Derivation₂ g g')
    (m₁ m₂ :
      Derivation₃
        (Derivation₂.vcomp (whiskerRight α g) (whiskerLeft f' β))
        (Derivation₂.vcomp (whiskerLeft f β) (whiskerRight α g'))) :
    Nonempty (Derivation₄ m₁ m₂) :=
  ⟨contractibility₄ m₁ m₂⟩

/-! ## Summary -/

/-!
We expose the omega-groupoid tower from `OmegaGroupoid` as an explicit
infinity-groupoid approximation, define a tower of `n`-groupoid truncations,
and package canonical coherence witnesses at each level.
-/

end InfinityGroupoid
end Path
end ComputationalPaths
