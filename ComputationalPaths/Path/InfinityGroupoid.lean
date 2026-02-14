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

/-- At stable dimensions, tower cells agree with the original cell type. -/
theorem truncationTower_cells_eq_cellType_of_le {n k : Nat} (hk : k ≤ n) :
    (truncationTower A n).cells k = cellType A k := by
  simpa [truncationTower, compPathTruncation] using
    truncCell_eq_cellType_of_le (A := A) n k hk

/-- Above the truncation cutoff, tower cells collapse to `PUnit`. -/
theorem truncationTower_cells_eq_punit_of_gt {n k : Nat} (hk : n < k) :
    (truncationTower A n).cells k = PUnit := by
  simpa [truncationTower, compPathTruncation] using
    truncCell_eq_punit_of_gt (A := A) n k hk

/-- Functoriality along `n ≤ m ≤ l` identifies levels `m` and `l` below `n`. -/
theorem truncation_functorial_middle {n m l k : Nat}
    (h₁ : n ≤ m) (h₂ : m ≤ l) (hk : k ≤ n) :
    truncCell A l k = truncCell A m k := by
  have hkm : k ≤ m := Nat.le_trans hk h₁
  have hkl : k ≤ l := Nat.le_trans hkm h₂
  simp [truncCell, hkm, hkl]

/-- Functoriality along `n ≤ m` is invertible below level `n`. -/
theorem truncation_functorial_step_symm {n m k : Nat} (h : n ≤ m) (hk : k ≤ n) :
    truncCell A n k = truncCell A m k :=
  (truncation_functorial_step (A := A) h hk).symm

/-- Middle-level functoriality is invertible on stable dimensions. -/
theorem truncation_functorial_middle_symm {n m l k : Nat}
    (h₁ : n ≤ m) (h₂ : m ≤ l) (hk : k ≤ n) :
    truncCell A m k = truncCell A l k :=
  (truncation_functorial_middle (A := A) h₁ h₂ hk).symm

/-- Tower-level functoriality along `n ≤ m` is invertible on stable dimensions. -/
theorem truncationTower_cells_eq_of_le_symm {n m k : Nat} (h : n ≤ m) (hk : k ≤ n) :
    (truncationTower A n).cells k = (truncationTower A m).cells k :=
  (truncationTower_cells_eq_of_le (A := A) h hk).symm

/-- Truncating exactly at level `n` preserves the `n`-cells. -/
theorem truncCell_eq_cellType_self (n : Nat) :
    truncCell A n n = cellType A n :=
  truncCell_eq_cellType_of_le (A := A) n n (Nat.le_refl n)

/-- At successor dimension, the `n`-truncation has already collapsed to `PUnit`. -/
theorem truncCell_eq_punit_succ (n : Nat) :
    truncCell A n (n + 1) = PUnit :=
  truncCell_eq_punit_of_gt (A := A) n (n + 1) (Nat.lt_succ_self n)

/-- In the truncation tower, `n`-cells at level `n` agree with the original cell tower. -/
theorem truncationTower_cells_eq_cellType_self (n : Nat) :
    (truncationTower A n).cells n = cellType A n := by
  simpa using
    truncationTower_cells_eq_cellType_of_le (A := A) (n := n) (k := n) (Nat.le_refl n)

/-- In the truncation tower, cells at level `n+1` are collapsed at stage `n`. -/
theorem truncationTower_cells_eq_punit_succ (n : Nat) :
    (truncationTower A n).cells (n + 1) = PUnit := by
  simpa using
    truncationTower_cells_eq_punit_of_gt (A := A) (n := n) (k := n + 1) (Nat.lt_succ_self n)

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

/-- The tower Kan filler is definitionally the truncation coherence field. -/
theorem truncationTowerKanFiller_eq_tower_coherence (n : Nat) :
    truncationTowerKanFiller (A := A) n = (truncationTower A n).coherence := by
  rfl

/-- Kan fillers exist uniformly at every truncation level. -/
theorem truncationTower_kan_condition_all :
    ∀ n : Nat, Nonempty (CoherenceAt (A := A) n) :=
  fun n => truncationTower_kan_condition (A := A) n

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

/-- The canonical infinity-groupoid satisfies the Kan condition in every dimension. -/
theorem compPathInfinityGroupoid_kan_condition (n : Nat) :
    Nonempty (CoherenceAt (A := A) n) :=
  ⟨(compPathInfinityGroupoid A).coherence n⟩

/-- Every level-2 filler is connected to the canonical tower filler by a 4-cell. -/
theorem truncationTower_kan₂_connected_to_canonical {a b : A} {p q : Path a b}
    (d₁ d₂ : Derivation₂ p q) (m : Derivation₃ d₁ d₂) :
    Nonempty (Derivation₄ m (truncationTowerKanFiller (A := A) 2 d₁ d₂)) :=
  ⟨contractibility₄ m (truncationTowerKanFiller (A := A) 2 d₁ d₂)⟩

/-- Every level-3 filler is connected to the canonical tower filler by a higher cell. -/
theorem truncationTower_kan₃_connected_to_canonical {a b : A} {p q : Path a b}
    {d₁ d₂ : Derivation₂ p q} (m₁ m₂ : Derivation₃ d₁ d₂)
    (c : Derivation₄ m₁ m₂) :
    Nonempty (DerivationHigh 0 c (truncationTowerKanFiller (A := A) 3 m₁ m₂)) :=
  ⟨contractibilityHigh 0 c (truncationTowerKanFiller (A := A) 3 m₁ m₂)⟩

/-- The canonical level-2 Kan filler is coherently reflexive. -/
theorem truncationTower_kan₂_canonical_reflexive {a b : A} {p q : Path a b}
    (d₁ d₂ : Derivation₂ p q) :
    Nonempty
      (Derivation₄
        (truncationTowerKanFiller (A := A) 2 d₁ d₂)
        (truncationTowerKanFiller (A := A) 2 d₁ d₂)) :=
  ⟨Derivation₄.refl (truncationTowerKanFiller (A := A) 2 d₁ d₂)⟩

/-- The canonical level-3 Kan filler is coherently reflexive at higher level. -/
theorem truncationTower_kan₃_canonical_reflexive {a b : A} {p q : Path a b}
    {d₁ d₂ : Derivation₂ p q} (m₁ m₂ : Derivation₃ d₁ d₂) :
    Nonempty
      (DerivationHigh 0
        (truncationTowerKanFiller (A := A) 3 m₁ m₂)
        (truncationTowerKanFiller (A := A) 3 m₁ m₂)) :=
  ⟨DerivationHigh.refl (truncationTowerKanFiller (A := A) 3 m₁ m₂)⟩

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

/-- Adjacent-level stability identifies the lower truncation with the original cell tower. -/
theorem adjacent_truncCell_eq_cellType {n k : Nat} (hk : k ≤ n) :
    truncCell A n k = cellType A k :=
  truncCell_eq_cellType_of_le (A := A) n k hk

/-- Adjacent-level stability also identifies the successor truncation with the original cells. -/
theorem adjacent_truncCell_succ_eq_cellType {n k : Nat} (hk : k ≤ n) :
    truncCell A (n + 1) k = cellType A k := by
  have hk' : k ≤ n + 1 := Nat.le_trans hk (Nat.le_succ n)
  simpa using truncCell_eq_cellType_of_le (A := A) (n := n + 1) (k := k) hk'

/-- Adjacent-level agreement can be obtained by comparison through `cellType`. -/
theorem adjacent_truncCell_eq_via_cellType {n k : Nat} (hk : k ≤ n) :
    truncCell A n k = truncCell A (n + 1) k := by
  calc
    truncCell A n k = cellType A k := adjacent_truncCell_eq_cellType (A := A) hk
    _ = truncCell A (n + 1) k := (adjacent_truncCell_succ_eq_cellType (A := A) hk).symm

/-- The lower adjacent truncation level is equivalent to `cellType` on stable dimensions. -/
theorem adjacent_truncCell_equiv_cellType {n k : Nat} (hk : k ≤ n) :
    Nonempty (truncCell A n k → cellType A k) ∧
      Nonempty (cellType A k → truncCell A n k) := by
  let e : truncCell A n k = cellType A k := adjacent_truncCell_eq_cellType (A := A) hk
  exact ⟨⟨Eq.mp e⟩, ⟨Eq.mp e.symm⟩⟩

/-- The successor adjacent truncation level is equivalent to `cellType` on stable dimensions. -/
theorem adjacent_truncCell_succ_equiv_cellType {n k : Nat} (hk : k ≤ n) :
    Nonempty (truncCell A (n + 1) k → cellType A k) ∧
      Nonempty (cellType A k → truncCell A (n + 1) k) := by
  let e : truncCell A (n + 1) k = cellType A k :=
    adjacent_truncCell_succ_eq_cellType (A := A) hk
  exact ⟨⟨Eq.mp e⟩, ⟨Eq.mp e.symm⟩⟩

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

/-- Interchange in horizontal-composition form has a canonical witness. -/
theorem coherenceInterchange_hcomp_form
    {a b c : A} {f f' : Path a b} {g g' : Path b c}
    (α : Derivation₂ f f') (β : Derivation₂ g g') :
    Nonempty
      (Derivation₃
        (hcomp α β)
        (Derivation₂.vcomp (whiskerLeft f β) (whiskerRight α g'))) := by
  exact ⟨by simpa [hcomp] using coherenceInterchange (A := A) α β⟩

/-- Symmetric interchange in horizontal-composition form has a canonical witness. -/
theorem coherenceInterchange_hcomp_form_symm
    {a b c : A} {f f' : Path a b} {g g' : Path b c}
    (α : Derivation₂ f f') (β : Derivation₂ g g') :
    Nonempty
      (Derivation₃
        (Derivation₂.vcomp (whiskerLeft f β) (whiskerRight α g'))
        (hcomp α β)) := by
  rcases coherenceInterchange_hcomp_form (A := A) α β with ⟨m⟩
  exact ⟨.inv m⟩

/-- Any two horizontal-form interchange witnesses are connected by a 4-cell. -/
theorem coherence_interchange_hcomp_connected
    {a b c : A} {f f' : Path a b} {g g' : Path b c}
    (α : Derivation₂ f f') (β : Derivation₂ g g')
    (m₁ m₂ :
      Derivation₃
        (hcomp α β)
        (Derivation₂.vcomp (whiskerLeft f β) (whiskerRight α g'))) :
    Nonempty (Derivation₄ m₁ m₂) :=
  ⟨contractibility₄ m₁ m₂⟩

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

/-- Interchange connectivity is symmetric. -/
theorem coherence_interchange_connected_symm
    {a b c : A} {f f' : Path a b} {g g' : Path b c}
    (α : Derivation₂ f f') (β : Derivation₂ g g')
    (m₁ m₂ :
      Derivation₃
        (Derivation₂.vcomp (whiskerRight α g) (whiskerLeft f' β))
        (Derivation₂.vcomp (whiskerLeft f β) (whiskerRight α g'))) :
    Nonempty (Derivation₄ m₂ m₁) := by
  rcases coherence_interchange_connected (A := A) α β m₁ m₂ with ⟨c⟩
  exact ⟨Derivation₄.inv c⟩

/-- The canonical interchange witness is connected to itself by reflexivity. -/
theorem coherenceInterchange_self_connected
    {a b c : A} {f f' : Path a b} {g g' : Path b c}
    (α : Derivation₂ f f') (β : Derivation₂ g g') :
    Nonempty
      (Derivation₄
        (coherenceInterchange (A := A) α β)
        (coherenceInterchange (A := A) α β)) :=
  ⟨Derivation₄.refl (coherenceInterchange (A := A) α β)⟩

/-- The canonical interchange witness is coherently connected to its inverse. -/
theorem coherenceInterchange_connected_to_inverse
    {a b c : A} {f f' : Path a b} {g g' : Path b c}
    (α : Derivation₂ f f') (β : Derivation₂ g g') :
    Nonempty
      (Derivation₄
        (coherenceInterchange (A := A) α β)
        (Derivation₃.inv (coherenceInterchange (A := A) α β))) :=
  ⟨contractibility₄ _ _⟩

/-- Any horizontal-form interchange witness is connected to the canonical one. -/
theorem coherence_interchange_hcomp_contractible
    {a b c : A} {f f' : Path a b} {g g' : Path b c}
    (α : Derivation₂ f f') (β : Derivation₂ g g')
    (m :
      Derivation₃
        (hcomp α β)
        (Derivation₂.vcomp (whiskerLeft f β) (whiskerRight α g'))) :
    Nonempty
      (Derivation₄ m (by simpa [hcomp] using coherenceInterchange (A := A) α β)) := by
  refine ⟨contractibility₄ m ?_⟩
  simpa [hcomp] using coherenceInterchange (A := A) α β

/-! ## Summary -/

/-!
We expose the omega-groupoid tower from `OmegaGroupoid` as an explicit
infinity-groupoid approximation, define a tower of `n`-groupoid truncations,
and package canonical coherence witnesses at each level.
-/

end InfinityGroupoid
end Path
end ComputationalPaths
