/-
# Infinite Combinatorics via Computational Paths

This module formalizes infinite combinatorics using computational paths:
Ramsey theory, partition calculus, trees, and well-quasi-orders.

## Key Results

| Definition/Theorem                 | Description                                |
|-----------------------------------|--------------------------------------------|
| `CombStep`                        | Rewrite steps for combinatorial operations |
| `Coloring` / `Monochromatic`     | k-colorings with Path witnesses             |
| `InfiniteSubset` / `InfiniteRamsey` | Infinite Ramsey data                    |
| `FiniteTree` / `TreeEmbed`       | Trees and embeddings for Kruskal           |
| `WellQuasiOrder`                  | WQO with Path coherences                   |

## References

- Graham, Rothschild, Spencer, "Ramsey Theory"
- Kruskal, "Well-quasi-ordering, the Tree Theorem"
-/

import ComputationalPaths.Path.Rewrite.RwEq
import Mathlib.Data.Fintype.Card

namespace ComputationalPaths
namespace Path
namespace Logic
namespace InfiniteCombinatrics

universe u

open ComputationalPaths.Path

/-! ## Rewrite Steps -/

inductive CombStep : Type 1
  | mono_restrict
  | color_exhaust
  | embed_trans
  | wqo_product
  | pigeonhole

/-! ## Colorings -/

structure Coloring (X : Type u) (k : Nat) where
  color : X → X → Fin k
  symmetric : (x y : X) → Path (color x y) (color y x)

structure Monochromatic {X : Type u} {k : Nat}
    (c : Coloring X k) (S : X → Prop) (col : Fin k) where
  mono_witness : (x y : X) → S x → S y → x ≠ y →
    Path (c.color x y) col

def Monochromatic.restrict {X : Type u} {k : Nat}
    {c : Coloring X k} {S : X → Prop} {col : Fin k}
    (m : Monochromatic c S col)
    (T : X → Prop) (hTS : ∀ x, T x → S x) :
    Monochromatic c T col where
  mono_witness := fun x y hx hy hne =>
    m.mono_witness x y (hTS x hx) (hTS y hy) hne

/-! ## Pigeonhole -/

/-- Pigeonhole principle (Path from statement to True). -/
def pigeonhole_path (n : Nat) (f : Fin (n + 1) → Fin n) (_ : 0 < n) :
    Path (∃ i j : Fin (n + 1), i ≠ j ∧ f i = f j : Prop) True :=
  Path.stepChain (by
    simp only [eq_iff_iff]
    exact ⟨fun _ => trivial, fun _ => by
      -- f cannot be injective: |Fin (n+1)| > |Fin n|
      exact Classical.byContradiction fun h => by
        have hinj : Function.Injective f := by
          intro i j hij
          exact Classical.byContradiction fun hne => h ⟨i, j, hne, hij⟩
        exact absurd (Fintype.card_le_of_injective f hinj) (by omega)⟩)

/-! ## Infinite Ramsey -/

structure InfiniteSubset where
  enum : Nat → Nat
  strict_mono : (i j : Nat) → i < j → enum i < enum j

structure InfiniteRamsey (k : Nat) where
  find_infinite_mono : (c : Coloring Nat k) →
    Σ' (col : Fin k) (S : InfiniteSubset),
      ∀ i j : Nat, i < j → Path (c.color (S.enum i) (S.enum j)) col

/-- Monochromatic color uniqueness via Path composition. -/
def mono_color_unique {k : Nat} (c : Coloring Nat k)
    (S : InfiniteSubset) (col₁ col₂ : Fin k)
    (h₁ : Path (c.color (S.enum 0) (S.enum 1)) col₁)
    (h₂ : Path (c.color (S.enum 0) (S.enum 1)) col₂) :
    Path col₁ col₂ :=
  Path.trans (Path.symm h₁) h₂

/-- RwEq: symm_symm on coloring. -/
noncomputable def mono_symm_rweq {k : Nat} (c : Coloring Nat k)
    (S : InfiniteSubset) (col : Fin k)
    (h : Path (c.color (S.enum 0) (S.enum 1)) col) :
    RwEq (Path.symm (Path.symm h)) h :=
  RwEq.step (Step.symm_symm _)

/-! ## Partition Regularity -/

structure PartitionRegular (X : Type u) where
  family : (X → Prop) → Prop
  regular : (k : Nat) → (color : X → Fin k) →
    Σ' (col : Fin k) (S : X → Prop),
      family S ∧ (∀ x, S x → color x = col)

/-! ## Trees -/

inductive FiniteTree (L : Type u) : Type u
  | leaf : L → FiniteTree L
  | node : L → List (FiniteTree L) → FiniteTree L

def FiniteTree.label {L : Type u} : FiniteTree L → L
  | FiniteTree.leaf l => l
  | FiniteTree.node l _ => l

def FiniteTree.size {L : Type u} : FiniteTree L → Nat
  | FiniteTree.leaf _ => 1
  | FiniteTree.node _ cs => 1 + cs.foldl (fun acc t => acc + t.size) 0

/-- Tree embedding (Prop: s can be embedded into t). -/
def TreeEmbed (L : Type u) (le : L → L → Prop)
    (s t : FiniteTree L) : Prop :=
  match s, t with
  | FiniteTree.leaf a, FiniteTree.leaf b => le a b
  | FiniteTree.leaf _, FiniteTree.node _ _ => True  -- simplified
  | FiniteTree.node _ _, FiniteTree.leaf _ => False
  | FiniteTree.node a _, FiniteTree.node b _ => le a b  -- simplified

def tree_leaf_refl (L : Type u) (le : L → L → Prop)
    (a : L) (hle : le a a) :
    TreeEmbed L le (FiniteTree.leaf a) (FiniteTree.leaf a) := by
  simp [TreeEmbed]; exact hle

/-! ## Well-Quasi-Orders -/

structure WellQuasiOrder (X : Type u) where
  le : X → X → Prop
  le_refl : (x : X) → le x x
  le_trans : (x y z : X) → le x y → le y z → le x z
  wqo : (f : Nat → X) → ∃ i j : Nat, i < j ∧ le (f i) (f j)

/-- WQO property as Path to True. -/
def wqo_path {X : Type u} (W : WellQuasiOrder X) (f : Nat → X) :
    Path (∃ i j : Nat, i < j ∧ W.le (f i) (f j) : Prop) True :=
  Path.stepChain (by simp only [eq_iff_iff]; exact ⟨fun _ => trivial, fun _ => W.wqo f⟩)

/-- WQO reflexive path. -/
def wqo_refl_path {X : Type u} (W : WellQuasiOrder X) (f : Nat → X) :
    Path (∃ i j : Nat, i < j ∧ W.le (f i) (f j) : Prop)
         (∃ i j : Nat, i < j ∧ W.le (f i) (f j) : Prop) :=
  Path.refl _

/-- Kruskal data. -/
structure KruskalData (L : Type u) where
  label_le : L → L → Prop
  label_wqo : WellQuasiOrder L
  tree_wqo : (f : Nat → FiniteTree L) →
    ∃ i j : Nat, i < j ∧ TreeEmbed L label_le (f i) (f j)

/-- Kruskal as Path to True. -/
def kruskal_path {L : Type u} (K : KruskalData L)
    (f : Nat → FiniteTree L) :
    Path (∃ i j, i < j ∧ TreeEmbed L K.label_le (f i) (f j) : Prop) True :=
  Path.stepChain (by simp only [eq_iff_iff]; exact ⟨fun _ => trivial, fun _ => K.tree_wqo f⟩)

/-- Ramsey multiplicity. -/
structure RamseyMultiplicity where
  n : Nat
  m : Nat
  count_lower_bound : Nat
  bound_witness : Path (count_lower_bound > 0 : Prop) True

/-! ## RwEq Coherences -/

noncomputable def restrict_rweq {X : Type u} {k : Nat}
    {c : Coloring X k} {S : X → Prop} {col : Fin k}
    (m : Monochromatic c S col) (T : X → Prop) (hTS : ∀ x, T x → S x)
    (x y : X) (hx : T x) (hy : T y) (hne : x ≠ y) :
    RwEq ((Monochromatic.restrict m T hTS).mono_witness x y hx hy hne)
         (m.mono_witness x y (hTS x hx) (hTS y hy) hne) :=
  RwEq.refl _

noncomputable def coloring_trans_refl_rweq {k : Nat} (c : Coloring Nat k)
    (S : InfiniteSubset) (col : Fin k)
    (h : Path (c.color (S.enum 0) (S.enum 1)) col) :
    RwEq (Path.trans (Path.refl _) h) h :=
  RwEq.step (Step.trans_refl_left _)

noncomputable def coloring_refl_trans_rweq {k : Nat} (c : Coloring Nat k)
    (S : InfiniteSubset) (col : Fin k)
    (h : Path (c.color (S.enum 0) (S.enum 1)) col) :
    RwEq (Path.trans h (Path.refl _)) h :=
  RwEq.step (Step.trans_refl_right _)

noncomputable def wqo_path_rweq {X : Type u} (W : WellQuasiOrder X) (f : Nat → X) :
    RwEq (wqo_path W f) (wqo_path W f) :=
  RwEq.refl _

noncomputable def kruskal_rweq {L : Type u} (K : KruskalData L)
    (f : Nat → FiniteTree L) :
    RwEq (kruskal_path K f) (kruskal_path K f) :=
  RwEq.refl _

end InfiniteCombinatrics
end Logic
end Path
end ComputationalPaths
