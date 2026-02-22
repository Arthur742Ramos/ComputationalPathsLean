/-
# Descriptive Set Theory via Computational Paths

This module formalizes descriptive set theory concepts using computational
paths: the Borel hierarchy, analytic and coanalytic sets, Suslin's theorem,
Polish space structure, and the Wadge hierarchy with Path coherences.

## Mathematical Background

Descriptive set theory studies definable subsets of Polish spaces. The Borel
hierarchy stratifies sets by complexity. Analytic sets (Σ¹₁) are continuous
images of Borel sets; Suslin's theorem states that a set both analytic and
coanalytic is Borel.

## Key Results

| Definition/Theorem                | Description                                  |
|----------------------------------|----------------------------------------------|
| `DSTStep`                        | Rewrite steps for descriptive set operations |
| `BorelSet`                       | Borel hierarchy with Path witnesses          |
| `AnalyticSet` / `CoanalyticSet` | Projective hierarchy                          |
| `SuslinWitness`                  | Suslin's theorem data                        |
| `PolishSpace`                    | Polish space structure with Paths            |
| `WadgeReducible`                 | Wadge hierarchy with Path witnesses          |
| `BaireCategoryData`              | Baire category theorem data                  |

## References

- Kechris, "Classical Descriptive Set Theory"
- Moschovakis, "Descriptive Set Theory"
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Logic
namespace DescriptiveSetTheory

universe u

open ComputationalPaths.Path

/-! ## Rewrite Steps -/

/-- Elementary rewrite steps for descriptive set theory. -/
inductive DSTStep : Type 1
  | compl_compl
  | de_morgan_union
  | de_morgan_inter
  | sigma_closure
  | pi_closure
  | borel_union
  | borel_complement
  | analytic_union

/-! ## Topology -/

/-- A topological space. -/
structure TopologyData (X : Type u) where
  isOpen : (X → Prop) → Prop
  open_univ : isOpen (fun _ => True)
  open_empty : isOpen (fun _ => False)
  open_inter : (U V : X → Prop) → isOpen U → isOpen V →
    isOpen (fun x => U x ∧ V x)

/-- A set is closed when its complement is open. -/
def isClosed {X : Type u} (τ : TopologyData X) (C : X → Prop) : Prop :=
  τ.isOpen (fun x => ¬ C x)

/-! ## Borel Hierarchy -/

/-- Level in the Borel hierarchy. -/
inductive BorelLevel
  | zero : BorelLevel
  | succ : BorelLevel → BorelLevel
  | limit : (Nat → BorelLevel) → BorelLevel

/-- A Borel set at a given level. -/
inductive BorelSet (X : Type u) (τ : TopologyData X) :
    BorelLevel → (X → Prop) → Prop
  | open_set (S : X → Prop) (h : τ.isOpen S) :
    BorelSet X τ BorelLevel.zero S
  | complement (α : BorelLevel) (S : X → Prop) (h : BorelSet X τ α S) :
    BorelSet X τ (BorelLevel.succ α) (fun x => ¬ S x)
  | countable_union (α : BorelLevel) (S : Nat → X → Prop)
    (h : ∀ n, BorelSet X τ α (S n)) :
    BorelSet X τ (BorelLevel.succ α) (fun x => ∃ n, S n x)
  | monotone (α β : BorelLevel) (S : X → Prop) (h : BorelSet X τ α S) :
    BorelSet X τ (BorelLevel.succ β) S

/-- Σ⁰₁ (open sets). -/
def Sigma01 (X : Type u) (τ : TopologyData X) (S : X → Prop) : Prop :=
  BorelSet X τ BorelLevel.zero S

/-- Π⁰₁ (closed sets). -/
def Pi01 (X : Type u) (τ : TopologyData X) (S : X → Prop) : Prop :=
  ∃ U : X → Prop, Sigma01 X τ U ∧ S = fun x => ¬ U x

/-- Σ⁰₂ (Fσ sets). -/
def Sigma02 (X : Type u) (τ : TopologyData X) (S : X → Prop) : Prop :=
  BorelSet X τ (BorelLevel.succ BorelLevel.zero) S

/-- Complement of open is Π⁰₁. -/
theorem complement_of_open_is_pi01 {X : Type u} (τ : TopologyData X)
    (S : X → Prop) (hS : Sigma01 X τ S) :
    Pi01 X τ (fun x => ¬ S x) :=
  ⟨S, hS, rfl⟩

/-- Borel set at level α is also at level succ β (via monotonicity). -/
theorem borel_lift {X : Type u} {τ : TopologyData X}
    {α β : BorelLevel} {S : X → Prop}
    (h : BorelSet X τ α S) :
    BorelSet X τ (BorelLevel.succ β) S :=
  BorelSet.monotone α β S h

/-! ## Analytic and Coanalytic Sets -/

/-- A tree on natural numbers. -/
structure NatTree where
  mem : List Nat → Prop
  closed_prefix : (s t : List Nat) → mem (s ++ t) → mem s

/-- An infinite branch through a tree. -/
structure InfiniteBranch (T : NatTree) where
  branch : Nat → Nat
  in_tree : (n : Nat) → T.mem (List.ofFn (fun i : Fin n => branch i))

/-- An analytic (Σ¹₁) set. -/
structure AnalyticSet (X : Type u) where
  pred : X → Prop
  tree : X → NatTree
  analytic_witness : (x : X) → Path (pred x : Prop)
    (Nonempty (InfiniteBranch (tree x)) : Prop)

/-- A coanalytic (Π¹₁) set. -/
structure CoanalyticSet (X : Type u) where
  complement_of : AnalyticSet X
  pred : X → Prop
  is_complement : (x : X) → Path (pred x : Prop)
    (¬ complement_of.pred x : Prop)

/-- RwEq: analytic witness is self-consistent. -/
noncomputable def analytic_rweq {X : Type u} (A : AnalyticSet X) (x : X) :
    RwEq (A.analytic_witness x) (A.analytic_witness x) :=
  RwEq.refl _

/-- RwEq: symm(symm(is_complement)) simplifies. -/
noncomputable def coanalytic_symm_rweq {X : Type u} (C : CoanalyticSet X) (x : X) :
    RwEq (Path.symm (Path.symm (C.is_complement x)))
         (C.is_complement x) :=
  RwEq.step (Step.symm_symm _)

/-! ## Suslin's Theorem -/

/-- Suslin's theorem data. -/
structure SuslinWitness (X : Type u) (τ : TopologyData X) where
  S : X → Prop
  is_analytic : AnalyticSet X
  is_coanalytic : CoanalyticSet X
  analytic_eq : (x : X) → Path (is_analytic.pred x : Prop) (S x : Prop)
  coanalytic_eq : (x : X) → Path (is_coanalytic.pred x : Prop) (¬ S x : Prop)
  borel_level : BorelLevel
  borel_membership : BorelSet X τ borel_level S

/-- Complementarity: compose analytic_eq and coanalytic_eq. -/
def suslin_complementarity_path {X : Type u} {τ : TopologyData X}
    (sw : SuslinWitness X τ) (x : X) :
    Path (sw.is_analytic.pred x : Prop) (¬ sw.is_coanalytic.pred x : Prop) :=
  -- analytic_eq : pred x = S x
  -- coanalytic_eq : co_pred x = ¬ S x
  -- so: analytic_pred x = S x, coanalytic_pred x = ¬ S x
  -- want: analytic_pred x = ¬ coanalytic_pred x
  -- i.e. S x = ¬ (¬ S x) = S x  — but that's classical
  -- We use Path.trans through S x
  Path.stepChain (by
    have h₁ := (sw.analytic_eq x).proof
    have h₂ := (sw.coanalytic_eq x).proof
    rw [h₁, h₂]
    simp only [eq_iff_iff]
    exact ⟨fun h => fun hns => hns h, fun h => Classical.byContradiction h⟩)

/-! ## Polish Spaces -/

/-- A Polish space: completely metrizable, separable. -/
structure PolishSpace (X : Type u) extends TopologyData X where
  dense_seq : Nat → X
  density : (U : X → Prop) → isOpen U → (∃ x, U x) → ∃ n, U (dense_seq n)
  complete : (s : Nat → X) → (modulus : Nat → Nat) → X

/-- Density as a Path from the density statement to True. -/
def density_path {X : Type u} (P : PolishSpace X)
    (U : X → Prop) (hU : P.isOpen U) (hne : ∃ x, U x) :
    Path (∃ n, U (P.dense_seq n) : Prop) True :=
  Path.stepChain (by
    simp only [eq_iff_iff]
    exact ⟨fun _ => trivial, fun _ => P.density U hU hne⟩)

/-! ## Baire Space Topology -/

/-- The Baire space ℕ^ℕ topology. -/
def BaireTopology : TopologyData (Nat → Nat) where
  isOpen := fun U => ∀ f, U f → ∃ n, ∀ g, (∀ i, i < n → f i = g i) → U g
  open_univ := fun _ _ => ⟨0, fun _ _ => trivial⟩
  open_empty := fun _ h => False.elim h
  open_inter := fun U V hU hV f ⟨hu, hv⟩ => by
    obtain ⟨n₁, hn₁⟩ := hU f hu
    obtain ⟨n₂, hn₂⟩ := hV f hv
    exact ⟨Nat.max n₁ n₂, fun g hg =>
      ⟨hn₁ g (fun i hi => hg i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))),
       hn₂ g (fun i hi => hg i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _)))⟩⟩

/-- The Cantor space 2^ℕ embeds into Baire space. -/
def CantorToBaire : (Nat → Bool) → (Nat → Nat) :=
  fun f n => if f n then 1 else 0

/-- Path: Cantor embedding definition. -/
def cantor_baire_path (f : Nat → Bool) (n : Nat) :
    Path (CantorToBaire f n) (if f n then 1 else 0) :=
  Path.refl _

/-! ## Baire Category -/

/-- A set is nowhere dense. -/
structure NowhereDense (X : Type u) (τ : TopologyData X) where
  S : X → Prop
  witness : (U : X → Prop) → τ.isOpen U → (∃ x, U x) →
    ∃ V : X → Prop, τ.isOpen V ∧ (∀ x, V x → U x) ∧ (∀ x, V x → ¬ S x)

/-- A set is meager (first category). -/
structure Meager (X : Type u) (τ : TopologyData X) where
  S : X → Prop
  pieces : Nat → NowhereDense X τ
  is_union : (x : X) → Path (S x : Prop) (∃ n, (pieces n).S x : Prop)

/-- Baire category theorem data. -/
structure BaireCategoryData (X : Type u) (P : PolishSpace X) where
  dense_Gδ : (U : Nat → X → Prop) →
    (∀ n, P.isOpen (U n)) →
    (∀ n, ∃ x, U n x) →
    Path (∀ V, P.isOpen V → (∃ x, V x) → ∃ x, V x ∧ ∀ n, U n x : Prop) True

/-! ## Perfect Set Property -/

/-- Perfect set property data. -/
structure PerfectSetProperty (X : Type u) (τ : TopologyData X) where
  S : X → Prop
  isCountable : Option (Σ' (enum : X → Nat),
    ∀ x y, S x → S y → enum x = enum y → Path x y)
  hasPerfect : Option (Σ' (embed : (Nat → Bool) → X), ∀ f, S (embed f))

/-- RwEq: perfect set is self-consistent. -/
noncomputable def perfect_set_rweq {X : Type u} {τ : TopologyData X}
    (psp : PerfectSetProperty X τ) :
    RwEq (Path.refl (psp.S : X → Prop)) (Path.refl psp.S) :=
  RwEq.refl _

/-! ## Wadge Hierarchy -/

/-- Wadge reducibility: A ≤_W B via a continuous reduction. -/
structure WadgeReducible (X : Type u) (τ : TopologyData X)
    (A B : X → Prop) where
  reduce : X → X
  reduces : (x : X) → Path (A x : Prop) (B (reduce x) : Prop)

/-- Wadge reducibility is reflexive. -/
def WadgeReducible.refl_wadge {X : Type u} (τ : TopologyData X)
    (A : X → Prop) : WadgeReducible X τ A A where
  reduce := id
  reduces := fun x => Path.refl (A x)

/-- Wadge reducibility is transitive via Path.trans. -/
def WadgeReducible.trans_wadge {X : Type u} {τ : TopologyData X}
    {A B C : X → Prop}
    (h₁ : WadgeReducible X τ A B) (h₂ : WadgeReducible X τ B C) :
    WadgeReducible X τ A C where
  reduce := fun x => h₂.reduce (h₁.reduce x)
  reduces := fun x => Path.trans (h₁.reduces x) (h₂.reduces (h₁.reduce x))

/-- Triple transitivity. -/
def wadge_triple_trans {X : Type u} {τ : TopologyData X}
    {A B C D : X → Prop}
    (h₁ : WadgeReducible X τ A B)
    (h₂ : WadgeReducible X τ B C)
    (h₃ : WadgeReducible X τ C D) :
    WadgeReducible X τ A D :=
  WadgeReducible.trans_wadge (WadgeReducible.trans_wadge h₁ h₂) h₃

/-- RwEq: Wadge transitivity is self-consistent. -/
noncomputable def wadge_trans_rweq {X : Type u} {τ : TopologyData X}
    {A B C : X → Prop}
    (h₁ : WadgeReducible X τ A B) (h₂ : WadgeReducible X τ B C) (x : X) :
    RwEq ((WadgeReducible.trans_wadge h₁ h₂).reduces x)
         ((WadgeReducible.trans_wadge h₁ h₂).reduces x) :=
  RwEq.refl _

/-- RwEq: symm(symm(reduces)) simplifies via Step.symm_symm. -/
noncomputable def wadge_symm_symm_rweq {X : Type u} {τ : TopologyData X}
    {A B : X → Prop} (h : WadgeReducible X τ A B) (x : X) :
    RwEq (Path.symm (Path.symm (h.reduces x))) (h.reduces x) :=
  RwEq.step (Step.symm_symm _)

/-- RwEq: trans with refl simplifies. -/
noncomputable def wadge_trans_refl_rweq {X : Type u} {τ : TopologyData X}
    {A B : X → Prop} (h : WadgeReducible X τ A B) (x : X) :
    RwEq (Path.trans (h.reduces x) (Path.refl _)) (h.reduces x) :=
  RwEq.step (Step.trans_refl_right _)

/-- RwEq: refl trans simplifies. -/
noncomputable def wadge_refl_trans_rweq {X : Type u} {τ : TopologyData X}
    {A B : X → Prop} (h : WadgeReducible X τ A B) (x : X) :
    RwEq (Path.trans (Path.refl _) (h.reduces x)) (h.reduces x) :=
  RwEq.step (Step.trans_refl_left _)

end DescriptiveSetTheory
end Logic
end Path
end ComputationalPaths
