/-
# Tree Automata via Paths

This module formalizes tree automata through computational paths:
bottom-up and top-down tree automata, tree rewriting as paths,
ground tree transducers, and regular tree languages as path-definable sets.

## References

- Comon et al., "Tree Automata Techniques and Applications"
- Gécseg, Steinby, "Tree Languages and Tree Automata"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Computation
namespace TreeAutomataPaths

universe u

/-! ## Tree Definition -/

/-- Ranked trees: nodes labeled from Sigma with variable arity. -/
inductive RTree (Sigma : Type u) : Type u
  | leaf : Sigma → RTree Sigma
  | node : Sigma → List (RTree Sigma) → RTree Sigma

/-- Tree size (number of nodes). -/
def treeSize {Sigma : Type u} : RTree Sigma → Nat
  | .leaf _ => 1
  | .node _ children => 1 + children.foldl (fun acc c => acc + treeSize c) 0

/-- Tree size is always positive. -/
theorem treeSize_pos {Sigma : Type u} (t : RTree Sigma) : 0 < treeSize t := by
  cases t <;> simp [treeSize] <;> omega

/-- Tree depth. -/
def treeDepth {Sigma : Type u} : RTree Sigma → Nat
  | .leaf _ => 0
  | .node _ children => 1 + children.foldl (fun acc c => max acc (treeDepth c)) 0

/-- Leaf has depth 0. -/
theorem leaf_depth {Sigma : Type u} (a : Sigma) : treeDepth (RTree.leaf a) = 0 := by
  simp [treeDepth]

/-- Tree yield: leaves read left to right. -/
def treeYield {Sigma : Type u} : RTree Sigma → List Sigma
  | .leaf a => [a]
  | .node _ children => children.foldl (fun acc c => acc ++ treeYield c) []

/-! ## Bottom-Up Tree Automaton -/

/-- Bottom-up finite tree automaton (BFTA). -/
structure BUTreeAuto (Q : Type u) (Sigma : Type u) where
  /-- Transition for leaves. -/
  δLeaf : Sigma → Q
  /-- Transition for internal nodes: label × child-states → state. -/
  δNode : Sigma → List Q → Q
  /-- Accepting states. -/
  accept : Q → Prop

/-- Run of a BFTA on a tree: computes the state. -/
noncomputable def buRun {Q Sigma : Type u} (A : BUTreeAuto Q Sigma) : RTree Sigma → Q
  | .leaf a => A.δLeaf a
  | .node f children => A.δNode f (children.map (buRun A))

/-- BFTA acceptance. -/
noncomputable def buAccepts {Q Sigma : Type u} (A : BUTreeAuto Q Sigma) (t : RTree Sigma) : Prop :=
  A.accept (buRun A t)

/-- BFTA leaf run path. -/
noncomputable def bu_leaf_run {Q Sigma : Type u} (A : BUTreeAuto Q Sigma) (a : Sigma) :
    Path (buRun A (RTree.leaf a)) (A.δLeaf a) := by
  unfold buRun; exact Path.refl _

/-- BFTA node run path. -/
noncomputable def bu_node_run {Q Sigma : Type u} (A : BUTreeAuto Q Sigma)
    (f : Sigma) (children : List (RTree Sigma)) :
    Path (buRun A (RTree.node f children))
         (A.δNode f (children.map (buRun A))) := by
  unfold buRun; exact Path.refl _

/-! ## Top-Down Tree Automaton -/

/-- Top-down finite tree automaton (TDFTA). -/
structure TDTreeAuto (Q : Type u) (Sigma : Type u) where
  /-- Initial state. -/
  q₀ : Q
  /-- Transition: state × label → list of child states. -/
  δ : Q → Sigma → List Q
  /-- Leaf acceptance: state × label → Prop. -/
  acceptLeaf : Q → Sigma → Prop

/-- Top-down run acceptance for a tree. -/
inductive tdAccepts {Q Sigma : Type u} (A : TDTreeAuto Q Sigma) : Q → RTree Sigma → Prop
  | leaf (q : Q) (a : Sigma) (h : A.acceptLeaf q a) : tdAccepts A q (RTree.leaf a)
  | node (q : Q) (f : Sigma) (children : List (RTree Sigma))
      (qs : List Q) (hq : A.δ q f = qs)
      (hlen : qs.length = children.length)
      (hchildren : ∀ i (hi : i < qs.length),
        tdAccepts A (qs.get ⟨i, hi⟩)
                    (children.get ⟨i, by omega⟩)) :
      tdAccepts A q (RTree.node f children)

/-- TD automaton accepts a tree starting from initial state. -/
def tdAcceptsTree {Q Sigma : Type u} (A : TDTreeAuto Q Sigma) (t : RTree Sigma) : Prop :=
  tdAccepts A A.q₀ t

/-! ## Product Construction for Tree Automata -/

/-- Product of two BU tree automata. -/
def ProductBUTA {Q₁ Q₂ Sigma : Type u}
    (A₁ : BUTreeAuto Q₁ Sigma) (A₂ : BUTreeAuto Q₂ Sigma) :
    BUTreeAuto (Q₁ × Q₂) Sigma where
  δLeaf := fun a => (A₁.δLeaf a, A₂.δLeaf a)
  δNode := fun f qs =>
    (A₁.δNode f (qs.map Prod.fst), A₂.δNode f (qs.map Prod.snd))
  accept := fun ⟨q₁, q₂⟩ => A₁.accept q₁ ∧ A₂.accept q₂

/-- Product BUTA leaf run decomposes. -/
noncomputable def product_bu_leaf {Q₁ Q₂ Sigma : Type u}
    (A₁ : BUTreeAuto Q₁ Sigma) (A₂ : BUTreeAuto Q₂ Sigma) (a : Sigma) :
    Path (buRun (ProductBUTA A₁ A₂) (RTree.leaf a))
         (A₁.δLeaf a, A₂.δLeaf a) := by
  simp [buRun, ProductBUTA]
  exact Path.refl _

/-! ## Tree Rewriting as Paths -/

/-- A tree rewrite rule: pattern → replacement. -/
structure TreeRewriteRule (Sigma : Type u) where
  lhs : RTree Sigma
  rhs : RTree Sigma

/-- One-step tree rewrite at root. -/
def treeRewriteRoot {Sigma : Type u} (rule : TreeRewriteRule Sigma)
    (t : RTree Sigma) (_ : t = rule.lhs) : RTree Sigma :=
  rule.rhs

/-- Path witness for tree rewriting. -/
def treeRewritePath {Sigma : Type u} (rule : TreeRewriteRule Sigma)
    (h : rule.lhs = rule.rhs) : Path rule.lhs rule.rhs :=
  Path.ofEq h

/-- Reflexive tree rewrite. -/
def treeRewriteRefl {Sigma : Type u} (t : RTree Sigma) :
    Path t t := Path.refl t

/-- Symmetric tree rewrite path. -/
def treeRewriteSymm {Sigma : Type u} {t₁ t₂ : RTree Sigma}
    (p : Path t₁ t₂) : Path t₂ t₁ :=
  Path.symm p

/-- Transitive tree rewrite path. -/
def treeRewriteTrans {Sigma : Type u} {t₁ t₂ t₃ : RTree Sigma}
    (p : Path t₁ t₂) (q : Path t₂ t₃) : Path t₁ t₃ :=
  Path.trans p q

/-! ## Ground Tree Transducers -/

/-- Ground tree transducer: transforms trees by rewriting. -/
structure GroundTransducer (Sigma : Type u) where
  /-- Set of rewrite rules. -/
  rules : List (TreeRewriteRule Sigma)

/-- Transducer produces tree via rule application. -/
def transducerApply {Sigma : Type u} [DecidableEq (RTree Sigma)]
    (G : GroundTransducer Sigma) (t : RTree Sigma) :
    RTree Sigma :=
  match G.rules.find? (fun r => t = r.lhs) with
  | some rule => rule.rhs
  | none => t

/-- Transducer on non-matching tree is identity. -/
theorem transducer_id {Sigma : Type u} [DecidableEq (RTree Sigma)]
    (G : GroundTransducer Sigma) (t : RTree Sigma)
    (h : ∀ r ∈ G.rules, t ≠ r.lhs) :
    transducerApply G t = t := by
  unfold transducerApply
  have : G.rules.find? (fun r => t = r.lhs) = none := by
    rw [List.find?_eq_none]
    intro r hr
    simp [h r hr]
  rw [this]

/-! ## Regular Tree Languages -/

/-- A tree language: set of trees. -/
def TreeLang (Sigma : Type u) := RTree Sigma → Prop

/-- Language recognized by a BU tree automaton. -/
noncomputable def buLang {Q Sigma : Type u} (A : BUTreeAuto Q Sigma) : TreeLang Sigma :=
  fun t => buAccepts A t

/-- Union of tree languages. -/
def treeLangUnion {Sigma : Type u} (L₁ L₂ : TreeLang Sigma) : TreeLang Sigma :=
  fun t => L₁ t ∨ L₂ t

/-- Intersection of tree languages. -/
def treeLangInter {Sigma : Type u} (L₁ L₂ : TreeLang Sigma) : TreeLang Sigma :=
  fun t => L₁ t ∧ L₂ t

/-- Union is commutative. -/
theorem treeLang_union_comm {Sigma : Type u} (L₁ L₂ : TreeLang Sigma) (t : RTree Sigma) :
    treeLangUnion L₁ L₂ t ↔ treeLangUnion L₂ L₁ t := by
  constructor <;> intro h <;> cases h with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h

/-- Intersection is commutative. -/
theorem treeLang_inter_comm {Sigma : Type u} (L₁ L₂ : TreeLang Sigma) (t : RTree Sigma) :
    treeLangInter L₁ L₂ t ↔ treeLangInter L₂ L₁ t := by
  exact And.comm

/-- Union is associative. -/
theorem treeLang_union_assoc {Sigma : Type u} (L₁ L₂ L₃ : TreeLang Sigma) (t : RTree Sigma) :
    treeLangUnion (treeLangUnion L₁ L₂) L₃ t ↔ treeLangUnion L₁ (treeLangUnion L₂ L₃) t := by
  simp [treeLangUnion, or_assoc]

/-- Intersection distributes over union. -/
theorem treeLang_inter_union_distrib {Sigma : Type u}
    (L₁ L₂ L₃ : TreeLang Sigma) (t : RTree Sigma) :
    treeLangInter L₁ (treeLangUnion L₂ L₃) t ↔
    treeLangUnion (treeLangInter L₁ L₂) (treeLangInter L₁ L₃) t := by
  simp [treeLangInter, treeLangUnion, and_or_left]

/-! ## TreeAutomataStep Rewrite Rules -/

/-- Rewrite steps for tree automata computations. -/
inductive TreeAutoStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Bottom-up run reduction. -/
  | bu_reduce {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : TreeAutoStep p q
  /-- Top-down run reduction. -/
  | td_reduce {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : TreeAutoStep p q
  /-- Tree rewrite step. -/
  | tree_rewrite {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : TreeAutoStep p q
  /-- Identity elimination. -/
  | id_elim {A : Type u} {a : A} (p : Path a a) :
      TreeAutoStep p (Path.refl a)

/-- TreeAutoStep is sound. -/
theorem treeAutoStep_sound {A : Type u} {a b : A} {p q : Path a b}
    (h : TreeAutoStep p q) : p.proof = q.proof := by
  cases h with
  | bu_reduce _ _ h => exact h
  | td_reduce _ _ h => exact h
  | tree_rewrite _ _ h => exact h
  | id_elim _ => rfl

/-! ## RwEq Instances -/

/-- RwEq: tree rewrite refl is stable. -/
theorem rwEq_tree_refl {Sigma : Type u} (t : RTree Sigma) :
    RwEq (treeRewriteRefl t) (treeRewriteRefl t) :=
  RwEq.refl _

/-- symm ∘ symm for tree paths. -/
theorem symm_symm_tree {Sigma : Type u} (t : RTree Sigma) :
    Path.toEq (Path.symm (Path.symm (treeRewriteRefl t))) =
    Path.toEq (treeRewriteRefl t) := by simp

/-- congrArg for tree node construction. -/
def congrArg_tree_node {Sigma : Type u} (f : Sigma)
    {cs₁ cs₂ : List (RTree Sigma)} (h : Path cs₁ cs₂) :
    Path (RTree.node f cs₁) (RTree.node f cs₂) :=
  Path.congrArg (RTree.node f) h

/-- transport for tree language membership. -/
theorem transport_tree_lang {Sigma : Type u} (L : TreeLang Sigma)
    {t₁ t₂ : RTree Sigma} (h : Path t₁ t₂) :
    L t₁ ↔ L t₂ := by
  cases h with | mk steps proof => cases proof; exact Iff.rfl

/-- trans with refl for tree rewrite paths. -/
theorem trans_refl_tree {Sigma : Type u} (t : RTree Sigma) :
    Path.trans (treeRewriteRefl t) (Path.refl t) = treeRewriteRefl t := by simp

/-- RwEq for tree rewrite symmetry. -/
theorem rwEq_tree_symm {Sigma : Type u} {t₁ t₂ : RTree Sigma}
    (p : Path t₁ t₂) : RwEq (treeRewriteSymm p) (treeRewriteSymm p) :=
  RwEq.refl _

/-- Leaf tree has singleton yield. -/
theorem leaf_yield {Sigma : Type u} (a : Sigma) :
    treeYield (RTree.leaf a) = [a] := by
  simp [treeYield]

end TreeAutomataPaths
end Computation
end Path
end ComputationalPaths
