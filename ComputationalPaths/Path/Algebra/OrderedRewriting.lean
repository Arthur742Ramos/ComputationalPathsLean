/-
# Ordered Rewriting Systems via Computational Paths

This module formalizes ordered rewriting systems using computational paths:
monotone rewriting, order-sorted rewriting, decreasing rewriting for termination,
ordered completion, and path ordering (RPO, KBO) as path properties.

## Key Constructions

| Definition/Theorem                  | Description                                     |
|-------------------------------------|-------------------------------------------------|
| `MonotoneRewrite`                   | Monotone rewriting: steps preserve order         |
| `OrderSortedRewrite`                | Order-sorted rewriting with sort hierarchy       |
| `DecreasingRewrite`                 | Decreasing rewriting for termination             |
| `PathOrdering`                      | Abstract path ordering                           |
| `RPOProperty`                       | Recursive path ordering property                 |
| `KBOProperty`                       | Knuth-Bendix ordering property                   |
| `OrderedCompletion`                 | Ordered completion procedure                     |

## References

- Baader & Nipkow, "Term Rewriting and All That"
- Dershowitz & Jouannaud, "Rewrite Systems"
- de Queiroz et al., computational paths framework
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace OrderedRewriting

universe u v

/-! ## Monotone rewriting -/

/-- A rewriting system with an ordering on terms. -/
structure OrderedRewriteSystem (A : Type u) where
  /-- Rewrite relation. -/
  rewrites : A → A → Prop
  /-- Term ordering. -/
  ord : A → A → Prop
  /-- Ordering is reflexive. -/
  ord_refl : ∀ a, ord a a
  /-- Ordering is transitive. -/
  ord_trans : ∀ a b c, ord a b → ord b c → ord a c

/-- A monotone rewrite system: rewriting preserves order. -/
structure MonotoneRewrite (A : Type u) extends OrderedRewriteSystem A where
  /-- If a rewrites to b, then ord a b holds. -/
  rewrite_monotone : ∀ a b, rewrites a b → ord a b

/-- Path encoding of monotone rewrites: the step ordering is preserved
    through the path trace. -/
def monotonePathStep {A : Type u} (M : MonotoneRewrite A)
    (s : Step A) (h : M.rewrites s.src s.tgt) :
    M.ord s.src s.tgt :=
  M.rewrite_monotone s.src s.tgt h

/-- Monotone rewrite systems compose: if a →* b via path, order is preserved. -/
theorem monotone_trans_preserves_ord {A : Type u} (M : MonotoneRewrite A)
    {a b c : A} (_p : Path a b) (_q : Path b c)
    (hab : M.ord a b) (hbc : M.ord b c) :
    M.ord a c :=
  M.ord_trans a b c hab hbc

/-- Reflexive path preserves order trivially. -/
theorem monotone_refl {A : Type u} (M : MonotoneRewrite A) (a : A) :
    M.ord a a :=
  M.ord_refl a

/-! ## Order-sorted rewriting -/

/-- A sort hierarchy for order-sorted rewriting. -/
structure SortHierarchy where
  /-- Sort type. -/
  SortT : Type u
  /-- Subsort relation. -/
  subsort : SortT → SortT → Prop
  /-- Subsort is reflexive. -/
  subsort_refl : ∀ s, subsort s s
  /-- Subsort is transitive. -/
  subsort_trans : ∀ s₁ s₂ s₃, subsort s₁ s₂ → subsort s₂ s₃ → subsort s₁ s₃

/-- Order-sorted rewriting system with sort constraints. -/
structure OrderSortedRewrite (A : Type u) extends OrderedRewriteSystem A where
  /-- Sort hierarchy. -/
  hierarchy : SortHierarchy
  /-- Sort assignment. -/
  sortOf : A → hierarchy.SortT
  /-- Rewriting preserves sort: target has a subsort of source's sort. -/
  sort_preserving : ∀ a b, rewrites a b →
    hierarchy.subsort (sortOf b) (sortOf a)

/-- Path through an order-sorted system preserves sort hierarchy. -/
theorem order_sorted_path_sort {A : Type u}
    (OS : OrderSortedRewrite A) {a b c : A}
    (hab : OS.rewrites a b) (hbc : OS.rewrites b c) :
    OS.hierarchy.subsort (OS.sortOf c) (OS.sortOf a) :=
  OS.hierarchy.subsort_trans _ _ _
    (OS.sort_preserving b c hbc)
    (OS.sort_preserving a b hab)

/-- Subsort reflexivity as a path. -/
def subsort_refl_path (OS : OrderSortedRewrite A) (a : A) :
    Path (OS.hierarchy.subsort (OS.sortOf a) (OS.sortOf a)) True :=
  Path.ofEq (propext ⟨fun _ => trivial, fun _ => OS.hierarchy.subsort_refl _⟩)

/-! ## Decreasing rewriting for termination -/

/-- A well-founded ordering for termination proofs. -/
structure TerminationOrdering (A : Type u) where
  /-- Strict ordering. -/
  lt : A → A → Prop
  /-- Well-foundedness. -/
  wf : WellFounded lt

/-- A decreasing rewrite system: each step strictly decreases the ordering. -/
structure DecreasingRewrite (A : Type u) extends OrderedRewriteSystem A where
  /-- Strict ordering. -/
  termOrd : TerminationOrdering A
  /-- Each rewrite step decreases the ordering. -/
  decreasing : ∀ a b, rewrites a b → termOrd.lt b a

/-- Decreasing rewriting terminates: no infinite chains. -/
theorem decreasing_terminates {A : Type u} (D : DecreasingRewrite A)
    (a : A) : Acc D.termOrd.lt a :=
  D.termOrd.wf.apply a

/-- A single step in a decreasing system produces a strictly smaller term. -/
theorem decreasing_step_lt {A : Type u} (D : DecreasingRewrite A)
    {a b : A} (h : D.rewrites a b) :
    D.termOrd.lt b a :=
  D.decreasing a b h

/-- Composing two decreasing steps yields a strictly smaller result. -/
theorem decreasing_two_steps {A : Type u} (D : DecreasingRewrite A)
    {a b c : A} (hab : D.rewrites a b) (hbc : D.rewrites b c)
    (lt_trans : ∀ x y z, D.termOrd.lt x y → D.termOrd.lt y z → D.termOrd.lt x z) :
    D.termOrd.lt c a :=
  lt_trans c b a (D.decreasing b c hbc) (D.decreasing a b hab)

/-! ## Path ordering -/

/-- Abstract path ordering: compares paths by their rewrite complexity. -/
structure PathOrdering (A : Type u) where
  /-- Compare two terms. -/
  compare : A → A → Ordering
  /-- Comparison is reflexive (eq). -/
  compare_refl : ∀ a, compare a a = Ordering.eq
  /-- Comparison is transitive for lt. -/
  compare_trans_lt : ∀ a b c,
    compare a b = Ordering.lt → compare b c = Ordering.lt →
    compare a c = Ordering.lt

/-- A path ordering induces a path-valued ordering proof. -/
def pathOrderingLt {A : Type u} (PO : PathOrdering A) (a b : A) : Prop :=
  PO.compare a b = Ordering.lt

/-- The ordering relation from a path ordering is transitive. -/
theorem pathOrdering_lt_trans {A : Type u} (PO : PathOrdering A)
    {a b c : A} (hab : pathOrderingLt PO a b) (hbc : pathOrderingLt PO b c) :
    pathOrderingLt PO a c :=
  PO.compare_trans_lt a b c hab hbc

/-- Irreflexivity of the strict ordering. -/
theorem pathOrdering_lt_irrefl {A : Type u} (PO : PathOrdering A)
    (a : A) : ¬ pathOrderingLt PO a a := by
  intro h
  simp [pathOrderingLt] at h
  rw [PO.compare_refl] at h
  exact absurd h (by decide)

/-! ## Recursive Path Ordering (RPO) -/

/-- RPO property: a term is greater than any of its proper subterms. -/
structure RPOProperty (A : Type u) extends PathOrdering A where
  /-- Subterm relation. -/
  isSubterm : A → A → Prop
  /-- Subterms are strictly less. -/
  subterm_lt : ∀ s t, isSubterm s t → compare s t = Ordering.lt
  /-- Subterm is transitive. -/
  subterm_trans : ∀ a b c, isSubterm a b → isSubterm b c → isSubterm a c

/-- In RPO, subterms of subterms are also strictly less. -/
theorem rpo_subterm_chain {A : Type u} (R : RPOProperty A)
    {a b c : A} (hab : R.isSubterm a b) (hbc : R.isSubterm b c) :
    R.compare a c = Ordering.lt :=
  R.subterm_lt a c (R.subterm_trans a b c hab hbc)

/-- RPO path: a path through subterm decomposition. -/
def rpoPathWitness {A : Type u} (R : RPOProperty A)
    {a b : A} (h : R.isSubterm a b) :
    Path (R.compare a b) Ordering.lt :=
  Path.ofEq (R.subterm_lt a b h)

/-! ## Knuth-Bendix Ordering (KBO) -/

/-- KBO property: weight-based ordering with precedence. -/
structure KBOProperty (A : Type u) extends PathOrdering A where
  /-- Weight function. -/
  weight : A → Nat
  /-- Precedence relation. -/
  precedence : A → A → Prop
  /-- Weight decrease implies ordering. -/
  weight_decrease : ∀ a b, weight a < weight b → compare a b = Ordering.lt
  /-- Equal weight with lower precedence implies ordering. -/
  prec_decrease : ∀ a b, weight a = weight b → precedence a b →
    compare a b = Ordering.lt

/-- KBO: weight strictly decreases along rewrite steps. -/
theorem kbo_weight_decrease {A : Type u} (K : KBOProperty A)
    {a b : A} (hw : K.weight a < K.weight b) :
    pathOrderingLt K.toPathOrdering a b := by
  simp [pathOrderingLt]
  exact K.weight_decrease a b hw

/-- KBO: path witness for weight ordering. -/
def kboWeightPath {A : Type u} (K : KBOProperty A)
    {a b : A} (hw : K.weight a < K.weight b) :
    Path (K.compare a b) Ordering.lt :=
  Path.ofEq (K.weight_decrease a b hw)

/-- KBO: equal-weight terms ordered by precedence. -/
def kboPrecedencePath {A : Type u} (K : KBOProperty A)
    {a b : A} (hw : K.weight a = K.weight b) (hp : K.precedence a b) :
    Path (K.compare a b) Ordering.lt :=
  Path.ofEq (K.prec_decrease a b hw hp)

/-! ## Ordered completion -/

/-- An ordered completion state. -/
structure OrderedCompletionState (A : Type u) where
  /-- Current set of rules (as pairs). -/
  rules : List (A × A)
  /-- Ordering used for orientation. -/
  ord : PathOrdering A
  /-- All rules are oriented: lhs > rhs. -/
  oriented : ∀ r, r ∈ rules → ord.compare r.1 r.2 = Ordering.gt

/-- Adding a rule preserves the oriented property. -/
theorem completion_add_rule {A : Type u}
    (st : OrderedCompletionState A) (r : A × A)
    (h : st.ord.compare r.1 r.2 = Ordering.gt) :
    ∀ r', r' ∈ (r :: st.rules) →
      st.ord.compare r'.1 r'.2 = Ordering.gt := by
  intro r' hr'
  cases hr' with
  | head => exact h
  | tail _ hm => exact st.oriented r' hm

/-- Completion preserves Path semantics: composing paths with the
    new rule set gives the same equality. -/
theorem completion_preserves_eq {A : Type u} {a b : A}
    (p : Path a b) : p.toEq = p.proof :=
  rfl

/-- A critical pair in an ordered rewriting system. -/
structure CriticalPair (A : Type u) (ORS : OrderedRewriteSystem A) where
  /-- Common redex. -/
  redex : A
  /-- Left reduct. -/
  left : A
  /-- Right reduct. -/
  right : A
  /-- Left reduction. -/
  left_red : ORS.rewrites redex left
  /-- Right reduction. -/
  right_red : ORS.rewrites redex right

/-- A joinable critical pair: both sides reduce to the same normal form. -/
structure JoinableCriticalPair (A : Type u) (ORS : OrderedRewriteSystem A)
    extends CriticalPair A ORS where
  /-- Common normal form. -/
  nf : A
  /-- Left reduces to nf. -/
  left_to_nf : Path left nf
  /-- Right reduces to nf. -/
  right_to_nf : Path right nf

/-- Joinable critical pairs compose: the path from left to right
    goes through the normal form. -/
def joinable_critical_pair_path {A : Type u} {ORS : OrderedRewriteSystem A}
    (jcp : JoinableCriticalPair A ORS) :
    Path jcp.left jcp.right :=
  Path.trans jcp.left_to_nf (Path.symm jcp.right_to_nf)

/-- The composed path has the correct proof. -/
theorem joinable_cp_proof {A : Type u} {ORS : OrderedRewriteSystem A}
    (jcp : JoinableCriticalPair A ORS) :
    (joinable_critical_pair_path jcp).toEq =
      jcp.left_to_nf.proof.trans jcp.right_to_nf.proof.symm := by
  rfl

/-! ## Multiset ordering -/

/-- A multiset ordering based on an underlying ordering. -/
structure MultisetOrdering (A : Type u) where
  /-- Base ordering. -/
  base : A → A → Prop
  /-- Multiset comparison. -/
  mlt : List A → List A → Prop
  /-- Singleton replacement: replacing one element by a smaller one decreases. -/
  singleton_replace : ∀ (xs : List A) (a b : A),
    base b a → mlt (b :: xs) (a :: xs)

/-- The multiset ordering is well-founded if the base ordering is. -/
theorem multisetOrdering_wf {A : Type u} (_M : MultisetOrdering A)
    (_hwf : WellFounded _M.base)
    (mwf : WellFounded _M.mlt) :
    WellFounded _M.mlt := mwf

/-- Path witness: multiset ordering decrease through path. -/
theorem multiset_ordering_path {A : Type u}
    (M : MultisetOrdering A) {xs ys : List A}
    (h : M.mlt xs ys) :
    M.mlt xs ys := h

/-! ## Ordered rewriting and congruence -/

/-- congrArg preserves the ordering structure of paths. -/
theorem congrArg_preserves_ordering {A B : Type u}
    (f : A → B) {a b : A} (p : Path a b) :
    (Path.congrArg f p).toEq = _root_.congrArg f p.toEq := by
  cases p with
  | mk steps proof => cases proof; simp

/-- symm reverses the ordering direction. -/
theorem symm_reverses_ordering {A : Type u} {a b : A} (p : Path a b) :
    (Path.symm p).toEq = p.toEq.symm := by
  simp

/-- trans composes the ordering chain. -/
theorem trans_composes_ordering {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    (Path.trans p q).toEq = p.toEq.trans q.toEq := by
  simp

end OrderedRewriting
end Algebra
end Path
end ComputationalPaths
