/-
# Ordered Rewriting Systems via Computational Paths

Monotone rewriting, order-sorted rewriting, decreasing chains for
termination, ordered completion, and path-ordering properties (RPO / KBO)
— all expressed via `Path`, `Step`, `trans`, `symm`, `congrArg`,
`transport`.

## Main results (25 theorems/defs)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.OrderedRewriting

open ComputationalPaths.Path

universe u v

variable {A : Type u} {B : Type v}

/-! ## Monotone rewriting -/

/-- A rewriting system with an ordering on terms. -/
structure OrderedRwSys (A : Type u) where
  rw : A → A → Prop
  ord : A → A → Prop
  ord_refl : ∀ a, ord a a
  ord_trans : ∀ a b c, ord a b → ord b c → ord a c

/-- Monotone: every rewrite preserves the order. -/
structure MonotoneRw (A : Type u) extends OrderedRwSys A where
  mono : ∀ a b, rw a b → ord a b

/-- Encoding a monotone rewrite step as a `Step`. -/
def monoStep (_M : MonotoneRw A) {a b : A} (h : a = b) : Step A :=
  Step.mk a b h

/-- A single monotone step composes to a `Path`. -/
def monoStepPath (_M : MonotoneRw A) {a b : A} (h : a = b) : Path a b :=
  Path.mk [Step.mk _ _ h] h

/-- Two monotone paths compose: step-lists concatenate. -/
theorem mono_trans_steps (_M : MonotoneRw A) {a b c : A}
    (p : Path a b) (q : Path b c) :
    (Path.trans p q).steps = p.steps ++ q.steps := by
  simp

/-- Monotone rewriting is closed under trans of the ordering. -/
theorem mono_ord_trans (M : MonotoneRw A) {a b c : A}
    (hab : M.ord a b) (hbc : M.ord b c) :
    M.ord a c :=
  M.ord_trans a b c hab hbc

/-- Refl preserves order. -/
theorem mono_refl (M : MonotoneRw A) (a : A) : M.ord a a :=
  M.ord_refl a

/-! ## Order-sorted rewriting -/

/-- Sort hierarchy. -/
structure SortHierarchy where
  Carrier : Type u
  subsort : Carrier → Carrier → Prop
  subsort_refl : ∀ s, subsort s s
  subsort_trans : ∀ s₁ s₂ s₃, subsort s₁ s₂ → subsort s₂ s₃ → subsort s₁ s₃

/-- Order-sorted rw: each step preserves sort. -/
structure OrderSortedRw (A : Type u) extends OrderedRwSys A where
  hierarchy : SortHierarchy
  sortOf : A → hierarchy.Carrier
  sort_pres : ∀ a b, rw a b → hierarchy.subsort (sortOf b) (sortOf a)

/-- Two-step sort preservation via trans. -/
theorem orderSorted_two_step (OS : OrderSortedRw A) {a b c : A}
    (hab : OS.rw a b) (hbc : OS.rw b c) :
    OS.hierarchy.subsort (OS.sortOf c) (OS.sortOf a) :=
  OS.hierarchy.subsort_trans _ _ _ (OS.sort_pres b c hbc) (OS.sort_pres a b hab)

/-- Sort-preserving path: `congrArg sortOf` witnesses the chain. -/
def sortPathWitness (OS : OrderSortedRw A) {a b : A} (p : Path a b) :
    Path (OS.sortOf a) (OS.sortOf b) :=
  Path.congrArg OS.sortOf p

/-- The sort-witness path has the correct steps count. -/
theorem sortPathWitness_length (OS : OrderSortedRw A) {a b : A}
    (p : Path a b) :
    (sortPathWitness OS p).steps.length = p.steps.length := by
  simp [sortPathWitness]

/-! ## Decreasing rewriting for termination -/

/-- A strict well-founded ordering for termination. -/
structure TermOrd (A : Type u) where
  lt : A → A → Prop
  wf : WellFounded lt

/-- Decreasing rw: each step strictly decreases. -/
structure DecreasingRw (A : Type u) extends OrderedRwSys A where
  termOrd : TermOrd A
  decr : ∀ a b, rw a b → termOrd.lt b a

/-- Every element is accessible. -/
theorem decr_acc (D : DecreasingRw A) (a : A) : Acc D.termOrd.lt a :=
  D.termOrd.wf.apply a

/-- A single step strictly decreases. -/
theorem decr_step (D : DecreasingRw A) {a b : A} (h : D.rw a b) :
    D.termOrd.lt b a :=
  D.decr a b h

/-- Two-step chain strictly decreases. -/
theorem decr_two_steps (D : DecreasingRw A) {a b c : A}
    (hab : D.rw a b) (hbc : D.rw b c)
    (lt_trans : ∀ x y z, D.termOrd.lt x y → D.termOrd.lt y z → D.termOrd.lt x z) :
    D.termOrd.lt c a :=
  lt_trans c b a (D.decr b c hbc) (D.decr a b hab)

/-! ## Path ordering (RPO / KBO) -/

/-- Abstract path ordering (comparison function). -/
structure PathOrdering (A : Type u) where
  cmp : A → A → Ordering
  cmp_refl : ∀ a, cmp a a = .eq
  cmp_lt_trans : ∀ a b c,
    cmp a b = .lt → cmp b c = .lt → cmp a c = .lt

def poLt (PO : PathOrdering A) (a b : A) : Prop :=
  PO.cmp a b = .lt

theorem poLt_trans (PO : PathOrdering A) {a b c : A}
    (h1 : poLt PO a b) (h2 : poLt PO b c) :
    poLt PO a c :=
  PO.cmp_lt_trans a b c h1 h2

theorem poLt_irrefl (PO : PathOrdering A) (a : A) :
    ¬ poLt PO a a := by
  intro h; simp [poLt] at h; rw [PO.cmp_refl] at h; exact absurd h (by decide)

/-! ## RPO -/

/-- Recursive path ordering: subterms are strictly smaller. -/
structure RPO (A : Type u) extends PathOrdering A where
  isSub : A → A → Prop
  sub_lt : ∀ s t, isSub s t → cmp s t = .lt
  sub_trans : ∀ a b c, isSub a b → isSub b c → isSub a c

theorem rpo_sub_chain (R : RPO A) {a b c : A}
    (h1 : R.isSub a b) (h2 : R.isSub b c) :
    R.cmp a c = .lt :=
  R.sub_lt a c (R.sub_trans a b c h1 h2)

/-- RPO witness as a `Path` from `cmp a b` to `.lt`. -/
def rpoWitness (R : RPO A) {a b : A} (h : R.isSub a b) :
    Path (R.cmp a b) .lt :=
  Path.mk [Step.mk _ _ (R.sub_lt a b h)] (R.sub_lt a b h)

/-! ## KBO -/

/-- Knuth-Bendix ordering: weight + precedence. -/
structure KBO (A : Type u) extends PathOrdering A where
  weight : A → Nat
  prec : A → A → Prop
  wt_lt : ∀ a b, weight a < weight b → cmp a b = .lt
  prec_lt : ∀ a b, weight a = weight b → prec a b → cmp a b = .lt

theorem kbo_wt_lt (K : KBO A) {a b : A} (h : K.weight a < K.weight b) :
    poLt K.toPathOrdering a b :=
  K.wt_lt a b h

/-- KBO weight-decrease witness as a `Path`. -/
def kboWtPath (K : KBO A) {a b : A} (h : K.weight a < K.weight b) :
    Path (K.cmp a b) .lt :=
  Path.mk [Step.mk _ _ (K.wt_lt a b h)] (K.wt_lt a b h)

/-! ## Ordered completion -/

/-- Ordered completion state. -/
structure OCState (A : Type u) where
  rules : List (A × A)
  ord : PathOrdering A
  oriented : ∀ r, r ∈ rules → ord.cmp r.2 r.1 = .lt

/-- Adding an oriented rule preserves orientation. -/
theorem oc_add_rule (st : OCState A) (r : A × A)
    (h : st.ord.cmp r.2 r.1 = .lt) :
    ∀ r', r' ∈ (r :: st.rules) → st.ord.cmp r'.2 r'.1 = .lt := by
  intro r' hr'
  cases hr' with
  | head => exact h
  | tail _ hm => exact st.oriented r' hm

/-! ## Path-level proofs of ordering -/

/-- `congrArg` preserves step-count ordering structure. -/
theorem congrArg_preserves_steps (f : A → B) {a b : A} (p : Path a b) :
    (Path.congrArg f p).toEq = _root_.congrArg f p.toEq := by
  cases p with | mk s h => cases h; simp

/-- `symm` reverses the equality direction. -/
theorem symm_toEq {a b : A} (p : Path a b) :
    (Path.symm p).toEq = p.toEq.symm := by simp

/-- `trans` composes equalities. -/
theorem trans_toEq {a b c : A} (p : Path a b) (q : Path b c) :
    (Path.trans p q).toEq = p.toEq.trans q.toEq := by simp

end ComputationalPaths.Path.Algebra.OrderedRewriting
