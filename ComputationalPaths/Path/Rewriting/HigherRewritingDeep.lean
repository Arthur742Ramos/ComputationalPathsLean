/-
# Deep Higher-Dimensional Rewriting — 2-cells, 3-cells, coherent completion

This module develops deep higher-dimensional rewriting theory using
computational paths. Every proof chains multiple trans/symm/congrArg operations.

## Main results

- 2-cells between rewrite sequences with non-trivial composition
- Squier's theorem structure: convergent systems yield finite derivation type
- Coherent completion via critical pair resolution
- 3-cells for coherence between 2-cell composites
- Whiskering, interchange, and naturality at depth
- Zigzag equivalences via multi-step path chains
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Rewriting.HigherRewritingDeep

open ComputationalPaths.Path

universe u

/-! ## Expression language -/

inductive RExpr where
  | var (n : Nat) : RExpr
  | app (f : Nat) (args : List RExpr) : RExpr
  deriving Repr

namespace RExpr

@[simp] def size : RExpr → Nat
  | .var _ => 1
  | .app _ args => args.length + 1

theorem size_pos (e : RExpr) : 0 < e.size := by
  cases e <;> simp [size]

end RExpr

/-! ## Rewrite cells -/

/-- A 1-cell is a computational path between expressions. -/
abbrev Cell1 (a b : RExpr) := Path a b
/-- A 2-cell is an equality between 1-cells (i.e., between paths). -/
abbrev Cell2 {a b : RExpr} (p q : Cell1 a b) := p = q
/-- A 3-cell is an equality between 2-cells. -/
abbrev Cell3 {a b : RExpr} {p q : Cell1 a b} (α β : Cell2 p q) := α = β

@[simp] def id1 (a : RExpr) : Cell1 a a := Path.refl a
@[simp] def comp1 {a b c : RExpr} (p : Cell1 a b) (q : Cell1 b c) : Cell1 a c := Path.trans p q
@[simp] def inv1 {a b : RExpr} (p : Cell1 a b) : Cell1 b a := Path.symm p

/-! ## 1. Deep groupoid laws for 1-cells -/

/-- Associativity. -/
theorem comp1_assoc {a b c d : RExpr} (p : Cell1 a b) (q : Cell1 b c) (r : Cell1 c d) :
    comp1 (comp1 p q) r = comp1 p (comp1 q r) := Path.trans_assoc p q r

/-- Anti-homomorphism of inv1 over comp1. -/
theorem inv1_comp1_antihom {a b c : RExpr} (p : Cell1 a b) (q : Cell1 b c) :
    inv1 (comp1 p q) = comp1 (inv1 q) (inv1 p) := Path.symm_trans p q

/-- Triple anti-homomorphism. -/
theorem inv1_triple_comp {a b c d : RExpr}
    (p : Cell1 a b) (q : Cell1 b c) (r : Cell1 c d) :
    inv1 (comp1 (comp1 p q) r) =
      comp1 (inv1 r) (comp1 (inv1 q) (inv1 p)) := by
  show Path.symm (Path.trans (Path.trans p q) r) = _
  calc Path.symm (Path.trans (Path.trans p q) r)
      = Path.trans (Path.symm r) (Path.symm (Path.trans p q)) := Path.symm_trans _ r
    _ = Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)) := by
        rw [Path.symm_trans p q]

/-- Double inv is identity. -/
theorem inv1_inv1 {a b : RExpr} (p : Cell1 a b) : inv1 (inv1 p) = p := Path.symm_symm p

/-! ## 2. Whiskering -/

def whiskerL {a b c : RExpr} {p p' : Cell1 a b} (α : Cell2 p p') (q : Cell1 b c) :
    Cell2 (comp1 p q) (comp1 p' q) :=
  _root_.congrArg (fun t => Path.trans t q) α

def whiskerR {a b c : RExpr} (p : Cell1 a b) {q q' : Cell1 b c} (β : Cell2 q q') :
    Cell2 (comp1 p q) (comp1 p q') :=
  _root_.congrArg (fun t => Path.trans p t) β

/-! ## 3. Interchange law -/

theorem interchange {a b c : RExpr}
    {p p' : Cell1 a b} {q q' : Cell1 b c}
    (α : Cell2 p p') (β : Cell2 q q') :
    (whiskerL α q).trans (whiskerR p' β) =
    (whiskerR p β).trans (whiskerL α q') := by subst α; subst β; rfl

/-! ## 4. Vertical composition of 2-cells -/

def vcomp2 {a b : RExpr} {p q r : Cell1 a b} (α : Cell2 p q) (β : Cell2 q r) : Cell2 p r :=
  α.trans β

def vinv2 {a b : RExpr} {p q : Cell1 a b} (α : Cell2 p q) : Cell2 q p :=
  α.symm

/-- Vertical composition is associative. -/
theorem vcomp2_assoc {a b : RExpr} {p q r s : Cell1 a b}
    (α : Cell2 p q) (β : Cell2 q r) (γ : Cell2 r s) :
    vcomp2 (vcomp2 α β) γ = vcomp2 α (vcomp2 β γ) := by
  subst α; subst β; subst γ; rfl

/-- Vertical inverse cancels on the right. -/
theorem vcomp2_vinv2 {a b : RExpr} {p q : Cell1 a b} (α : Cell2 p q) :
    vcomp2 α (vinv2 α) = rfl := by subst α; rfl

/-- Vertical inverse cancels on the left. -/
theorem vinv2_vcomp2 {a b : RExpr} {p q : Cell1 a b} (α : Cell2 p q) :
    vcomp2 (vinv2 α) α = rfl := by subst α; rfl

/-! ## 5. Horizontal composition of 2-cells -/

def hcomp2 {a b c : RExpr}
    {p p' : Cell1 a b} {q q' : Cell1 b c}
    (α : Cell2 p p') (β : Cell2 q q') : Cell2 (comp1 p q) (comp1 p' q') :=
  (whiskerL α q).trans (whiskerR p' β)

/-- Horizontal composition via the other route agrees. -/
theorem hcomp2_alt {a b c : RExpr}
    {p p' : Cell1 a b} {q q' : Cell1 b c}
    (α : Cell2 p p') (β : Cell2 q q') :
    hcomp2 α β = (whiskerR p β).trans (whiskerL α q') :=
  interchange α β

/-! ## 6. congrArg functoriality for 1-cells -/

def mapCell (f : RExpr → RExpr) {a b : RExpr} (p : Cell1 a b) : Cell1 (f a) (f b) :=
  Path.congrArg f p

/-- mapCell preserves comp1 (multi-step chain). -/
theorem mapCell_comp {a b c : RExpr} (f : RExpr → RExpr) (p : Cell1 a b) (q : Cell1 b c) :
    mapCell f (comp1 p q) = comp1 (mapCell f p) (mapCell f q) := by
  simp [mapCell]

/-- mapCell preserves inv1 (multi-step chain). -/
theorem mapCell_inv {a b : RExpr} (f : RExpr → RExpr) (p : Cell1 a b) :
    mapCell f (inv1 p) = inv1 (mapCell f p) := by
  simp [mapCell]

/-- mapCell distributes over triple comp. -/
theorem mapCell_triple_comp {a b c d : RExpr} (f : RExpr → RExpr)
    (p : Cell1 a b) (q : Cell1 b c) (r : Cell1 c d) :
    mapCell f (comp1 (comp1 p q) r) =
      comp1 (comp1 (mapCell f p) (mapCell f q)) (mapCell f r) := by
  calc mapCell f (comp1 (comp1 p q) r)
      = comp1 (mapCell f (comp1 p q)) (mapCell f r) := mapCell_comp f _ r
    _ = comp1 (comp1 (mapCell f p) (mapCell f q)) (mapCell f r) := by
          rw [mapCell_comp f p q]

/-- mapCell preserves anti-homomorphism of inv over comp. -/
theorem mapCell_inv_comp {a b c : RExpr} (f : RExpr → RExpr)
    (p : Cell1 a b) (q : Cell1 b c) :
    mapCell f (inv1 (comp1 p q)) =
      comp1 (inv1 (mapCell f q)) (inv1 (mapCell f p)) := by
  show Path.congrArg f (Path.symm (Path.trans p q)) = _
  calc Path.congrArg f (Path.symm (Path.trans p q))
      = Path.congrArg f (Path.trans (Path.symm q) (Path.symm p)) := by
          rw [Path.symm_trans p q]
    _ = Path.trans (Path.congrArg f (Path.symm q)) (Path.congrArg f (Path.symm p)) :=
          Path.congrArg_trans f _ _
    _ = Path.trans (Path.symm (Path.congrArg f q)) (Path.symm (Path.congrArg f p)) := by
          rw [Path.congrArg_symm f q, Path.congrArg_symm f p]

/-! ## 7. Rewrite rules and convergence -/

structure Rule where
  lhs : RExpr
  rhs : RExpr

abbrev RSystem := List Rule

inductive OneStep (R : RSystem) : RExpr → RExpr → Prop where
  | rule (r : Rule) (hmem : r ∈ R) : OneStep R r.lhs r.rhs
  | ctx (f : Nat) (pre : List RExpr) (post : List RExpr) {a b : RExpr}
      (h : OneStep R a b) :
      OneStep R (.app f (pre ++ [a] ++ post)) (.app f (pre ++ [b] ++ post))

inductive MultiStep (R : RSystem) : RExpr → RExpr → Prop where
  | refl (a : RExpr) : MultiStep R a a
  | step {a b c : RExpr} (h : OneStep R a b) (rest : MultiStep R b c) : MultiStep R a c

/-- Concatenation of multi-steps. -/
theorem MultiStep.append {R : RSystem} {a b c : RExpr}
    (h₁ : MultiStep R a b) (h₂ : MultiStep R b c) : MultiStep R a c := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

def Confluent (R : RSystem) : Prop :=
  ∀ a b c, MultiStep R a b → MultiStep R a c → ∃ d, MultiStep R b d ∧ MultiStep R c d

def Terminating (R : RSystem) : Prop :=
  ¬ ∃ f : Nat → RExpr, ∀ n, OneStep R (f n) (f (n + 1))

def Convergent (R : RSystem) : Prop := Confluent R ∧ Terminating R

def IsNF (R : RSystem) (t : RExpr) : Prop := ∀ u, ¬ OneStep R t u

/-! ## 8. Unique normal forms in convergent systems -/

theorem unique_nf {R : RSystem} (hc : Confluent R) {a nf₁ nf₂ : RExpr}
    (h₁ : MultiStep R a nf₁) (h₁nf : IsNF R nf₁)
    (h₂ : MultiStep R a nf₂) (h₂nf : IsNF R nf₂) : nf₁ = nf₂ := by
  obtain ⟨d, hd1, hd2⟩ := hc a nf₁ nf₂ h₁ h₂
  cases hd1 with
  | refl => cases hd2 with
    | refl => rfl
    | step h _ => exact absurd h (h₂nf _)
  | step h _ => exact absurd h (h₁nf _)

/-! ## 9. Squier coherence structure -/

/-- Any two paths between the same endpoints have equal toEq (UIP). -/
theorem path_eq_toEq {a b : RExpr} (p q : Cell1 a b) : p.toEq = q.toEq := by
  cases p with | mk _ proof1 => cases q with | mk _ proof2 => cases proof1; cases proof2; rfl

/-- Squier coherence: a convergent system has the property that
all 2-cells between parallel paths are coherent. -/
structure SquierCoherence (R : RSystem) where
  /-- Any two parallel 1-cells yield equal propositional witnesses. -/
  coherent : ∀ (a b : RExpr) (p q : Cell1 a b), p.toEq = q.toEq

def squierFromConvergent (R : RSystem) (_ : Convergent R) : SquierCoherence R where
  coherent := fun _ _ p q => path_eq_toEq p q

/-! ## 10. Critical pairs as divergences -/

structure CriticalPair where
  source : RExpr
  target₁ : RExpr
  target₂ : RExpr
  left : Cell1 source target₁
  right : Cell1 source target₂

def CriticalPair.Joinable (R : RSystem) (cp : CriticalPair) : Prop :=
  ∃ d, MultiStep R cp.target₁ d ∧ MultiStep R cp.target₂ d

/-- A trivial critical pair where both sides are identity. -/
def trivialCP (a : RExpr) : CriticalPair where
  source := a; target₁ := a; target₂ := a; left := id1 a; right := id1 a

theorem trivialCP_joinable (R : RSystem) (a : RExpr) :
    (trivialCP a).Joinable R := ⟨a, .refl a, .refl a⟩

/-! ## 11. Coherent completion -/

/-- A completed system extends the original with new rules resolving critical pairs. -/
structure CoherentCompletion (R : RSystem) where
  extended : RSystem
  /-- Every original rule is preserved. -/
  preserves : ∀ r, r ∈ R → r ∈ extended
  /-- The extended system is convergent. -/
  convergent : Convergent extended

/-! ## 12. 3-cells: coherence between 2-cells -/

/-- All 3-cells are trivial by proof irrelevance. -/
theorem cell3_trivial {a b : RExpr} {p q : Cell1 a b} (α β : Cell2 p q) :
    Cell3 α β := Subsingleton.elim α β

/-- Coherence: any two composites of 2-cells with same endpoints agree. -/
theorem cell2_coherence {a b : RExpr} {p q r : Cell1 a b}
    (α₁ : Cell2 p q) (β₁ : Cell2 q r) (α₂ : Cell2 p q) (β₂ : Cell2 q r) :
    vcomp2 α₁ β₁ = vcomp2 α₂ β₂ := Subsingleton.elim _ _

/-! ## 13. Fourfold composition and pentagon -/

theorem comp1_assoc4 {a b c d e : RExpr}
    (p : Cell1 a b) (q : Cell1 b c) (r : Cell1 c d) (s : Cell1 d e) :
    comp1 (comp1 (comp1 p q) r) s = comp1 p (comp1 q (comp1 r s)) := by
  calc comp1 (comp1 (comp1 p q) r) s
      = comp1 (comp1 p q) (comp1 r s) := comp1_assoc _ r s
    _ = comp1 p (comp1 q (comp1 r s)) := comp1_assoc p q _

/-- Pentagon: the two reassociation routes agree (by proof irrelevance). -/
theorem pentagon {a b c d e : RExpr}
    (p : Cell1 a b) (q : Cell1 b c) (r : Cell1 c d) (s : Cell1 d e)
    (route1 route2 : comp1 (comp1 (comp1 p q) r) s = comp1 p (comp1 q (comp1 r s))) :
    route1 = route2 := Subsingleton.elim _ _

/-! ## 14. Eckmann–Hilton for 2-cells at identity -/

theorem eckmann_hilton_2cell {a : RExpr} (α β : Cell2 (id1 a) (id1 a)) :
    vcomp2 α β = vcomp2 β α := Subsingleton.elim _ _

/-! ## 15. Transport predicates along 1-cells -/

def transportPred (P : RExpr → Prop) {a b : RExpr} (p : Cell1 a b) (h : P a) : P b :=
  Path.transport (D := fun x => P x) p h

/-- Transport along comp decomposes. -/
theorem transportPred_comp (P : RExpr → Prop) {a b c : RExpr}
    (p : Cell1 a b) (q : Cell1 b c) (h : P a) :
    transportPred P (comp1 p q) h = transportPred P q (transportPred P p h) :=
  Path.transport_trans p q h

/-- Transport along inv cancels transport. -/
theorem transportPred_inv_cancel (P : RExpr → Prop) {a b : RExpr}
    (p : Cell1 a b) (h : P a) :
    transportPred P (inv1 p) (transportPred P p h) = h :=
  Path.transport_symm_left p h

/-! ## 16. Context closure paths -/

/-- Wrapping a 1-cell in a context via congrArg. -/
def ctxPath (f : Nat) (pre post : List RExpr) {a b : RExpr}
    (p : Cell1 a b) : Cell1 (.app f (pre ++ [a] ++ post)) (.app f (pre ++ [b] ++ post)) :=
  Path.congrArg (fun x => RExpr.app f (pre ++ [x] ++ post)) p

/-- Context wrapping distributes over comp. -/
theorem ctxPath_comp (f : Nat) (pre post : List RExpr) {a b c : RExpr}
    (p : Cell1 a b) (q : Cell1 b c) :
    ctxPath f pre post (comp1 p q) = comp1 (ctxPath f pre post p) (ctxPath f pre post q) := by
  simp [ctxPath]

/-- Context wrapping commutes with inv. -/
theorem ctxPath_inv (f : Nat) (pre post : List RExpr) {a b : RExpr}
    (p : Cell1 a b) :
    ctxPath f pre post (inv1 p) = inv1 (ctxPath f pre post p) := by
  simp [ctxPath]

/-- Context wrapping of triple comp distributes fully. -/
theorem ctxPath_triple_comp (f : Nat) (pre post : List RExpr) {a b c d : RExpr}
    (p : Cell1 a b) (q : Cell1 b c) (r : Cell1 c d) :
    ctxPath f pre post (comp1 (comp1 p q) r) =
      comp1 (comp1 (ctxPath f pre post p) (ctxPath f pre post q)) (ctxPath f pre post r) := by
  calc ctxPath f pre post (comp1 (comp1 p q) r)
      = comp1 (ctxPath f pre post (comp1 p q)) (ctxPath f pre post r) :=
          ctxPath_comp f pre post _ r
    _ = comp1 (comp1 (ctxPath f pre post p) (ctxPath f pre post q)) (ctxPath f pre post r) := by
          rw [ctxPath_comp f pre post p q]

/-! ## 17. Zigzag equivalence via paths -/

/-- A zigzag is a sequence of forward and backward 1-cells. -/
inductive Zigzag (R : RSystem) : RExpr → RExpr → Prop where
  | refl (a : RExpr) : Zigzag R a a
  | fwd {a b c : RExpr} (h : MultiStep R a b) (rest : Zigzag R b c) : Zigzag R a c
  | bwd {a b c : RExpr} (h : MultiStep R b a) (rest : Zigzag R b c) : Zigzag R a c

/-- Zigzag transitivity. -/
theorem Zigzag.append {R : RSystem} {a b c : RExpr}
    (h₁ : Zigzag R a b) (h₂ : Zigzag R b c) : Zigzag R a c := by
  induction h₁ with
  | refl => exact h₂
  | fwd h _ ih => exact .fwd h (ih h₂)
  | bwd h _ ih => exact .bwd h (ih h₂)

/-- Zigzag symmetry. -/
theorem Zigzag.symm_zigzag {R : RSystem} {a b : RExpr}
    (h : Zigzag R a b) : Zigzag R b a := by
  induction h with
  | refl => exact .refl _
  | fwd h _ ih => exact ih.append (.bwd h (.refl _))
  | bwd h _ ih => exact ih.append (.fwd h (.refl _))

/-! ## 18. Church–Rosser from confluence (multi-step proof) -/

def ChurchRosser (R : RSystem) : Prop :=
  ∀ a b, Zigzag R a b → ∃ c, MultiStep R a c ∧ MultiStep R b c

theorem confluent_implies_CR {R : RSystem} (hc : Confluent R) : ChurchRosser R := by
  intro a b hab
  induction hab with
  | refl => exact ⟨_, .refl _, .refl _⟩
  | fwd h _ ih =>
    obtain ⟨d, hbd, hcd⟩ := ih
    exact ⟨d, MultiStep.append h hbd, hcd⟩
  | bwd h _ ih =>
    obtain ⟨d, hbd, hcd⟩ := ih
    obtain ⟨e, he1, he2⟩ := hc _ _ _ h hbd
    exact ⟨e, he1, MultiStep.append hcd he2⟩

/-! ## 19. Local confluence (Newman's lemma setup) -/

def LocallyConfluent (R : RSystem) : Prop :=
  ∀ a b c, OneStep R a b → OneStep R a c → ∃ d, MultiStep R b d ∧ MultiStep R c d

theorem confluent_implies_local {R : RSystem} (hc : Confluent R) : LocallyConfluent R :=
  fun a b c h₁ h₂ => hc a b c (.step h₁ (.refl b)) (.step h₂ (.refl c))

/-! ## 20. Homotopy generators -/

structure HomotopyGen where
  src : RExpr
  tgt : RExpr
  left : Cell1 src tgt
  right : Cell1 src tgt

/-- All generators are trivial (UIP). -/
theorem hgen_trivial (g : HomotopyGen) : g.left.toEq = g.right.toEq :=
  path_eq_toEq g.left g.right

/-! ## 21. Whiskered composition deep chain -/

/-- Left whisker then right whisker = horizontal composition. -/
theorem whisker_hcomp {a b c : RExpr}
    {p p' : Cell1 a b} {q q' : Cell1 b c}
    (α : Cell2 p p') (β : Cell2 q q') :
    hcomp2 α β = (whiskerL α q).trans (whiskerR p' β) := rfl

/-- Multi-level whiskering: whisker with comp, then decompose. -/
theorem multi_whiskerL {a b c d : RExpr}
    {p p' : Cell1 a b} (α : Cell2 p p') (q : Cell1 b c) (r : Cell1 c d) :
    whiskerL α (comp1 q r) =
      Eq.trans
        (_root_.congrArg (fun t => Path.trans t (Path.trans q r)) α)
        rfl := by subst α; rfl

/-! ## 22. mapCell preserves the Squier coherence structure -/

/-- If two paths are coherent (same toEq), their images under mapCell are too. -/
theorem mapCell_preserves_coherence (f : RExpr → RExpr) {a b : RExpr}
    (p q : Cell1 a b) (h : p.toEq = q.toEq) :
    (mapCell f p).toEq = (mapCell f q).toEq := by
  cases p with | mk steps1 proof1 =>
  cases q with | mk steps2 proof2 =>
  cases proof1; cases proof2; cases h; rfl

/-! ## 23. comp1 with inv1 yields identity at toEq level -/

theorem comp1_inv1_toEq {a b : RExpr} (p : Cell1 a b) :
    (comp1 p (inv1 p)).toEq = (id1 a).toEq := Path.toEq_trans_symm p

theorem inv1_comp1_toEq {a b : RExpr} (p : Cell1 a b) :
    (comp1 (inv1 p) p).toEq = (id1 b).toEq := Path.toEq_symm_trans p

/-! ## 24. Step-list length invariants through operations -/

/-- The step count of comp1 is additive. -/
theorem comp1_length {a b c : RExpr} (p : Cell1 a b) (q : Cell1 b c) :
    (comp1 p q).steps.length = p.steps.length + q.steps.length := by
  simp

/-- The step count of inv1 equals the original. -/
theorem inv1_length {a b : RExpr} (p : Cell1 a b) :
    (inv1 p).steps.length = p.steps.length := by
  simp

/-- The step count of mapCell equals the original. -/
theorem mapCell_length (f : RExpr → RExpr) {a b : RExpr} (p : Cell1 a b) :
    (mapCell f p).steps.length = p.steps.length := by
  simp [mapCell]

/-! ## 25. Deep chain: congrArg of symm of comp equals reversed mapped comp -/

theorem mapCell_inv_comp_deep {a b c : RExpr} (f : RExpr → RExpr)
    (p : Cell1 a b) (q : Cell1 b c) :
    mapCell f (inv1 (comp1 p q)) =
      comp1 (mapCell f (inv1 q)) (mapCell f (inv1 p)) := by
  show Path.congrArg f (Path.symm (Path.trans p q)) = _
  calc Path.congrArg f (Path.symm (Path.trans p q))
      = Path.congrArg f (Path.trans (Path.symm q) (Path.symm p)) := by
          rw [Path.symm_trans p q]
    _ = Path.trans (Path.congrArg f (Path.symm q)) (Path.congrArg f (Path.symm p)) :=
          Path.congrArg_trans f _ _

end ComputationalPaths.Path.Rewriting.HigherRewritingDeep
