/-
# Higher-Dimensional Rewriting via Structural Computational Paths

This module formalizes higher-dimensional rewriting where:
- 2-cells are equalities between Paths (path rewrites)
- Coherence conditions are expressed via Path algebra
- Squier's theorem relates finite convergent systems to coherence
- Path composition, symmetry, congrArg used throughout

## References

- Squier, "Word problems and a homological finiteness condition" (1994)
- Guiraud & Malbos, "Higher-dimensional normalisation strategies" (2012)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Rewriting.HigherRewritingPaths

open ComputationalPaths.Path

universe u

/-! ## Expression language for higher rewriting -/

inductive HRExpr where
  | var (n : Nat) : HRExpr
  | const (c : Nat) : HRExpr
  | unary (op : Nat) (e : HRExpr) : HRExpr
  | binary (op : Nat) (l r : HRExpr) : HRExpr
  deriving DecidableEq, Repr

namespace HRExpr

@[simp] def size : HRExpr → Nat
  | .var _ => 1
  | .const _ => 1
  | .unary _ e => e.size + 1
  | .binary _ l r => l.size + r.size + 1

theorem size_pos (e : HRExpr) : 0 < e.size := by cases e <;> simp <;> omega

@[simp] def depth : HRExpr → Nat
  | .var _ => 0
  | .const _ => 0
  | .unary _ e => e.depth + 1
  | .binary _ l r => max l.depth r.depth + 1

@[simp] def isGround : HRExpr → Bool
  | .var _ => false
  | .const _ => true
  | .unary _ e => e.isGround
  | .binary _ l r => l.isGround && r.isGround

end HRExpr

/-! ## 1-cells and 2-cells -/

abbrev Cell1 (a b : HRExpr) := Path a b
abbrev Cell2 {a b : HRExpr} (p q : Cell1 a b) := p = q

@[simp] def id1 (a : HRExpr) : Cell1 a a := Path.refl a
@[simp] def comp1 {a b c : HRExpr} (p : Cell1 a b) (q : Cell1 b c) : Cell1 a c := Path.trans p q
@[simp] def inv1 {a b : HRExpr} (p : Cell1 a b) : Cell1 b a := Path.symm p

/-! ## 1-cell coherence -/

theorem comp1_assoc {a b c d : HRExpr} (p : Cell1 a b) (q : Cell1 b c) (r : Cell1 c d) :
    comp1 (comp1 p q) r = comp1 p (comp1 q r) := Path.trans_assoc p q r

theorem comp1_id_left {a b : HRExpr} (p : Cell1 a b) : comp1 (id1 a) p = p := Path.trans_refl_left p
theorem comp1_id_right {a b : HRExpr} (p : Cell1 a b) : comp1 p (id1 b) = p := Path.trans_refl_right p

theorem inv1_inv1 {a b : HRExpr} (p : Cell1 a b) : inv1 (inv1 p) = p := Path.symm_symm p

theorem inv1_comp1 {a b c : HRExpr} (p : Cell1 a b) (q : Cell1 b c) :
    inv1 (comp1 p q) = comp1 (inv1 q) (inv1 p) := Path.symm_trans p q

theorem inv1_id1 (a : HRExpr) : inv1 (id1 a) = id1 a := Path.symm_refl a

/-! ## 2-cell coherence -/

theorem cell2_refl {a b : HRExpr} (p : Cell1 a b) : Cell2 p p := rfl
theorem cell2_symm {a b : HRExpr} {p q : Cell1 a b} (α : Cell2 p q) : Cell2 q p := α.symm
theorem cell2_trans {a b : HRExpr} {p q r : Cell1 a b} (α : Cell2 p q) (β : Cell2 q r) : Cell2 p r := α.trans β

theorem cell2_trans_assoc {a b : HRExpr} {p q r s : Cell1 a b}
    (α : Cell2 p q) (β : Cell2 q r) (γ : Cell2 r s) :
    (α.trans β).trans γ = α.trans (β.trans γ) := by subst α; subst β; subst γ; rfl

theorem cell2_symm_trans {a b : HRExpr} {p q : Cell1 a b} (α : Cell2 p q) :
    α.symm.trans α = rfl := by subst α; rfl

theorem cell2_trans_symm {a b : HRExpr} {p q : Cell1 a b} (α : Cell2 p q) :
    α.trans α.symm = rfl := by subst α; rfl

theorem cell2_symm_symm {a b : HRExpr} {p q : Cell1 a b} (α : Cell2 p q) :
    α.symm.symm = α := by subst α; rfl

/-! ## Whiskering -/

def whiskerL {a b c : HRExpr} {p p' : Cell1 a b}
    (α : Cell2 p p') (q : Cell1 b c) : Cell2 (comp1 p q) (comp1 p' q) :=
  _root_.congrArg (fun t => Path.trans t q) α

def whiskerR {a b c : HRExpr} (p : Cell1 a b)
    {q q' : Cell1 b c} (β : Cell2 q q') : Cell2 (comp1 p q) (comp1 p q') :=
  _root_.congrArg (fun t => Path.trans p t) β

theorem interchange {a b c : HRExpr}
    {p p' : Cell1 a b} {q q' : Cell1 b c}
    (α : Cell2 p p') (β : Cell2 q q') :
    (whiskerL α q).trans (whiskerR p' β) =
    (whiskerR p β).trans (whiskerL α q') := by subst α; subst β; rfl

theorem whisker_naturality {a b c : HRExpr}
    {p p' : Cell1 a b} {q q' : Cell1 b c}
    (α : Cell2 p p') (β : Cell2 q q') :
    (whiskerR p β).trans (whiskerL α q') =
    (whiskerL α q).trans (whiskerR p' β) := by subst α; subst β; rfl

/-! ## congrArg functoriality -/

def mapCell1 (f : HRExpr → HRExpr) {a b : HRExpr} (p : Cell1 a b) : Cell1 (f a) (f b) :=
  Path.congrArg f p

theorem mapCell1_id {a b : HRExpr} (p : Cell1 a b) :
    mapCell1 (fun x => x) p = p := by
  simp [mapCell1]

theorem mapCell1_refl (f : HRExpr → HRExpr) (a : HRExpr) :
    mapCell1 f (id1 a) = id1 (f a) := by
  simp [mapCell1]

theorem mapCell1_comp1 (f : HRExpr → HRExpr) {a b c : HRExpr}
    (p : Cell1 a b) (q : Cell1 b c) :
    mapCell1 f (comp1 p q) = comp1 (mapCell1 f p) (mapCell1 f q) := by
  simp [mapCell1]

theorem mapCell1_inv1 (f : HRExpr → HRExpr) {a b : HRExpr} (p : Cell1 a b) :
    mapCell1 f (inv1 p) = inv1 (mapCell1 f p) := by
  simp [mapCell1]

/-! ## Rewrite rules and multi-step -/

structure HRRule where
  lhs : HRExpr
  rhs : HRExpr

abbrev HRS := List HRRule

inductive HROneStep (R : HRS) : HRExpr → HRExpr → Prop where
  | rule (r : HRRule) (hmem : r ∈ R) : HROneStep R r.lhs r.rhs
  | unaryCtx (op : Nat) {a b : HRExpr} (h : HROneStep R a b) :
      HROneStep R (.unary op a) (.unary op b)
  | binaryCtxL (op : Nat) {a b : HRExpr} (r : HRExpr) (h : HROneStep R a b) :
      HROneStep R (.binary op a r) (.binary op b r)
  | binaryCtxR (op : Nat) (l : HRExpr) {a b : HRExpr} (h : HROneStep R a b) :
      HROneStep R (.binary op l a) (.binary op l b)

inductive HRMultiStep (R : HRS) : HRExpr → HRExpr → Prop where
  | refl (a : HRExpr) : HRMultiStep R a a
  | step {a b c : HRExpr} (h : HROneStep R a b) (rest : HRMultiStep R b c) : HRMultiStep R a c

theorem HRMultiStep.single {R : HRS} {a b : HRExpr} (h : HROneStep R a b) :
    HRMultiStep R a b := .step h (.refl b)

theorem HRMultiStep.append {R : HRS} {a b c : HRExpr}
    (h₁ : HRMultiStep R a b) (h₂ : HRMultiStep R b c) : HRMultiStep R a c := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

/-! ## Confluence, termination, convergence -/

def HRConfluent (R : HRS) : Prop :=
  ∀ a b c, HRMultiStep R a b → HRMultiStep R a c → ∃ d, HRMultiStep R b d ∧ HRMultiStep R c d

def HRTerminating (R : HRS) : Prop :=
  ¬ ∃ f : Nat → HRExpr, ∀ n, HROneStep R (f n) (f (n + 1))

def HRConvergent (R : HRS) : Prop := HRConfluent R ∧ HRTerminating R

def HRIsNF (R : HRS) (t : HRExpr) : Prop := ∀ u, ¬ HROneStep R t u

theorem unique_nf {R : HRS} (hc : HRConfluent R) {a nf1 nf2 : HRExpr}
    (h1 : HRMultiStep R a nf1) (h1nf : HRIsNF R nf1)
    (h2 : HRMultiStep R a nf2) (h2nf : HRIsNF R nf2) : nf1 = nf2 := by
  obtain ⟨d, hd1, hd2⟩ := hc a nf1 nf2 h1 h2
  cases hd1 with
  | refl => cases hd2 with
    | refl => rfl
    | step h _ => exact absurd h (h2nf _)
  | step h _ => exact absurd h (h1nf _)

/-! ## Empty system -/

theorem no_step_empty {a b : HRExpr} : ¬ HROneStep ([] : HRS) a b := by
  intro h
  induction h with
  | rule _ hmem => simp at hmem
  | unaryCtx _ _ ih => exact ih
  | binaryCtxL _ _ _ ih => exact ih
  | binaryCtxR _ _ _ ih => exact ih

theorem empty_confluent : HRConfluent ([] : HRS) := by
  intro a b c h1 _
  cases h1 with
  | refl => exact ⟨c, ‹_›, .refl c⟩
  | step h _ => exact absurd h no_step_empty

theorem empty_terminating : HRTerminating ([] : HRS) := by
  intro ⟨f, hf⟩; exact absurd (hf 0) no_step_empty

theorem empty_convergent : HRConvergent ([] : HRS) := ⟨empty_confluent, empty_terminating⟩

/-! ## Church-Rosser -/

inductive HRConversion (R : HRS) : HRExpr → HRExpr → Prop where
  | fwd {a b} : HRMultiStep R a b → HRConversion R a b
  | bwd {a b} : HRMultiStep R b a → HRConversion R a b
  | trans {a b c} : HRConversion R a b → HRConversion R b c → HRConversion R a c

def HRChurchRosser (R : HRS) : Prop :=
  ∀ a b, HRConversion R a b → ∃ c, HRMultiStep R a c ∧ HRMultiStep R b c

theorem confluent_implies_churchRosser {R : HRS} (hc : HRConfluent R) : HRChurchRosser R := by
  intro a b hab
  induction hab with
  | fwd h => exact ⟨_, h, .refl _⟩
  | bwd h => exact ⟨_, .refl _, h⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨d₁, ha_d₁, hb_d₁⟩ := ih1
    obtain ⟨d₂, hb_d₂, hc_d₂⟩ := ih2
    obtain ⟨d₃, hd₁_d₃, hd₂_d₃⟩ := hc _ _ _ hb_d₁ hb_d₂
    exact ⟨d₃, HRMultiStep.append ha_d₁ hd₁_d₃, HRMultiStep.append hc_d₂ hd₂_d₃⟩

/-! ## Transport along paths -/

def transportPred (P : HRExpr → Prop) {a b : HRExpr} (p : Cell1 a b) (h : P a) : P b :=
  Path.transport (D := fun x => P x) p h

theorem transportPred_refl (P : HRExpr → Prop) (a : HRExpr) (h : P a) :
    transportPred P (id1 a) h = h := rfl

theorem transportPred_comp (P : HRExpr → Prop) {a b c : HRExpr}
    (p : Cell1 a b) (q : Cell1 b c) (h : P a) :
    transportPred P (comp1 p q) h = transportPred P q (transportPred P p h) :=
  Path.transport_trans p q h

theorem transportPred_symm_left (P : HRExpr → Prop) {a b : HRExpr}
    (p : Cell1 a b) (h : P a) :
    transportPred P (inv1 p) (transportPred P p h) = h :=
  Path.transport_symm_left p h

/-! ## congrArg paths for constructors -/

def unaryPath (op : Nat) {a b : HRExpr} (p : Cell1 a b) :
    Cell1 (.unary op a) (.unary op b) := Path.congrArg (HRExpr.unary op) p

def binaryLeftPath (op : Nat) {a b : HRExpr} (r : HRExpr) (p : Cell1 a b) :
    Cell1 (.binary op a r) (.binary op b r) := Path.congrArg (fun x => HRExpr.binary op x r) p

def binaryRightPath (op : Nat) (l : HRExpr) {a b : HRExpr} (p : Cell1 a b) :
    Cell1 (.binary op l a) (.binary op l b) := Path.congrArg (fun x => HRExpr.binary op l x) p

theorem unaryPath_refl (op : Nat) (a : HRExpr) :
    unaryPath op (id1 a) = id1 (.unary op a) := by simp [unaryPath]

theorem binaryLeftPath_refl (op : Nat) (a r : HRExpr) :
    binaryLeftPath op r (id1 a) = id1 (.binary op a r) := by simp [binaryLeftPath]

theorem binaryRightPath_refl (op : Nat) (l a : HRExpr) :
    binaryRightPath op l (id1 a) = id1 (.binary op l a) := by simp [binaryRightPath]

theorem unaryPath_comp (op : Nat) {a b c : HRExpr} (p : Cell1 a b) (q : Cell1 b c) :
    unaryPath op (comp1 p q) = comp1 (unaryPath op p) (unaryPath op q) := by
  simp [unaryPath]

theorem binaryLeftPath_comp (op : Nat) (r : HRExpr) {a b c : HRExpr}
    (p : Cell1 a b) (q : Cell1 b c) :
    binaryLeftPath op r (comp1 p q) = comp1 (binaryLeftPath op r p) (binaryLeftPath op r q) := by
  simp [binaryLeftPath]

theorem binaryRightPath_comp (op : Nat) (l : HRExpr) {a b c : HRExpr}
    (p : Cell1 a b) (q : Cell1 b c) :
    binaryRightPath op l (comp1 p q) = comp1 (binaryRightPath op l p) (binaryRightPath op l q) := by
  simp [binaryRightPath]

/-! ## Pentagon coherence -/

theorem comp1_pentagon {a b c d e : HRExpr}
    (p : Cell1 a b) (q : Cell1 b c) (r : Cell1 c d) (s : Cell1 d e) :
    comp1 (comp1 (comp1 p q) r) s = comp1 p (comp1 q (comp1 r s)) :=
  Path.trans_assoc_fourfold p q r s

/-! ## Step-level constructions -/

def stepUnary (op : Nat) (s : Step HRExpr) : Step HRExpr := Step.map (HRExpr.unary op) s
def stepBinaryL (op : Nat) (r : HRExpr) (s : Step HRExpr) : Step HRExpr := Step.map (fun x => HRExpr.binary op x r) s
def stepBinaryR (op : Nat) (l : HRExpr) (s : Step HRExpr) : Step HRExpr := Step.map (fun x => HRExpr.binary op l x) s

theorem stepUnary_symm (op : Nat) (s : Step HRExpr) :
    (stepUnary op s).symm = stepUnary op s.symm := by simp [stepUnary]

theorem stepBinaryL_symm (op : Nat) (r : HRExpr) (s : Step HRExpr) :
    (stepBinaryL op r s).symm = stepBinaryL op r s.symm := by simp [stepBinaryL]

theorem stepBinaryR_symm (op : Nat) (l : HRExpr) (s : Step HRExpr) :
    (stepBinaryR op l s).symm = stepBinaryR op l s.symm := by simp [stepBinaryR]

/-! ## Squier-style coherence -/

/-- In UIP, any two paths with the same endpoints have equal toEq. -/
theorem path_toEq_unique {a b : HRExpr} (p q : Cell1 a b) : p.toEq = q.toEq := by
  cases p with | mk _ proof1 => cases q with | mk _ proof2 => cases proof1; cases proof2; rfl

structure SquierCoherence (R : HRS) where
  coherent : ∀ (a b : HRExpr) (p q : Path a b), p.toEq = q.toEq

def squierCoherenceFromUIP (R : HRS) : SquierCoherence R where
  coherent := fun _ _ p q => path_toEq_unique p q

/-! ## Homotopy basis -/

structure HomotopyGenerator where
  src : HRExpr
  tgt : HRExpr
  left : Path src tgt
  right : Path src tgt

abbrev HomotopyBasis := List HomotopyGenerator

def HomotopyGenerator.IsTrivial (g : HomotopyGenerator) : Prop := g.left.toEq = g.right.toEq

theorem all_generators_trivial (g : HomotopyGenerator) : g.IsTrivial :=
  path_toEq_unique g.left g.right

/-! ## Critical pairs as path divergences -/

structure CriticalPairHR where
  source : HRExpr
  target1 : HRExpr
  target2 : HRExpr
  left : Cell1 source target1
  right : Cell1 source target2

def CriticalPairHR.Joinable (R : HRS) (cp : CriticalPairHR) : Prop :=
  ∃ d, HRMultiStep R cp.target1 d ∧ HRMultiStep R cp.target2 d

def trivialCriticalPair (a : HRExpr) : CriticalPairHR where
  source := a; target1 := a; target2 := a; left := id1 a; right := id1 a

theorem trivialCriticalPair_joinable (R : HRS) (a : HRExpr) :
    (trivialCriticalPair a).Joinable R := ⟨a, .refl a, .refl a⟩

/-! ## Local confluence -/

def HRLocallyConfluent (R : HRS) : Prop :=
  ∀ a b c, HROneStep R a b → HROneStep R a c → ∃ d, HRMultiStep R b d ∧ HRMultiStep R c d

theorem confluent_implies_locally {R : HRS} (hc : HRConfluent R) : HRLocallyConfluent R := by
  intro a b c h1 h2; exact hc a b c (HRMultiStep.single h1) (HRMultiStep.single h2)

/-! ## Dimension analysis -/

inductive CellDim where
  | zero | one | two
  deriving DecidableEq

def cell1_src {a b : HRExpr} (_ : Cell1 a b) : HRExpr := a
def cell1_tgt {a b : HRExpr} (_ : Cell1 a b) : HRExpr := b

theorem cell1_src_refl (a : HRExpr) : cell1_src (id1 a) = a := rfl
theorem cell1_tgt_refl (a : HRExpr) : cell1_tgt (id1 a) = a := rfl
theorem cell1_src_comp {a b c : HRExpr} (p : Cell1 a b) (q : Cell1 b c) : cell1_src (comp1 p q) = cell1_src p := rfl
theorem cell1_tgt_comp {a b c : HRExpr} (p : Cell1 a b) (q : Cell1 b c) : cell1_tgt (comp1 p q) = cell1_tgt q := rfl

/-! ## Globular identities -/

theorem globular_src_src {a b : HRExpr} (p : Cell1 a b) :
    cell1_src (id1 (cell1_src p)) = cell1_src p := rfl

theorem globular_tgt_tgt {a b : HRExpr} (p : Cell1 a b) :
    cell1_tgt (id1 (cell1_tgt p)) = cell1_tgt p := rfl

/-! ## Convergent system properties -/

theorem convergent_unique_nf {R : HRS} (hconv : HRConvergent R) {a nf1 nf2 : HRExpr}
    (h1 : HRMultiStep R a nf1) (h1nf : HRIsNF R nf1)
    (h2 : HRMultiStep R a nf2) (h2nf : HRIsNF R nf2) : nf1 = nf2 :=
  unique_nf hconv.1 h1 h1nf h2 h2nf

/-! ## Eckmann-Hilton -/

theorem eckmann_hilton {a : HRExpr} (α β : Cell2 (id1 a) (id1 a)) :
    α.trans β = β.trans α := Subsingleton.elim _ _

/-! ## Multi-step path helpers -/

def multiStepReflPath (a : HRExpr) : Cell1 a a := id1 a

theorem multiStepReflPath_is_id (a : HRExpr) : multiStepReflPath a = id1 a := rfl

def multiStepTransPath {a b c : HRExpr} (p : Cell1 a b) (q : Cell1 b c) : Cell1 a c := comp1 p q

theorem multiStepTransPath_assoc {a b c d : HRExpr}
    (p : Cell1 a b) (q : Cell1 b c) (r : Cell1 c d) :
    multiStepTransPath (multiStepTransPath p q) r =
    multiStepTransPath p (multiStepTransPath q r) := comp1_assoc p q r

end ComputationalPaths.Path.Rewriting.HigherRewritingPaths
