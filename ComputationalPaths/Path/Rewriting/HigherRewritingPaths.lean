/-
# Higher-Dimensional Rewriting via Structural Computational Paths

This module formalizes higher-dimensional rewriting where 1-cells are
Paths between expressions, coherence laws use Path algebra (trans, symm,
congrArg, transport), and Squier-style coherence connects to UIP.

## References

- Squier, "Word problems and a homological finiteness condition" (1994)
- Guiraud & Malbos, "Higher-dimensional normalisation strategies" (2012)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Rewriting.HigherRewritingPaths

open ComputationalPaths.Path

universe u

/-! ## Expression language -/

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
end HRExpr

/-! ## 1-cells as Paths -/

abbrev Cell1 (a b : HRExpr) := ComputationalPaths.Path a b

@[simp] def id1 (a : HRExpr) : Cell1 a a := Path.refl a

@[simp] def comp1 {a b c : HRExpr} (p : Cell1 a b) (q : Cell1 b c) : Cell1 a c :=
  Path.trans p q

@[simp] def inv1 {a b : HRExpr} (p : Cell1 a b) : Cell1 b a :=
  Path.symm p

/-! ## 1-cell coherence -/

theorem comp1_assoc {a b c d : HRExpr}
    (p : Cell1 a b) (q : Cell1 b c) (r : Cell1 c d) :
    comp1 (comp1 p q) r = comp1 p (comp1 q r) :=
  Path.trans_assoc p q r

theorem comp1_id_left {a b : HRExpr} (p : Cell1 a b) :
    comp1 (id1 a) p = p := Path.trans_refl_left p

theorem comp1_id_right {a b : HRExpr} (p : Cell1 a b) :
    comp1 p (id1 b) = p := Path.trans_refl_right p

theorem inv1_inv1 {a b : HRExpr} (p : Cell1 a b) :
    inv1 (inv1 p) = p := Path.symm_symm p

theorem inv1_comp1 {a b c : HRExpr} (p : Cell1 a b) (q : Cell1 b c) :
    inv1 (comp1 p q) = comp1 (inv1 q) (inv1 p) :=
  Path.symm_trans p q

theorem inv1_right_toEq {a b : HRExpr} (p : Cell1 a b) :
    (comp1 p (inv1 p)).toEq = rfl := Path.toEq_trans_symm p

theorem inv1_left_toEq {a b : HRExpr} (p : Cell1 a b) :
    (comp1 (inv1 p) p).toEq = rfl := Path.toEq_symm_trans p

theorem comp1_pentagon {a b c d e : HRExpr}
    (p : Cell1 a b) (q : Cell1 b c) (r : Cell1 c d) (s : Cell1 d e) :
    comp1 (comp1 (comp1 p q) r) s = comp1 p (comp1 q (comp1 r s)) :=
  Path.trans_assoc_fourfold p q r s

/-! ## congrArg-based functoriality for expression constructors -/

def mapCell1 (f : HRExpr → HRExpr) {a b : HRExpr}
    (p : Cell1 a b) : Cell1 (f a) (f b) :=
  Path.congrArg f p

@[simp] theorem mapCell1_refl (f : HRExpr → HRExpr) (a : HRExpr) :
    mapCell1 f (id1 a) = id1 (f a) := by simp [mapCell1]

@[simp] theorem mapCell1_trans (f : HRExpr → HRExpr) {a b c : HRExpr}
    (p : Cell1 a b) (q : Cell1 b c) :
    mapCell1 f (comp1 p q) = comp1 (mapCell1 f p) (mapCell1 f q) := by
  simp [mapCell1]

@[simp] theorem mapCell1_symm (f : HRExpr → HRExpr) {a b : HRExpr}
    (p : Cell1 a b) :
    mapCell1 f (inv1 p) = inv1 (mapCell1 f p) := by simp [mapCell1]

/-- unary congruence path. -/
def unaryPath (op : Nat) {a b : HRExpr} (p : Cell1 a b) :
    Cell1 (HRExpr.unary op a) (HRExpr.unary op b) :=
  Path.congrArg (HRExpr.unary op) p

/-- binary-left congruence path. -/
def binaryLeftPath (op : Nat) (r : HRExpr) {a b : HRExpr} (p : Cell1 a b) :
    Cell1 (HRExpr.binary op a r) (HRExpr.binary op b r) :=
  Path.congrArg (fun x => HRExpr.binary op x r) p

/-- binary-right congruence path. -/
def binaryRightPath (op : Nat) (l : HRExpr) {a b : HRExpr} (p : Cell1 a b) :
    Cell1 (HRExpr.binary op l a) (HRExpr.binary op l b) :=
  Path.congrArg (fun x => HRExpr.binary op l x) p

@[simp] theorem unaryPath_refl (op : Nat) (a : HRExpr) :
    unaryPath op (id1 a) = id1 (HRExpr.unary op a) := by
  simp [unaryPath]

@[simp] theorem binaryLeftPath_refl (op : Nat) (r a : HRExpr) :
    binaryLeftPath op r (id1 a) = id1 (HRExpr.binary op a r) := by
  simp [binaryLeftPath]

@[simp] theorem binaryRightPath_refl (op : Nat) (l a : HRExpr) :
    binaryRightPath op l (id1 a) = id1 (HRExpr.binary op l a) := by
  simp [binaryRightPath]

@[simp] theorem unaryPath_trans (op : Nat) {a b c : HRExpr}
    (p : Cell1 a b) (q : Cell1 b c) :
    unaryPath op (comp1 p q) = comp1 (unaryPath op p) (unaryPath op q) := by
  simp [unaryPath]

@[simp] theorem unaryPath_symm (op : Nat) {a b : HRExpr}
    (p : Cell1 a b) :
    unaryPath op (inv1 p) = inv1 (unaryPath op p) := by
  simp [unaryPath]

@[simp] theorem binaryLeftPath_trans (op : Nat) (r : HRExpr) {a b c : HRExpr}
    (p : Cell1 a b) (q : Cell1 b c) :
    binaryLeftPath op r (comp1 p q) =
      comp1 (binaryLeftPath op r p) (binaryLeftPath op r q) := by
  simp [binaryLeftPath]

@[simp] theorem binaryRightPath_trans (op : Nat) (l : HRExpr) {a b c : HRExpr}
    (p : Cell1 a b) (q : Cell1 b c) :
    binaryRightPath op l (comp1 p q) =
      comp1 (binaryRightPath op l p) (binaryRightPath op l q) := by
  simp [binaryRightPath]

/-! ## Rewriting Systems -/

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
  | step {a b c : HRExpr} (h : HROneStep R a b) (rest : HRMultiStep R b c) :
      HRMultiStep R a c

theorem HRMultiStep.single {R : HRS} {a b : HRExpr} (h : HROneStep R a b) :
    HRMultiStep R a b := .step h (.refl b)

theorem HRMultiStep.trans {R : HRS} {a b c : HRExpr}
    (h₁ : HRMultiStep R a b) (h₂ : HRMultiStep R b c) :
    HRMultiStep R a c := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

/-! ## Confluence -/

def HRConfluent (R : HRS) : Prop :=
  ∀ a b c : HRExpr, HRMultiStep R a b → HRMultiStep R a c →
    ∃ d, HRMultiStep R b d ∧ HRMultiStep R c d

def HRIsNF (R : HRS) (t : HRExpr) : Prop :=
  ∀ u : HRExpr, ¬ HROneStep R t u

theorem unique_nf {R : HRS} (hc : HRConfluent R)
    {a nf1 nf2 : HRExpr}
    (h1 : HRMultiStep R a nf1) (h1nf : HRIsNF R nf1)
    (h2 : HRMultiStep R a nf2) (h2nf : HRIsNF R nf2) :
    nf1 = nf2 := by
  obtain ⟨d, hd1, hd2⟩ := hc a nf1 nf2 h1 h2
  cases hd1 with
  | refl => cases hd2 with
    | refl => rfl
    | step h _ => exact absurd h (h2nf _)
  | step h _ => exact absurd h (h1nf _)

/-! ## Squier-style Coherence -/

theorem path_toEq_unique {a b : HRExpr} (p q : Cell1 a b) :
    p.toEq = q.toEq := by
  cases p with | mk _ proof1 => cases q with | mk _ proof2 =>
    cases proof1; cases proof2; rfl

theorem squier_coherence {a nf : HRExpr} (p q : Cell1 a nf) :
    p.toEq = q.toEq := path_toEq_unique p q

/-! ## Empty System -/

theorem no_step_empty {a b : HRExpr} : ¬ HROneStep ([] : HRS) a b := by
  intro h
  cases h with
  | rule r hmem => simp at hmem
  | unaryCtx _ h => exact no_step_empty h
  | binaryCtxL _ _ h => exact no_step_empty h
  | binaryCtxR _ _ h => exact no_step_empty h

theorem empty_confluent : HRConfluent ([] : HRS) := by
  intro a b c h1 h2
  cases h1 with
  | refl => exact ⟨c, h2, .refl c⟩
  | step h _ => exact absurd h no_step_empty

/-! ## Transport along Higher Rewrite Paths -/

@[simp] def transportPred (P : HRExpr → Prop) {a b : HRExpr}
    (p : Cell1 a b) (h : P a) : P b :=
  Path.transport (D := fun x => P x) p h

theorem transportPred_refl (P : HRExpr → Prop) (a : HRExpr) (h : P a) :
    transportPred P (id1 a) h = h := rfl

theorem transportPred_comp (P : HRExpr → Prop) {a b c : HRExpr}
    (p : Cell1 a b) (q : Cell1 b c) (h : P a) :
    transportPred P (comp1 p q) h =
      transportPred P q (transportPred P p h) := by simp

theorem transportPred_symm (P : HRExpr → Prop) {a b : HRExpr}
    (p : Cell1 a b) (h : P a) :
    transportPred P (inv1 p) (transportPred P p h) = h := by simp

/-! ## congrArg for HRExpr.size -/

def sizePath {a b : HRExpr} (p : Cell1 a b) :
    ComputationalPaths.Path a.size b.size :=
  Path.congrArg HRExpr.size p

@[simp] theorem sizePath_refl (a : HRExpr) :
    sizePath (id1 a) = Path.refl a.size := by simp [sizePath]

@[simp] theorem sizePath_comp {a b c : HRExpr}
    (p : Cell1 a b) (q : Cell1 b c) :
    sizePath (comp1 p q) = Path.trans (sizePath p) (sizePath q) := by
  simp [sizePath]

@[simp] theorem sizePath_inv {a b : HRExpr}
    (p : Cell1 a b) :
    sizePath (inv1 p) = Path.symm (sizePath p) := by simp [sizePath]

/-! ## Church-Rosser -/

inductive HRConversion (R : HRS) : HRExpr → HRExpr → Prop where
  | fwd {a b : HRExpr} : HRMultiStep R a b → HRConversion R a b
  | bwd {a b : HRExpr} : HRMultiStep R b a → HRConversion R a b
  | trans {a b c : HRExpr} : HRConversion R a b → HRConversion R b c →
      HRConversion R a c

def HRChurchRosser (R : HRS) : Prop :=
  ∀ a b : HRExpr, HRConversion R a b →
    ∃ c, HRMultiStep R a c ∧ HRMultiStep R b c

theorem confluent_implies_churchRosser {R : HRS}
    (hc : HRConfluent R) : HRChurchRosser R := by
  intro x y hxy
  induction hxy with
  | fwd h => exact ⟨_, h, .refl _⟩
  | bwd h => exact ⟨_, .refl _, h⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨c1, hac1, hbc1⟩ := ih1
    obtain ⟨c2, hbc2, hcc2⟩ := ih2
    obtain ⟨d, hc1d, hc2d⟩ := hc _ c1 c2 hbc1 hbc2
    exact ⟨d, hac1.trans hc1d, hcc2.trans hc2d⟩

end ComputationalPaths.Path.Rewriting.HigherRewritingPaths
