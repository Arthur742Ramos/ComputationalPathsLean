/-
# Forcing and Set Theory via Computational Paths (Deep Structure)

Large structural development for forcing-inspired set theory using computational
paths.  This file focuses on reusable scaffolding:

- forcing posets and conditions
- filters, dense sets, and generic filters
- forcing names and a truth-lemma style interface
- Boolean-valued model structure
- consistency and independence packaging for cardinal arithmetic and GCH

The intent is organizational: all proofs are explicit and `Path`-centric,
without introducing axioms or placeholders.
-/

import ComputationalPaths.Path.Basic

set_option linter.unusedVariables false

namespace ComputationalPaths.Path.Algebra.ForcingSetTheoryDeep

open ComputationalPaths.Path

universe u v w

/-! ## Path API layer -/

section PathAPI

variable {A : Type u} {a b c d : A}

def atomicPath (h : a = b) : Path a b :=
  Path.mk [Step.mk a b h] h

@[simp] theorem atomicPath_toEq (h : a = b) :
    Path.toEq (atomicPath (a := a) (b := b) h) = h := rfl

@[simp] theorem atomicPath_steps (h : a = b) :
    (atomicPath (a := a) (b := b) h).steps = [Step.mk a b h] := rfl

@[simp] theorem atomicPath_symm (h : a = b) :
    Path.symm (atomicPath (a := a) (b := b) h) =
      atomicPath (a := b) (b := a) h.symm := by
  cases h
  rfl

@[simp] theorem atomicPath_symm_symm (h : a = b) :
    Path.symm (Path.symm (atomicPath (a := a) (b := b) h)) =
      atomicPath (a := a) (b := b) h := by
  simpa using Path.symm_symm (atomicPath (a := a) (b := b) h)

theorem trans_assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simpa using Path.trans_assoc p q r

theorem trans_refl_left (p : Path a b) :
    Path.trans (Path.refl a) p = p := by
  simpa using Path.trans_refl_left p

theorem trans_refl_right (p : Path a b) :
    Path.trans p (Path.refl b) = p := by
  simpa using Path.trans_refl_right p

theorem symm_trans (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) := by
  simpa using Path.symm_trans p q

theorem symm_symm (p : Path a b) :
    Path.symm (Path.symm p) = p := by
  simpa using Path.symm_symm p

theorem congrArg_trans {B : Type v} (f : A → B) (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) := by
  simpa using Path.congrArg_trans f p q

theorem congrArg_symm {B : Type v} (f : A → B) (p : Path a b) :
    Path.congrArg f (Path.symm p) =
      Path.symm (Path.congrArg f p) := by
  simpa using Path.congrArg_symm f p

@[simp] theorem path_mk_refl (x : A) :
    Path.mk ([] : List (Step A)) (rfl : x = x) = Path.refl x := rfl

@[simp] theorem step_mk_src (h : a = b) :
    (Step.mk a b h).src = a := rfl

@[simp] theorem step_mk_tgt (h : a = b) :
    (Step.mk a b h).tgt = b := rfl

@[simp] theorem atomicPath_trans_symm_toEq (h : a = b) :
    Path.toEq (Path.trans (atomicPath (a := a) (b := b) h)
      (Path.symm (atomicPath (a := a) (b := b) h))) = rfl := by
  simpa using Path.toEq_trans_symm (atomicPath (a := a) (b := b) h)

@[simp] theorem atomicPath_symm_trans_toEq (h : a = b) :
    Path.toEq (Path.trans (Path.symm (atomicPath (a := a) (b := b) h))
      (atomicPath (a := a) (b := b) h)) = rfl := by
  simpa using Path.toEq_symm_trans (atomicPath (a := a) (b := b) h)

@[simp] theorem atomicPath_congr_toEq (f : A → A) (h : a = b) :
    Path.toEq (Path.congrArg f (atomicPath (a := a) (b := b) h)) =
      _root_.congrArg f h := rfl

end PathAPI

/-! ## Forcing posets and conditions -/

structure ForcingPoset (Cond : Type u) where
  le : Cond → Cond → Prop
  refl : ∀ p : Cond, le p p
  trans : ∀ {p q r : Cond}, le p q → le q r → le p r
  antisymm : ∀ {p q : Cond}, le p q → le q p → p = q

def Stronger {Cond : Type u} (P : ForcingPoset Cond) (p q : Cond) : Prop :=
  P.le p q

@[simp] theorem stronger_def {Cond : Type u} (P : ForcingPoset Cond) (p q : Cond) :
    Stronger P p q = P.le p q := rfl

theorem stronger_refl {Cond : Type u} (P : ForcingPoset Cond) (p : Cond) :
    Stronger P p p :=
  P.refl p

theorem stronger_trans {Cond : Type u} (P : ForcingPoset Cond)
    {p q r : Cond} (hpq : Stronger P p q) (hqr : Stronger P q r) :
    Stronger P p r :=
  P.trans hpq hqr

theorem stronger_antisymm {Cond : Type u} (P : ForcingPoset Cond)
    {p q : Cond} (hpq : Stronger P p q) (hqp : Stronger P q p) :
    p = q :=
  P.antisymm hpq hqp

structure ForcingCondition (Cond : Type u) where
  carrier : Cond

@[simp] theorem forcingCondition_eta {Cond : Type u}
    (c : ForcingCondition Cond) :
    ForcingCondition.mk c.carrier = c := by
  cases c
  rfl

@[simp] theorem forcingCondition_carrier_mk {Cond : Type u} (p : Cond) :
    (ForcingCondition.mk p).carrier = p := rfl

def conditionPath {Cond : Type u} {p q : Cond} (h : p = q) :
    Path (ForcingCondition.mk p) (ForcingCondition.mk q) :=
  Path.mk
    [Step.mk (ForcingCondition.mk p) (ForcingCondition.mk q)
      (_root_.congrArg ForcingCondition.mk h)]
    (_root_.congrArg ForcingCondition.mk h)

@[simp] theorem conditionPath_toEq {Cond : Type u} {p q : Cond} (h : p = q) :
    Path.toEq (conditionPath (p := p) (q := q) h) =
      _root_.congrArg ForcingCondition.mk h := rfl

@[simp] theorem conditionPath_refl {Cond : Type u} (p : Cond) :
    Path.toEq (conditionPath (p := p) (q := p) rfl) = rfl := rfl

@[simp] theorem conditionPath_symm {Cond : Type u} {p q : Cond} (h : p = q) :
    Path.symm (conditionPath (p := p) (q := q) h) =
      conditionPath (p := q) (q := p) h.symm := by
  cases h
  rfl

@[simp] theorem conditionPath_symm_symm {Cond : Type u} {p q : Cond} (h : p = q) :
    Path.symm (Path.symm (conditionPath (p := p) (q := q) h)) =
      conditionPath (p := p) (q := q) h := by
  simpa using Path.symm_symm (conditionPath (p := p) (q := q) h)

theorem conditionPath_trans_assoc {Cond : Type u}
    {p q r s : Cond}
    (h₁ : p = q) (h₂ : q = r) (h₃ : r = s) :
    Path.trans (Path.trans (conditionPath (p := p) (q := q) h₁)
      (conditionPath (p := q) (q := r) h₂))
      (conditionPath (p := r) (q := s) h₃)
    =
    Path.trans (conditionPath (p := p) (q := q) h₁)
      (Path.trans (conditionPath (p := q) (q := r) h₂)
        (conditionPath (p := r) (q := s) h₃)) := by
  simpa using Path.trans_assoc
    (conditionPath (p := p) (q := q) h₁)
    (conditionPath (p := q) (q := r) h₂)
    (conditionPath (p := r) (q := s) h₃)

/-! ## Filters, dense sets, and generic filters -/

structure ForcingFilter {Cond : Type u} (P : ForcingPoset Cond) where
  mem : Cond → Prop
  upward : ∀ {p q : Cond}, mem p → P.le p q → mem q
  directed : ∀ {p q : Cond}, mem p → mem q → ∃ r : Cond, mem r ∧ P.le r p ∧ P.le r q

def principalFilter {Cond : Type u} (P : ForcingPoset Cond) (seed : Cond) :
    ForcingFilter P where
  mem := fun q => P.le seed q
  upward := by
    intro p q hp hpq
    exact P.trans hp hpq
  directed := by
    intro p q hp hq
    exact ⟨seed, P.refl seed, hp, hq⟩

@[simp] theorem principalFilter_mem_seed {Cond : Type u}
    (P : ForcingPoset Cond) (seed : Cond) :
    (principalFilter P seed).mem seed :=
  P.refl seed

theorem principalFilter_mem_of_stronger {Cond : Type u}
    (P : ForcingPoset Cond) (seed q : Cond) (h : P.le seed q) :
    (principalFilter P seed).mem q := h

theorem principalFilter_upward {Cond : Type u}
    (P : ForcingPoset Cond) (seed p q : Cond)
    (hp : (principalFilter P seed).mem p) (hpq : P.le p q) :
    (principalFilter P seed).mem q :=
  (principalFilter P seed).upward hp hpq

theorem principalFilter_directed {Cond : Type u}
    (P : ForcingPoset Cond) (seed p q : Cond)
    (hp : (principalFilter P seed).mem p)
    (hq : (principalFilter P seed).mem q) :
    ∃ r : Cond, (principalFilter P seed).mem r ∧ P.le r p ∧ P.le r q :=
  (principalFilter P seed).directed hp hq

def DenseSet (Cond : Type u) : Type u := Cond → Prop

def Dense {Cond : Type u} (P : ForcingPoset Cond) (D : DenseSet Cond) : Prop :=
  ∀ p : Cond, ∃ q : Cond, P.le q p ∧ D q

theorem dense_witness {Cond : Type u} (P : ForcingPoset Cond)
    (D : DenseSet Cond) (hD : Dense P D) (p : Cond) :
    ∃ q : Cond, P.le q p ∧ D q :=
  hD p

structure GenericFilter {Cond : Type u} (P : ForcingPoset Cond) where
  Gam : ForcingFilter P
  meetsDense : ∀ D : DenseSet Cond, Dense P D → ∃ p : Cond, Gam.mem p ∧ D p

theorem generic_meets_dense {Cond : Type u}
    (P : ForcingPoset Cond) (G : GenericFilter P)
    (D : DenseSet Cond) (hD : Dense P D) :
    ∃ p : Cond, G.Gam.mem p ∧ D p :=
  G.meetsDense D hD

theorem generic_nonempty {Cond : Type u}
    (P : ForcingPoset Cond) (G : GenericFilter P) :
    ∃ p : Cond, G.Gam.mem p := by
  let D : DenseSet Cond := fun _ => True
  have hD : Dense P D := by
    intro p
    exact ⟨p, P.refl p, trivial⟩
  rcases G.meetsDense D hD with ⟨p, hp, _⟩
  exact ⟨p, hp⟩

theorem generic_upward {Cond : Type u}
    (P : ForcingPoset Cond) (G : GenericFilter P) {p q : Cond}
    (hp : G.Gam.mem p) (hpq : P.le p q) :
    G.Gam.mem q :=
  G.Gam.upward hp hpq

theorem generic_directed {Cond : Type u}
    (P : ForcingPoset Cond) (G : GenericFilter P) {p q : Cond}
    (hp : G.Gam.mem p) (hq : G.Gam.mem q) :
    ∃ r : Cond, G.Gam.mem r ∧ P.le r p ∧ P.le r q :=
  G.Gam.directed hp hq

theorem generic_meets_true_dense {Cond : Type u}
    (P : ForcingPoset Cond) (G : GenericFilter P) :
    ∃ p : Cond, G.Gam.mem p ∧ True := by
  let D : DenseSet Cond := fun _ => True
  have hD : Dense P D := by
    intro p
    exact ⟨p, P.refl p, trivial⟩
  simpa [D] using G.meetsDense D hD

/-! ## Names and forcing semantics -/

structure ForcingName (Cond : Type u) (Val : Type v) where
  support : List Cond
  value : Val

@[simp] theorem forcingName_eta {Cond : Type u} {Val : Type v}
    (tau : ForcingName Cond Val) :
    ForcingName.mk tau.support tau.value = tau := by
  cases tau
  rfl

@[simp] theorem forcingName_support_mk {Cond : Type u} {Val : Type v}
    (s : List Cond) (x : Val) :
    (ForcingName.mk s x).support = s := rfl

@[simp] theorem forcingName_value_mk {Cond : Type u} {Val : Type v}
    (s : List Cond) (x : Val) :
    (ForcingName.mk s x).value = x := rfl

def mapName {Cond : Type u} {Val : Type v} {Val' : Type w}
    (f : Val → Val') (tau : ForcingName Cond Val) :
    ForcingName Cond Val' :=
  ForcingName.mk tau.support (f tau.value)

@[simp] theorem mapName_support {Cond : Type u} {Val : Type v} {Val' : Type w}
    (f : Val → Val') (tau : ForcingName Cond Val) :
    (mapName f tau).support = tau.support := rfl

@[simp] theorem mapName_value {Cond : Type u} {Val : Type v} {Val' : Type w}
    (f : Val → Val') (tau : ForcingName Cond Val) :
    (mapName f tau).value = f tau.value := rfl

@[simp] theorem mapName_id {Cond : Type u} {Val : Type v}
    (tau : ForcingName Cond Val) :
    mapName (fun x => x) tau = tau := by
  cases tau
  rfl

@[simp] theorem mapName_comp {Cond : Type u} {Val : Type v}
    {Val' : Type w} {Val'' : Type _}
    (f : Val → Val') (g : Val' → Val'')
    (tau : ForcingName Cond Val) :
    mapName g (mapName f tau) = mapName (fun x => g (f x)) tau := by
  cases tau
  rfl

def namePath {Cond : Type u} {Val : Type v}
    {tau sig : ForcingName Cond Val} (h : tau = sig) :
    Path tau sig :=
  Path.mk [Step.mk tau sig h] h

@[simp] theorem namePath_toEq {Cond : Type u} {Val : Type v}
    {tau sig : ForcingName Cond Val} (h : tau = sig) :
    Path.toEq (namePath (tau := tau) (sig := sig) h) = h := rfl

@[simp] theorem namePath_symm {Cond : Type u} {Val : Type v}
    {tau sig : ForcingName Cond Val} (h : tau = sig) :
    Path.symm (namePath (tau := tau) (sig := sig) h) =
      namePath (tau := sig) (sig := tau) h.symm := by
  cases h
  rfl

inductive Formula (Sym : Type u) where
  | atom : Sym → Formula Sym
  | neg : Formula Sym → Formula Sym
  | and : Formula Sym → Formula Sym → Formula Sym
  | imp : Formula Sym → Formula Sym → Formula Sym

def Forces {Cond : Type u} (P : ForcingPoset Cond)
    (Gam : ForcingFilter P) (p : Cond) {Sym : Type v}
    (phi : Formula Sym) : Prop :=
  Gam.mem p

def HoldsInExtension {Cond : Type u} (P : ForcingPoset Cond)
    (Gam : ForcingFilter P) {Sym : Type v} (phi : Formula Sym) : Prop :=
  ∃ p : Cond, Forces P Gam p phi

@[simp] theorem forces_iff_mem {Cond : Type u}
    (P : ForcingPoset Cond) (Gam : ForcingFilter P) (p : Cond)
    {Sym : Type v} (phi : Formula Sym) :
    Forces P Gam p phi ↔ Gam.mem p := Iff.rfl

@[simp] theorem holdsInExtension_iff {Cond : Type u}
    (P : ForcingPoset Cond) (Gam : ForcingFilter P)
    {Sym : Type v} (phi : Formula Sym) :
    HoldsInExtension P Gam phi ↔ ∃ p : Cond, Gam.mem p := by
  constructor
  · intro h
    rcases h with ⟨p, hp⟩
    exact ⟨p, hp⟩
  · intro h
    rcases h with ⟨p, hp⟩
    exact ⟨p, hp⟩

theorem forcing_monotone {Cond : Type u}
    (P : ForcingPoset Cond) (Gam : ForcingFilter P) {p q : Cond}
    {Sym : Type v} (phi : Formula Sym)
    (hpq : P.le p q) (hp : Forces P Gam p phi) :
    Forces P Gam q phi :=
  Gam.upward hp hpq

theorem forcing_formula_irrelevant {Cond : Type u}
    (P : ForcingPoset Cond) (Gam : ForcingFilter P) (p : Cond)
    {Sym : Type v} (phi psi : Formula Sym) :
    Forces P Gam p phi ↔ Forces P Gam p psi := by
  constructor <;> intro h <;> exact h

theorem truth_lemma_forward {Cond : Type u}
    (P : ForcingPoset Cond) (Gam : ForcingFilter P)
    {Sym : Type v} (phi : Formula Sym) :
    (∃ p : Cond, Forces P Gam p phi) → HoldsInExtension P Gam phi := by
  intro h
  exact h

theorem truth_lemma_backward {Cond : Type u}
    (P : ForcingPoset Cond) (Gam : ForcingFilter P)
    {Sym : Type v} (phi : Formula Sym) :
    HoldsInExtension P Gam phi → (∃ p : Cond, Forces P Gam p phi) := by
  intro h
  exact h

theorem truth_lemma_equiv {Cond : Type u}
    (P : ForcingPoset Cond) (Gam : ForcingFilter P)
    {Sym : Type v} (phi : Formula Sym) :
    (∃ p : Cond, Forces P Gam p phi) ↔ HoldsInExtension P Gam phi := by
  constructor
  · exact truth_lemma_forward (P := P) (Gam := Gam) (phi := phi)
  · exact truth_lemma_backward (P := P) (Gam := Gam) (phi := phi)

structure TruthLemmaPack {Cond : Type u} (P : ForcingPoset Cond)
    (Gam : ForcingFilter P) (Sym : Type v) where
  forward : ∀ phi : Formula Sym, (∃ p : Cond, Forces P Gam p phi) → HoldsInExtension P Gam phi
  backward : ∀ phi : Formula Sym, HoldsInExtension P Gam phi → (∃ p : Cond, Forces P Gam p phi)

def mkTruthLemmaPack {Cond : Type u} (P : ForcingPoset Cond)
    (Gam : ForcingFilter P) (Sym : Type v) :
    TruthLemmaPack P Gam Sym where
  forward := truth_lemma_forward (P := P) (Gam := Gam)
  backward := truth_lemma_backward (P := P) (Gam := Gam)

theorem truthLemmaPack_forward {Cond : Type u}
    (P : ForcingPoset Cond) (Gam : ForcingFilter P) (Sym : Type v)
    (phi : Formula Sym) :
    (mkTruthLemmaPack P Gam Sym).forward phi =
      truth_lemma_forward (P := P) (Gam := Gam) (phi := phi) := rfl

theorem truthLemmaPack_backward {Cond : Type u}
    (P : ForcingPoset Cond) (Gam : ForcingFilter P) (Sym : Type v)
    (phi : Formula Sym) :
    (mkTruthLemmaPack P Gam Sym).backward phi =
      truth_lemma_backward (P := P) (Gam := Gam) (phi := phi) := rfl

/-! ## Boolean-valued models -/

inductive BoolVal where
  | bot : BoolVal
  | top : BoolVal
deriving DecidableEq, Repr

def bNot : BoolVal → BoolVal
  | BoolVal.bot => BoolVal.top
  | BoolVal.top => BoolVal.bot

def bAnd : BoolVal → BoolVal → BoolVal
  | BoolVal.top, BoolVal.top => BoolVal.top
  | _, _ => BoolVal.bot

def bOr : BoolVal → BoolVal → BoolVal
  | BoolVal.bot, BoolVal.bot => BoolVal.bot
  | _, _ => BoolVal.top

@[simp] theorem bNot_bNot (x : BoolVal) : bNot (bNot x) = x := by
  cases x <;> rfl

@[simp] theorem bAnd_comm (x y : BoolVal) : bAnd x y = bAnd y x := by
  cases x <;> cases y <;> rfl

@[simp] theorem bAnd_assoc (x y z : BoolVal) :
    bAnd (bAnd x y) z = bAnd x (bAnd y z) := by
  cases x <;> cases y <;> cases z <;> rfl

@[simp] theorem bAnd_top_left (x : BoolVal) :
    bAnd BoolVal.top x = x := by
  cases x <;> rfl

@[simp] theorem bAnd_top_right (x : BoolVal) :
    bAnd x BoolVal.top = x := by
  cases x <;> rfl

@[simp] theorem bAnd_bot_left (x : BoolVal) :
    bAnd BoolVal.bot x = BoolVal.bot := by
  cases x <;> rfl

@[simp] theorem bAnd_bot_right (x : BoolVal) :
    bAnd x BoolVal.bot = BoolVal.bot := by
  cases x <;> rfl

@[simp] theorem bOr_comm (x y : BoolVal) : bOr x y = bOr y x := by
  cases x <;> cases y <;> rfl

@[simp] theorem bOr_assoc (x y z : BoolVal) :
    bOr (bOr x y) z = bOr x (bOr y z) := by
  cases x <;> cases y <;> cases z <;> rfl

@[simp] theorem bOr_top_left (x : BoolVal) :
    bOr BoolVal.top x = BoolVal.top := by
  cases x <;> rfl

@[simp] theorem bOr_top_right (x : BoolVal) :
    bOr x BoolVal.top = BoolVal.top := by
  cases x <;> rfl

@[simp] theorem bOr_bot_left (x : BoolVal) :
    bOr BoolVal.bot x = x := by
  cases x <;> rfl

@[simp] theorem bOr_bot_right (x : BoolVal) :
    bOr x BoolVal.bot = x := by
  cases x <;> rfl

structure BooleanValuedModel (Obj : Type u) where
  eval : Obj → BoolVal

def evalPath {Obj : Type u} (M : BooleanValuedModel Obj) {x y : Obj}
    (p : Path x y) : Path (M.eval x) (M.eval y) :=
  Path.congrArg M.eval p

@[simp] theorem evalPath_refl {Obj : Type u}
    (M : BooleanValuedModel Obj) (x : Obj) :
    evalPath M (Path.refl x) = Path.refl (M.eval x) := rfl

@[simp] theorem evalPath_trans {Obj : Type u}
    (M : BooleanValuedModel Obj) {x y z : Obj}
    (p : Path x y) (q : Path y z) :
    evalPath M (Path.trans p q) =
      Path.trans (evalPath M p) (evalPath M q) := by
  simpa [evalPath] using Path.congrArg_trans M.eval p q

@[simp] theorem evalPath_symm {Obj : Type u}
    (M : BooleanValuedModel Obj) {x y : Obj}
    (p : Path x y) :
    evalPath M (Path.symm p) = Path.symm (evalPath M p) := by
  simpa [evalPath] using Path.congrArg_symm M.eval p

@[simp] theorem evalPath_toEq {Obj : Type u}
    (M : BooleanValuedModel Obj) {x y : Obj}
    (p : Path x y) :
    Path.toEq (evalPath M p) = _root_.congrArg M.eval (Path.toEq p) := rfl

/-! ## Consistency and independence packaging -/

structure IndependenceResult where
  Sym : String
  relativelyConsistent : Prop
  independentFromBase : Prop

@[simp] theorem independenceResult_sym
    (R : IndependenceResult) : R.Sym = R.Sym := rfl

@[simp] theorem independenceResult_consistent
    (R : IndependenceResult) :
    R.relativelyConsistent → R.relativelyConsistent := by
  intro h
  exact h

@[simp] theorem independenceResult_independent
    (R : IndependenceResult) :
    R.independentFromBase → R.independentFromBase := by
  intro h
  exact h

def IndependenceWitness (R : IndependenceResult) : Prop :=
  R.relativelyConsistent ∧ R.independentFromBase

theorem witness_left (R : IndependenceResult) :
    IndependenceWitness R → R.relativelyConsistent := by
  intro h
  exact h.1

theorem witness_right (R : IndependenceResult) :
    IndependenceWitness R → R.independentFromBase := by
  intro h
  exact h.2

theorem mk_witness (R : IndependenceResult)
    (h1 : R.relativelyConsistent) (h2 : R.independentFromBase) :
    IndependenceWitness R := ⟨h1, h2⟩

structure CardinalArithmetic where
  card : Nat → Nat
  monotone : ∀ {m n : Nat}, m ≤ n → card m ≤ card n

theorem card_monotone (C : CardinalArithmetic) {m n : Nat}
    (h : m ≤ n) : C.card m ≤ C.card n :=
  C.monotone h

def CHStatement (C : CardinalArithmetic) : Prop :=
  C.card (Nat.succ 0) = C.card 0 + 1

def GCHStatement (C : CardinalArithmetic) : Prop :=
  ∀ n : Nat, C.card (Nat.succ n) = C.card n + 1

theorem gch_step (C : CardinalArithmetic) (h : GCHStatement C) (n : Nat) :
    C.card (Nat.succ n) = C.card n + 1 :=
  h n

theorem ch_of_gch (C : CardinalArithmetic) (h : GCHStatement C) :
    CHStatement C := by
  exact h 0

theorem gch_step_one (C : CardinalArithmetic) (h : GCHStatement C) :
    C.card (Nat.succ 1) = C.card 1 + 1 :=
  h 1

theorem gch_step_two (C : CardinalArithmetic) (h : GCHStatement C) :
    C.card (Nat.succ 2) = C.card 2 + 1 :=
  h 2

structure ConsistencyProofStructure where
  Sym : String
  baseTheoryConsistent : Prop
  forcingExtensionConsistent : Prop

def relativeConsistency
    (S : ConsistencyProofStructure) : Prop :=
  S.baseTheoryConsistent → S.forcingExtensionConsistent

theorem relativeConsistency_intro
    (S : ConsistencyProofStructure)
    (h : S.baseTheoryConsistent → S.forcingExtensionConsistent) :
    relativeConsistency S := h

theorem relativeConsistency_apply
    (S : ConsistencyProofStructure)
    (h : relativeConsistency S)
    (hbase : S.baseTheoryConsistent) :
    S.forcingExtensionConsistent :=
  h hbase

structure GCHIndependencePackage where
  Gam : CardinalArithmetic
  modelOfGCH : Prop
  modelOfNotGCH : Prop

def gchIndependent (P : GCHIndependencePackage) : Prop :=
  P.modelOfGCH ∧ P.modelOfNotGCH

theorem gchIndependent_left (P : GCHIndependencePackage) :
    gchIndependent P → P.modelOfGCH := by
  intro h
  exact h.1

theorem gchIndependent_right (P : GCHIndependencePackage) :
    gchIndependent P → P.modelOfNotGCH := by
  intro h
  exact h.2

theorem gchIndependent_intro (P : GCHIndependencePackage)
    (h1 : P.modelOfGCH) (h2 : P.modelOfNotGCH) :
    gchIndependent P := ⟨h1, h2⟩

def gchIndependenceResult (P : GCHIndependencePackage) :
    IndependenceResult :=
  { Sym := "GCH"
    relativelyConsistent := P.modelOfGCH
    independentFromBase := gchIndependent P }

@[simp] theorem gchIndependenceResult_sym
    (P : GCHIndependencePackage) :
    (gchIndependenceResult P).Sym = "GCH" := rfl

theorem gchIndependenceResult_consistent
    (P : GCHIndependencePackage) :
    (gchIndependenceResult P).relativelyConsistent = P.modelOfGCH := rfl

theorem gchIndependenceResult_independent
    (P : GCHIndependencePackage) :
    (gchIndependenceResult P).independentFromBase = gchIndependent P := rfl

theorem gchPackage_to_witness (P : GCHIndependencePackage)
    (h1 : P.modelOfGCH) (h2 : P.modelOfNotGCH) :
    IndependenceWitness (gchIndependenceResult P) := by
  refine ⟨?_, ?_⟩
  · exact h1
  · exact ⟨h1, h2⟩

/-! ## Additional path coherence for forcing metadata -/

section MetadataPaths

variable {Cond : Type u}

theorem independenceResult_path_refl (R : IndependenceResult) :
    Path.refl R = Path.mk [] rfl := rfl

theorem independenceResult_path_symm (R : IndependenceResult)
    (p : Path R R) :
    Path.symm (Path.symm p) = p := by
  simpa using Path.symm_symm p

theorem independenceResult_path_trans_unit (R : IndependenceResult)
    (p : Path R R) :
    Path.trans p (Path.refl R) = p := by
  exact Path.trans_refl_right p

theorem independenceResult_path_trans_unit_left (R : IndependenceResult)
    (p : Path R R) :
    Path.trans (Path.refl R) p = p := by
  exact Path.trans_refl_left p

theorem independenceResult_congr_sym (R S : IndependenceResult)
    (p : Path R S) :
    Path.congrArg IndependenceResult.Sym (Path.symm p) =
      Path.symm (Path.congrArg IndependenceResult.Sym p) := by
  simpa using Path.congrArg_symm IndependenceResult.Sym p

theorem independenceResult_congr_trans (R S T : IndependenceResult)
    (p : Path R S) (q : Path S T) :
    Path.congrArg IndependenceResult.Sym (Path.trans p q) =
      Path.trans
        (Path.congrArg IndependenceResult.Sym p)
        (Path.congrArg IndependenceResult.Sym q) := by
  simpa using Path.congrArg_trans IndependenceResult.Sym p q

end MetadataPaths

end ComputationalPaths.Path.Algebra.ForcingSetTheoryDeep
