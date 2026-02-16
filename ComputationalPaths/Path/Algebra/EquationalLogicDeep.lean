/-
  ComputationalPaths.Path.Algebra.EquationalLogicDeep

  Equational Logic via Computational Paths
  =========================================

  We develop core equational logic — signatures, terms, substitution,
  equational axioms, derivation rules — all modeled through Path operations.

  Key ideas:
  • Derivation composition = Path.trans
  • Symmetry rule = Path.symm
  • Congruence rule = Path.congrArg
  • Reflexivity = Path.refl
  • Substitution = Path.congrArg with substitution functions

  62+ theorems establishing algebraic properties of equational reasoning
  via computational paths.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.EquationalLogicDeep

open ComputationalPaths.Path

/-! ## Section 1: Algebraic Signatures and Terms -/

/-- An operation symbol with a name and arity -/
structure OpSym where
  name : String
  arity : Nat
  deriving DecidableEq, Repr

/-- A simple algebraic signature: a list of operation symbols -/
structure Signature where
  ops : List OpSym
  deriving Repr

/-- Variables are natural numbers -/
abbrev Var := Nat

/-- Terms over a signature -/
inductive Term where
  | var : Var → Term
  | const : String → Term
  | app : String → Term → Term
  | binApp : String → Term → Term → Term
  deriving DecidableEq, Repr

namespace Term

/-- Substitution: replace variables using a mapping -/
def subst (sigma : Var → Term) : Term → Term
  | var x => sigma x
  | const c => const c
  | app f t => app f (t.subst sigma)
  | binApp f t1 t2 => binApp f (t1.subst sigma) (t2.subst sigma)

/-- Identity substitution -/
def idSubst : Var → Term := fun x => var x

/-- Composition of substitutions -/
def compSubst (sigma tau : Var → Term) : Var → Term :=
  fun x => (tau x).subst sigma

-- Theorem 1: Substitution with identity is identity
theorem subst_id (t : Term) : t.subst idSubst = t := by
  induction t with
  | var x => rfl
  | const c => rfl
  | app f t ih => simp [subst, ih]
  | binApp f t1 t2 ih1 ih2 => simp [subst, ih1, ih2]

-- Theorem 2: Constant terms are unaffected by substitution
theorem subst_const (sigma : Var → Term) (c : String) :
    (const c).subst sigma = const c := rfl

-- Theorem 3: Double substitution equals composed substitution
theorem subst_comp (t : Term) (sigma tau : Var → Term) :
    (t.subst tau).subst sigma = t.subst (compSubst sigma tau) := by
  induction t with
  | var x => simp [subst, compSubst]
  | const c => rfl
  | app f t ih => simp [subst, ih]
  | binApp f t1 t2 ih1 ih2 => simp [subst, ih1, ih2]

-- Theorem 4: Identity substitution on the left of composition
theorem compSubst_id_left (sigma : Var → Term) :
    compSubst idSubst sigma = sigma := by
  ext x; simp [compSubst, subst_id]

-- Theorem 5: App substitution distributes
theorem subst_app (sigma : Var → Term) (f : String) (t : Term) :
    (app f t).subst sigma = app f (t.subst sigma) := rfl

end Term

/-! ## Section 2: Equational Axioms and Theories -/

/-- An equation is a pair of terms -/
structure Equation where
  lhs : Term
  rhs : Term
  deriving DecidableEq, Repr

/-- An equational theory is a set of axioms (equations) -/
structure EqTheory where
  axioms_ : List Equation
  deriving Repr

/-! ## Section 3: Evaluation in an Algebra -/

/-- An algebra interprets terms into a carrier type -/
structure Algebra (A : Type) where
  interpConst : String → A
  interpApp : String → A → A
  interpBinApp : String → A → A → A

/-- Evaluate a term in an algebra given a variable assignment -/
def eval {A : Type} (alg : Algebra A) (env : Var → A) : Term → A
  | Term.var x => env x
  | Term.const c => alg.interpConst c
  | Term.app f t => alg.interpApp f (eval alg env t)
  | Term.binApp f t1 t2 => alg.interpBinApp f (eval alg env t1) (eval alg env t2)

-- Theorem 6: Evaluation respects substitution
theorem eval_subst {A : Type} (alg : Algebra A) (env : Var → A)
    (sigma : Var → Term) (t : Term) :
    eval alg env (t.subst sigma) = eval alg (fun x => eval alg env (sigma x)) t := by
  induction t with
  | var x => simp [Term.subst, eval]
  | const c => simp [Term.subst, eval]
  | app f t ih => simp [Term.subst, eval, ih]
  | binApp f t1 t2 ih1 ih2 => simp [Term.subst, eval, ih1, ih2]

-- Theorem 7: Evaluation of constants ignores environment
theorem eval_const {A : Type} (alg : Algebra A) (env : Var → A) (c : String) :
    eval alg env (Term.const c) = alg.interpConst c := rfl

-- Theorem 8: Evaluation of variables extracts from environment
theorem eval_var {A : Type} (alg : Algebra A) (env : Var → A) (x : Var) :
    eval alg env (Term.var x) = env x := rfl

/-! ## Section 4: Path-based Derivation Rules -/

/-- Reflexivity derivation as Path -/
def derivRefl {A : Type} (a : A) : Path a a :=
  Path.refl a

/-- Symmetry derivation as Path -/
def derivSymm {A : Type} {a b : A} (d : Path a b) : Path b a :=
  Path.symm d

/-- Transitivity derivation: compose two derivation paths -/
def derivTrans {A : Type} {a b c : A}
    (d1 : Path a b) (d2 : Path b c) : Path a c :=
  Path.trans d1 d2

/-- Congruence derivation: apply a function to both sides -/
def derivCongr {A B : Type} {a b : A} (f : A → B)
    (d : Path a b) : Path (f a) (f b) :=
  Path.congrArg f d

/-! ## Section 5: Derivation Chain Properties via Paths -/

section DerivationProperties

variable {A : Type}

-- Theorem 9: Trans associativity for derivation chains
theorem deriv_trans_assoc {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

-- Theorem 10: Left identity of trans
theorem deriv_trans_refl_left {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  trans_refl_left p

-- Theorem 11: Right identity of trans
theorem deriv_trans_refl_right {a b : A} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  trans_refl_right p

-- Theorem 12: Symmetry is involutive
theorem deriv_symm_symm {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  symm_symm p

-- Theorem 13: Symmetry distributes over trans (reversed order)
theorem deriv_symm_trans {a b c : A} (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

-- Theorem 14: Congruence distributes over trans
theorem deriv_congr_trans {B : Type} {a b c : A} (f : A → B)
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  congrArg_trans f p q

-- Theorem 15: Congruence distributes over symm
theorem deriv_congr_symm {B : Type} {a b : A} (f : A → B) (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  congrArg_symm f p

-- Theorem 16: Congruence with identity function is identity
theorem deriv_congr_id {a b : A} (p : Path a b) :
    Path.congrArg (fun x : A => x) p = p :=
  congrArg_id p

-- Theorem 17: Congruence composition (f ∘ g)
theorem deriv_congr_comp {B C : Type} (f : B → C) (g : A → B) {a b : A}
    (p : Path a b) :
    Path.congrArg (fun x => f (g x)) p = Path.congrArg f (Path.congrArg g p) :=
  congrArg_comp f g p

-- Theorem 18: Symmetry of refl is refl
theorem deriv_symm_refl (a : A) : Path.symm (Path.refl a) = Path.refl a :=
  symm_refl a

-- Theorem 19: toEq for trans-symm
theorem deriv_toEq_trans_symm {a b : A} (p : Path a b) :
    Path.toEq (Path.trans p (Path.symm p)) = rfl :=
  toEq_trans_symm p

-- Theorem 20: toEq for symm-trans
theorem deriv_toEq_symm_trans {a b : A} (p : Path a b) :
    Path.toEq (Path.trans (Path.symm p) p) = rfl :=
  toEq_symm_trans p

-- Theorem 21: Derivation yields equality
theorem deriv_to_eq {a b : A} (d : Path a b) : a = b :=
  Path.toEq d

-- Theorem 22: Left cancellation for paths
theorem deriv_left_cancel {a b c : A}
    (p : Path a b) (q r : Path b c) (h : Path.trans p q = Path.trans p r) :
    q = r :=
  trans_left_cancel p q r h

-- Theorem 23: Right cancellation for paths
theorem deriv_right_cancel {a b c : A}
    (p q : Path a b) (r : Path b c) (h : Path.trans p r = Path.trans q r) :
    p = q :=
  trans_right_cancel p q r h

end DerivationProperties

/-! ## Section 6: Equational Closure Properties -/

/-- A proof-relevant equational closure -/
structure EqClosure (A : Type) where
  carrier : A → A → Prop
  refl_closed : ∀ a, carrier a a
  symm_closed : ∀ a b, carrier a b → carrier b a
  trans_closed : ∀ a b c, carrier a b → carrier b c → carrier a c

/-- The trivial closure: everything equals itself -/
def trivialClosure (A : Type) : EqClosure A where
  carrier := fun a b => a = b
  refl_closed := fun _ => rfl
  symm_closed := fun _ _ h => h.symm
  trans_closed := fun _ _ _ h1 h2 => h1.trans h2

-- Theorem 24: Trivial closure is reflexive
theorem trivial_refl {A : Type} (a : A) : (trivialClosure A).carrier a a :=
  rfl

-- Theorem 25: Trivial closure is symmetric
theorem trivial_symm {A : Type} {a b : A} (h : a = b) :
    (trivialClosure A).carrier b a :=
  h.symm

-- Theorem 26: Trivial closure is transitive
theorem trivial_trans {A : Type} {a b c : A} (h1 : a = b) (h2 : b = c) :
    (trivialClosure A).carrier a c :=
  h1.trans h2

/-! ## Section 7: Term Congruence and Quotient Structure -/

/-- Congruence relation on terms -/
structure TermCong where
  rel : Term → Term → Prop
  isRefl : ∀ t, rel t t
  isSymm : ∀ s t, rel s t → rel t s
  isTrans : ∀ s t u, rel s t → rel t u → rel s u
  appCong : ∀ f s t, rel s t → rel (Term.app f s) (Term.app f t)
  binAppCong : ∀ f s1 s2 t1 t2, rel s1 t1 → rel s2 t2 →
    rel (Term.binApp f s1 s2) (Term.binApp f t1 t2)

/-- The identity congruence -/
def idCong : TermCong where
  rel := fun s t => s = t
  isRefl := fun _ => rfl
  isSymm := fun _ _ h => h.symm
  isTrans := fun _ _ _ h1 h2 => h1.trans h2
  appCong := fun _ _ _ h => congrArg _ h
  binAppCong := fun f _ _ _ _ h1 h2 => by simp [h1, h2]

-- Theorem 27: Identity congruence is reflexive
theorem idCong_refl (t : Term) : idCong.rel t t := rfl

-- Theorem 28: Identity congruence is symmetric
theorem idCong_symm {s t : Term} (h : idCong.rel s t) : idCong.rel t s :=
  h.symm

-- Theorem 29: Identity congruence is transitive
theorem idCong_trans {s t u : Term} (h1 : idCong.rel s t) (h2 : idCong.rel t u) :
    idCong.rel s u :=
  h1.trans h2

/-! ## Section 8: Path-based Derivation Chains -/

/-- A derivation chain via trans -/
def chainTwo {A : Type} {a b c : A} (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

def chainThree {A : Type} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) : Path a d :=
  Path.trans (Path.trans p q) r

def chainFour {A : Type} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) : Path a e :=
  Path.trans (Path.trans (Path.trans p q) r) s

-- Theorem 30: Chain of two equals trans
theorem chain_two_eq_trans {A : Type} {a b c : A} (p : Path a b) (q : Path b c) :
    chainTwo p q = Path.trans p q :=
  rfl

-- Theorem 31: Chain of three reassociates
theorem chain_three_assoc {A : Type} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    chainThree p q r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

-- Theorem 32: Chain with refl at start
theorem chain_refl_start {A : Type} {a b : A} (p : Path a b) :
    chainTwo (Path.refl a) p = p :=
  trans_refl_left p

-- Theorem 33: Chain with refl at end
theorem chain_refl_end {A : Type} {a b : A} (p : Path a b) :
    chainTwo p (Path.refl b) = p :=
  trans_refl_right p

/-! ## Section 9: Substitution Rule as Congruence -/

/-- Substitution rule: from a path a~b, get f(a)~f(b) -/
def substRule {A B : Type} {a b : A} (f : A → B) (p : Path a b) :
    Path (f a) (f b) :=
  Path.congrArg f p

-- Theorem 34: Substitution rule preserves composition
theorem substRule_trans {A B : Type} {a b c : A} (f : A → B)
    (p : Path a b) (q : Path b c) :
    substRule f (Path.trans p q) =
    Path.trans (substRule f p) (substRule f q) :=
  congrArg_trans f p q

-- Theorem 35: Substitution rule preserves symmetry
theorem substRule_symm {A B : Type} {a b : A} (f : A → B)
    (p : Path a b) :
    substRule f (Path.symm p) = Path.symm (substRule f p) :=
  congrArg_symm f p

-- Theorem 36: Substitution composed with substitution
theorem substRule_comp {A B C : Type} {a b : A} (f : B → C) (g : A → B)
    (p : Path a b) :
    substRule f (substRule g p) = substRule (fun x => f (g x)) p :=
  (congrArg_comp f g p).symm

/-! ## Section 10: Equational Reasoning Combinators -/

/-- Apply symmetry then transitivity: from b=a and b=c derive a=c -/
def symmThenTrans {A : Type} {a b c : A}
    (p : Path b a) (q : Path b c) : Path a c :=
  Path.trans (Path.symm p) q

/-- Apply transitivity then symmetry: from a=b and c=b derive a=c -/
def transThenSymm {A : Type} {a b c : A}
    (p : Path a b) (q : Path c b) : Path a c :=
  Path.trans p (Path.symm q)

-- Theorem 37: symmThenTrans with refl
theorem symmThenTrans_refl_right {A : Type} {a b : A} (p : Path b a) :
    symmThenTrans p (Path.refl b) = Path.symm p :=
  trans_refl_right _

-- Theorem 38: transThenSymm with refl
theorem transThenSymm_refl_right {A : Type} {a b : A} (p : Path a b) :
    transThenSymm p (Path.refl b) = p := by
  simp [transThenSymm]

-- Theorem 39: symmThenTrans with same path: symm(p) ▸ p has trivial equality
theorem symmThenTrans_same_toEq {A : Type} {a b : A} (p : Path a b) :
    Path.toEq (symmThenTrans p p) = rfl := by
  simp [symmThenTrans]

/-! ## Section 11: Congruence Rule for Binary Operations -/

/-- Congruence for binary operation: from a₁=b₁ and a₂=b₂ derive f(a₁,a₂)=f(b₁,b₂) -/
def binCongRule {A B C : Type} {a1 b1 : A} {a2 b2 : B}
    (f : A → B → C) (p1 : Path a1 b1) (p2 : Path a2 b2) :
    Path (f a1 a2) (f b1 b2) :=
  let step1 : Path (f a1 a2) (f b1 a2) := Path.congrArg (f · a2) p1
  let step2 : Path (f b1 a2) (f b1 b2) := Path.congrArg (f b1 ·) p2
  Path.trans step1 step2

-- Theorem 40: Binary congruence with refl on right
theorem binCong_refl_right {A B C : Type} {a1 b1 : A}
    (f : A → B → C) (p : Path a1 b1) (b : B) :
    binCongRule f p (Path.refl b) = Path.congrArg (f · b) p := by
  simp [binCongRule]

-- Theorem 41: Binary congruence with refl on left
theorem binCong_refl_left {A B C : Type} {a2 b2 : B}
    (f : A → B → C) (a : A) (p : Path a2 b2) :
    binCongRule f (Path.refl a) p = Path.congrArg (f a ·) p := by
  simp [binCongRule]

-- Theorem 42: Binary congruence toEq correctness
theorem binCong_toEq {A B C : Type} {a1 b1 : A} {a2 b2 : B}
    (f : A → B → C) (p1 : Path a1 b1) (p2 : Path a2 b2) :
    Path.toEq (binCongRule f p1 p2) =
    (congrArg (f · a2) (Path.toEq p1)).trans (congrArg (f b1 ·) (Path.toEq p2)) := by
  simp [binCongRule]

/-! ## Section 12: Unification as Path Construction -/

/-- A unification problem -/
structure UnifProblem where
  left : Term
  right : Term

/-- A unifier maps variables to terms -/
abbrev Unifier := Var → Term

/-- Check if a substitution unifies two terms -/
def isUnifier (sigma : Unifier) (prob : UnifProblem) : Prop :=
  prob.left.subst sigma = prob.right.subst sigma

-- Theorem 43: Identical terms are trivially unifiable
theorem trivialUnifier (t : Term) : isUnifier Term.idSubst ⟨t, t⟩ := by
  simp [isUnifier, Term.subst_id]

-- Theorem 44: Substitution preserves unification
theorem unif_subst_preserves {sigma : Unifier} {l r : Term}
    (h : l.subst sigma = r.subst sigma) (tau : Unifier) :
    (l.subst sigma).subst tau = (r.subst sigma).subst tau := by
  rw [h]

-- Theorem 45: Composing with identity unifier
theorem unif_id_comp {t : Term} :
    t.subst (Term.compSubst Term.idSubst Term.idSubst) = t := by
  rw [← Term.subst_comp]
  simp [Term.subst_id]

/-! ## Section 13: Path Witnesses for Unification -/

/-- When evaluation is equal, we can build a path -/
def unifPath {A : Type} (alg : Algebra A) (env : Var → A)
    {l r : Term} (h : eval alg env l = eval alg env r) :
    Path (eval alg env l) (eval alg env r) :=
  Path.ofEq h

-- Theorem 46: Unification path for identical terms is refl via toEq
theorem unifPath_ident_toEq {A : Type} (alg : Algebra A) (env : Var → A)
    (t : Term) :
    Path.toEq (unifPath alg env (rfl : eval alg env t = eval alg env t)) = rfl := by
  rfl

-- Theorem 47: Symmetry of unification path toEq
theorem unifPath_symm_toEq {A : Type} (alg : Algebra A) (env : Var → A)
    {l r : Term} (h : eval alg env l = eval alg env r) :
    Path.toEq (Path.symm (unifPath alg env h)) = h.symm := by
  simp [unifPath]

/-! ## Section 14: Equational Theory and Models -/

/-- An equation holds in an algebra -/
def satisfies {A : Type} (alg : Algebra A) (eq_ : Equation) : Prop :=
  ∀ env : Var → A, eval alg env eq_.lhs = eval alg env eq_.rhs

/-- All axioms of a theory hold in an algebra -/
def models {A : Type} (alg : Algebra A) (thy : EqTheory) : Prop :=
  ∀ eq_ ∈ thy.axioms_, satisfies alg eq_

/-- An equation is a semantic consequence of a theory -/
def isConsequence (thy : EqTheory) (eq_ : Equation) : Prop :=
  ∀ (A : Type) (alg : Algebra A), models alg thy → satisfies alg eq_

-- Theorem 48: Reflexive equations are always consequences
theorem refl_is_consequence (thy : EqTheory) (t : Term) :
    isConsequence thy ⟨t, t⟩ :=
  fun _ _ _ _ => rfl

-- Theorem 49: Axioms are consequences of their theory
theorem axiom_is_consequence (thy : EqTheory) (eq_ : Equation)
    (hmem : eq_ ∈ thy.axioms_) :
    isConsequence thy eq_ :=
  fun _ alg hmod => hmod eq_ hmem

-- Theorem 50: Symmetric equations are consequences if the original is
theorem symm_consequence (thy : EqTheory) (eq_ : Equation)
    (h : isConsequence thy eq_) :
    isConsequence thy ⟨eq_.rhs, eq_.lhs⟩ :=
  fun A alg hmod env => (h A alg hmod env).symm

/-! ## Section 15: Path-based Model Theory -/

/-- Build a path from a satisfaction proof -/
def satisfactionPath {A : Type} (alg : Algebra A) (env : Var → A)
    (eq_ : Equation) (h : satisfies alg eq_) :
    Path (eval alg env eq_.lhs) (eval alg env eq_.rhs) :=
  Path.ofEq (h env)

-- Theorem 51: Satisfaction path toEq
theorem satPath_toEq {A : Type} (alg : Algebra A) (env : Var → A)
    (eq_ : Equation) (h : satisfies alg eq_) :
    Path.toEq (satisfactionPath alg env eq_ h) = h env := by
  simp [satisfactionPath]

-- Theorem 52: Satisfaction path for reflexive equation
theorem satPath_refl_toEq {A : Type} (alg : Algebra A) (env : Var → A) (t : Term) :
    Path.toEq (satisfactionPath alg env ⟨t, t⟩ (fun _ => rfl)) = rfl := by
  simp [satisfactionPath]

-- Theorem 53: Symmetry of satisfaction path witnesses reverse equation
theorem satPath_symm_toEq {A : Type} (alg : Algebra A) (env : Var → A)
    (eq_ : Equation) (h : satisfies alg eq_) :
    Path.toEq (Path.symm (satisfactionPath alg env eq_ h)) = (h env).symm := by
  simp [satisfactionPath]

/-! ## Section 16: Derivation Rules Package -/

/-- Package: all five derivation rules as path operations -/
structure DerivRules (A : Type) where
  reflRule : ∀ (a : A), Path a a
  symmRule : ∀ {a b : A}, Path a b → Path b a
  transRule : ∀ {a b c : A}, Path a b → Path b c → Path a c
  congrRule : ∀ {a b : A} (f : A → A), Path a b → Path (f a) (f b)
  substRule_ : ∀ {B : Type} {a b : A} (f : A → B), Path a b → Path (f a) (f b)

/-- The canonical derivation rules from Path -/
def canonicalRules (A : Type) : DerivRules A where
  reflRule := Path.refl
  symmRule := Path.symm
  transRule := Path.trans
  congrRule := fun f p => Path.congrArg f p
  substRule_ := fun f p => Path.congrArg f p

-- Theorem 54: Canonical refl
theorem canonical_refl {A : Type} (a : A) :
    (canonicalRules A).reflRule a = Path.refl a := rfl

-- Theorem 55: Canonical symm
theorem canonical_symm {A : Type} {a b : A} (p : Path a b) :
    (canonicalRules A).symmRule p = Path.symm p := rfl

-- Theorem 56: Canonical trans
theorem canonical_trans {A : Type} {a b c : A} (p : Path a b) (q : Path b c) :
    (canonicalRules A).transRule p q = Path.trans p q := rfl

-- Theorem 57: Canonical congr
theorem canonical_congr {A : Type} {a b : A} (f : A → A) (p : Path a b) :
    (canonicalRules A).congrRule f p = Path.congrArg f p := rfl

/-! ## Section 17: Birkhoff-style Completeness Structure -/

/-- A derivation system is complete if every consequence has a derivation path -/
structure Complete (thy : EqTheory) where
  witness : ∀ (A : Type) (alg : Algebra A) (env : Var → A)
    (eq_ : Equation), isConsequence thy eq_ → models alg thy →
    Path (eval alg env eq_.lhs) (eval alg env eq_.rhs)

/-- Build the completeness witness using satisfaction -/
def mkComplete (thy : EqTheory) : Complete thy where
  witness := fun A alg env eq_ hcons hmod =>
    satisfactionPath alg env eq_ (hcons A alg hmod)

-- Theorem 58: Completeness witness yields correct equality
theorem complete_toEq (thy : EqTheory) (A : Type)
    (alg : Algebra A) (env : Var → A) (eq_ : Equation)
    (hcons : isConsequence thy eq_) (hmod : models alg thy) :
    Path.toEq ((mkComplete thy).witness A alg env eq_ hcons hmod) =
    hcons A alg hmod env := by
  simp [mkComplete, satisfactionPath]

/-! ## Section 18: Extended Algebraic Path Properties -/

-- Theorem 59: Pentagon identity for four paths
theorem pentagon_paths {A : Type} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans (Path.trans p q) r) s =
    Path.trans p (Path.trans q (Path.trans r s)) := by
  rw [trans_assoc, trans_assoc]

-- Theorem 60: congrArg preserves chain structure
theorem congrArg_chain {A B : Type} {a b c : A} (f : A → B)
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (chainTwo p q) =
    chainTwo (Path.congrArg f p) (Path.congrArg f q) :=
  congrArg_trans f p q

-- Theorem 61: Four-step chain reassociation
theorem chain_four_assoc {A : Type} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    chainFour p q r s =
    Path.trans p (Path.trans q (Path.trans r s)) := by
  unfold chainFour
  rw [trans_assoc, trans_assoc]

-- Theorem 62: Congruence preserves evaluation for app terms
theorem congr_app_eval {A : Type} (alg : Algebra A) (env : Var → A)
    (f : String) {s t : Term} (h : eval alg env s = eval alg env t) :
    eval alg env (Term.app f s) = eval alg env (Term.app f t) := by
  simp [eval, h]

-- Theorem 63: Path witness for congruence in app
def congr_app_path {A : Type} (alg : Algebra A) (env : Var → A)
    (f : String) {s t : Term} (p : Path (eval alg env s) (eval alg env t)) :
    Path (eval alg env (Term.app f s)) (eval alg env (Term.app f t)) :=
  Path.congrArg (alg.interpApp f) p

-- Theorem 64: Composing satisfaction path with its symm gives trivial toEq
theorem satPath_trans_symm_toEq {A : Type} (alg : Algebra A) (env : Var → A)
    (eq_ : Equation) (h : satisfies alg eq_) :
    Path.toEq (Path.trans
      (satisfactionPath alg env eq_ h)
      (Path.symm (satisfactionPath alg env eq_ h))) = rfl := by
  simp [satisfactionPath]

/-! ## Section 19: Free Variables and Ground Terms -/

/-- Compute the set of free variables in a term -/
def freeVars : Term → List Var
  | Term.var x => [x]
  | Term.const _ => []
  | Term.app _ t => freeVars t
  | Term.binApp _ t1 t2 => freeVars t1 ++ freeVars t2

-- Theorem 65: Constants have no free variables
theorem freeVars_const (c : String) : freeVars (Term.const c) = [] := rfl

-- Theorem 66: Variables have themselves as free variable
theorem freeVars_var (x : Var) : freeVars (Term.var x) = [x] := rfl

/-- A ground term has no variables -/
def isGround (t : Term) : Prop := freeVars t = []

-- Theorem 67: Ground terms are invariant under evaluation in term algebra
theorem ground_subst_invariant (t : Term) (h : isGround t) (sigma : Var → Term) :
    eval (A := Term) ⟨Term.const, Term.app, Term.binApp⟩ sigma t = t := by
  induction t with
  | var x => simp [isGround, freeVars] at h
  | const c => rfl
  | app f t ih =>
    simp [eval]
    exact ih (by simp [isGround, freeVars] at h; exact h)
  | binApp f t1 t2 ih1 ih2 =>
    simp [eval]
    simp [isGround, freeVars] at h
    exact ⟨ih1 h.1, ih2 h.2⟩

/-! ## Section 20: Extended Derivation Properties -/

-- Theorem 68: Congruence path for binary app terms
def congr_binApp_path {A : Type} (alg : Algebra A) (env : Var → A)
    (f : String) {s1 t1 s2 t2 : Term}
    (p1 : Path (eval alg env s1) (eval alg env t1))
    (p2 : Path (eval alg env s2) (eval alg env t2)) :
    Path (eval alg env (Term.binApp f s1 s2)) (eval alg env (Term.binApp f t1 t2)) :=
  binCongRule (alg.interpBinApp f) p1 p2

-- Theorem 69: Three-step derivation via trans (toEq)
theorem three_step_toEq {A : Type} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.toEq (chainThree p q r) =
    ((Path.toEq p).trans (Path.toEq q)).trans (Path.toEq r) := by
  simp [chainThree]

-- Theorem 70: derivCongr distributes over derivTrans
theorem derivCongr_derivTrans {A B : Type} {a b c : A} (f : A → B)
    (p : Path a b) (q : Path b c) :
    derivCongr f (derivTrans p q) = derivTrans (derivCongr f p) (derivCongr f q) :=
  congrArg_trans f p q

-- Theorem 71: derivSymm of derivCongr
theorem derivSymm_derivCongr {A B : Type} {a b : A} (f : A → B)
    (p : Path a b) :
    derivSymm (derivCongr f p) = derivCongr f (derivSymm p) :=
  (congrArg_symm f p).symm

-- Theorem 72: derivTrans with derivRefl
theorem derivTrans_derivRefl_left {A : Type} {a b : A} (p : Path a b) :
    derivTrans (derivRefl a) p = p :=
  trans_refl_left p

-- Theorem 73: derivTrans with derivRefl right
theorem derivTrans_derivRefl_right {A : Type} {a b : A} (p : Path a b) :
    derivTrans p (derivRefl b) = p :=
  trans_refl_right p

end ComputationalPaths.EquationalLogicDeep
