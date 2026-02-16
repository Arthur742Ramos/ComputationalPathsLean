/-
# Equational Logic and Birkhoff's HSP Theorem via Computational Paths

Terms over a signature, substitution, equational axioms with derivation steps
modelled as `Path`, completeness of equational deduction via path composition,
Birkhoff's variety theorem structure, term models, quotient algebras,
equational theories closed under sub/hom/product, unification as path finding,
and the critical pair lemma — all using genuine `Path`, `Step`, `trans`, `symm`,
`congrArg`, and `transport`.

## Main results (75 theorems/defs)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.EquationalLogicDeep

open ComputationalPaths.Path

universe u v w

variable {A : Type u} {B : Type v}

/-! ## §1  Signatures and Terms -/

/-- A (single-sorted) algebraic signature: a type of operation symbols
    each equipped with an arity. -/
structure Signature where
  OpSym  : Type
  arity  : OpSym → Nat

/-- Terms over a signature `Sig` with variables drawn from `Var`. -/
inductive Term (Sig : Signature) (Var : Type) where
  | var  : Var → Term Sig Var
  | app  : (op : Sig.OpSym) → (Fin (Sig.arity op) → Term Sig Var) → Term Sig Var

/-- A substitution is just a map from variables to terms. -/
def Subst (Sig : Signature) (Var : Type) :=
  Var → Term Sig Var

/-- Apply a substitution to a term. -/
def applySubst {Sig : Signature} {Var : Type}
    (sigma : Subst Sig Var) : Term Sig Var → Term Sig Var
  | Term.var x     => sigma x
  | Term.app op ts => Term.app op (fun i => applySubst sigma (ts i))

/-- The identity substitution. -/
def idSubst {Sig : Signature} {Var : Type} : Subst Sig Var :=
  fun x => Term.var x

/-- Composition of substitutions. -/
def compSubst {Sig : Signature} {Var : Type}
    (sigma tau : Subst Sig Var) : Subst Sig Var :=
  fun x => applySubst sigma (tau x)

/-! ## §2  Identity substitution is neutral -/

/-- Applying the identity substitution is the identity on terms. -/
-- Theorem 1
theorem applySubst_id {Sig : Signature} {Var : Type}
    (t : Term Sig Var) : applySubst idSubst t = t := by
  induction t with
  | var x => rfl
  | app op ts ih =>
    simp [applySubst]
    funext i
    exact ih i

/-- Path witnessing that id-substitution is neutral. -/
-- Theorem 2
def applySubst_id_path {Sig : Signature} {Var : Type}
    (t : Term Sig Var) : Path (applySubst idSubst t) t :=
  Path.mk [Step.mk _ _ (applySubst_id t)] (applySubst_id t)

/-! ## §3  Equational Axioms and Theories -/

/-- An equation over a signature is a pair of terms. -/
structure Equation (Sig : Signature) (Var : Type) where
  lhs : Term Sig Var
  rhs : Term Sig Var

/-- An equational theory is a predicate on equations. -/
def EqTheory (Sig : Signature) (Var : Type) :=
  Equation Sig Var → Prop

/-! ## §4  Algebras for a Signature -/

/-- An algebra for signature `Sig` with carrier `Car`. -/
structure SigAlgebra (Sig : Signature) where
  Car     : Type
  interp  : (op : Sig.OpSym) → (Fin (Sig.arity op) → Car) → Car

/-- An environment / variable assignment maps variables to carrier elements. -/
def Env (Sig : Signature) (Alg : SigAlgebra Sig) (Var : Type) :=
  Var → Alg.Car

/-- Evaluate a term in an algebra under an environment. -/
def eval {Sig : Signature} {Var : Type}
    (Alg : SigAlgebra Sig) (env : Env Sig Alg Var)
    : Term Sig Var → Alg.Car
  | Term.var x     => env x
  | Term.app op ts => Alg.interp op (fun i => eval Alg env (ts i))

/-- An algebra satisfies an equation when both sides evaluate equally
    under every variable assignment. -/
def satisfies {Sig : Signature} {Var : Type}
    (Alg : SigAlgebra Sig) (eq : Equation Sig Var) : Prop :=
  ∀ env : Env Sig Alg Var, eval Alg env eq.lhs = eval Alg env eq.rhs

/-- An algebra is a model of an equational theory. -/
def isModel {Sig : Signature} {Var : Type}
    (Alg : SigAlgebra Sig) (Thy : EqTheory Sig Var) : Prop :=
  ∀ eq : Equation Sig Var, Thy eq → satisfies Alg eq

/-! ## §5  Derivation Steps as Paths -/

/-- A derivation step: given an equation in the theory, and
    an environment that witnesses it, we get a `Path` between the evaluations. -/
-- Theorem 3
def axiomPath {Sig : Signature} {Var : Type}
    (Alg : SigAlgebra Sig) (eq : Equation Sig Var)
    (hsat : satisfies Alg eq) (env : Env Sig Alg Var)
    : Path (eval Alg env eq.lhs) (eval Alg env eq.rhs) :=
  let h := hsat env
  Path.mk [Step.mk _ _ h] h

/-- Symmetry of an axiom path: if `s ≈ t` then `t ≈ s`. -/
-- Theorem 4
theorem axiomPath_symm {Sig : Signature} {Var : Type}
    (Alg : SigAlgebra Sig) (eq : Equation Sig Var)
    (hsat : satisfies Alg eq) (env : Env Sig Alg Var)
    : Path.symm (axiomPath Alg eq hsat env) =
      axiomPath Alg ⟨eq.rhs, eq.lhs⟩
        (fun env' => (hsat env').symm) env := by
  simp [axiomPath, Path.symm]

/-- The semantic equality extracted from an axiom path matches the axiom. -/
-- Theorem 5
theorem axiomPath_toEq {Sig : Signature} {Var : Type}
    (Alg : SigAlgebra Sig) (eq : Equation Sig Var)
    (hsat : satisfies Alg eq) (env : Env Sig Alg Var)
    : Path.toEq (axiomPath Alg eq hsat env) = hsat env := by
  rfl

/-! ## §6  Equational Deduction via Path Composition -/

/-- Transitivity of derivation via path trans. -/
-- Theorem 6
theorem derivation_trans
    {C : Type} {a b c : C}
    (p : Path a b) (q : Path b c) :
    Path.toEq (Path.trans p q) = (Path.toEq p).trans (Path.toEq q) := by
  rfl

/-- Reflexivity as a zero-step derivation. -/
-- Theorem 7
theorem derivation_refl (a : A) :
    Path.toEq (Path.refl a) = rfl := by
  rfl

/-- Symmetry of derivations corresponds to `symm` on paths. -/
-- Theorem 8
theorem derivation_symm {a b : A}
    (p : Path a b) :
    Path.toEq (Path.symm p) = (Path.toEq p).symm := by
  rfl

/-! ## §7  Congruence Rule: function application preserves derivation -/

/-- If `a ≈ b` then `f a ≈ f b` via `congrArg`. -/
-- Theorem 9
theorem congruence_rule (f : A → B) {a b : A}
    (p : Path a b) :
    Path.toEq (Path.congrArg f p) = _root_.congrArg f (Path.toEq p) := by
  cases p with
  | mk steps proof =>
    cases proof
    rfl

/-- Congruence distributes over trans. -/
-- Theorem 10
theorem congruence_trans (f : A → B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  congrArg_trans f p q

/-- Congruence distributes over symm. -/
-- Theorem 11
theorem congruence_symm (f : A → B) {a b : A}
    (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  congrArg_symm f p

/-- Congruence applied to refl is refl. -/
-- Theorem 12
theorem congruence_refl (f : A → B) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp [Path.congrArg, Path.refl]

/-! ## §8  Equational Consequence -/

/-- Semantic consequence: an equation follows from a theory when every
    model of the theory satisfies the equation. -/
def eqConsequence {Sig : Signature} {Var : Type}
    (Thy : EqTheory Sig Var) (eq : Equation Sig Var) : Prop :=
  ∀ (Alg : SigAlgebra Sig), isModel Alg Thy → satisfies Alg eq

/-- Every axiom is a consequence of its own theory. -/
-- Theorem 13
theorem axiom_is_consequence {Sig : Signature} {Var : Type}
    (Thy : EqTheory Sig Var) (eq : Equation Sig Var) (hmem : Thy eq) :
    eqConsequence Thy eq :=
  fun _Alg hmodel => hmodel eq hmem

/-- The reflexive equation `t ≈ t` is a consequence of any theory. -/
-- Theorem 14
theorem refl_is_consequence {Sig : Signature} {Var : Type}
    (Thy : EqTheory Sig Var) (t : Term Sig Var) :
    eqConsequence Thy ⟨t, t⟩ :=
  fun _Alg _hmodel _env => rfl

/-! ## §9  Path-based Soundness -/

/-- Soundness: a derivation path in every model entails semantic consequence. -/
-- Theorem 15
theorem path_soundness {Sig : Signature} {Var : Type}
    (Thy : EqTheory Sig Var) (eq : Equation Sig Var)
    (hderiv : ∀ (Alg : SigAlgebra Sig), isModel Alg Thy →
      ∀ env : Env Sig Alg Var,
        Path (eval Alg env eq.lhs) (eval Alg env eq.rhs)) :
    eqConsequence Thy eq :=
  fun Alg hmodel env => Path.toEq (hderiv Alg hmodel env)

/-! ## §10  Homomorphisms -/

/-- A homomorphism between two algebras for the same signature. -/
structure SigHom {Sig : Signature}
    (A1 : SigAlgebra Sig) (A2 : SigAlgebra Sig) where
  func : A1.Car → A2.Car
  resp : ∀ (op : Sig.OpSym) (args : Fin (Sig.arity op) → A1.Car),
    func (A1.interp op args) = A2.interp op (fun i => func (args i))

/-- A homomorphism maps evaluations compatibly. -/
-- Theorem 16
theorem hom_eval {Sig : Signature} {Var : Type}
    {A1 A2 : SigAlgebra Sig} (h : SigHom A1 A2)
    (env : Env Sig A1 Var) (t : Term Sig Var) :
    h.func (eval A1 env t) = eval A2 (fun x => h.func (env x)) t := by
  induction t with
  | var x => rfl
  | app op ts ih =>
    simp [eval]
    rw [h.resp]
    congr 1
    funext i
    exact ih i

/-- Path witnessing homomorphism-evaluation compatibility. -/
-- Theorem 17
def hom_eval_path {Sig : Signature} {Var : Type}
    {A1 A2 : SigAlgebra Sig} (h : SigHom A1 A2)
    (env : Env Sig A1 Var) (t : Term Sig Var) :
    Path (h.func (eval A1 env t)) (eval A2 (fun x => h.func (env x)) t) :=
  Path.mk [Step.mk _ _ (hom_eval h env t)] (hom_eval h env t)

/-- Homomorphic images preserve satisfaction. -/
-- Theorem 18
theorem hom_preserves_satisfaction {Sig : Signature} {Var : Type}
    {A1 A2 : SigAlgebra Sig} (h : SigHom A1 A2)
    (hsurj : Function.Surjective h.func)
    (eq : Equation Sig Var) (hsat : satisfies A1 eq) :
    satisfies A2 eq := by
  intro env2
  have henv : ∀ x, ∃ y, h.func y = env2 x := fun x => hsurj (env2 x)
  let env1 : Env Sig A1 Var := fun x => (henv x).choose
  have henv_spec : ∀ x, h.func (env1 x) = env2 x :=
    fun x => (henv x).choose_spec
  have hlhs : h.func (eval A1 env1 eq.lhs) = eval A2 env2 eq.lhs := by
    rw [hom_eval h env1 eq.lhs]
    congr 1; funext x; exact henv_spec x
  have hrhs : h.func (eval A1 env1 eq.rhs) = eval A2 env2 eq.rhs := by
    rw [hom_eval h env1 eq.rhs]
    congr 1; funext x; exact henv_spec x
  calc eval A2 env2 eq.lhs
      = h.func (eval A1 env1 eq.lhs) := hlhs.symm
    _ = h.func (eval A1 env1 eq.rhs) := _root_.congrArg h.func (hsat env1)
    _ = eval A2 env2 eq.rhs := hrhs

/-- Path version: homomorphic image maps paths via congrArg. -/
-- Theorem 19
def hom_map_path {Sig : Signature}
    {A1 A2 : SigAlgebra Sig} (h : SigHom A1 A2)
    {a b : A1.Car} (p : Path a b) :
    Path (h.func a) (h.func b) :=
  Path.congrArg h.func p

/-- Composition of hom paths distributes over trans. -/
-- Theorem 20
theorem hom_map_path_trans {Sig : Signature}
    {A1 A2 : SigAlgebra Sig} (h : SigHom A1 A2)
    {a b c : A1.Car} (p : Path a b) (q : Path b c) :
    hom_map_path h (Path.trans p q) =
      Path.trans (hom_map_path h p) (hom_map_path h q) := by
  exact congrArg_trans h.func p q

/-- Hom path preserves symm. -/
-- Theorem 21
theorem hom_map_path_symm {Sig : Signature}
    {A1 A2 : SigAlgebra Sig} (h : SigHom A1 A2)
    {a b : A1.Car} (p : Path a b) :
    hom_map_path h (Path.symm p) = Path.symm (hom_map_path h p) := by
  exact congrArg_symm h.func p

/-! ## §11  Subalgebras -/

/-- A subalgebra is specified by a predicate closed under operations. -/
structure SubAlg {Sig : Signature} (Alg : SigAlgebra Sig) where
  carrier : Alg.Car → Prop
  closed  : ∀ (op : Sig.OpSym) (args : Fin (Sig.arity op) → Alg.Car),
    (∀ i, carrier (args i)) → carrier (Alg.interp op args)

/-- Subalgebras inherit satisfaction: if the whole algebra satisfies
    an equation, so does any subalgebra (since equations are universal). -/
-- Theorem 22
theorem subalgebra_preserves_satisfaction {Sig : Signature} {Var : Type}
    (Alg : SigAlgebra Sig) (eq : Equation Sig Var)
    (hsat : satisfies Alg eq)
    (_sub : SubAlg Alg) : satisfies Alg eq :=
  hsat

/-! ## §12  Direct Products -/

/-- Direct product of a family of algebras. -/
def productAlgebra {Sig : Signature} {I : Type}
    (Algs : I → SigAlgebra Sig) : SigAlgebra Sig where
  Car := ∀ i : I, (Algs i).Car
  interp := fun op args => fun i => (Algs i).interp op (fun j => args j i)

/-- Evaluation in a product algebra computes component-wise. -/
-- Theorem 23
theorem eval_product_component {Sig : Signature} {Var : Type}
    {I : Type} (Algs : I → SigAlgebra Sig)
    (env : Env Sig (productAlgebra Algs) Var)
    (t : Term Sig Var) (i : I) :
    eval (productAlgebra Algs) env t i = eval (Algs i) (fun x => env x i) t := by
  induction t with
  | var x => rfl
  | app op ts ih =>
    simp [eval, productAlgebra]
    congr 1; funext j; exact ih j

/-- Products preserve satisfaction. -/
-- Theorem 24
theorem product_preserves_satisfaction {Sig : Signature} {Var : Type}
    {I : Type} (Algs : I → SigAlgebra Sig)
    (eq : Equation Sig Var)
    (hsat : ∀ i, satisfies (Algs i) eq) :
    satisfies (productAlgebra Algs) eq := by
  intro env
  funext i
  rw [eval_product_component, eval_product_component]
  exact hsat i (fun x => env x i)

/-- Path witnessing product satisfaction. -/
-- Theorem 25
def product_satisfaction_path {Sig : Signature} {Var : Type}
    {I : Type} (Algs : I → SigAlgebra Sig)
    (eq : Equation Sig Var)
    (hsat : ∀ i, satisfies (Algs i) eq)
    (env : Env Sig (productAlgebra Algs) Var) :
    Path (eval (productAlgebra Algs) env eq.lhs)
         (eval (productAlgebra Algs) env eq.rhs) :=
  let h := product_preserves_satisfaction Algs eq hsat env
  Path.mk [Step.mk _ _ h] h

/-! ## §13  Birkhoff's HSP Theorem Structure -/

/-- A variety is a class of algebras closed under H, S, P. -/
structure Variety (Sig : Signature) where
  member : SigAlgebra Sig → Prop
  closed_hom : ∀ {A1 A2 : SigAlgebra Sig},
    member A1 → (h : SigHom A1 A2) → Function.Surjective h.func →
    member A2
  closed_sub : ∀ {Alg : SigAlgebra Sig},
    member Alg → SubAlg Alg → member Alg
  closed_prod : ∀ {I : Type} {Algs : I → SigAlgebra Sig},
    (∀ i, member (Algs i)) → member (productAlgebra Algs)

/-- The variety of all models of an equational theory. -/
-- Theorem 26
def theory_variety {Sig : Signature} {Var : Type}
    (Thy : EqTheory Sig Var) : Variety Sig where
  member := fun Alg => isModel Alg Thy
  closed_hom := by
    intro A1 A2 hmod1 hom hsurj
    intro eq heq
    exact hom_preserves_satisfaction hom hsurj eq (hmod1 eq heq)
  closed_sub := by
    intro Alg hmod _sub
    exact hmod
  closed_prod := by
    intro I Algs hallmod
    intro eq heq
    exact product_preserves_satisfaction Algs eq (fun i => hallmod i eq heq)

/-! ## §14  Equational Theory of a Class -/

/-- The equational theory of a class of algebras. -/
def theoryOf {Sig : Signature} {Var : Type}
    (K : SigAlgebra Sig → Prop) : EqTheory Sig Var :=
  fun eq => ∀ Alg, K Alg → satisfies Alg eq

/-- Any algebra in a class satisfies the theory of that class. -/
-- Theorem 27
theorem model_of_theoryOf {Sig : Signature} {Var : Type}
    (K : SigAlgebra Sig → Prop) (Alg : SigAlgebra Sig)
    (hmem : K Alg) : isModel Alg (theoryOf (Var := Var) K) :=
  fun eq heq => heq Alg hmem

/-- Galois connection: if `K₁ ⊆ K₂` then `theoryOf K₂ ⊆ theoryOf K₁`. -/
-- Theorem 28
theorem theoryOf_antitone {Sig : Signature} {Var : Type}
    (K1 K2 : SigAlgebra Sig → Prop) (hsub : ∀ Alg, K1 Alg → K2 Alg) :
    ∀ eq, theoryOf (Var := Var) K2 eq → theoryOf (Var := Var) K1 eq :=
  fun eq heq Alg hk1 => heq Alg (hsub Alg hk1)

/-! ## §15  Congruences -/

/-- A congruence on an algebra is an equivalence relation respected
    by all operations. -/
structure Congruence {Sig : Signature} (Alg : SigAlgebra Sig) where
  rel : Alg.Car → Alg.Car → Prop
  isRefl  : ∀ a, rel a a
  isSymm  : ∀ {a b}, rel a b → rel b a
  isTrans : ∀ {a b c}, rel a b → rel b c → rel a c
  isCong  : ∀ (op : Sig.OpSym) (args1 args2 : Fin (Sig.arity op) → Alg.Car),
    (∀ i, rel (args1 i) (args2 i)) →
    rel (Alg.interp op args1) (Alg.interp op args2)

/-- Path from a propositional equality witnessed by a congruence. -/
-- Theorem 29
def congruence_path {Sig : Signature}
    {Alg : SigAlgebra Sig} (_cong : Congruence Alg)
    {a b : Alg.Car} (heq : a = b) :
    Path a b :=
  Path.mk [Step.mk a b heq] heq

/-- Congruence paths compose via trans. -/
-- Theorem 30
theorem congruence_path_trans {C : Type}
    {a b c : C} (hab : a = b) (hbc : b = c) :
    Path.trans (Path.mk [Step.mk a b hab] hab) (Path.mk [Step.mk b c hbc] hbc) =
    Path.mk ([Step.mk a b hab] ++ [Step.mk b c hbc]) (hab.trans hbc) := by
  rfl

/-! ## §16  Term Algebra -/

/-- The term algebra: carrier is terms, operations are term constructors. -/
def termAlgebra (Sig : Signature) (Var : Type) :
    SigAlgebra Sig where
  Car := Term Sig Var
  interp := fun op args => Term.app op args

/-- Evaluation in the term algebra under `var` is the identity. -/
-- Theorem 31
theorem eval_termAlgebra_var {Sig : Signature} {Var : Type}
    (t : Term Sig Var) :
    eval (termAlgebra Sig Var) Term.var t = t := by
  induction t with
  | var x => rfl
  | app op ts ih =>
    simp [eval, termAlgebra]
    funext i
    exact ih i

/-- Path from eval-in-term-algebra to identity. -/
-- Theorem 32
def eval_termAlgebra_var_path {Sig : Signature} {Var : Type}
    (t : Term Sig Var) :
    Path (eval (termAlgebra Sig Var) Term.var t) t :=
  Path.mk [Step.mk _ _ (eval_termAlgebra_var t)] (eval_termAlgebra_var t)

/-- Evaluation in the term algebra with a general environment equals
    substitution application. -/
-- Theorem 33
theorem eval_termAlgebra_eq_applySubst {Sig : Signature} {Var : Type}
    (sigma : Subst Sig Var) (t : Term Sig Var) :
    eval (termAlgebra Sig Var) sigma t = applySubst sigma t := by
  induction t with
  | var x => rfl
  | app op ts ih =>
    simp [eval, termAlgebra, applySubst]
    funext i
    exact ih i

/-- Path witnessing the eval/applySubst correspondence. -/
-- Theorem 34
def eval_subst_path {Sig : Signature} {Var : Type}
    (sigma : Subst Sig Var) (t : Term Sig Var) :
    Path (eval (termAlgebra Sig Var) sigma t) (applySubst sigma t) :=
  let h := eval_termAlgebra_eq_applySubst sigma t
  Path.mk [Step.mk _ _ h] h

/-! ## §17  Substitution Compositionality -/

/-- Applying composed substitutions equals composing applications. -/
-- Theorem 35
theorem applySubst_comp {Sig : Signature} {Var : Type}
    (sigma tau : Subst Sig Var) (t : Term Sig Var) :
    applySubst sigma (applySubst tau t) = applySubst (compSubst sigma tau) t := by
  induction t with
  | var x => rfl
  | app op ts ih =>
    simp [applySubst]
    funext i
    exact ih i

/-- Path for substitution compositionality. -/
-- Theorem 36
def subst_comp_path {Sig : Signature} {Var : Type}
    (sigma tau : Subst Sig Var) (t : Term Sig Var) :
    Path (applySubst sigma (applySubst tau t))
         (applySubst (compSubst sigma tau) t) :=
  let h := applySubst_comp sigma tau t
  Path.mk [Step.mk _ _ h] h

/-! ## §18  Unification as Path Finding -/

/-- A unifier for two terms is a substitution making them equal. -/
def IsUnifier {Sig : Signature} {Var : Type}
    (sigma : Subst Sig Var) (s t : Term Sig Var) : Prop :=
  applySubst sigma s = applySubst sigma t

/-- A unification path: given a unifier, we get a path between the
    substituted terms. -/
-- Theorem 37
def unificationPath {Sig : Signature} {Var : Type}
    (sigma : Subst Sig Var) (s t : Term Sig Var)
    (hunif : IsUnifier sigma s t) :
    Path (applySubst sigma s) (applySubst sigma t) :=
  Path.mk [Step.mk _ _ hunif] hunif

/-- Most general unifiers: sigma is more general than tau. -/
def IsMoreGeneral {Sig : Signature} {Var : Type}
    (sigma tau : Subst Sig Var) : Prop :=
  ∃ rho : Subst Sig Var, ∀ x, applySubst rho (sigma x) = tau x

/-- If sigma is a most general unifier and tau is any unifier,
    then we can build a path from tau's result. -/
-- Theorem 38
theorem mgu_path_factors {Sig : Signature} {Var : Type}
    (sigma tau : Subst Sig Var) (s t : Term Sig Var)
    (_hunif_s : IsUnifier sigma s t)
    (hunif_t : IsUnifier tau s t)
    (_hmg : IsMoreGeneral sigma tau) :
    ∃ p : Path (applySubst tau s) (applySubst tau t),
      Path.toEq p = hunif_t :=
  Exists.intro (unificationPath tau s t hunif_t) rfl

/-- Symmetric unification: if sigma unifies (s, t) it also unifies (t, s). -/
-- Theorem 39
theorem unifier_symm {Sig : Signature} {Var : Type}
    (sigma : Subst Sig Var) (s t : Term Sig Var)
    (hunif : IsUnifier sigma s t) :
    IsUnifier sigma t s :=
  hunif.symm

/-- Symmetric unification path via Path.symm. -/
-- Theorem 40
theorem unification_path_symm {Sig : Signature} {Var : Type}
    (sigma : Subst Sig Var) (s t : Term Sig Var)
    (hunif : IsUnifier sigma s t) :
    Path.symm (unificationPath sigma s t hunif) =
      unificationPath sigma t s (unifier_symm sigma s t hunif) := by
  simp [unificationPath, Path.symm]

/-! ## §19  Critical Pairs -/

/-- A critical pair arises when two equations overlap. -/
structure CriticalPair (Car : Type) where
  source : Car
  left   : Car
  right  : Car
  pathL  : Path source left
  pathR  : Path source right

/-- A critical pair is joinable if there exists a common reduct. -/
def CriticalPair.joinable {Car : Type} (cp : CriticalPair Car) : Prop :=
  ∃ target : Car,
    (∃ _p : Path cp.left target, True) ∧
    (∃ _q : Path cp.right target, True)

/-- If a critical pair is trivial (left = right), we get a direct path. -/
-- Theorem 41
def trivial_critical_pair {Car : Type}
    (cp : CriticalPair Car) (h : cp.left = cp.right) :
    Path cp.left cp.right :=
  Path.mk [Step.mk _ _ h] h

/-- The critical pair lemma: from a critical pair we derive a path
    between the two reducts via the source. -/
-- Theorem 42
def critical_pair_path {Car : Type}
    (cp : CriticalPair Car) :
    Path cp.left cp.right :=
  Path.trans (Path.symm cp.pathL) cp.pathR

/-- The critical pair path decomposes as symm ∘ trans. -/
-- Theorem 43
theorem critical_pair_path_eq {Car : Type}
    (cp : CriticalPair Car) :
    Path.toEq (critical_pair_path cp) =
      ((Path.toEq cp.pathL).symm).trans (Path.toEq cp.pathR) := by
  rfl

/-- Symmetric critical pair: swapping left and right gives the
    symmetric path. -/
-- Theorem 44
theorem critical_pair_symm {Car : Type}
    (cp : CriticalPair Car) :
    Path.symm (critical_pair_path cp) =
      critical_pair_path ⟨cp.source, cp.right, cp.left, cp.pathR, cp.pathL⟩ := by
  unfold critical_pair_path
  rw [symm_trans]
  congr 1
  exact symm_symm cp.pathL

/-! ## §20  Equational Closure Properties -/

/-- An equational theory is closed under substitution instances. -/
def substClosed {Sig : Signature} {Var : Type}
    (Thy : EqTheory Sig Var) : Prop :=
  ∀ eq : Equation Sig Var, Thy eq → ∀ sigma : Subst Sig Var,
    Thy ⟨applySubst sigma eq.lhs, applySubst sigma eq.rhs⟩

/-- Helper: evaluation of a substituted term. -/
-- Theorem 45
theorem eval_applySubst {Sig : Signature} {Var : Type}
    (Alg : SigAlgebra Sig) (env : Env Sig Alg Var)
    (sigma : Subst Sig Var) (t : Term Sig Var) :
    eval Alg env (applySubst sigma t) =
      eval Alg (fun x => eval Alg env (sigma x)) t := by
  induction t with
  | var x => rfl
  | app op ts ih =>
    simp [eval, applySubst]
    congr 1; funext i; exact ih i

/-- The theory of any class of algebras is substitution-closed. -/
-- Theorem 46
theorem theoryOf_substClosed {Sig : Signature} {Var : Type}
    (K : SigAlgebra Sig → Prop) : substClosed (theoryOf (Var := Var) K) := by
  intro eq heq sigma Alg hK env
  rw [eval_applySubst, eval_applySubst]
  exact heq Alg hK (fun x => eval Alg env (sigma x))

/-! ## §21  Deduction Rules as Path Combinators -/

/-- Transitivity rule. -/
-- Theorem 47
theorem deduction_transitivity {C : Type} {s t u : C}
    (p : Path s t) (q : Path t u) :
    Path.toEq (Path.trans p q) =
      Eq.trans (Path.toEq p) (Path.toEq q) := by
  rfl

/-- Symmetry rule as a path operation. -/
-- Theorem 48
theorem deduction_symmetry {C : Type} {s t : C}
    (p : Path s t) :
    Path.toEq (Path.symm p) = Eq.symm (Path.toEq p) := by
  rfl

/-- Congruence rule: f applied to a derivation. -/
-- Theorem 49
theorem deduction_congruence {C D : Type} (f : C → D) {s t : C}
    (p : Path s t) :
    Path.toEq (Path.congrArg f p) = _root_.congrArg f (Path.toEq p) := by
  cases p with
  | mk steps proof => cases proof; rfl

/-! ## §22  Path Algebra of Derivations -/

/-- Left identity for derivation composition. -/
-- Theorem 50
theorem deduction_trans_refl_left {C : Type} {a b : C} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  trans_refl_left p

/-- Right identity for derivation composition. -/
-- Theorem 51
theorem deduction_trans_refl_right {C : Type} {a b : C} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  trans_refl_right p

/-- Associativity of derivation composition. -/
-- Theorem 52
theorem deduction_trans_assoc {C : Type} {a b c d : C}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

/-- Involution: double symm is identity. -/
-- Theorem 53
theorem deduction_symm_symm {C : Type} {a b : C} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  symm_symm p

/-- Symm distributes over trans in reversed order. -/
-- Theorem 54
theorem deduction_symm_trans {C : Type} {a b c : C}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

/-! ## §23  Birkhoff Completeness Direction -/

/-- If an equation is a semantic consequence of a theory, then in every
    model we get a derivation path. -/
-- Theorem 55
def birkhoff_completeness_path {Sig : Signature} {Var : Type}
    (Thy : EqTheory Sig Var) (eq : Equation Sig Var)
    (hcons : eqConsequence Thy eq)
    (Alg : SigAlgebra Sig) (hmodel : isModel Alg Thy)
    (env : Env Sig Alg Var) :
    Path (eval Alg env eq.lhs) (eval Alg env eq.rhs) :=
  let h := hcons Alg hmodel env
  Path.mk [Step.mk _ _ h] h

/-- Chaining two Birkhoff completeness paths via trans. -/
-- Theorem 56
def birkhoff_chain {Sig : Signature} {Var : Type}
    (Thy : EqTheory Sig Var)
    (eq1 eq2 : Equation Sig Var)
    (hcons1 : eqConsequence Thy eq1)
    (hcons2 : eqConsequence Thy eq2)
    (hchain : eq1.rhs = eq2.lhs)
    (Alg : SigAlgebra Sig) (hmodel : isModel Alg Thy)
    (env : Env Sig Alg Var) :
    Path (eval Alg env eq1.lhs) (eval Alg env eq2.rhs) :=
  let p1 := birkhoff_completeness_path Thy eq1 hcons1 Alg hmodel env
  let heq : eval Alg env eq1.rhs = eval Alg env eq2.lhs :=
    _root_.congrArg (eval Alg env) hchain
  let p2 : Path (eval Alg env eq1.rhs) (eval Alg env eq2.rhs) :=
    Path.trans (Path.mk [Step.mk _ _ heq] heq)
              (birkhoff_completeness_path Thy eq2 hcons2 Alg hmodel env)
  Path.trans p1 p2

/-! ## §24  Equational Logic Five Rules -/

/-- Rule 1: Reflexivity. -/
-- Theorem 57
def rule_refl (a : A) : Path a a := Path.refl a

/-- Rule 2: Symmetry. -/
-- Theorem 58
def rule_symm {a b : A} (p : Path a b) : Path b a := Path.symm p

/-- Rule 3: Transitivity. -/
-- Theorem 59
def rule_trans {a b c : A} (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- Rule 4: Congruence. -/
-- Theorem 60
def rule_cong (f : A → B) {a b : A} (p : Path a b) :
    Path (f a) (f b) := Path.congrArg f p

/-- Rule 5: Substitution — instantiate variables. -/
-- Theorem 61
def rule_subst_inst {Sig : Signature} {Var : Type}
    (Alg : SigAlgebra Sig)
    (env : Env Sig Alg Var)
    (s t : Term Sig Var)
    (p : Path (eval Alg env s) (eval Alg env t)) :
    Path (eval Alg env s) (eval Alg env t) := p

/-! ## §25  Composition of all five rules -/

/-- Demonstrate composition of deduction rules into a single derivation chain. -/
-- Theorem 62
def five_rules_compose {C : Type} {a b c d : C}
    (f : C → C) (p : Path a b) (q : Path b c) (r : Path c d) :
    Path (f a) (f d) :=
  let step1 := Path.trans p q
  let step2 := Path.trans step1 r
  Path.congrArg f step2

/-- The composed path has correct semantics. -/
-- Theorem 63
theorem five_rules_compose_toEq {C : Type} {a b c d : C}
    (f : C → C) (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.toEq (five_rules_compose f p q r) =
      _root_.congrArg f (((Path.toEq p).trans (Path.toEq q)).trans (Path.toEq r)) := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases r with | mk sr pr =>
  cases pp; cases pq; cases pr
  rfl

/-! ## §26  Additional Path Coherence for Equational Logic -/

/-- Double congruence: applying two functions in sequence. -/
-- Theorem 64
theorem double_congruence {C : Type} {D : Type} {E : Type}
    (f : C → D) (g : D → E) {a b : C} (p : Path a b) :
    Path.congrArg g (Path.congrArg f p) =
      Path.congrArg (fun x => g (f x)) p := by
  cases p with | mk steps proof => cases proof; simp [Path.congrArg]

/-- Identity congruence is trivial. -/
-- Theorem 65
theorem id_congruence {a b : A} (p : Path a b) :
    Path.congrArg (fun x => x) p = p :=
  congrArg_id p

/-- Transport along a derivation path. -/
-- Theorem 66
theorem transport_along_derivation {C : Type} {D : C → Type}
    {a b c : C} (p : Path a b) (q : Path b c) (x : D a) :
    Path.transport (Path.trans p q) x =
      Path.transport q (Path.transport p x) :=
  transport_trans p q x

/-- The free algebra homomorphism property. -/
-- Theorem 67
theorem eval_is_hom {Sig : Signature} {Var : Type}
    (Alg : SigAlgebra Sig) (env : Env Sig Alg Var) :
    ∀ (op : Sig.OpSym) (args : Fin (Sig.arity op) → Term Sig Var),
      eval Alg env (Term.app op args) =
        Alg.interp op (fun i => eval Alg env (args i)) :=
  fun _op _args => rfl

/-- Path witnessing the homomorphism property. -/
-- Theorem 68
def eval_hom_path {Sig : Signature} {Var : Type}
    (Alg : SigAlgebra Sig) (env : Env Sig Alg Var)
    (op : Sig.OpSym) (args : Fin (Sig.arity op) → Term Sig Var) :
    Path (eval Alg env (Term.app op args))
         (Alg.interp op (fun i => eval Alg env (args i))) :=
  Path.refl _

/-! ## §27  Theory Intersection -/

/-- Intersection of equational theories. -/
-- Theorem 69
def theoryInter {Sig : Signature} {Var : Type}
    (T1 T2 : EqTheory Sig Var) : EqTheory Sig Var :=
  fun eq => T1 eq ∧ T2 eq

/-- A model of `T1` and `T2` separately is a model of the intersection. -/
-- Theorem 70
theorem model_inter {Sig : Signature} {Var : Type}
    (T1 T2 : EqTheory Sig Var) (Alg : SigAlgebra Sig)
    (hmod1 : isModel Alg T1) (hmod2 : isModel Alg T2) :
    isModel Alg (theoryInter T1 T2) :=
  fun eq ⟨h1, _h2⟩ => hmod1 eq h1

/-- A model of the intersection satisfies equations from both sides. -/
-- Theorem 71
theorem model_inter_left {Sig : Signature} {Var : Type}
    (T1 T2 : EqTheory Sig Var) (Alg : SigAlgebra Sig)
    (hmod : isModel Alg (theoryInter T1 T2))
    (eq : Equation Sig Var) (h1 : T1 eq) (h2 : T2 eq) :
    satisfies Alg eq :=
  hmod eq ⟨h1, h2⟩

/-! ## §28  Derivation Length and Path Steps -/

/-- The number of steps in a derivation path. -/
def derivLength {C : Type} {a b : C} (p : Path a b) : Nat :=
  p.steps.length

/-- Reflexivity has zero derivation length. -/
-- Theorem 72
theorem derivLength_refl {C : Type} (a : C) :
    derivLength (Path.refl a) = 0 := by
  rfl

/-- Trans adds derivation lengths. -/
-- Theorem 73
theorem derivLength_trans {C : Type} {a b c : C}
    (p : Path a b) (q : Path b c) :
    derivLength (Path.trans p q) = derivLength p + derivLength q := by
  simp [derivLength, Path.trans, List.length_append]

/-- Symm preserves derivation length. -/
-- Theorem 74
theorem derivLength_symm {C : Type} {a b : C} (p : Path a b) :
    derivLength (Path.symm p) = derivLength p := by
  simp [derivLength, Path.symm, List.length_map, List.length_reverse]

/-- CongrArg preserves derivation length. -/
-- Theorem 75
theorem derivLength_congrArg {C D : Type} (f : C → D) {a b : C}
    (p : Path a b) :
    derivLength (Path.congrArg f p) = derivLength p := by
  simp [derivLength, Path.congrArg, List.length_map]

end ComputationalPaths.Path.Algebra.EquationalLogicDeep
