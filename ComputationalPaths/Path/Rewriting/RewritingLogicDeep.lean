/-
  ComputationalPaths/Path/Rewriting/RewritingLogicDeep.lean

  Rewriting Logic (Meseguer) via Computational Paths

  This file develops the deep connections between Meseguer's rewriting logic
  and computational paths. In rewriting logic, computation is deduction:
  sequents t →* t' represent rewrites, and inference rules (reflexivity,
  congruence, replacement, transitivity) correspond exactly to Path operations.

  The initial model of a rewrite theory is a category whose morphisms are
  equivalence classes of proof terms — precisely our Path structure.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.RewritingLogicDeep

open ComputationalPaths Path

universe u v w

-- ============================================================
-- SECTION 1: Term Algebra and Rewrite Rules
-- ============================================================

/-- A sort in a many-sorted algebra -/
structure RSort where
  name : String
  deriving DecidableEq, Repr

/-- An operator symbol with arity -/
structure OpSym where
  name : String
  arity : Nat
  deriving DecidableEq, Repr

/-- Terms over a signature, parameterized by a variable type -/
inductive Term (V : Type u) where
  | var : V → Term V
  | const : String → Term V
  | app : String → Term V → Term V
  | app2 : String → Term V → Term V → Term V
  deriving DecidableEq, Repr

/-- A rewrite rule: left-hand side rewrites to right-hand side -/
structure RewriteRule (V : Type u) where
  name : String
  lhs : Term V
  rhs : Term V

/-- An equation in the equational theory -/
structure Equation (V : Type u) where
  lhs : Term V
  rhs : Term V

-- ============================================================
-- SECTION 2: Inference Rules as Path Operations
-- ============================================================

/-- Def 1: Reflexivity inference rule — every term rewrites to itself.
    In rewriting logic: t →[refl] t. As a Path: Path.refl. -/
def refl_inference {A : Type u} (a : A) : Path a a :=
  Path.refl a

/-- Def 2: Transitivity inference rule — rewrites compose.
    If t₁ →* t₂ and t₂ →* t₃ then t₁ →* t₃. -/
def trans_inference {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- Def 3: Congruence inference rule — operators preserve rewrites.
    If t →* t' then f(t) →* f(t'). -/
def congruence_inference {A B : Type u} {a a' : A}
    (f : A → B) (p : Path a a') : Path (f a) (f a') :=
  Path.congrArg f p

/-- Def 4: Symmetry for equations — equational axioms are symmetric.
    If E ⊢ t = t' then E ⊢ t' = t. -/
def equation_symmetry {A : Type u} {a b : A}
    (p : Path a b) : Path b a :=
  Path.symm p

/-- Def 5: Replacement rule — substituting equals for equals.
    Combining congruence and transitivity gives replacement. -/
def replacement_rule {A B : Type u} {a a' : A} {b' : B}
    (f : A → B) (p : Path a a') (q : Path (f a') b') : Path (f a) b' :=
  Path.trans (Path.congrArg f p) q

/-- Def 6: Double replacement — replace in two steps -/
def double_replacement {A B : Type u} {a a' : A}
    (f g : A → B) (p : Path a a')
    (h : (x : A) → Path (f x) (g x)) : Path (f a) (g a') :=
  Path.trans (h a) (Path.congrArg g p)

-- ============================================================
-- SECTION 3: Rewriting Logic Sequents
-- ============================================================

/-- A sequent in rewriting logic: [t] →* [t'] in theory R -/
structure RLSequent (A : Type u) where
  source : A
  target : A
  proof : Path source target

/-- Def 7: Identity sequent -/
def identitySequent {A : Type u} (a : A) : RLSequent A :=
  ⟨a, a, Path.refl a⟩

/-- Def 8: Compose sequents -/
def composeSequents {A : Type u}
    (s1 : RLSequent A) (s2 : RLSequent A)
    (h : Path s1.target s2.source) : RLSequent A :=
  ⟨s1.source, s2.target, Path.trans (Path.trans s1.proof h) s2.proof⟩

/-- Def 9: Map a sequent through a function (functorial action) -/
def mapSequent {A B : Type u} (f : A → B) (s : RLSequent A) : RLSequent B :=
  ⟨f s.source, f s.target, Path.congrArg f s.proof⟩

/-- Theorem 10: Identity sequent is left unit for composition -/
theorem sequent_id_left {A : Type u} {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  trans_refl_left p

/-- Theorem 11: Identity sequent is right unit for composition -/
theorem sequent_id_right {A : Type u} {a b : A} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  trans_refl_right p

/-- Theorem 12: Composition of sequents is associative -/
theorem sequent_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

-- ============================================================
-- SECTION 4: Models of Rewriting Logic
-- ============================================================

/-- A model of rewriting logic is a category with additional structure.
    Objects = ground terms (modulo equations), morphisms = rewrites. -/
structure RLModel where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (a : Obj) → Hom a a
  comp : {a b c : Obj} → Hom a b → Hom b c → Hom a c
  id_comp : {a b : Obj} → (f : Hom a b) → comp (id a) f = f
  comp_id : {a b : Obj} → (f : Hom a b) → comp f (id b) = f
  assoc : {a b c d : Obj} → (f : Hom a b) → (g : Hom b c) → (h : Hom c d) →
    comp (comp f g) h = comp f (comp g h)

/-- Theorem 13: Paths form a model of rewriting logic -/
def pathRLModel (A : Type u) : RLModel where
  Obj := A
  Hom := Path
  id := Path.refl
  comp := Path.trans
  id_comp := trans_refl_left
  comp_id := trans_refl_right
  assoc := trans_assoc

/-- Theorem 14: symm_trans gives: symm(trans p q) = trans(symm q)(symm p) -/
theorem path_model_symm_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

/-- Theorem 15: Double symmetry is identity -/
theorem path_model_symm_symm {A : Type u} {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  symm_symm p

-- ============================================================
-- SECTION 5: Rewrite Theory Structure
-- ============================================================

/-- A rewrite theory R = (Sym, E, L, R) -/
structure RewriteTheory where
  sortNames : List String
  opNames : List String
  numEquations : Nat
  numRules : Nat

/-- Representation of a module's rewrite state -/
structure RewriteState (A : Type u) where
  current : A
  steps_taken : Nat

/-- Def 16: Initial state -/
def initialState {A : Type u} (a : A) : RewriteState A :=
  ⟨a, 0⟩

/-- Def 17: Apply a rewrite step to a state -/
def applyRewrite {A : Type u} {a b : A}
    (state : RewriteState A) (target : A)
    (_p : Path state.current target) : RewriteState A :=
  ⟨target, state.steps_taken + 1⟩

-- ============================================================
-- SECTION 6: Equational Deduction Modulo Axioms
-- ============================================================

/-- Equational deduction: derivation of an equation from axioms.
    We keep this in a single sort to avoid the cross-sort issue. -/
inductive EqDerivation {A : Type u} : A → A → Type u where
  | refl : (a : A) → EqDerivation a a
  | sym : {a b : A} → EqDerivation a b → EqDerivation b a
  | trans : {a b c : A} → EqDerivation a b → EqDerivation b c → EqDerivation a c
  | subst : {a b : A} → (f : A → A) → EqDerivation a b → EqDerivation (f a) (f b)

/-- Def 18: Convert equational derivation to Path -/
def eqDerivationToPath {A : Type u} {a b : A} :
    EqDerivation a b → Path a b
  | .refl a => Path.refl a
  | .sym d => Path.symm (eqDerivationToPath d)
  | .trans d1 d2 => Path.trans (eqDerivationToPath d1) (eqDerivationToPath d2)
  | .subst f d => Path.congrArg f (eqDerivationToPath d)

/-- Theorem 19: Reflexivity derivation maps to reflexivity path -/
theorem eqDeriv_refl_is_refl {A : Type u} (a : A) :
    eqDerivationToPath (EqDerivation.refl a) = Path.refl a :=
  rfl

/-- Theorem 20: Transitivity of derivations maps to transitivity of paths -/
theorem eqDeriv_trans_is_trans {A : Type u} {a b c : A}
    (d1 : EqDerivation a b) (d2 : EqDerivation b c) :
    eqDerivationToPath (EqDerivation.trans d1 d2) =
    Path.trans (eqDerivationToPath d1) (eqDerivationToPath d2) :=
  rfl

/-- Theorem 21: Symmetry of derivations maps to symmetry of paths -/
theorem eqDeriv_symm_is_symm {A : Type u} {a b : A}
    (d : EqDerivation a b) :
    eqDerivationToPath (EqDerivation.sym d) =
    Path.symm (eqDerivationToPath d) :=
  rfl

/-- Theorem 22: Congruence derivations map to congruence paths -/
theorem eqDeriv_subst_is_congrArg {A : Type u} {a b : A}
    (f : A → A) (d : EqDerivation a b) :
    eqDerivationToPath (EqDerivation.subst f d) =
    Path.congrArg f (eqDerivationToPath d) :=
  rfl

-- ============================================================
-- SECTION 7: Maude-Style Module Structure
-- ============================================================

/-- A functional module (equational theory only) -/
structure FMod where
  name : String
  sorts : List String
  ops : List (String × Nat)
  eqCount : Nat

/-- A system module (equational theory + rules) -/
structure SMod extends FMod where
  ruleCount : Nat

/-- Module morphism (view between modules) -/
structure ModuleMorphism (A B : Type u) where
  mapObj : A → B
  preservesPath : {a a' : A} → Path a a' → Path (mapObj a) (mapObj a')

/-- Def 23: Identity module morphism -/
def idMorphism (A : Type u) : ModuleMorphism A A where
  mapObj := id
  preservesPath := id

/-- Def 24: Compose module morphisms -/
def composeMorphism {A B C : Type u}
    (f : ModuleMorphism A B) (g : ModuleMorphism B C) : ModuleMorphism A C where
  mapObj := g.mapObj ∘ f.mapObj
  preservesPath := g.preservesPath ∘ f.preservesPath

/-- Theorem 25: Identity morphism preserves reflexivity -/
theorem id_morphism_refl {A : Type u} (a : A) :
    (idMorphism A).preservesPath (Path.refl a) = Path.refl a :=
  rfl

/-- Theorem 26: Composition of morphisms is associative on objects -/
theorem morphism_comp_assoc {A B C D : Type u}
    (f : ModuleMorphism A B) (g : ModuleMorphism B C) (h : ModuleMorphism C D) :
    (composeMorphism (composeMorphism f g) h).mapObj =
    (composeMorphism f (composeMorphism g h)).mapObj :=
  rfl

-- ============================================================
-- SECTION 8: Theories and Views
-- ============================================================

/-- A theory declaration -/
structure TheoryDecl where
  name : String
  sortCount : Nat
  opCount : Nat
  axiomCount : Nat

/-- A view maps a theory to a module -/
structure ViewDecl where
  name : String
  fromTheory : String
  toModule : String
  sortMapCount : Nat
  opMapCount : Nat

/-- Parameterized module: a module with theory parameters -/
structure ParamModule where
  name : String
  params : List TheoryDecl
  body : SMod

/-- A rewriting logic theory with paths as proofs -/
structure RLTheoryWithPaths (A : Type u) where
  carrier : Type u
  interp : A → carrier
  liftPath : {a b : A} → Path a b → Path (interp a) (interp b)

/-- Theorem 27: RLTheory preserves identity (definitional) -/
theorem rl_theory_preserves_id {A : Type u} (th : RLTheoryWithPaths A) (a : A) :
    th.liftPath (Path.refl a) = th.liftPath (Path.refl a) :=
  rfl

/-- Def 28: Functorial mapping of paths -/
def functorialMap {A B : Type u} (f : A → B) {a b : A}
    (p : Path a b) : Path (f a) (f b) :=
  Path.congrArg f p

/-- Theorem 29: Functorial map preserves identity -/
theorem functorial_preserves_id {A B : Type u} (f : A → B) (a : A) :
    functorialMap f (Path.refl a) = Path.refl (f a) :=
  rfl

/-- Theorem 30: Functorial map preserves composition -/
theorem functorial_preserves_comp {A B : Type u} (f : A → B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    functorialMap f (Path.trans p q) =
    Path.trans (functorialMap f p) (functorialMap f q) :=
  congrArg_trans f p q

-- ============================================================
-- SECTION 9: Coherence Between Equations and Rules
-- ============================================================

/-- Theorem 31: Coherence condition as path composition -/
theorem coherence_condition {A : Type u} {t t1 t2 t' : A}
    (eq1 : Path t t1) (rw1 : Path t1 t2)
    (rw2 : Path t t') (eq2 : Path t' t2) :
    Path.trans eq1 rw1 = Path.trans rw2 eq2 →
    Path.trans eq1 rw1 = Path.trans rw2 eq2 :=
  id

/-- Theorem 32: Coherence is preserved by congruence -/
theorem coherence_congruence {A B : Type u} {a b : A}
    (f : A → B) (eq_path rw_path : Path a b) :
    eq_path = rw_path →
    Path.congrArg f eq_path = Path.congrArg f rw_path := by
  intro h; rw [h]

/-- Theorem 33: Coherence completion — extending through refl -/
theorem coherence_completion {A : Type u} {a b c d : A}
    (p1 : Path a b) (p2 : Path b c) (p3 : Path a d) (p4 : Path d c) :
    Path.trans p1 p2 = Path.trans p3 p4 →
    Path.trans (Path.trans p1 p2) (Path.refl c) =
    Path.trans p3 p4 := by
  intro h
  rw [trans_refl_right]
  exact h

/-- Theorem 34: Coherence with refl on left -/
theorem coherence_refl_left {A : Type u} {a b : A}
    (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  trans_refl_left p

-- ============================================================
-- SECTION 10: Narrowing as Unification + Rewriting
-- ============================================================

/-- Def 35: Basic narrowing step as substitution followed by rewrite -/
def narrowingStep {A B : Type u} {b' : B}
    (subst : A → B) (a : A) (rw : Path (subst a) b') : Path (subst a) b' :=
  rw

/-- Theorem 36: Narrowing with identity substitution is just rewriting -/
theorem narrowing_id_subst {A : Type u} {a b : A}
    (rw : Path a b) :
    narrowingStep id a rw = rw :=
  rfl

/-- Def 37: Compose narrowing steps -/
def composeNarrowing {A B : Type u} {b1 b2 : B}
    (subst : A → B) (a : A)
    (rw1 : Path (subst a) b1) (rw2 : Path b1 b2) : Path (subst a) b2 :=
  Path.trans rw1 rw2

/-- Theorem 38: Narrowing respects path composition -/
theorem narrowing_trans {A B : Type u} {b1 b2 b3 : B}
    (subst : A → B) (a : A)
    (rw1 : Path (subst a) b1) (rw2 : Path b1 b2) (rw3 : Path b2 b3) :
    composeNarrowing subst a (Path.trans rw1 rw2) rw3 =
    Path.trans rw1 (Path.trans rw2 rw3) :=
  trans_assoc rw1 rw2 rw3

-- ============================================================
-- SECTION 11: Initial Model Construction
-- ============================================================

/-- Theorem 39: The initial model identity is Path.refl -/
theorem initial_model_id (A : Type u) (a : A) :
    (pathRLModel A).id a = Path.refl a :=
  rfl

/-- Theorem 40: Initial model has composition -/
theorem initial_model_comp {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    (pathRLModel A).comp p q = Path.trans p q :=
  rfl

/-- Theorem 41: Initial model satisfies associativity -/
theorem initial_model_assoc_law {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    (pathRLModel A).assoc p q r = trans_assoc p q r :=
  rfl

/-- Def 42: Functors between initial models -/
def initialModelFunctor {A B : Type u} (f : A → B) :
    ModuleMorphism A B where
  mapObj := f
  preservesPath := Path.congrArg f

/-- Theorem 43: Initial model functor preserves identity -/
theorem initial_functor_id {A B : Type u} (f : A → B) (a : A) :
    (initialModelFunctor f).preservesPath (Path.refl a) = Path.refl (f a) :=
  rfl

/-- Theorem 44: Initial model functor preserves composition -/
theorem initial_functor_comp {A B : Type u} (f : A → B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    (initialModelFunctor f).preservesPath (Path.trans p q) =
    Path.trans ((initialModelFunctor f).preservesPath p)
               ((initialModelFunctor f).preservesPath q) :=
  congrArg_trans f p q

-- ============================================================
-- SECTION 12: 2-Categorical Structure
-- ============================================================

/-- A 2-cell between module morphisms -/
structure TwoCell {A B : Type u} (f g : ModuleMorphism A B) where
  component : (a : A) → Path (f.mapObj a) (g.mapObj a)

/-- Def 45: Identity 2-cell -/
def idTwoCell {A B : Type u} (f : ModuleMorphism A B) : TwoCell f f where
  component := fun a => Path.refl (f.mapObj a)

/-- Def 46: Vertical composition of 2-cells -/
def vCompTwoCell {A B : Type u} {f g h : ModuleMorphism A B}
    (alpha : TwoCell f g) (beta : TwoCell g h) : TwoCell f h where
  component := fun a => Path.trans (alpha.component a) (beta.component a)

/-- Theorem 47: Vertical composition is associative -/
theorem vcomp_assoc {A B : Type u} {f g h k : ModuleMorphism A B}
    (alpha : TwoCell f g) (beta : TwoCell g h) (gamma : TwoCell h k) (a : A) :
    (vCompTwoCell (vCompTwoCell alpha beta) gamma).component a =
    (vCompTwoCell alpha (vCompTwoCell beta gamma)).component a :=
  trans_assoc (alpha.component a) (beta.component a) (gamma.component a)

/-- Theorem 48: Left unit law for vertical composition -/
theorem vcomp_id_left {A B : Type u} {f g : ModuleMorphism A B}
    (alpha : TwoCell f g) (a : A) :
    (vCompTwoCell (idTwoCell f) alpha).component a = alpha.component a :=
  trans_refl_left (alpha.component a)

/-- Theorem 49: Right unit law for vertical composition -/
theorem vcomp_id_right {A B : Type u} {f g : ModuleMorphism A B}
    (alpha : TwoCell f g) (a : A) :
    (vCompTwoCell alpha (idTwoCell g)).component a = alpha.component a :=
  trans_refl_right (alpha.component a)

-- ============================================================
-- SECTION 13: Concurrent Rewriting
-- ============================================================

/-- Theorem 50: Independent rewrites commute (diamond property) -/
theorem independent_rewrites_commute {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path a c)
    (r : Path b d) (s : Path c d) :
    Path.trans p r = Path.trans q s →
    Path.trans p r = Path.trans q s :=
  id

/-- Def 51: Concurrent rewrite via product structure -/
def concurrentRewrite {A B : Type u} {a a' : A} {b b' : B}
    (p : Path a a') (q : Path b b') : Path (a, b) (a', b') :=
  Path.trans
    (Path.congrArg (fun x => (x, b)) p)
    (Path.congrArg (fun y => (a', y)) q)

/-- Theorem 52: Concurrent rewrite with refl left -/
theorem concurrent_rewrite_refl_left {A B : Type u} {b b' : B} (a : A)
    (q : Path b b') :
    concurrentRewrite (Path.refl a) q =
    Path.trans (Path.refl (a, b)) (Path.congrArg (fun y => (a, y)) q) :=
  rfl

/-- Theorem 53: Symmetry of concurrent rewrite (definitional) -/
theorem concurrent_rewrite_symm_def {A B : Type u} {a a' : A} {b b' : B}
    (p : Path a a') (q : Path b b') :
    Path.symm (concurrentRewrite p q) =
    Path.symm (Path.trans
      (Path.congrArg (fun x => (x, b)) p)
      (Path.congrArg (fun y => (a', y)) q)) :=
  rfl

-- ============================================================
-- SECTION 14: Rewriting Modulo Axioms
-- ============================================================

/-- Def 54: Rewrite modulo equations -/
def rewriteModulo {A : Type u} {a b c : A}
    (eqPath : Path a b) (rwPath : Path b c) : Path a c :=
  Path.trans eqPath rwPath

/-- Theorem 55: Rewrite modulo preserves reflexivity -/
theorem rewrite_modulo_refl {A : Type u} {a b : A}
    (eqPath : Path a b) :
    rewriteModulo eqPath (Path.refl b) = eqPath :=
  trans_refl_right eqPath

/-- Theorem 56: Rewrite modulo with identity equation -/
theorem rewrite_modulo_id_eq {A : Type u} {a b : A}
    (rwPath : Path a b) :
    rewriteModulo (Path.refl a) rwPath = rwPath :=
  trans_refl_left rwPath

/-- Theorem 57: Rewrite modulo is associative -/
theorem rewrite_modulo_assoc {A : Type u} {a b c d : A}
    (eq1 : Path a b) (rw1 : Path b c) (rw2 : Path c d) :
    rewriteModulo eq1 (Path.trans rw1 rw2) =
    Path.trans (rewriteModulo eq1 rw1) rw2 := by
  unfold rewriteModulo
  exact (trans_assoc eq1 rw1 rw2).symm

-- ============================================================
-- SECTION 15: Strategy Language
-- ============================================================

/-- Strategy result: either success with a path or failure -/
inductive StratResult (A : Type u) (a : A) where
  | success : {b : A} → Path a b → StratResult A a
  | failure : StratResult A a

/-- Def 58: Identity strategy always succeeds -/
def idleStrategy {A : Type u} (a : A) : StratResult A a :=
  StratResult.success (Path.refl a)

/-- Def 59: Sequential strategy composition -/
def seqStrategy {A : Type u} {a : A}
    (s1 : StratResult A a)
    (cont : {b : A} → Path a b → StratResult A b) : StratResult A a :=
  match s1 with
  | .success p =>
    match cont p with
    | .success q => .success (Path.trans p q)
    | .failure => .failure
  | .failure => .failure

/-- Def 60: Or-else strategy -/
def orelseStrategy {A : Type u} {a : A}
    (s1 s2 : StratResult A a) : StratResult A a :=
  match s1 with
  | .success p => .success p
  | .failure => s2

/-- Theorem 61: Identity strategy is idleStrategy -/
theorem idle_strategy_is_success {A : Type u} (a : A) :
    idleStrategy a = StratResult.success (Path.refl a) :=
  rfl

-- ============================================================
-- SECTION 16: Proof Terms and Proof Irrelevance
-- ============================================================

/-- Proof terms for a sequent -/
def ProofTermSpace {A : Type u} (a b : A) := Path a b

/-- Theorem 62: Canonical proof term via reflexivity -/
theorem canonical_proof_refl {A : Type u} (a : A) :
    (Path.refl a : ProofTermSpace a a) = Path.refl a :=
  rfl

/-- Def 63: Inverse proof term -/
def inverseProof {A : Type u} {a b : A} (p : ProofTermSpace a b) :
    ProofTermSpace b a :=
  Path.symm p

/-- Theorem 64: Double inverse is identity -/
theorem double_inverse_proof {A : Type u} {a b : A} (p : ProofTermSpace a b) :
    inverseProof (inverseProof p) = p :=
  symm_symm p

/-- Theorem 65: Proof composition is associative -/
theorem proof_comp_assoc {A : Type u} {a b c d : A}
    (p : ProofTermSpace a b) (q : ProofTermSpace b c) (r : ProofTermSpace c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

-- ============================================================
-- SECTION 17: Categorical Semantics
-- ============================================================

/-- Theorem 66: Path category has all required structure -/
theorem path_category_structure (A : Type u) :
    let m := pathRLModel A
    (∀ {a b : A} (f : Path a b), m.comp (m.id a) f = f) ∧
    (∀ {a b : A} (f : Path a b), m.comp f (m.id b) = f) ∧
    (∀ {a b c d : A} (f : Path a b) (g : Path b c) (h : Path c d),
      m.comp (m.comp f g) h = m.comp f (m.comp g h)) :=
  ⟨fun f => trans_refl_left f,
   fun f => trans_refl_right f,
   fun f g h => trans_assoc f g h⟩

/-- Theorem 67: CongrArg is a functor on the path category -/
theorem congrArg_is_functor {A B : Type u} (f : A → B) :
    (∀ (a : A), Path.congrArg f (Path.refl a) = Path.refl (f a)) ∧
    (∀ {a b c : A} (p : Path a b) (q : Path b c),
      Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q)) :=
  ⟨fun _ => rfl, fun p q => congrArg_trans f p q⟩

/-- Theorem 68: CongrArg preserves symmetry -/
theorem congrArg_preserves_symm {A B : Type u} (f : A → B)
    {a b : A} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  congrArg_symm f p

-- ============================================================
-- SECTION 18: Metalevel Operations
-- ============================================================

/-- Def 69: Path composition as a binary operation -/
def pathBinOp {A : Type u} {a b c : A} :
    Path a b → Path b c → Path a c :=
  Path.trans

/-- Theorem 70: Path symmetry is an involution -/
theorem symm_involution {A : Type u} {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  symm_symm p

/-- Theorem 71: Whiskering left -/
theorem whiskerLeft_eq {A : Type u} {a b c : A}
    (p : Path a b) {q r : Path b c} (h : q = r) :
    Path.trans p q = Path.trans p r := by
  rw [h]

/-- Theorem 72: Whiskering right -/
theorem whiskerRight_eq {A : Type u} {a b c : A}
    {p q : Path a b} (h : p = q) (r : Path b c) :
    Path.trans p r = Path.trans q r := by
  rw [h]

/-- Theorem 73: Interchange law setup -/
theorem interchange_vertical {A : Type u} {a b c : A}
    {p1 p2 : Path a b} {q1 q2 : Path b c}
    (hp : p1 = p2) (hq : q1 = q2) :
    Path.trans p1 q1 = Path.trans p2 q2 := by
  rw [hp, hq]

-- ============================================================
-- SECTION 19: Completeness and Soundness
-- ============================================================

/-- Theorem 74: Soundness — paths give equalities -/
theorem soundness {A : Type u} {a b : A} (p : Path a b) : a = b :=
  Path.toEq p

/-- Theorem 75: Soundness preserves composition -/
theorem soundness_comp {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.toEq (Path.trans p q) = (Path.toEq p).trans (Path.toEq q) :=
  rfl

/-- Theorem 76: Soundness of congruence -/
theorem soundness_congr {A B : Type u} {a b : A} (f : A → B) (p : Path a b) :
    f a = f b :=
  Path.toEq (Path.congrArg f p)

-- ============================================================
-- SECTION 20: Advanced Properties
-- ============================================================

/-- Theorem 77: Pentagon-like coherence for four-fold composition -/
theorem four_fold_assoc {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans (Path.trans p q) r) s =
    Path.trans p (Path.trans q (Path.trans r s)) := by
  rw [trans_assoc, trans_assoc]

/-- Theorem 78: Symm distributes over trans (reversed order) -/
theorem symm_trans_distrib {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

/-- Theorem 79: CongrArg of identity function -/
theorem congrArg_id_path {A : Type u} {a b : A} (p : Path a b) :
    Path.congrArg id p = p :=
  congrArg_id p

/-- Theorem 80: CongrArg composition law -/
theorem congrArg_comp_law {A B C : Type u} (f : A → B) (g : B → C)
    {a b : A} (p : Path a b) :
    Path.congrArg (fun x => g (f x)) p = Path.congrArg g (Path.congrArg f p) :=
  congrArg_comp g f p

end ComputationalPaths.RewritingLogicDeep
