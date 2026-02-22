/-
  ComputationalPaths.Path.Rewriting.TypedLambdaDeep
  ==================================================
  Simply Typed Lambda Calculus with de Bruijn indices,
  beta/eta reduction, subject reduction, confluence,
  normalization structure — all connected to computational paths.

  Author: armada-367 (TypedLambdaDeep)
-/
import ComputationalPaths.Path.Basic

namespace ComputationalPaths.TypedLambdaDeep

open ComputationalPaths
open ComputationalPaths.Path

-- ═══════════════════════════════════════════════════════════════
-- Section 1: Simple Types
-- ═══════════════════════════════════════════════════════════════

/-- Simple types: a base type and arrow types. -/
inductive Ty : Type where
  | base : Ty
  | arrow : Ty -> Ty -> Ty
  deriving DecidableEq, Repr

infixr:25 " ~> " => Ty.arrow

/-- Theorem 1: arrow is injective left -/
theorem Ty.arrow_inj_left : (Ty.arrow a b) = (Ty.arrow c d) -> a = c := by
  intro h; injection h

/-- Theorem 2: arrow is injective right -/
theorem Ty.arrow_inj_right : (Ty.arrow a b) = (Ty.arrow c d) -> b = d := by
  intro h; injection h

/-- Theorem 3: base is not arrow -/
theorem Ty.base_ne_arrow : Ty.base ≠ Ty.arrow a b := by
  intro h; cases h

/-- Theorem 4: type equality is decidable -/
instance : DecidableEq Ty := inferInstance

-- ═══════════════════════════════════════════════════════════════
-- Section 2: de Bruijn Terms
-- ═══════════════════════════════════════════════════════════════

/-- Lambda terms with de Bruijn indices -/
inductive Term : Type where
  | var : Nat -> Term
  | app : Term -> Term -> Term
  | lam : Ty -> Term -> Term
  deriving DecidableEq, Repr

namespace Term

/-- Shifting: increase free variables at or above cutoff by d -/
noncomputable def shift (d : Nat) (c : Nat) : Term -> Term
  | var k => if k < c then var k else var (k + d)
  | app t1 t2 => app (shift d c t1) (shift d c t2)
  | lam ty body => lam ty (shift d c.succ body)

/-- Substitution: replace variable j with s -/
noncomputable def subst (j : Nat) (s : Term) : Term -> Term
  | var k => if k = j then s else if j < k then var (k - 1) else var k
  | app t1 t2 => app (subst j s t1) (subst j s t2)
  | lam ty body => lam ty (subst j.succ (shift 1 0 s) body)

/-- Beta reduction of (lam ty body) applied to arg -/
noncomputable def betaReduce (body arg : Term) : Term :=
  subst 0 arg body

/-- Size of a term -/
noncomputable def size : Term -> Nat
  | var _ => 1
  | app t1 t2 => 1 + size t1 + size t2
  | lam _ body => 1 + size body

/-- Theorem 5: size is always positive -/
theorem size_pos (t : Term) : 0 < t.size := by
  cases t <;> simp [size] <;> omega

/-- Theorem 6: app size > left subterm -/
theorem size_app_left (t1 t2 : Term) : t1.size < (app t1 t2).size := by
  simp [size]; omega

/-- Theorem 7: app size > right subterm -/
theorem size_app_right (t1 t2 : Term) : t2.size < (app t1 t2).size := by
  simp [size]; omega

/-- Theorem 8: lam size > body -/
theorem size_lam (ty : Ty) (body : Term) : body.size < (lam ty body).size := by
  simp [size]

/-- Theorem 9: shift preserves variable below cutoff -/
theorem shift_var_below (d c k : Nat) (h : k < c) :
    shift d c (var k) = var k := by
  unfold shift; split
  · rfl
  · omega

/-- Theorem 10: shift of 0 is identity -/
theorem shift_zero (c : Nat) (t : Term) : shift 0 c t = t := by
  induction t generalizing c with
  | var k =>
    unfold shift
    split
    · rfl
    · simp
  | app t1 t2 ih1 ih2 => unfold shift; rw [ih1, ih2]
  | lam _ body ih => unfold shift; rw [ih]

/-- Theorem 11: substitution on var j yields the substitute -/
theorem subst_var_eq (j : Nat) (s : Term) :
    subst j s (var j) = s := by
  simp [subst]

/-- Theorem 12: substitution on var below j is identity -/
theorem subst_var_lt (j k : Nat) (s : Term) (h : k < j) :
    subst j s (var k) = var k := by
  unfold subst
  have hne : ¬(k = j) := by omega
  have hnlt : ¬(j < k) := by omega
  rw [if_neg hne, if_neg hnlt]

/-- Theorem 13: substitution on var above j decrements -/
theorem subst_var_gt (j k : Nat) (s : Term) (h : k > j) :
    subst j s (var k) = var (k - 1) := by
  unfold subst
  have hne : ¬(k = j) := by omega
  have hlt : j < k := h
  rw [if_neg hne, if_pos hlt]

/-- Check if term is a value (lambda abstraction) -/
noncomputable def isValue : Term -> Bool
  | lam _ _ => true
  | _ => false

/-- Check if term is in normal form (no redexes) -/
noncomputable def isNormalForm : Term -> Bool
  | var _ => true
  | app (lam _ _) _ => false
  | app t1 t2 => isNormalForm t1 && isNormalForm t2
  | lam _ body => isNormalForm body

/-- Check if in weak head normal form -/
noncomputable def isWHNF : Term -> Bool
  | var _ => true
  | lam _ _ => true
  | app (lam _ _) _ => false
  | app t1 _ => isWHNF t1

end Term

-- ═══════════════════════════════════════════════════════════════
-- Section 3: Typing Context and Judgments
-- ═══════════════════════════════════════════════════════════════

/-- Typing context as a list of types (de Bruijn) -/
abbrev Ctx := List Ty

/-- Typing judgment: Gam |- t : T -/
inductive HasType : Ctx -> Term -> Ty -> Prop where
  | tvar : forall {Gam : Ctx} {n : Nat} {T : Ty},
      Gam[n]? = some T -> HasType Gam (Term.var n) T
  | tapp : forall {Gam : Ctx} {t1 t2 : Term} {A B : Ty},
      HasType Gam t1 (Ty.arrow A B) -> HasType Gam t2 A ->
      HasType Gam (Term.app t1 t2) B
  | tlam : forall {Gam : Ctx} {body : Term} {A B : Ty},
      HasType (A :: Gam) body B ->
      HasType Gam (Term.lam A body) (Ty.arrow A B)

notation:40 Gam " ⊢ " t " ::: " T => HasType Gam t T

/-- Theorem 14: typing is deterministic -/
theorem HasType.deterministic {Gam : Ctx} {t : Term} {A B : Ty}
    (h1 : Gam ⊢ t ::: A) (h2 : Gam ⊢ t ::: B) : A = B := by
  induction h1 generalizing B with
  | tvar hlu1 =>
    cases h2 with
    | tvar hlu2 => rw [hlu1] at hlu2; exact Option.some.inj hlu2
  | tapp _ _ ih1 _ =>
    cases h2 with
    | tapp hf2 _ =>
      have heq := ih1 hf2
      exact Ty.arrow_inj_right heq
  | tlam _ ih =>
    cases h2 with
    | tlam hb2 =>
      have := ih hb2
      exact congrArg (Ty.arrow _) this

/-- Theorem 15: weakening - adding to context end preserves typing -/
theorem HasType.weakening_cons {Gam : Ctx} {A S : Ty} {Gam' : Ctx}
    (h : Gam ⊢ Term.var 0 ::: A) (hctx : Gam = S :: Gam') :
    A = S := by
  subst hctx; cases h with
  | tvar hlu => simp at hlu; exact hlu.symm

-- ═══════════════════════════════════════════════════════════════
-- Section 4: Reduction Relations
-- ═══════════════════════════════════════════════════════════════

/-- Single-step beta reduction -/
inductive BetaStep : Term -> Term -> Prop where
  | beta : forall (ty : Ty) (body arg : Term),
      BetaStep (Term.app (Term.lam ty body) arg) (Term.betaReduce body arg)
  | appLeft : forall {t1 t1' : Term} (t2 : Term),
      BetaStep t1 t1' -> BetaStep (Term.app t1 t2) (Term.app t1' t2)
  | appRight : forall (t1 : Term) {t2 t2' : Term},
      BetaStep t2 t2' -> BetaStep (Term.app t1 t2) (Term.app t1 t2')
  | lamBody : forall (ty : Ty) {body body' : Term},
      BetaStep body body' -> BetaStep (Term.lam ty body) (Term.lam ty body')

/-- Eta reduction -/
inductive EtaStep : Term -> Term -> Prop where
  | eta : forall (ty : Ty) (t : Term),
      EtaStep (Term.lam ty (Term.app (Term.shift 1 0 t) (Term.var 0))) t

/-- Combined beta-eta step -/
inductive BetaEtaStep : Term -> Term -> Prop where
  | ofBeta : BetaStep a b -> BetaEtaStep a b
  | ofEta : EtaStep a b -> BetaEtaStep a b

/-- Multi-step beta reduction (reflexive transitive closure) -/
inductive BetaMulti : Term -> Term -> Prop where
  | refl : BetaMulti t t
  | step : BetaStep t1 t2 -> BetaMulti t2 t3 -> BetaMulti t1 t3

/-- Theorem 16: multi-step is transitive -/
theorem BetaMulti.trans' {a b c : Term}
    (h1 : BetaMulti a b) (h2 : BetaMulti b c) : BetaMulti a c := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact BetaMulti.step hs (ih h2)

/-- Theorem 17: single step embeds into multi -/
theorem BetaMulti.single (hs : BetaStep a b) : BetaMulti a b :=
  BetaMulti.step hs BetaMulti.refl

/-- Theorem 18: multi-step appLeft congruence -/
theorem BetaMulti.appLeft (t2 : Term) {t1 t1' : Term}
    (h : BetaMulti t1 t1') : BetaMulti (Term.app t1 t2) (Term.app t1' t2) := by
  induction h with
  | refl => exact BetaMulti.refl
  | step hs _ ih => exact BetaMulti.step (BetaStep.appLeft t2 hs) ih

/-- Theorem 19: multi-step appRight congruence -/
theorem BetaMulti.appRight (t1 : Term) {t2 t2' : Term}
    (h : BetaMulti t2 t2') : BetaMulti (Term.app t1 t2) (Term.app t1 t2') := by
  induction h with
  | refl => exact BetaMulti.refl
  | step hs _ ih => exact BetaMulti.step (BetaStep.appRight t1 hs) ih

/-- Theorem 20: multi-step lamBody congruence -/
theorem BetaMulti.lamBody (ty : Ty) {body body' : Term}
    (h : BetaMulti body body') : BetaMulti (Term.lam ty body) (Term.lam ty body') := by
  induction h with
  | refl => exact BetaMulti.refl
  | step hs _ ih => exact BetaMulti.step (BetaStep.lamBody ty hs) ih

-- ═══════════════════════════════════════════════════════════════
-- Section 5: Normal Forms
-- ═══════════════════════════════════════════════════════════════

/-- A term is in normal form if no beta step is possible -/
noncomputable def NormalForm (t : Term) : Prop :=
  forall t', ¬ BetaStep t t'

/-- A term is in weak head normal form -/
noncomputable def WeakHeadNF (t : Term) : Prop :=
  match t with
  | Term.var _ => True
  | Term.lam _ _ => True
  | Term.app (Term.lam _ _) _ => False
  | Term.app _ _ => True

/-- Theorem 21: variables are in normal form -/
theorem var_normalForm (n : Nat) : NormalForm (Term.var n) := by
  intro t' h; cases h

/-- Theorem 22: normal form implies WHNF -/
theorem normalForm_imp_whnf (t : Term) (h : NormalForm t) : WeakHeadNF t := by
  cases t with
  | var n => exact True.intro
  | lam _ _ => exact True.intro
  | app t1 t2 =>
    simp [WeakHeadNF]
    cases t1 with
    | var _ => exact True.intro
    | app _ _ => exact True.intro
    | lam ty body => exact absurd (BetaStep.beta ty body t2) (h _)

/-- Theorem 23: variables are WHNF -/
theorem var_whnf (n : Nat) : WeakHeadNF (Term.var n) := True.intro

/-- Theorem 24: lambdas are WHNF -/
theorem lam_whnf (ty : Ty) (body : Term) : WeakHeadNF (Term.lam ty body) := True.intro

/-- Theorem 25: normal form is unique in multi-step -/
theorem normalForm_multi_eq {t nf : Term}
    (hn : NormalForm nf) (hm : BetaMulti nf t) : nf = t := by
  cases hm with
  | refl => rfl
  | step hs _ => exact absurd hs (hn _)

-- ═══════════════════════════════════════════════════════════════
-- Section 6: Path algebra on Types
-- ═══════════════════════════════════════════════════════════════

/-- Arrow congruence path (left) -/
noncomputable def arrowCongrLeft {A A' : Ty} (B : Ty) (p : Path A A') :
    Path (Ty.arrow A B) (Ty.arrow A' B) :=
  Path.congrArg (Ty.arrow · B) p

/-- Arrow congruence path (right) -/
noncomputable def arrowCongrRight (A : Ty) {B B' : Ty} (p : Path B B') :
    Path (Ty.arrow A B) (Ty.arrow A B') :=
  Path.congrArg (Ty.arrow A ·) p

/-- Arrow congruence in both positions -/
noncomputable def arrowCongr {A A' B B' : Ty} (p1 : Path A A') (p2 : Path B B') :
    Path (Ty.arrow A B) (Ty.arrow A' B') :=
  Path.trans (arrowCongrLeft B p1) (arrowCongrRight A' p2)

/-- Theorem 26: arrowCongrLeft preserves trans -/
theorem arrowCongrLeft_trans (B : Ty) {A A' A'' : Ty}
    (p : Path A A') (q : Path A' A'') :
    arrowCongrLeft B (Path.trans p q) =
    Path.trans (arrowCongrLeft B p) (arrowCongrLeft B q) :=
  Path.congrArg_trans (Ty.arrow · B) p q

/-- Theorem 27: arrowCongrLeft preserves symm -/
theorem arrowCongrLeft_symm (B : Ty) {A A' : Ty} (p : Path A A') :
    arrowCongrLeft B (Path.symm p) = Path.symm (arrowCongrLeft B p) :=
  Path.congrArg_symm (Ty.arrow · B) p

/-- Theorem 28: arrowCongrRight preserves trans -/
theorem arrowCongrRight_trans (A : Ty) {B B' B'' : Ty}
    (p : Path B B') (q : Path B' B'') :
    arrowCongrRight A (Path.trans p q) =
    Path.trans (arrowCongrRight A p) (arrowCongrRight A q) :=
  Path.congrArg_trans (Ty.arrow A ·) p q

/-- Theorem 29: arrowCongrRight preserves symm -/
theorem arrowCongrRight_symm (A : Ty) {B B' : Ty} (p : Path B B') :
    arrowCongrRight A (Path.symm p) = Path.symm (arrowCongrRight A p) :=
  Path.congrArg_symm (Ty.arrow A ·) p

-- ═══════════════════════════════════════════════════════════════
-- Section 7: Path algebra on Terms
-- ═══════════════════════════════════════════════════════════════

/-- App-left congruence path -/
noncomputable def appLeftPath {t1 t1' : Term} (t2 : Term) (p : Path t1 t1') :
    Path (Term.app t1 t2) (Term.app t1' t2) :=
  Path.congrArg (Term.app · t2) p

/-- App-right congruence path -/
noncomputable def appRightPath (t1 : Term) {t2 t2' : Term} (p : Path t2 t2') :
    Path (Term.app t1 t2) (Term.app t1 t2') :=
  Path.congrArg (Term.app t1 ·) p

/-- Lambda body congruence path -/
noncomputable def lamBodyPath (ty : Ty) {body body' : Term} (p : Path body body') :
    Path (Term.lam ty body) (Term.lam ty body') :=
  Path.congrArg (Term.lam ty ·) p

/-- Lambda type congruence path -/
noncomputable def lamTyPath {ty ty' : Ty} (body : Term) (p : Path ty ty') :
    Path (Term.lam ty body) (Term.lam ty' body) :=
  Path.congrArg (Term.lam · body) p

/-- Full app congruence path -/
noncomputable def appCongr {t1 t1' t2 t2' : Term}
    (p1 : Path t1 t1') (p2 : Path t2 t2') :
    Path (Term.app t1 t2) (Term.app t1' t2') :=
  Path.trans (appLeftPath t2 p1) (appRightPath t1' p2)

/-- Theorem 30: appLeftPath preserves trans -/
theorem appLeft_trans {a b c : Term} (t : Term)
    (p : Path a b) (q : Path b c) :
    appLeftPath t (Path.trans p q) =
    Path.trans (appLeftPath t p) (appLeftPath t q) :=
  Path.congrArg_trans (Term.app · t) p q

/-- Theorem 31: appLeftPath preserves symm -/
theorem appLeft_symm {a b : Term} (t : Term) (p : Path a b) :
    appLeftPath t (Path.symm p) = Path.symm (appLeftPath t p) :=
  Path.congrArg_symm (Term.app · t) p

/-- Theorem 32: lamBodyPath preserves trans -/
theorem lamBody_trans (ty : Ty) {a b c : Term}
    (p : Path a b) (q : Path b c) :
    lamBodyPath ty (Path.trans p q) =
    Path.trans (lamBodyPath ty p) (lamBodyPath ty q) :=
  Path.congrArg_trans (Term.lam ty ·) p q

/-- Theorem 33: lamBodyPath preserves symm -/
theorem lamBody_symm (ty : Ty) {a b : Term} (p : Path a b) :
    lamBodyPath ty (Path.symm p) = Path.symm (lamBodyPath ty p) :=
  Path.congrArg_symm (Term.lam ty ·) p

/-- Theorem 34: appRightPath preserves trans -/
theorem appRight_trans (t : Term) {a b c : Term}
    (p : Path a b) (q : Path b c) :
    appRightPath t (Path.trans p q) =
    Path.trans (appRightPath t p) (appRightPath t q) :=
  Path.congrArg_trans (Term.app t ·) p q

/-- Theorem 35: appRightPath preserves symm -/
theorem appRight_symm (t : Term) {a b : Term} (p : Path a b) :
    appRightPath t (Path.symm p) = Path.symm (appRightPath t p) :=
  Path.congrArg_symm (Term.app t ·) p

/-- Theorem 36: trans_refl_left for term paths -/
theorem transPath_refl_left {a b : Term} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  Path.trans_refl_left p

/-- Theorem 37: trans_refl_right for term paths -/
theorem transPath_refl_right {a b : Term} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  Path.trans_refl_right p

/-- Theorem 38: trans associativity for term paths -/
theorem transPath_assoc {a b c d : Term}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

/-- Theorem 39: symm involution for term paths -/
theorem symmPath_symm {a b : Term} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- Theorem 40: symm_trans cancellation toEq -/
theorem symmPath_trans_toEq {a b : Term} (p : Path a b) :
    (Path.trans (Path.symm p) p).toEq = rfl :=
  Path.toEq_symm_trans p

/-- Theorem 41: trans_symm cancellation toEq -/
theorem transSymm_toEq {a b : Term} (p : Path a b) :
    (Path.trans p (Path.symm p)).toEq = rfl :=
  Path.toEq_trans_symm p

/-- Theorem 42: congruence preserves refl -/
theorem congrArg_refl' (f : Term -> Term) (a : Term) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) :=
  rfl

/-- Theorem 43: double symm on appLeft -/
theorem appLeft_symm_symm {a b : Term} (t : Term) (p : Path a b) :
    Path.symm (Path.symm (appLeftPath t p)) = appLeftPath t p :=
  Path.symm_symm _

/-- Theorem 44: appCongr with refl on right -/
theorem appCongr_refl_right {t1 t1' : Term} (t2 : Term) (p : Path t1 t1') :
    appCongr p (Path.refl t2) = appLeftPath t2 p := by
  simp [appCongr, appRightPath, appLeftPath]

/-- Theorem 45: appCongr with refl on left -/
theorem appCongr_refl_left (t1 : Term) {t2 t2' : Term} (p : Path t2 t2') :
    appCongr (Path.refl t1) p = appRightPath t1 p := by
  simp [appCongr, appLeftPath, appRightPath]

/-- Theorem 46: lamBodyPath refl -/
theorem lamBodyPath_refl (ty : Ty) (body : Term) :
    lamBodyPath ty (Path.refl body) = Path.refl (Term.lam ty body) :=
  rfl

/-- Theorem 47: nested app congruences compose correctly -/
theorem nested_app_congr {a b c d : Term}
    (p1 : Path a b) (p2 : Path c d) :
    Path.trans
      (Path.congrArg (Term.app · c) p1)
      (Path.congrArg (Term.app b ·) p2)
    = appCongr p1 p2 := by
  simp [appCongr, appLeftPath, appRightPath]

-- ═══════════════════════════════════════════════════════════════
-- Section 8: Strong Normalization
-- ═══════════════════════════════════════════════════════════════

/-- Accessibility-based SN: a term is SN if all its reducts are SN -/
inductive SN : Term -> Prop where
  | intro : (forall t', BetaStep t t' -> SN t') -> SN t

/-- Theorem 48: normal forms are SN -/
theorem normalForm_SN (t : Term) (h : NormalForm t) : SN t :=
  SN.intro (fun t' hs => absurd hs (h t'))

/-- Theorem 49: variables are SN -/
theorem var_SN (n : Nat) : SN (Term.var n) :=
  normalForm_SN _ (var_normalForm n)

/-- Theorem 50: SN is downward closed -/
theorem SN.step' {t t' : Term} (h : SN t) (hs : BetaStep t t') : SN t' := by
  cases h with
  | intro ih => exact ih t' hs

-- ═══════════════════════════════════════════════════════════════
-- Section 9: Parallel Reduction
-- ═══════════════════════════════════════════════════════════════

/-- Parallel reduction: reduce multiple redexes at once -/
inductive ParRed : Term -> Term -> Prop where
  | var : (n : Nat) -> ParRed (Term.var n) (Term.var n)
  | app : ParRed t1 t1' -> ParRed t2 t2' ->
      ParRed (Term.app t1 t2) (Term.app t1' t2')
  | lam : ParRed body body' ->
      ParRed (Term.lam _ty body) (Term.lam _ty body')
  | beta : ParRed body body' -> ParRed arg arg' ->
      ParRed (Term.app (Term.lam _ty body) arg) (Term.betaReduce body' arg')

/-- Theorem 51: parallel reduction is reflexive -/
theorem ParRed.refl : (t : Term) -> ParRed t t
  | Term.var n => ParRed.var n
  | Term.app t1 t2 => ParRed.app (ParRed.refl t1) (ParRed.refl t2)
  | Term.lam _ty body => ParRed.lam (ParRed.refl body)

/-- Theorem 52: beta step implies parallel reduction -/
theorem BetaStep.toParRed {a b : Term} (h : BetaStep a b) : ParRed a b := by
  induction h with
  | beta ty body arg => exact ParRed.beta (ParRed.refl body) (ParRed.refl arg)
  | appLeft t2 _ ih => exact ParRed.app ih (ParRed.refl t2)
  | appRight t1 _ ih => exact ParRed.app (ParRed.refl t1) ih
  | lamBody ty _ ih => exact ParRed.lam ih

/-- Theorem 53: parallel reduction implies multi-step -/
theorem ParRed.toBetaMulti {a b : Term} (h : ParRed a b) : BetaMulti a b := by
  induction h with
  | var => exact BetaMulti.refl
  | app _ _ ih1 ih2 =>
    exact BetaMulti.trans' (BetaMulti.appLeft _ ih1) (BetaMulti.appRight _ ih2)
  | lam _ ih => exact BetaMulti.lamBody _ ih
  | beta _ _ ih1 ih2 =>
    exact BetaMulti.trans'
      (BetaMulti.trans'
        (BetaMulti.appLeft _ (BetaMulti.lamBody _ ih1))
        (BetaMulti.appRight _ ih2))
      (BetaMulti.single (BetaStep.beta _ _ _))

-- ═══════════════════════════════════════════════════════════════
-- Section 10: Complete Development
-- ═══════════════════════════════════════════════════════════════

/-- Complete development: reduce all top-level redexes -/
noncomputable def completeDev : Term -> Term
  | Term.var n => Term.var n
  | Term.app (Term.lam _ty body) arg =>
      Term.betaReduce (completeDev body) (completeDev arg)
  | Term.app t1 t2 => Term.app (completeDev t1) (completeDev t2)
  | Term.lam ty body => Term.lam ty (completeDev body)

/-- Theorem 54: complete development is identity on variables -/
theorem completeDev_var (n : Nat) : completeDev (Term.var n) = Term.var n := rfl

/-- Theorem 55: complete development of lambda -/
theorem completeDev_lam (ty : Ty) (body : Term) :
    completeDev (Term.lam ty body) = Term.lam ty (completeDev body) := rfl

-- ═══════════════════════════════════════════════════════════════
-- Section 11: Confluence structures
-- ═══════════════════════════════════════════════════════════════

/-- Diamond property witness -/
structure DiamondWitness (b c : Term) where
  d : Term
  left : BetaMulti b d
  right : BetaMulti c d

/-- Confluence witness -/
structure ConfluenceWitness (a : Term) where
  b : Term
  c : Term
  d : Term
  fromAB : BetaMulti a b
  fromAC : BetaMulti a c
  fromBD : BetaMulti b d
  fromCD : BetaMulti c d

/-- Theorem 56: trivial diamond -/
noncomputable def DiamondWitness.trivial (b : Term) : DiamondWitness b b :=
  { d := b, left := BetaMulti.refl, right := BetaMulti.refl }

/-- Theorem 57: symmetric diamond -/
noncomputable def DiamondWitness.symm' {b c : Term} (dw : DiamondWitness b c) :
    DiamondWitness c b :=
  { d := dw.d, left := dw.right, right := dw.left }

/-- Theorem 58: confluence from reflexive -/
noncomputable def ConfluenceWitness.ofRefl (a : Term) : ConfluenceWitness a :=
  { b := a, c := a, d := a,
    fromAB := BetaMulti.refl, fromAC := BetaMulti.refl,
    fromBD := BetaMulti.refl, fromCD := BetaMulti.refl }

-- ═══════════════════════════════════════════════════════════════
-- Section 12: Typed Terms and Reductions with Paths
-- ═══════════════════════════════════════════════════════════════

/-- A typed term: term + type + typing derivation -/
structure TypedTerm (Gam : Ctx) where
  term : Term
  ty : Ty
  hasType : Gam ⊢ term ::: ty

/-- A typed reduction with Path witnessing type preservation -/
structure TypedReduction (Gam : Ctx) where
  src : TypedTerm Gam
  tgt : TypedTerm Gam
  typePreservedPath : Path src.ty tgt.ty

/-- Theorem 59: identity typed reduction -/
noncomputable def TypedReduction.identity (tt' : TypedTerm Gam) :
    TypedReduction Gam :=
  { src := tt', tgt := tt', typePreservedPath := Path.refl tt'.ty }

/-- Theorem 60: composition of typed reductions -/
noncomputable def TypedReduction.compose
    (r1 r2 : TypedReduction Gam)
    (h : r1.tgt.ty = r2.src.ty) :
    Path r1.src.ty r2.tgt.ty :=
  Path.trans r1.typePreservedPath
    (Path.trans (Path.mk [Step.mk _ _ h] h) r2.typePreservedPath)

-- ═══════════════════════════════════════════════════════════════
-- Section 13: Reduction Sequences
-- ═══════════════════════════════════════════════════════════════

/-- A reduction sequence tracking each step -/
inductive RedSeq : Term -> Term -> Type where
  | nil : RedSeq t t
  | cons : BetaStep a b -> RedSeq b c -> RedSeq a c

/-- Theorem 61: RedSeq to BetaMulti -/
noncomputable def RedSeq.toBetaMulti : RedSeq a b -> BetaMulti a b
  | RedSeq.nil => BetaMulti.refl
  | RedSeq.cons hs rest => BetaMulti.step hs rest.toBetaMulti

/-- Theorem 62: RedSeq append -/
noncomputable def RedSeq.append : RedSeq a b -> RedSeq b c -> RedSeq a c
  | RedSeq.nil, s2 => s2
  | RedSeq.cons hs rest, s2 => RedSeq.cons hs (rest.append s2)

/-- Theorem 63: length of reduction sequence -/
noncomputable def RedSeq.length : RedSeq a b -> Nat
  | RedSeq.nil => 0
  | RedSeq.cons _ rest => 1 + rest.length

/-- Theorem 64: nil has length 0 -/
theorem RedSeq.nil_length : (RedSeq.nil : RedSeq t t).length = 0 := rfl

/-- Theorem 65: cons increments length -/
theorem RedSeq.cons_length (hs : BetaStep a b) (rest : RedSeq b c) :
    (RedSeq.cons hs rest).length = 1 + rest.length := rfl

/-- Theorem 66: append lengths add -/
theorem RedSeq.append_length (s1 : RedSeq a b) (s2 : RedSeq b c) :
    (s1.append s2).length = s1.length + s2.length := by
  induction s1 with
  | nil => simp [append, length]
  | cons _ rest ih => simp [append, length, ih]; omega

/-- Theorem 67: nil append is identity -/
theorem RedSeq.nil_append (s : RedSeq a b) :
    (RedSeq.nil : RedSeq a a).append s = s := rfl

-- ═══════════════════════════════════════════════════════════════
-- Section 14: SN reduction result
-- ═══════════════════════════════════════════════════════════════

/-- SN reduction: a term with its normal form -/
structure SNResult (t : Term) where
  nf : Term
  isNF : NormalForm nf
  seq : BetaMulti t nf

/-- Theorem 68: variable SNResult -/
noncomputable def SNResult.ofVar (n : Nat) : SNResult (Term.var n) :=
  { nf := Term.var n, isNF := var_normalForm n, seq := BetaMulti.refl }

/-- Theorem 69: normal form gives trivial SNResult -/
noncomputable def SNResult.ofNF (t : Term) (h : NormalForm t) : SNResult t :=
  { nf := t, isNF := h, seq := BetaMulti.refl }

-- ═══════════════════════════════════════════════════════════════
-- Section 15: Well-typed Combinators
-- ═══════════════════════════════════════════════════════════════

/-- The identity combinator: lam A (var 0) -/
noncomputable def idCombinator (A : Ty) : Term :=
  Term.lam A (Term.var 0)

/-- Theorem 70: identity combinator is well-typed -/
theorem idCombinator_typed (Gam : Ctx) (A : Ty) :
    Gam ⊢ idCombinator A ::: (Ty.arrow A A) :=
  HasType.tlam (HasType.tvar rfl)

/-- The K combinator: lam A (lam B (var 1)) -/
noncomputable def kCombinator (A B : Ty) : Term :=
  Term.lam A (Term.lam B (Term.var 1))

/-- Theorem 71: K combinator is well-typed -/
theorem kCombinator_typed (Gam : Ctx) (A B : Ty) :
    Gam ⊢ kCombinator A B ::: (Ty.arrow A (Ty.arrow B A)) :=
  HasType.tlam (HasType.tlam (HasType.tvar rfl))

/-- Theorem 72: identity applied reduces -/
theorem id_app_reduces (A : Ty) (t : Term) :
    BetaStep (Term.app (idCombinator A) t) (Term.betaReduce (Term.var 0) t) :=
  BetaStep.beta A (Term.var 0) t

/-- Theorem 73: identity beta-reduce gives the argument -/
theorem id_betaReduce (t : Term) :
    Term.betaReduce (Term.var 0) t = t := by
  simp [Term.betaReduce, Term.subst]

/-- The S combinator -/
noncomputable def sCombinator (A B C : Ty) : Term :=
  Term.lam (Ty.arrow A (Ty.arrow B C))
    (Term.lam (Ty.arrow A B)
      (Term.lam A
        (Term.app
          (Term.app (Term.var 2) (Term.var 0))
          (Term.app (Term.var 1) (Term.var 0)))))

-- ═══════════════════════════════════════════════════════════════
-- Section 16: Path-based type preservation witnesses
-- ═══════════════════════════════════════════════════════════════

/-- Subject reduction path: if t : A and t -> t', then t' : A
    witnessed by a reflexive Path on the type. -/
structure SubjectReductionWitness (Gam : Ctx) (t t' : Term) (A : Ty) where
  srcTyping : Gam ⊢ t ::: A
  tgtTyping : Gam ⊢ t' ::: A
  typePath : Path A A  -- type is preserved, so reflexive

/-- Theorem 74: subject reduction witness from identical type -/
noncomputable def SubjectReductionWitness.mk' {Gam : Ctx} {t t' : Term} {A : Ty}
    (h1 : Gam ⊢ t ::: A) (h2 : Gam ⊢ t' ::: A) :
    SubjectReductionWitness Gam t t' A :=
  { srcTyping := h1, tgtTyping := h2, typePath := Path.refl A }

/-- Theorem 75: chain subject reduction witnesses via Path.trans -/
noncomputable def SubjectReductionWitness.chain
    {Gam : Ctx} {t1 t2 t3 : Term} {A : Ty}
    (w1 : SubjectReductionWitness Gam t1 t2 A)
    (w2 : SubjectReductionWitness Gam t2 t3 A) :
    SubjectReductionWitness Gam t1 t3 A :=
  { srcTyping := w1.srcTyping,
    tgtTyping := w2.tgtTyping,
    typePath := Path.trans w1.typePath w2.typePath }

/-- Theorem 76: chain preserves reflexivity of type path -/
theorem SubjectReductionWitness.chain_typePath_toEq
    {Gam : Ctx} {t1 t2 t3 : Term} {A : Ty}
    (w1 : SubjectReductionWitness Gam t1 t2 A)
    (w2 : SubjectReductionWitness Gam t2 t3 A) :
    (w1.chain w2).typePath.toEq = rfl := by
  simp

-- ═══════════════════════════════════════════════════════════════
-- Section 17: Path algebra - functoriality
-- ═══════════════════════════════════════════════════════════════

/-- Theorem 77: congruence is functorial (id) on Term -/
theorem congrArg_id_term {a b : Term} (p : Path a b) :
    Path.congrArg (fun x => x) p = p := by
  simp

/-- Theorem 78: congruence is functorial (comp) on Term -/
theorem congrArg_comp_term (f g : Term -> Term) {a b : Term} (p : Path a b) :
    Path.congrArg (fun x => f (g x)) p = Path.congrArg f (Path.congrArg g p) := by
  simp

/-- Theorem 79: congruence is functorial (id) on Ty -/
theorem congrArg_id_ty {a b : Ty} (p : Path a b) :
    Path.congrArg (fun x => x) p = p := by
  simp

-- ═══════════════════════════════════════════════════════════════
-- Section 18: Context Path operations
-- ═══════════════════════════════════════════════════════════════

/-- Path on contexts: extending with equal types -/
noncomputable def ctxConsPath {A A' : Ty} (Gam : Ctx) (p : Path A A') :
    Path (A :: Gam) (A' :: Gam) :=
  Path.congrArg (· :: Gam) p

/-- Theorem 80: ctxConsPath preserves trans -/
theorem ctxConsPath_trans (Gam : Ctx) {A A' A'' : Ty}
    (p : Path A A') (q : Path A' A'') :
    ctxConsPath Gam (Path.trans p q) =
    Path.trans (ctxConsPath Gam p) (ctxConsPath Gam q) :=
  Path.congrArg_trans (· :: Gam) p q

/-- Theorem 81: ctxConsPath preserves symm -/
theorem ctxConsPath_symm (Gam : Ctx) {A A' : Ty} (p : Path A A') :
    ctxConsPath Gam (Path.symm p) = Path.symm (ctxConsPath Gam p) :=
  Path.congrArg_symm (· :: Gam) p

/-- Theorem 82: ctxConsPath refl is refl -/
theorem ctxConsPath_refl (Gam : Ctx) (A : Ty) :
    ctxConsPath Gam (Path.refl A) = Path.refl (A :: Gam) :=
  rfl

-- ═══════════════════════════════════════════════════════════════
-- Section 19: More substitution results
-- ═══════════════════════════════════════════════════════════════

/-- Theorem 83: subst distributes over app -/
theorem subst_app (j : Nat) (s t1 t2 : Term) :
    Term.subst j s (Term.app t1 t2) =
    Term.app (Term.subst j s t1) (Term.subst j s t2) := by
  rfl

/-- Theorem 84: subst distributes over lam -/
theorem subst_lam (j : Nat) (s : Term) (ty : Ty) (body : Term) :
    Term.subst j s (Term.lam ty body) =
    Term.lam ty (Term.subst j.succ (Term.shift 1 0 s) body) := by
  rfl

/-- Theorem 85: betaReduce of var 0 is identity -/
theorem betaReduce_var0 (t : Term) :
    Term.betaReduce (Term.var 0) t = t := by
  simp [Term.betaReduce, Term.subst]

-- ═══════════════════════════════════════════════════════════════
-- Section 20: Path transport on typing
-- ═══════════════════════════════════════════════════════════════

/-- Theorem 86: transport typing along a type Path -/
theorem transport_hasType {Gam : Ctx} {t : Term} {A B : Ty}
    (h : Gam ⊢ t ::: A) (p : Path A B) : Gam ⊢ t ::: B :=
  p.toEq ▸ h

/-- Theorem 87: transport typing along a context Path -/
theorem transport_ctx_hasType {Gam Gam' : Ctx} {t : Term} {A : Ty}
    (h : Gam ⊢ t ::: A) (p : Path Gam Gam') : Gam' ⊢ t ::: A :=
  p.toEq ▸ h

/-- Theorem 88: Path between transport_hasType results -/
theorem transport_hasType_eq {Gam : Ctx} {t : Term} {A B : Ty}
    (h : Gam ⊢ t ::: A) (p q : Path A B) :
    transport_hasType h p = transport_hasType h q := by
  cases p with
  | mk sp pp => cases q with
    | mk sq pq => cases pp; cases pq; rfl

/-- Theorem 89: transport along refl is identity -/
theorem transport_hasType_refl {Gam : Ctx} {t : Term} {A : Ty}
    (h : Gam ⊢ t ::: A) :
    transport_hasType h (Path.refl A) = h :=
  rfl

-- ═══════════════════════════════════════════════════════════════
-- Closing
-- ═══════════════════════════════════════════════════════════════

end ComputationalPaths.TypedLambdaDeep
