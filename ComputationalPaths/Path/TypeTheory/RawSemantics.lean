/-
# Computational-path term semantics for raw MLTT

This module interprets the raw calculus in a deliberately small, fully
constructed semantic model.  At each scope `n`, the carrier is the quotient of
`Expr n` by the *source* definitional equality `DefEq`.  Thus source beta rules
become equalities of semantic values, and those equalities are retained as
trace-carrying `Path`s.  This is the standard syntactic (term) model; it is
independent of the pre-existing intrinsically typed Lean CwF and makes no
initiality, normalization, or decidable-type-checking claim.

The interpretation under an environment is the quotient-level map induced by
simultaneous substitution.  `DefEq.substitution` and `DefEq.subst_congr` prove
well-definedness in both term and environment representatives; identity and
composition hold on arbitrary quotient values.  Semantic typing is the
quotient saturation of a raw derivation, is itself substitution-stable, and
typed computation uses genuinely derived subject reduction.  Endpoint
conservativity is exact on this specified model: a target `Path` between two
quoted raw terms reflects to source `DefEq` by quotient exactness.

The second half defines source identity programs and their rewrite calculus.
The source constructors mention only `DefEq`, raw one-hole frames, and other
source identity programs.  No constructor accepts `Path.Step`, `RwEq`, or an
arbitrary target equality.  Evaluation into `Path` is then proved sound in
`RwEq`, including units, cancellation, associativity, inverse, composition,
and congruence.
-/

import ComputationalPaths.Path.TypeTheory.RawJudgments

namespace ComputationalPaths
namespace Path
namespace TypeTheory
namespace RawMLTT

noncomputable section

/-! ## Quotient-level substitution on the source term model -/

/-- The quotient-level action induced by a simultaneous raw substitution.

Well-definedness is exactly `DefEq.substitution`: definitionally equal
representatives remain definitionally equal after substitution. -/
def modelSubst {n m : Nat} (sigma : Sub n m) :
    TermModel n -> TermModel m :=
  Quotient.lift
    (fun t => denote (subst sigma t))
    (fun _ _ h => Quotient.sound (DefEq.substitution h sigma))

@[simp] theorem modelSubst_denote {n m : Nat} (sigma : Sub n m)
    (t : Expr n) :
    modelSubst sigma (denote t) = denote (subst sigma t) :=
  rfl

/-- Identity substitution acts identically on the quotient carrier. -/
@[simp] theorem modelSubst_identity {n : Nat} (x : TermModel n) :
    modelSubst (Sub.id n) x = x := by
  refine Quotient.inductionOn x ?_
  intro t
  exact _root_.congrArg denote (subst_id t)

/-- Quotient-level substitution composition follows from the independently
proved raw substitution-composition theorem. -/
@[simp] theorem modelSubst_composition {n m k : Nat}
    (sigma : Sub n m) (tau : Sub m k) (x : TermModel n) :
    modelSubst tau (modelSubst sigma x) =
      modelSubst (Sub.comp sigma tau) x := by
  refine Quotient.inductionOn x ?_
  intro t
  exact _root_.congrArg denote (subst_comp sigma tau t)

/-- Trace-carrying quotient-level substitution composition. -/
def modelSubst_composition_path {n m k : Nat}
    (sigma : Sub n m) (tau : Sub m k) (x : TermModel n) :
    Path
      (modelSubst tau (modelSubst sigma x))
      (modelSubst (Sub.comp sigma tau) x) :=
  Path.stepChain (modelSubst_composition sigma tau x)

/-- Quotient substitution is also well defined in its environment: pointwise
source-definitionally-equal substitutions induce the same semantic map. -/
theorem modelSubst_congr {n m : Nat} {sigma tau : Sub n m}
    (h : DefEq.SubDefEq sigma tau) (x : TermModel n) :
    modelSubst sigma x = modelSubst tau x := by
  refine Quotient.inductionOn x ?_
  intro t
  exact Quotient.sound (DefEq.subst_congr h t)

/-- Interpret an expression under a simultaneous raw environment. -/
def interpret {n m : Nat} (rho : Sub n m) (t : Expr n) : TermModel m :=
  modelSubst rho (denote t)

/-- Interpret a raw context declaration by declaration. -/
def interpretCtx {n : Nat} (Gamma : Ctx n) : Fin n -> TermModel n :=
  fun i => denote (Gamma i)

@[simp] theorem interpret_var {n m : Nat} (rho : Sub n m) (i : Fin n) :
    interpret rho (.var i) = denote (rho i) := rfl

@[simp] theorem interpret_sort {n m : Nat} (rho : Sub n m) (level : Nat) :
    interpret rho (.sort level) = denote (.sort level : Expr m) := rfl

@[simp] theorem interpret_pi {n m : Nat} (rho : Sub n m)
    (A : Expr n) (B : Expr (n + 1)) :
    interpret rho (.pi A B) =
      denote (.pi (subst rho A) (subst (Sub.lift rho) B)) := rfl

@[simp] theorem interpret_sigma {n m : Nat} (rho : Sub n m)
    (A : Expr n) (B : Expr (n + 1)) :
    interpret rho (.sigma A B) =
      denote (.sigma (subst rho A) (subst (Sub.lift rho) B)) := rfl

@[simp] theorem interpret_lam {n m : Nat} (rho : Sub n m)
    (body : Expr (n + 1)) :
    interpret rho (.lam body) =
      denote (.lam (subst (Sub.lift rho) body)) := rfl

@[simp] theorem interpret_app {n m : Nat} (rho : Sub n m)
    (f a : Expr n) :
    interpret rho (.app f a) =
      denote (.app (subst rho f) (subst rho a)) := rfl

@[simp] theorem interpret_pair {n m : Nat} (rho : Sub n m)
    (a b : Expr n) :
    interpret rho (.pair a b) =
      denote (.pair (subst rho a) (subst rho b)) := rfl

@[simp] theorem interpret_natElim {n m : Nat} (rho : Sub n m)
    (natLevel : Nat) (motive : Expr (n + 1)) (zeroCase : Expr n)
    (succCase : Expr (n + 2)) (scrutinee : Expr n) :
    interpret rho
        (.natElim natLevel motive zeroCase succCase scrutinee) =
      denote
        (.natElim
          natLevel
          (subst (Sub.lift rho) motive)
          (subst rho zeroCase)
          (subst (Sub.lift (Sub.lift rho)) succCase)
          (subst rho scrutinee)) := rfl

@[simp] theorem interpret_codePi {n m : Nat} (rho : Sub n m)
    (A : Expr n) (B : Expr (n + 1)) :
    interpret rho (.codePi A B) =
      denote (.codePi (subst rho A) (subst (Sub.lift rho) B)) := rfl

@[simp] theorem interpret_codeSigma {n m : Nat} (rho : Sub n m)
    (A : Expr n) (B : Expr (n + 1)) :
    interpret rho (.codeSigma A B) =
      denote (.codeSigma (subst rho A) (subst (Sub.lift rho) B)) := rfl

@[simp] theorem interpret_id {n m : Nat} (rho : Sub n m)
    (A a b : Expr n) :
    interpret rho (.id A a b) =
      denote (.id (subst rho A) (subst rho a) (subst rho b)) := rfl

@[simp] theorem interpret_eqJ {n m : Nat} (rho : Sub n m)
    (motive : Expr (n + 2)) (reflCase endpoint proof : Expr n) :
    interpret rho (.eqJ motive reflCase endpoint proof) =
      denote
        (.eqJ
          (subst (Sub.lift (Sub.lift rho)) motive)
          (subst rho reflCase)
          (subst rho endpoint)
          (subst rho proof)) := rfl

/-- Interpretation strictly respects identity substitution. -/
@[simp] theorem interpret_identity {n : Nat} (t : Expr n) :
    interpret (Sub.id n) t = denote t := by
  exact _root_.congrArg denote (subst_id t)

/-- Interpretation strictly respects substitution composition. -/
@[simp] theorem interpret_substitution {n m k : Nat}
    (sigma : Sub n m) (tau : Sub m k) (t : Expr n) :
    interpret tau (subst sigma t) = interpret (Sub.comp sigma tau) t := by
  exact _root_.congrArg denote (subst_comp sigma tau t)

/-- Trace-carrying substitution compatibility.  The single visible trace entry
is the independently proved raw substitution-composition equation. -/
def interpret_substitution_path {n m k : Nat}
    (sigma : Sub n m) (tau : Sub m k) (t : Expr n) :
    Path (interpret tau (subst sigma t))
      (interpret (Sub.comp sigma tau) t) :=
  Path.stepChain (interpret_substitution sigma tau t)

/-! ## Typing and computation soundness -/

/-- Quotient-saturated term-model typing.

This is not a second copy of the raw rules.  A semantic judgment consists of a
typed raw representative together with equations identifying the requested
quotient values with that representative.  The equations make the relation
stable under source definitional equality. -/
structure SemHasType {n : Nat} (Gamma : Ctx n)
    (term type : TermModel n) where
  representativeTerm : Expr n
  representativeType : Expr n
  derivation : HasType Gamma representativeTerm representativeType
  termEquation : term = denote representativeTerm
  typeEquation : type = denote representativeType

/-- Every raw typing derivation has a quotient-saturated interpretation. -/
def typing_sound {n : Nat} {Gamma : Ctx n} {t A : Expr n}
    (d : HasType Gamma t A) :
    SemHasType Gamma (denote t) (denote A) :=
  { representativeTerm := t
    representativeType := A
    derivation := d
    termEquation := rfl
    typeEquation := rfl }

/-- Semantic typing is compositional under quotient-level substitution. -/
noncomputable def semantic_typing_substitution
    {n m : Nat} {Gamma : Ctx n} {Delta : Ctx m}
    {term type : TermModel n} {sigma : Sub n m}
    (d : SemHasType Gamma term type)
    (hSigma : CtxSub Delta Gamma sigma) :
    SemHasType Delta (modelSubst sigma term) (modelSubst sigma type) := by
  refine
    { representativeTerm := subst sigma d.representativeTerm
      representativeType := subst sigma d.representativeType
      derivation :=
        HasType.substitution_preserves d.derivation sigma hSigma
      termEquation := ?_
      typeEquation := ?_ }
  · exact (_root_.congrArg (modelSubst sigma) d.termEquation).trans
      (modelSubst_denote sigma d.representativeTerm)
  · exact (_root_.congrArg (modelSubst sigma) d.typeEquation).trans
      (modelSubst_denote sigma d.representativeType)

/-- Primitive source computation is sound as a trace-carrying path. -/
def computation_sound {n : Nat} {t u : Expr n} (h : Computation t u) :
    Path (denote t) (denote u) :=
  computationPath h

/-- Computation soundness is natural in every raw environment. -/
def computation_substitution_sound {n m : Nat} (sigma : Sub n m)
    {t u : Expr n} (h : Computation t u) :
    Path (interpret sigma t) (interpret sigma u) :=
  computation_sound (Computation.substitution sigma h)

/-- The raw identity eliminator computes only at source reflexivity.  Its motive
contains endpoint/proof variables from the source calculus, not target trace
metadata. -/
def eqJ_beta_path {n : Nat} (motive : Expr (n + 2))
    (reflCase a : Expr n) :
    Path
      (denote (.eqJ motive reflCase a (.refl a)))
      (denote reflCase) :=
  computation_sound (Computation.eqJBeta motive reflCase a)

/-- Semantic certificate for a typed source computation. -/
structure TypedComputationSemantics {n : Nat} {Gamma : Ctx n}
    {source target : Expr n} (d : TypedComputation Gamma source target) where
  subjectReduction : SubjectReduction d
  sourceTyping :
    SemHasType Gamma (denote source) (denote d.type)
  targetTyping :
    SemHasType Gamma (denote target) (denote d.type)
  computationPath : Path (denote source) (denote target)
  trailingUnit :
    RwEq
      (Path.trans computationPath (Path.refl (denote target)))
      computationPath

/-- Typing preservation and beta soundness, with target typing derived by the
raw subject-reduction theorem rather than supplied as a premise. -/
def typed_computation_sound {n : Nat} {Gamma : Ctx n}
    {source target : Expr n} (d : TypedComputation Gamma source target) :
    TypedComputationSemantics d := by
  let p := computation_sound d.computation
  let reduction := subject_reduction d
  exact
    { subjectReduction := reduction
      sourceTyping := typing_sound d.sourceTyping
      targetTyping :=
        { representativeTerm := target
          representativeType := reduction.targetType
          derivation := reduction.targetTyping
          termEquation := rfl
          typeEquation :=
            (Quotient.sound reduction.typeCoherence).symm }
      computationPath := p
      trailingUnit :=
        rweq_of_step (Path.Step.trans_refl_right p) }

/-- **Endpoint conservativity of the raw term model.**

A target computational path between quoted raw expressions exists exactly when
the source expressions are definitionally equal.  Reflection uses only the
underlying quotient equality and is therefore restricted, explicitly, to this
term-model carrier. -/
theorem term_model_endpoint_adequacy {n : Nat} (t u : Expr n) :
    Nonempty (Path (denote t) (denote u)) <-> DefEq t u := by
  constructor
  · rintro ⟨p⟩
    exact Quotient.exact p.toEq
  · intro h
    exact ⟨defEqPath h⟩

/-! ## Raw one-hole congruence frames -/

/-- Auditable same-scope one-hole frames used by source identity congruence.
Binder congruence remains available in `DefEq`; these frames are the term-level
contexts required by identity-program evaluation. -/
inductive Frame (n : Nat) : Type where
  | appFun (argument : Expr n)
  | appArg (function : Expr n)
  | pairFst (second : Expr n)
  | pairSnd (first : Expr n)
  | fst
  | snd
  | succ (natLevel : Nat)
  | el
  | refl
  | idType (left right : Expr n)
  | idLeft (type right : Expr n)
  | idRight (type left : Expr n)
  | codeIdType (left right : Expr n)
  | codeIdLeft (type right : Expr n)
  | codeIdRight (type left : Expr n)
  deriving Repr

namespace Frame

/-- Fill the hole of a source frame. -/
def plug {n : Nat} : Frame n -> Expr n -> Expr n
  | .appFun a, t => .app t a
  | .appArg f, t => .app f t
  | .pairFst b, t => .pair t b
  | .pairSnd a, t => .pair a t
  | .fst, t => .fst t
  | .snd, t => .snd t
  | .succ natLevel, t => .succ natLevel t
  | .el, t => .el t
  | .refl, t => .refl t
  | .idType a b, t => .id t a b
  | .idLeft A b, t => .id A t b
  | .idRight A a, t => .id A a t
  | .codeIdType a b, t => .codeId t a b
  | .codeIdLeft A b, t => .codeId A t b
  | .codeIdRight A a, t => .codeId A a t

/-- Every frame preserves source definitional equality. -/
def congrDefEq {n : Nat} (C : Frame n) {t u : Expr n}
    (h : DefEq t u) : DefEq (plug C t) (plug C u) := by
  cases C with
  | appFun a => exact DefEq.appFun h
  | appArg f => exact DefEq.appArg h
  | pairFst b => exact DefEq.pairFst h
  | pairSnd a => exact DefEq.pairSnd h
  | fst => exact DefEq.fstCongr h
  | snd => exact DefEq.sndCongr h
  | succ natLevel => exact DefEq.succCongr natLevel h
  | el => exact DefEq.elCongr h
  | refl => exact DefEq.reflCongr h
  | idType a b => exact DefEq.idType h
  | idLeft A b => exact DefEq.idLeft h
  | idRight A a => exact DefEq.idRight h
  | codeIdType a b => exact DefEq.codeIdType h
  | codeIdLeft A b => exact DefEq.codeIdLeft h
  | codeIdRight A a => exact DefEq.codeIdRight h

/-- A raw frame descends to a total operation on the term model. -/
def map {n : Nat} (C : Frame n) : TermModel n -> TermModel n :=
  Quotient.lift
    (fun t => denote (plug C t))
    (fun _ _ h => Quotient.sound (congrDefEq C h))

@[simp] theorem map_denote {n : Nat} (C : Frame n) (t : Expr n) :
    map C (denote t) = denote (plug C t) := rfl

end Frame

/-! ## Independent source identity programs -/

/-- Source identity programs between raw expressions.

`atom` receives a source `DefEq` derivation, never a target rewrite.  `congr`
uses the finite source-frame grammar above. -/
inductive IdentityExpr {n : Nat} : Expr n -> Expr n -> Type where
  | atom {t u : Expr n} : DefEq t u -> IdentityExpr t u
  | refl (t : Expr n) : IdentityExpr t t
  | symm {t u : Expr n} : IdentityExpr t u -> IdentityExpr u t
  | trans {t u v : Expr n} :
      IdentityExpr t u -> IdentityExpr u v -> IdentityExpr t v
  | congr (C : Frame n) {t u : Expr n} :
      IdentityExpr t u -> IdentityExpr (C.plug t) (C.plug u)

namespace IdentityExpr

/-- Evaluate a source identity program in the computational-path term model. -/
def eval {n : Nat} {t u : Expr n} : IdentityExpr t u ->
    Path (denote t) (denote u)
  | .atom h => defEqPath h
  | .refl t => Path.refl (denote t)
  | .symm p => Path.symm p.eval
  | .trans p q => Path.trans p.eval q.eval
  | .congr C p => Path.congrArg (Frame.map C) p.eval

@[simp] theorem eval_refl {n : Nat} (t : Expr n) :
    (IdentityExpr.refl t).eval = Path.refl (denote t) := rfl

@[simp] theorem eval_symm {n : Nat} {t u : Expr n}
    (p : IdentityExpr t u) :
    (IdentityExpr.symm p).eval = Path.symm p.eval := rfl

@[simp] theorem eval_trans {n : Nat} {t u v : Expr n}
    (p : IdentityExpr t u) (q : IdentityExpr u v) :
    (IdentityExpr.trans p q).eval = Path.trans p.eval q.eval := rfl

@[simp] theorem eval_congr {n : Nat} (C : Frame n) {t u : Expr n}
    (p : IdentityExpr t u) :
    (IdentityExpr.congr C p).eval =
      Path.congrArg (Frame.map C) p.eval := rfl

end IdentityExpr

/-! ## Source identity rewrites and soundness -/

/-- One-step source rewrites between identity programs.  Every constructor is a
named groupoid or congruence law of the source calculus. -/
inductive IdentityStep {n : Nat} :
    {t u : Expr n} -> IdentityExpr t u -> IdentityExpr t u -> Type where
  | symmRefl (t : Expr n) :
      IdentityStep (.symm (.refl t)) (.refl t)
  | symmSymm {t u : Expr n} (p : IdentityExpr t u) :
      IdentityStep (.symm (.symm p)) p
  | transReflLeft {t u : Expr n} (p : IdentityExpr t u) :
      IdentityStep (.trans (.refl t) p) p
  | transReflRight {t u : Expr n} (p : IdentityExpr t u) :
      IdentityStep (.trans p (.refl u)) p
  | transSymm {t u : Expr n} (p : IdentityExpr t u) :
      IdentityStep (.trans p (.symm p)) (.refl t)
  | symmTrans {t u : Expr n} (p : IdentityExpr t u) :
      IdentityStep (.trans (.symm p) p) (.refl u)
  | inverseComposition {t u v : Expr n}
      (p : IdentityExpr t u) (q : IdentityExpr u v) :
      IdentityStep
        (.symm (.trans p q))
        (.trans (.symm q) (.symm p))
  | transAssoc {t u v w : Expr n}
      (p : IdentityExpr t u) (q : IdentityExpr u v)
      (r : IdentityExpr v w) :
      IdentityStep (.trans (.trans p q) r) (.trans p (.trans q r))
  | symmCongr {t u : Expr n} {p q : IdentityExpr t u} :
      IdentityStep p q ->
      IdentityStep (.symm p) (.symm q)
  | transCongrLeft {t u v : Expr n} {p q : IdentityExpr t u}
      (r : IdentityExpr u v) :
      IdentityStep p q ->
      IdentityStep (.trans p r) (.trans q r)
  | transCongrRight {t u v : Expr n} (p : IdentityExpr t u)
      {q r : IdentityExpr u v} :
      IdentityStep q r ->
      IdentityStep (.trans p q) (.trans p r)
  | frameCongr {t u : Expr n} (C : Frame n)
      {p q : IdentityExpr t u} :
      IdentityStep p q ->
      IdentityStep (.congr C p) (.congr C q)
  | frameRefl (C : Frame n) (t : Expr n) :
      IdentityStep
        (.congr C (.refl t))
        (.refl (C.plug t))

/-- Symmetric reflexive-transitive closure of source identity steps. -/
inductive IdentityRwEq {n : Nat} {t u : Expr n} :
    IdentityExpr t u -> IdentityExpr t u -> Type where
  | refl (p : IdentityExpr t u) : IdentityRwEq p p
  | step {p q : IdentityExpr t u} :
      IdentityStep p q -> IdentityRwEq p q
  | symm {p q : IdentityExpr t u} :
      IdentityRwEq p q -> IdentityRwEq q p
  | trans {p q r : IdentityExpr t u} :
      IdentityRwEq p q -> IdentityRwEq q r -> IdentityRwEq p r

/-- Every named source identity step is sound in target `RwEq`.  The induction
is the only point where target rewrite constructors are selected; none are
available to the source syntax. -/
def identityStep_sound {n : Nat} {t u : Expr n}
    {p q : IdentityExpr t u} (h : IdentityStep p q) :
    RwEq p.eval q.eval := by
  induction h with
  | symmRefl t =>
      exact rweq_of_step (Path.Step.symm_refl (denote t))
  | symmSymm p =>
      exact rweq_of_step (Path.Step.symm_symm p.eval)
  | transReflLeft p =>
      exact rweq_of_step (Path.Step.trans_refl_left p.eval)
  | transReflRight p =>
      exact rweq_of_step (Path.Step.trans_refl_right p.eval)
  | transSymm p =>
      exact rweq_of_step (Path.Step.trans_symm p.eval)
  | symmTrans p =>
      exact rweq_of_step (Path.Step.symm_trans p.eval)
  | inverseComposition p q =>
      exact rweq_of_step (Path.Step.symm_trans_congr p.eval q.eval)
  | transAssoc p q r =>
      exact rweq_of_step (Path.Step.trans_assoc p.eval q.eval r.eval)
  | symmCongr _ ih =>
      exact rweq_symm_congr ih
  | transCongrLeft r _ ih =>
      exact rweq_trans_congr_left r.eval ih
  | transCongrRight p _ ih =>
      exact rweq_trans_congr_right p.eval ih
  | frameCongr C _ ih =>
      exact rweq_congrArg_of_rweq (Frame.map C) ih
  | frameRefl C t =>
      exact rweq_congrArg_refl (Frame.map C) (denote t)

/-- Source identity rewrite equivalence is sound in computational-path rewrite
equivalence. -/
def identity_rweq_sound {n : Nat} {t u : Expr n}
    {p q : IdentityExpr t u} (h : IdentityRwEq p q) :
    RwEq p.eval q.eval := by
  induction h with
  | refl p => exact rweq_refl p.eval
  | step h => exact identityStep_sound h
  | symm _ ih => exact rweq_symm ih
  | trans _ _ ih₁ ih₂ => exact rweq_trans ih₁ ih₂

/-- A two-step source coherence derivation exercising associativity and a right
unit. -/
def reassociate_and_remove_unit {n : Nat} {t u v : Expr n}
    (p : IdentityExpr t u) (q : IdentityExpr u v) :
    IdentityRwEq
      (.trans (.trans p q) (.refl v))
      (.trans p q) :=
  IdentityRwEq.trans
    (IdentityRwEq.step
      (IdentityStep.transAssoc p q (.refl v)))
    (IdentityRwEq.step
      (IdentityStep.transCongrRight p
        (IdentityStep.transReflRight q)))

/-- The preceding genuinely multi-step source derivation evaluates to a
multi-rule `RwEq` certificate. -/
def reassociate_and_remove_unit_sound {n : Nat} {t u v : Expr n}
    (p : IdentityExpr t u) (q : IdentityExpr u v) :
    RwEq
      (Path.trans (Path.trans p.eval q.eval) (Path.refl (denote v)))
      (Path.trans p.eval q.eval) :=
  identity_rweq_sound (reassociate_and_remove_unit p q)

/-! ## Packaged raw adequacy result -/

/-- Machine-checked statement of the exact raw result established here. -/
structure RawAdequacyCertificate where
  definitionalEqualitySubstitution :
    forall {n m : Nat} {t u : Expr n},
      DefEq t u -> (sigma : Sub n m) ->
        DefEq (subst sigma t) (subst sigma u)
  quotientSubstitutionIdentity :
    forall {n : Nat} (x : TermModel n),
      modelSubst (Sub.id n) x = x
  quotientSubstitutionComposition :
    forall {n m k : Nat} (sigma : Sub n m) (tau : Sub m k)
      (x : TermModel n),
      modelSubst tau (modelSubst sigma x) =
        modelSubst (Sub.comp sigma tau) x
  quotientSubstitutionPath :
    forall {n m k : Nat} (sigma : Sub n m) (tau : Sub m k)
      (x : TermModel n),
      Path
        (modelSubst tau (modelSubst sigma x))
        (modelSubst (Sub.comp sigma tau) x)
  quotientSubstitutionEnvironment :
    forall {n m : Nat} {sigma tau : Sub n m},
      DefEq.SubDefEq sigma tau ->
      forall x : TermModel n, modelSubst sigma x = modelSubst tau x
  substitution :
    forall {n m k : Nat} (sigma : Sub n m) (tau : Sub m k)
      (t : Expr n),
      Path (interpret tau (subst sigma t))
        (interpret (Sub.comp sigma tau) t)
  typing :
    forall {n : Nat} {Gamma : Ctx n} {t A : Expr n},
      HasType Gamma t A ->
      SemHasType Gamma (denote t) (denote A)
  typingSubstitution :
    forall {n m : Nat} {Gamma : Ctx n} {Delta : Ctx m}
      {term type : TermModel n} {sigma : Sub n m},
      SemHasType Gamma term type ->
      CtxSub Delta Gamma sigma ->
      SemHasType Delta (modelSubst sigma term) (modelSubst sigma type)
  computation :
    forall {n : Nat} {t u : Expr n},
      Computation t u -> Path (denote t) (denote u)
  computationSubstitution :
    forall {n m : Nat} (sigma : Sub n m) {t u : Expr n},
      Computation t u ->
      Path (interpret sigma t) (interpret sigma u)
  typedComputation :
    forall {n : Nat} {Gamma : Ctx n} {t u : Expr n}
      (d : TypedComputation Gamma t u),
      TypedComputationSemantics d
  computationCertificate :
    forall {n : Nat} {Gamma : Ctx n} {t u : Expr n}
      (d : TypedComputation Gamma t u),
      ComputationPathCertificate d
  liftedNatSubjectReduction :
    forall {n : Nat} (Gamma : Ctx n) (level : Nat),
      SubjectReduction (liftedNatDecodeComputation Gamma level)
  identityRewrite :
    forall {n : Nat} {t u : Expr n}
      {p q : IdentityExpr t u},
      IdentityRwEq p q -> RwEq p.eval q.eval
  endpointConservativity :
    forall {n : Nat} (t u : Expr n),
      Nonempty (Path (denote t) (denote u)) <-> DefEq t u

/-- **Raw bounded MLTT computational-path adequacy.**

The theorem validates scoped substitution, raw typing, source beta computation,
and the independent identity rewrite calculus in the computational-path term
model.  Its reflection field is deliberately restricted to quoted raw terms in
that model. -/
def raw_computational_path_adequacy : RawAdequacyCertificate where
  definitionalEqualitySubstitution := fun h sigma =>
    DefEq.substitution h sigma
  quotientSubstitutionIdentity := modelSubst_identity
  quotientSubstitutionComposition := modelSubst_composition
  quotientSubstitutionPath := modelSubst_composition_path
  quotientSubstitutionEnvironment := fun h x => modelSubst_congr h x
  substitution := interpret_substitution_path
  typing := typing_sound
  typingSubstitution := semantic_typing_substitution
  computation := computation_sound
  computationSubstitution := computation_substitution_sound
  typedComputation := typed_computation_sound
  computationCertificate := computationPathCertificate
  liftedNatSubjectReduction := liftedNatDecode_subject_reduction
  identityRewrite := identity_rweq_sound
  endpointConservativity := term_model_endpoint_adequacy

end

end RawMLTT
end TypeTheory
end Path
end ComputationalPaths
