/-
# Contextual and multi-step reduction for the raw scoped calculus

`RawJudgments` supplies `Computation`, the ten *top-level* primitive redexes,
and derives subject reduction for each of them.  That leaves two structural
questions open: reduction inside a term, and iterated reduction.  This module
answers both.

`Reduction` is the congruence closure of `Computation`, enumerated by raw
constructor exactly as `DefEq` is, so the supported closure stays auditable.
`ReductionMany` is its reflexive-transitive closure.  Both are sound for source
definitional equality and stable under simultaneous substitution, and both
descend to the syntactic quotient.

Contextual subject reduction is *not* available in the raw calculus, and the
reason is precise rather than incidental: rebuilding an elimination around a
reduced subterm requires retyping that subterm at a definitionally equal type,
which is exactly the conversion rule `RawJudgments` deliberately omits.  Rather
than leave this as a gap, we isolate it.  `ConversionRules` bundles the two
structural rules the raw system does not have -- conversion and context
conversion -- as an explicit hypothesis record, never an axiom.  Given that
record, contextual and multi-step subject reduction follow for the full
congruence closure.  The theorems below therefore measure the exact distance
between the raw calculus and a conversion-closed one.
-/

import ComputationalPaths.Path.TypeTheory.RawJudgments

namespace ComputationalPaths
namespace Path
namespace TypeTheory
namespace RawMLTT

/-! ## Contextual one-step reduction -/

/-- Contextual one-step reduction: the congruence closure of the primitive
redexes.  Constructors mirror `DefEq` one for one, minus symmetry, transitivity
and reflexivity, so the closure remains directed and auditable. -/
inductive Reduction : {n : Nat} → Expr n → Expr n → Type where
  | head {n : Nat} {t u : Expr n} : Computation t u → Reduction t u
  | piDom {n : Nat} {A A' : Expr n} (B : Expr (n + 1)) :
      Reduction A A' → Reduction (.pi A B) (.pi A' B)
  | piCod {n : Nat} (A : Expr n) {B B' : Expr (n + 1)} :
      Reduction B B' → Reduction (.pi A B) (.pi A B')
  | sigmaDom {n : Nat} {A A' : Expr n} (B : Expr (n + 1)) :
      Reduction A A' → Reduction (.sigma A B) (.sigma A' B)
  | sigmaCod {n : Nat} (A : Expr n) {B B' : Expr (n + 1)} :
      Reduction B B' → Reduction (.sigma A B) (.sigma A B')
  | lamBody {n : Nat} {body body' : Expr (n + 1)} :
      Reduction body body' → Reduction (.lam body) (.lam body')
  | appFun {n : Nat} {f f' a : Expr n} :
      Reduction f f' → Reduction (.app f a) (.app f' a)
  | appArg {n : Nat} {f a a' : Expr n} :
      Reduction a a' → Reduction (.app f a) (.app f a')
  | pairFst {n : Nat} {a a' b : Expr n} :
      Reduction a a' → Reduction (.pair a b) (.pair a' b)
  | pairSnd {n : Nat} {a b b' : Expr n} :
      Reduction b b' → Reduction (.pair a b) (.pair a b')
  | fstCongr {n : Nat} {p p' : Expr n} :
      Reduction p p' → Reduction (.fst p) (.fst p')
  | sndCongr {n : Nat} {p p' : Expr n} :
      Reduction p p' → Reduction (.snd p) (.snd p')
  | succCongr {n : Nat} (natLevel : Nat) {t t' : Expr n} :
      Reduction t t' → Reduction (.succ natLevel t) (.succ natLevel t')
  | natMotive {n : Nat} (natLevel : Nat) {M M' : Expr (n + 1)}
      (z : Expr n) (s : Expr (n + 2)) (t : Expr n) :
      Reduction M M' →
      Reduction (.natElim natLevel M z s t) (.natElim natLevel M' z s t)
  | natZero {n : Nat} (natLevel : Nat) (M : Expr (n + 1)) {z z' : Expr n}
      (s : Expr (n + 2)) (t : Expr n) :
      Reduction z z' →
      Reduction (.natElim natLevel M z s t) (.natElim natLevel M z' s t)
  | natSucc {n : Nat} (natLevel : Nat) (M : Expr (n + 1)) (z : Expr n)
      {s s' : Expr (n + 2)} (t : Expr n) :
      Reduction s s' →
      Reduction (.natElim natLevel M z s t) (.natElim natLevel M z s' t)
  | natScrutinee {n : Nat} (natLevel : Nat) (M : Expr (n + 1)) (z : Expr n)
      (s : Expr (n + 2)) {t t' : Expr n} :
      Reduction t t' →
      Reduction (.natElim natLevel M z s t) (.natElim natLevel M z s t')
  | codePiDom {n : Nat} {A A' : Expr n} (B : Expr (n + 1)) :
      Reduction A A' → Reduction (.codePi A B) (.codePi A' B)
  | codePiCod {n : Nat} (A : Expr n) {B B' : Expr (n + 1)} :
      Reduction B B' → Reduction (.codePi A B) (.codePi A B')
  | codeSigmaDom {n : Nat} {A A' : Expr n} (B : Expr (n + 1)) :
      Reduction A A' → Reduction (.codeSigma A B) (.codeSigma A' B)
  | codeSigmaCod {n : Nat} (A : Expr n) {B B' : Expr (n + 1)} :
      Reduction B B' → Reduction (.codeSigma A B) (.codeSigma A B')
  | codeIdType {n : Nat} {A A' a b : Expr n} :
      Reduction A A' → Reduction (.codeId A a b) (.codeId A' a b)
  | codeIdLeft {n : Nat} {A a a' b : Expr n} :
      Reduction a a' → Reduction (.codeId A a b) (.codeId A a' b)
  | codeIdRight {n : Nat} {A a b b' : Expr n} :
      Reduction b b' → Reduction (.codeId A a b) (.codeId A a b')
  | elCongr {n : Nat} {code code' : Expr n} :
      Reduction code code' → Reduction (.el code) (.el code')
  | idType {n : Nat} {A A' a b : Expr n} :
      Reduction A A' → Reduction (.id A a b) (.id A' a b)
  | idLeft {n : Nat} {A a a' b : Expr n} :
      Reduction a a' → Reduction (.id A a b) (.id A a' b)
  | idRight {n : Nat} {A a b b' : Expr n} :
      Reduction b b' → Reduction (.id A a b) (.id A a b')
  | reflCongr {n : Nat} {a a' : Expr n} :
      Reduction a a' → Reduction (.refl a) (.refl a')
  | eqJMotive {n : Nat} {M M' : Expr (n + 2)} (r b p : Expr n) :
      Reduction M M' → Reduction (.eqJ M r b p) (.eqJ M' r b p)
  | eqJRefl {n : Nat} (M : Expr (n + 2)) {r r' : Expr n} (b p : Expr n) :
      Reduction r r' → Reduction (.eqJ M r b p) (.eqJ M r' b p)
  | eqJEndpoint {n : Nat} (M : Expr (n + 2)) (r : Expr n)
      {b b' : Expr n} (p : Expr n) :
      Reduction b b' → Reduction (.eqJ M r b p) (.eqJ M r b' p)
  | eqJProof {n : Nat} (M : Expr (n + 2)) (r b : Expr n) {p p' : Expr n} :
      Reduction p p' → Reduction (.eqJ M r b p) (.eqJ M r b p')

namespace Reduction

/-- Contextual reduction is sound for source definitional equality.  Every
constructor has a matching `DefEq` congruence, which is what makes the closure
auditable. -/
theorem toDefEq {n : Nat} {t u : Expr n} (r : Reduction t u) : DefEq t u := by
  induction r with
  | head h => exact DefEq.beta h
  | piDom B _ ih => exact DefEq.piDom B ih
  | piCod A _ ih => exact DefEq.piCod A ih
  | sigmaDom B _ ih => exact DefEq.sigmaDom B ih
  | sigmaCod A _ ih => exact DefEq.sigmaCod A ih
  | lamBody _ ih => exact DefEq.lamBody ih
  | appFun _ ih => exact DefEq.appFun ih
  | appArg _ ih => exact DefEq.appArg ih
  | pairFst _ ih => exact DefEq.pairFst ih
  | pairSnd _ ih => exact DefEq.pairSnd ih
  | fstCongr _ ih => exact DefEq.fstCongr ih
  | sndCongr _ ih => exact DefEq.sndCongr ih
  | succCongr natLevel _ ih => exact DefEq.succCongr natLevel ih
  | natMotive natLevel z s t _ ih => exact DefEq.natMotive natLevel z s t ih
  | natZero natLevel M s t _ ih => exact DefEq.natZero natLevel M s t ih
  | natSucc natLevel M z t _ ih => exact DefEq.natSucc natLevel M z t ih
  | natScrutinee natLevel M z s _ ih =>
      exact DefEq.natScrutinee natLevel M z s ih
  | codePiDom B _ ih => exact DefEq.codePiDom B ih
  | codePiCod A _ ih => exact DefEq.codePiCod A ih
  | codeSigmaDom B _ ih => exact DefEq.codeSigmaDom B ih
  | codeSigmaCod A _ ih => exact DefEq.codeSigmaCod A ih
  | codeIdType _ ih => exact DefEq.codeIdType ih
  | codeIdLeft _ ih => exact DefEq.codeIdLeft ih
  | codeIdRight _ ih => exact DefEq.codeIdRight ih
  | elCongr _ ih => exact DefEq.elCongr ih
  | idType _ ih => exact DefEq.idType ih
  | idLeft _ ih => exact DefEq.idLeft ih
  | idRight _ ih => exact DefEq.idRight ih
  | reflCongr _ ih => exact DefEq.reflCongr ih
  | eqJMotive r b p _ ih => exact DefEq.eqJMotive r b p ih
  | eqJRefl M b p _ ih => exact DefEq.eqJRefl M b p ih
  | eqJEndpoint M r p _ ih => exact DefEq.eqJEndpoint M r p ih
  | eqJProof M r b _ ih => exact DefEq.eqJProof M r b ih

/-- Contextual reduction is stable under simultaneous substitution.  Binder
cases use the explicit one- and two-variable lifts, exactly as the primitive
layer does. -/
noncomputable def substitution {n m : Nat} (sigma : Sub n m)
    {t u : Expr n} (r : Reduction t u) :
    Reduction (subst sigma t) (subst sigma u) := by
  induction r generalizing m with
  | head h => exact Reduction.head (Computation.substitution sigma h)
  | piDom B _ ih => exact Reduction.piDom _ (ih sigma)
  | piCod A _ ih => exact Reduction.piCod _ (ih (Sub.lift sigma))
  | sigmaDom B _ ih => exact Reduction.sigmaDom _ (ih sigma)
  | sigmaCod A _ ih => exact Reduction.sigmaCod _ (ih (Sub.lift sigma))
  | lamBody _ ih => exact Reduction.lamBody (ih (Sub.lift sigma))
  | appFun _ ih => exact Reduction.appFun (ih sigma)
  | appArg _ ih => exact Reduction.appArg (ih sigma)
  | pairFst _ ih => exact Reduction.pairFst (ih sigma)
  | pairSnd _ ih => exact Reduction.pairSnd (ih sigma)
  | fstCongr _ ih => exact Reduction.fstCongr (ih sigma)
  | sndCongr _ ih => exact Reduction.sndCongr (ih sigma)
  | succCongr natLevel _ ih => exact Reduction.succCongr natLevel (ih sigma)
  | natMotive natLevel z s t _ ih =>
      exact Reduction.natMotive natLevel _ _ _ (ih (Sub.lift sigma))
  | natZero natLevel M s t _ ih =>
      exact Reduction.natZero natLevel _ _ _ (ih sigma)
  | natSucc natLevel M z t _ ih =>
      exact Reduction.natSucc natLevel _ _ _
        (ih (Sub.lift (Sub.lift sigma)))
  | natScrutinee natLevel M z s _ ih =>
      exact Reduction.natScrutinee natLevel _ _ _ (ih sigma)
  | codePiDom B _ ih => exact Reduction.codePiDom _ (ih sigma)
  | codePiCod A _ ih => exact Reduction.codePiCod _ (ih (Sub.lift sigma))
  | codeSigmaDom B _ ih => exact Reduction.codeSigmaDom _ (ih sigma)
  | codeSigmaCod A _ ih =>
      exact Reduction.codeSigmaCod _ (ih (Sub.lift sigma))
  | codeIdType _ ih => exact Reduction.codeIdType (ih sigma)
  | codeIdLeft _ ih => exact Reduction.codeIdLeft (ih sigma)
  | codeIdRight _ ih => exact Reduction.codeIdRight (ih sigma)
  | elCongr _ ih => exact Reduction.elCongr (ih sigma)
  | idType _ ih => exact Reduction.idType (ih sigma)
  | idLeft _ ih => exact Reduction.idLeft (ih sigma)
  | idRight _ ih => exact Reduction.idRight (ih sigma)
  | reflCongr _ ih => exact Reduction.reflCongr (ih sigma)
  | eqJMotive r b p _ ih =>
      exact Reduction.eqJMotive _ _ _ (ih (Sub.lift (Sub.lift sigma)))
  | eqJRefl M b p _ ih => exact Reduction.eqJRefl _ _ _ (ih sigma)
  | eqJEndpoint M r p _ ih => exact Reduction.eqJEndpoint _ _ _ (ih sigma)
  | eqJProof M r b _ ih => exact Reduction.eqJProof _ _ _ (ih sigma)

end Reduction

/-! ## Multi-step reduction -/

/-- Reflexive-transitive closure of contextual reduction. -/
inductive ReductionMany : {n : Nat} → Expr n → Expr n → Type where
  | refl {n : Nat} (t : Expr n) : ReductionMany t t
  | step {n : Nat} {t u v : Expr n} :
      Reduction t u → ReductionMany u v → ReductionMany t v

namespace ReductionMany

/-- A single contextual step is a multi-step reduction. -/
noncomputable def one {n : Nat} {t u : Expr n} (r : Reduction t u) :
    ReductionMany t u :=
  ReductionMany.step r (ReductionMany.refl u)

/-- Multi-step reduction is transitive. -/
noncomputable def trans {n : Nat} {t u v : Expr n}
    (r : ReductionMany t u) (s : ReductionMany u v) : ReductionMany t v := by
  induction r with
  | refl _ => exact s
  | step h _ ih => exact ReductionMany.step h (ih s)

/-- Multi-step reduction is sound for source definitional equality. -/
theorem toDefEq {n : Nat} {t u : Expr n} (r : ReductionMany t u) :
    DefEq t u := by
  induction r with
  | refl t => exact DefEq.refl t
  | step h _ ih => exact DefEq.trans h.toDefEq ih

/-- Multi-step reduction is stable under simultaneous substitution. -/
noncomputable def substitution {n m : Nat} (sigma : Sub n m)
    {t u : Expr n} (r : ReductionMany t u) :
    ReductionMany (subst sigma t) (subst sigma u) := by
  induction r with
  | refl t => exact ReductionMany.refl _
  | step h _ ih =>
      exact ReductionMany.step (Reduction.substitution sigma h) ih

/-- The number of contextual steps recorded by a multi-step reduction. -/
def length {n : Nat} {t u : Expr n} : ReductionMany t u → Nat
  | .refl _ => 0
  | .step _ rest => rest.length + 1

@[simp] theorem length_refl {n : Nat} (t : Expr n) :
    (ReductionMany.refl t).length = 0 := rfl

end ReductionMany

/-! ## Reduction on the syntactic quotient -/

/-- Reducing a term does not move its class in the syntactic quotient: this is
soundness of `Reduction` for `DefEq`, transported through `Quotient.sound`. -/
theorem denote_reduction {n : Nat} {t u : Expr n} (r : Reduction t u) :
    denote t = denote u :=
  Quotient.sound r.toDefEq

/-- The same statement for multi-step reduction. -/
theorem denote_reductionMany {n : Nat} {t u : Expr n}
    (r : ReductionMany t u) : denote t = denote u :=
  Quotient.sound r.toDefEq

/-! ## Isolating the omitted structural rules

Contextual subject reduction fails in the raw calculus for one identifiable
reason.  Rebuilding an elimination around a reduced subterm requires that
subterm at a *definitionally equal* type, and `HasType` has no rule that
retypes a term along `DefEq`.  Reducing inside a domain annotation additionally
changes the context under a binder.  These are the conversion and
context-conversion rules.

We take them as an explicit hypothesis record.  No axiom is introduced: every
theorem below carries the record as an argument, so its dependence on the
omitted rules is visible in its statement. -/

/-- The two structural rules the raw calculus deliberately omits. -/
structure ConversionRules where
  /-- Retype a term along source definitional equality of its type. -/
  convert : ∀ {n : Nat} {Gamma : Ctx n} {t A A' : Expr n},
    HasType Gamma t A → DefEq A A' → HasType Gamma t A'
  /-- Retype a term along pointwise source definitional equality of the
  context. -/
  convertCtx : ∀ {n : Nat} {Gamma Delta : Ctx n} {t A : Expr n},
    (∀ i, DefEq (Gamma i) (Delta i)) → HasType Gamma t A → HasType Delta t A

/-- Pointwise definitional equality of contexts is preserved by extension. -/
theorem ctxDefEq_extend {n : Nat} {Gamma Delta : Ctx n} {A A' : Expr n}
    (hGamma : ∀ i, DefEq (Gamma i) (Delta i)) (hA : DefEq A A') :
    ∀ i, DefEq (Ctx.extend Gamma A i) (Ctx.extend Delta A' i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Ctx.extend_zero, subst_ofRen] using
      DefEq.substitution hA (Sub.ofRen (Ren.wk n))
  · simpa only [Ctx.extend_succ, subst_ofRen] using
      DefEq.substitution (hGamma j) (Sub.ofRen (Ren.wk n))

/-- Extension in the type slot alone. -/
theorem ctxDefEq_extend_type {n : Nat} (Gamma : Ctx n) {A A' : Expr n}
    (hA : DefEq A A') :
    ∀ i, DefEq (Ctx.extend Gamma A i) (Ctx.extend Gamma A' i) :=
  ctxDefEq_extend (fun i => DefEq.refl (Gamma i)) hA

/-- The natural-number successor context is congruent in its motive. -/
theorem natStepCtx_defEq {n : Nat} (Gamma : Ctx n) (natLevel : Nat)
    {M M' : Expr (n + 1)} (hM : DefEq M M') :
    ∀ i, DefEq (natStepCtx Gamma natLevel M i)
      (natStepCtx Gamma natLevel M' i) := by
  unfold natStepCtx
  exact ctxDefEq_extend_type _ hM

/-- The equality-motive context is congruent in both of its parameters. -/
theorem eqMotiveCtx_defEq {n : Nat} (Gamma : Ctx n) {A A' a a' : Expr n}
    (hA : DefEq A A') (ha : DefEq a a') :
    ∀ i, DefEq (eqMotiveCtx Gamma A a i) (eqMotiveCtx Gamma A' a' i) := by
  unfold eqMotiveCtx eqProofType weaken
  refine ctxDefEq_extend (ctxDefEq_extend_type Gamma hA) ?_
  refine DefEq.trans (DefEq.idType ?_) (DefEq.idLeft ?_)
  · simpa only [subst_ofRen] using
      DefEq.substitution hA (Sub.ofRen (Ren.wk n))
  · simpa only [subst_ofRen] using
      DefEq.substitution ha (Sub.ofRen (Ren.wk n))

/-- The successor-branch target type is congruent in its motive. -/
theorem natStepTarget_defEq {n : Nat} (natLevel : Nat)
    {M M' : Expr (n + 1)} (hM : DefEq M M') :
    DefEq (natStepTarget natLevel M) (natStepTarget natLevel M') := by
  unfold natStepTarget
  exact DefEq.substitution hM _

/-- One-variable instantiation is congruent in its *body*.  `DefEq` already
supplies congruence in the argument; this is the complementary direction, and
it is immediate from stability of `DefEq` under substitution. -/
theorem instantiate_congr_body {n : Nat} {M M' : Expr (n + 1)}
    (hM : DefEq M M') (a : Expr n) :
    DefEq (instantiate M a) (instantiate M' a) := by
  unfold instantiate
  exact DefEq.substitution hM _

/-- Two-variable instantiation is congruent in its body. -/
theorem instantiate₂_congr_body {n : Nat} {M M' : Expr (n + 2)}
    (hM : DefEq M M') (a p : Expr n) :
    DefEq (instantiate₂ M a p) (instantiate₂ M' a p) := by
  unfold instantiate₂
  exact DefEq.substitution hM _

/-! ## Contextual and multi-step subject reduction -/

/-- **Contextual subject reduction.**  Given the two omitted structural rules,
typing is preserved by reduction *anywhere inside a term*, at the very same
type.  The proof inverts the syntax-directed typing rule at each congruence
constructor, applies the induction hypothesis to the reduced subterm, and
rebuilds; conversion repairs the displayed type when an elimination mentions
the subterm, and context conversion repairs the context when a domain
annotation is reduced under a binder. -/
noncomputable def contextual_subject_reduction (C : ConversionRules)
    {n : Nat} {t u : Expr n} (r : Reduction t u) :
    ∀ {Gamma : Ctx n} {A : Expr n}, HasType Gamma t A → HasType Gamma u A := by
  induction r with
  | head hc =>
      intro Gamma A h
      exact C.convert
        (subject_reduction ⟨A, h, hc⟩).targetTyping
        (subject_reduction ⟨A, h, hc⟩).typeCoherence
  | @piDom _ A A' B rA ih =>
      intro Gamma T h
      cases h with
      | piForm hA hB =>
          exact HasType.piForm (ih hA)
            (C.convertCtx (ctxDefEq_extend_type Gamma rA.toDefEq) hB)
  | piCod A _ ih =>
      intro Gamma T h
      cases h with
      | piForm hA hB => exact HasType.piForm hA (ih hB)
  | @sigmaDom _ A A' B rA ih =>
      intro Gamma T h
      cases h with
      | sigmaForm hA hB =>
          exact HasType.sigmaForm (ih hA)
            (C.convertCtx (ctxDefEq_extend_type Gamma rA.toDefEq) hB)
  | sigmaCod A _ ih =>
      intro Gamma T h
      cases h with
      | sigmaForm hA hB => exact HasType.sigmaForm hA (ih hB)
  | lamBody _ ih =>
      intro Gamma T h
      cases h with
      | lamIntro hA hB hBody => exact HasType.lamIntro hA hB (ih hBody)
  | appFun _ ih =>
      intro Gamma T h
      cases h with
      | appElim hf ha => exact HasType.appElim (ih hf) ha
  | @appArg _ f a a' ra ih =>
      intro Gamma T h
      cases h with
      | @appElim _ _ A B _ _ hf ha =>
          exact C.convert (HasType.appElim hf (ih ha))
            (DefEq.instantiate_congr B (DefEq.symm ra.toDefEq))
  | @pairFst _ a a' b ra ih =>
      intro Gamma T h
      cases h with
      | @pairIntro _ _ A B _ _ ha hb =>
          exact HasType.pairIntro (ih ha)
            (C.convert hb (DefEq.instantiate_congr B ra.toDefEq))
  | pairSnd _ ih =>
      intro Gamma T h
      cases h with
      | pairIntro ha hb => exact HasType.pairIntro ha (ih hb)
  | fstCongr _ ih =>
      intro Gamma T h
      cases h with
      | fstElim hp => exact HasType.fstElim (ih hp)
  | @sndCongr _ p p' rp ih =>
      intro Gamma T h
      cases h with
      | @sndElim _ _ A B _ hp =>
          exact C.convert (HasType.sndElim (ih hp))
            (DefEq.instantiate_congr B
              (DefEq.fstCongr (DefEq.symm rp.toDefEq)))
  | succCongr natLevel _ ih =>
      intro Gamma T h
      cases h with
      | succIntro _ ht => exact HasType.succIntro _ (ih ht)
  | @natMotive _ natLevel M M' z s t rM ih =>
      intro Gamma T h
      cases h with
      | natElim hM hZero hSucc hScrutinee =>
          refine C.convert
            (HasType.natElim (ih hM)
              (C.convert hZero
                (instantiate_congr_body rM.toDefEq _))
              (C.convert
                (C.convertCtx
                  (natStepCtx_defEq Gamma natLevel rM.toDefEq) hSucc)
                (natStepTarget_defEq natLevel rM.toDefEq))
              hScrutinee)
            ?_
          exact DefEq.symm (instantiate_congr_body rM.toDefEq _)
  | natZero natLevel M s t _ ih =>
      intro Gamma T h
      cases h with
      | natElim hM hZero hSucc hScrutinee =>
          exact HasType.natElim hM (ih hZero) hSucc hScrutinee
  | natSucc natLevel M z t _ ih =>
      intro Gamma T h
      cases h with
      | natElim hM hZero hSucc hScrutinee =>
          exact HasType.natElim hM hZero (ih hSucc) hScrutinee
  | @natScrutinee _ natLevel M z s t t' rt ih =>
      intro Gamma T h
      cases h with
      | natElim hM hZero hSucc hScrutinee =>
          exact C.convert
            (HasType.natElim hM hZero hSucc (ih hScrutinee))
            (DefEq.instantiate_congr M (DefEq.symm rt.toDefEq))
  | @codePiDom _ A A' B rA ih =>
      intro Gamma T h
      cases h with
      | codePiIntro hA hB =>
          exact HasType.codePiIntro (ih hA)
            (C.convertCtx
              (ctxDefEq_extend_type Gamma (DefEq.elCongr rA.toDefEq)) hB)
  | codePiCod A _ ih =>
      intro Gamma T h
      cases h with
      | codePiIntro hA hB => exact HasType.codePiIntro hA (ih hB)
  | @codeSigmaDom _ A A' B rA ih =>
      intro Gamma T h
      cases h with
      | codeSigmaIntro hA hB =>
          exact HasType.codeSigmaIntro (ih hA)
            (C.convertCtx
              (ctxDefEq_extend_type Gamma (DefEq.elCongr rA.toDefEq)) hB)
  | codeSigmaCod A _ ih =>
      intro Gamma T h
      cases h with
      | codeSigmaIntro hA hB => exact HasType.codeSigmaIntro hA (ih hB)
  | @codeIdType _ A A' a b rA ih =>
      intro Gamma T h
      cases h with
      | codeIdIntro hA ha hb =>
          exact HasType.codeIdIntro (ih hA)
            (C.convert ha (DefEq.elCongr rA.toDefEq))
            (C.convert hb (DefEq.elCongr rA.toDefEq))
  | codeIdLeft _ ih =>
      intro Gamma T h
      cases h with
      | codeIdIntro hA ha hb => exact HasType.codeIdIntro hA (ih ha) hb
  | codeIdRight _ ih =>
      intro Gamma T h
      cases h with
      | codeIdIntro hA ha hb => exact HasType.codeIdIntro hA ha (ih hb)
  | elCongr _ ih =>
      intro Gamma T h
      cases h with
      | elForm hCode => exact HasType.elForm (ih hCode)
  | @idType _ A A' a b rA ih =>
      intro Gamma T h
      cases h with
      | idForm hA ha hb =>
          exact HasType.idForm (ih hA)
            (C.convert ha rA.toDefEq) (C.convert hb rA.toDefEq)
  | idLeft _ ih =>
      intro Gamma T h
      cases h with
      | idForm hA ha hb => exact HasType.idForm hA (ih ha) hb
  | idRight _ ih =>
      intro Gamma T h
      cases h with
      | idForm hA ha hb => exact HasType.idForm hA ha (ih hb)
  | @reflCongr _ a a' ra ih =>
      intro Gamma T h
      cases h with
      | @reflIntro _ _ A _ ha =>
          exact C.convert (HasType.reflIntro (ih ha))
            (DefEq.trans (DefEq.idLeft (DefEq.symm ra.toDefEq))
              (DefEq.idRight (DefEq.symm ra.toDefEq)))
  | @eqJMotive _ M M' rc b p rM ih =>
      intro Gamma T h
      cases h with
      | eqJElim hA ha hM hRefl hEndpoint hProof =>
          refine C.convert
            (HasType.eqJElim hA ha (ih hM)
              (C.convert hRefl
                (instantiate₂_congr_body rM.toDefEq _ _))
              hEndpoint hProof)
            ?_
          exact DefEq.symm (instantiate₂_congr_body rM.toDefEq _ _)
  | eqJRefl M b p _ ih =>
      intro Gamma T h
      cases h with
      | eqJElim hA ha hM hRefl hEndpoint hProof =>
          exact HasType.eqJElim hA ha hM (ih hRefl) hEndpoint hProof
  | @eqJEndpoint _ M rc b b' p rb ih =>
      intro Gamma T h
      cases h with
      | @eqJElim _ _ A a _ _ _ _ _ _ hA ha hM hRefl hEndpoint hProof =>
          exact C.convert
            (HasType.eqJElim hA ha hM hRefl (ih hEndpoint)
              (C.convert hProof (DefEq.idRight rb.toDefEq)))
            (DefEq.instantiate₂_congr M (DefEq.symm rb.toDefEq)
              (DefEq.refl p))
  | @eqJProof _ M rc b p p' rp ih =>
      intro Gamma T h
      cases h with
      | eqJElim hA ha hM hRefl hEndpoint hProof =>
          exact C.convert
            (HasType.eqJElim hA ha hM hRefl hEndpoint (ih hProof))
            (DefEq.instantiate₂_congr M (DefEq.refl b)
              (DefEq.symm rp.toDefEq))

/-- **Multi-step subject reduction.**  Iterating the contextual theorem. -/
noncomputable def multistep_subject_reduction (C : ConversionRules)
    {n : Nat} {Gamma : Ctx n} {t u A : Expr n}
    (h : HasType Gamma t A) (r : ReductionMany t u) : HasType Gamma u A := by
  induction r with
  | refl _ => exact h
  | step hstep _ ih =>
      exact ih (contextual_subject_reduction C hstep h)

end RawMLTT
end TypeTheory
end Path
end ComputationalPaths
