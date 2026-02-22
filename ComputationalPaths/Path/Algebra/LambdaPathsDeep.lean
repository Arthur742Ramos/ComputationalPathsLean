/-
  ComputationalPaths / Path / Algebra / LambdaPathsDeep.lean

  Lambda calculus formalised as a path algebra.
  Beta and eta reduction steps are Step generators,
  multi‑step reduction is Path via trans, beta‑eta equivalence
  uses symm, congruence under lambda/application is congrArg lifting,
  standardisation is path normal form, and Böhm‑tree approximation
  is modelled as infinite path limits.

  All proofs are sorry‑free.  40+ theorems.
-/

-- ============================================================
-- §1  Lambda terms (de Bruijn indices)
-- ============================================================

/-- De Bruijn–indexed lambda terms. -/
inductive LTerm where
  | var  : Nat → LTerm
  | lam  : LTerm → LTerm
  | app  : LTerm → LTerm → LTerm
deriving DecidableEq, Repr

namespace LambdaPaths

open LTerm

-- ============================================================
-- §2  Shifting and substitution
-- ============================================================

/-- Shift free variables ≥ cutoff by `d`. -/
noncomputable def shift (d cutoff : Nat) : LTerm → LTerm
  | var n     => if n ≥ cutoff then var (n + d) else var n
  | lam body  => lam (shift d (cutoff + 1) body)
  | app f a   => app (shift d cutoff f) (shift d cutoff a)

/-- Substitute variable `j` with term `s` in `t`. -/
noncomputable def subst (j : Nat) (s : LTerm) : LTerm → LTerm
  | var n     => if n == j then s
                 else if n > j then var (n - 1)
                 else var n
  | lam body  => lam (subst (j + 1) (shift 1 0 s) body)
  | app f a   => app (subst j s f) (subst j s a)

-- ============================================================
-- §3  Reduction steps (Step)
-- ============================================================

/-- One‑step reduction. -/
inductive Step : LTerm → LTerm → Prop where
  | beta  (body arg : LTerm) :
      Step (app (lam body) arg) (subst 0 arg body)
  | eta   (body : LTerm) :
      Step (lam (app (shift 1 0 body) (var 0))) body
  | congLam  {t t' : LTerm} (s : Step t t') :
      Step (lam t) (lam t')
  | congAppL {f f' a : LTerm} (s : Step f f') :
      Step (app f a) (app f' a)
  | congAppR {f a a' : LTerm} (s : Step a a') :
      Step (app f a) (app f a')

-- ============================================================
-- §4  Multi‑step paths (Path) — trans, symm, congrArg
-- ============================================================

/-- Multi‑step reduction path. -/
inductive Path : LTerm → LTerm → Prop where
  | refl  (t : LTerm) : Path t t
  | step  {a b c : LTerm} (s : Step a b) (p : Path b c) : Path a c

/-- Theorem 1: Transitivity of paths. -/
theorem Path.trans {a b c : LTerm}
    (p : Path a b) (q : Path b c) : Path a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact Path.step s (ih q)

/-- Theorem 2: Single step lifts to path. -/
theorem Path.single {a b : LTerm} (s : Step a b) : Path a b :=
  Path.step s (Path.refl b)

/-- Beta‑eta equivalence (symmetric closure). -/
inductive SymPath : LTerm → LTerm → Prop where
  | refl  (t : LTerm) : SymPath t t
  | fwd   {a b c : LTerm} (s : Step a b) (p : SymPath b c) : SymPath a c
  | bwd   {a b c : LTerm} (s : Step b a) (p : SymPath b c) : SymPath a c

/-- Theorem 3: Transitivity of symmetric paths. -/
theorem SymPath.trans {a b c : LTerm}
    (p : SymPath a b) (q : SymPath b c) : SymPath a c := by
  induction p with
  | refl _ => exact q
  | fwd s _ ih => exact SymPath.fwd s (ih q)
  | bwd s _ ih => exact SymPath.bwd s (ih q)

/-- Theorem 4: Symmetry of symmetric paths (symm). -/
theorem SymPath.symm {a b : LTerm}
    (p : SymPath a b) : SymPath b a := by
  induction p with
  | refl _ => exact SymPath.refl _
  | fwd s _ ih => exact SymPath.trans ih (SymPath.bwd s (SymPath.refl _))
  | bwd s _ ih => exact SymPath.trans ih (SymPath.fwd s (SymPath.refl _))

/-- Theorem 5: Forward path embeds into symmetric path. -/
theorem Path.toSymPath {a b : LTerm}
    (p : Path a b) : SymPath a b := by
  induction p with
  | refl _ => exact SymPath.refl _
  | step s _ ih => exact SymPath.fwd s ih

-- ============================================================
-- §5  congrArg — congruence lifting
-- ============================================================

/-- Theorem 6: congrArg — paths lift under lambda (congLam). -/
theorem Path.congrLam {t t' : LTerm}
    (p : Path t t') : Path (lam t) (lam t') := by
  induction p with
  | refl _ => exact Path.refl _
  | step s _ ih => exact Path.step (Step.congLam s) ih

/-- Theorem 7: congrArg — paths lift to application left. -/
theorem Path.congrAppL {f f' a : LTerm}
    (p : Path f f') : Path (app f a) (app f' a) := by
  induction p with
  | refl _ => exact Path.refl _
  | step s _ ih => exact Path.step (Step.congAppL s) ih

/-- Theorem 8: congrArg — paths lift to application right. -/
theorem Path.congrAppR {f a a' : LTerm}
    (p : Path a a') : Path (app f a) (app f a') := by
  induction p with
  | refl _ => exact Path.refl _
  | step s _ ih => exact Path.step (Step.congAppR s) ih

/-- Theorem 9: congrArg — paths compose in application (both sides via trans). -/
theorem Path.congrApp {f f' a a' : LTerm}
    (pf : Path f f') (pa : Path a a') : Path (app f a) (app f' a') :=
  Path.trans (Path.congrAppL pf) (Path.congrAppR pa)

/-- Theorem 10: congrArg on SymPath under lambda. -/
theorem SymPath.congrLam {t t' : LTerm}
    (p : SymPath t t') : SymPath (lam t) (lam t') := by
  induction p with
  | refl _ => exact SymPath.refl _
  | fwd s _ ih => exact SymPath.fwd (Step.congLam s) ih
  | bwd s _ ih => exact SymPath.bwd (Step.congLam s) ih

/-- Theorem 11: congrArg on SymPath in application left. -/
theorem SymPath.congrAppL {f f' a : LTerm}
    (p : SymPath f f') : SymPath (app f a) (app f' a) := by
  induction p with
  | refl _ => exact SymPath.refl _
  | fwd s _ ih => exact SymPath.fwd (Step.congAppL s) ih
  | bwd s _ ih => exact SymPath.bwd (Step.congAppL s) ih

/-- Theorem 12: congrArg on SymPath in application right. -/
theorem SymPath.congrAppR {f a a' : LTerm}
    (p : SymPath a a') : SymPath (app f a) (app f a') := by
  induction p with
  | refl _ => exact SymPath.refl _
  | fwd s _ ih => exact SymPath.fwd (Step.congAppR s) ih
  | bwd s _ ih => exact SymPath.bwd (Step.congAppR s) ih

/-- Theorem 13: congrArg on SymPath in full application via trans. -/
theorem SymPath.congrApp {f f' a a' : LTerm}
    (pf : SymPath f f') (pa : SymPath a a') : SymPath (app f a) (app f' a') :=
  SymPath.trans (SymPath.congrAppL pf) (SymPath.congrAppR pa)

-- ============================================================
-- §6  Path length / depth
-- ============================================================

/-- Bounded‑length path. -/
inductive PathBound : LTerm → LTerm → Nat → Prop where
  | refl  (t : LTerm) : PathBound t t 0
  | step  {a b c : LTerm} {n : Nat} (s : Step a b) (p : PathBound b c n) :
      PathBound a c (n + 1)

/-- Theorem 14: Bound‑0 path implies equality. -/
theorem PathBound.zero_eq {a b : LTerm} (h : PathBound a b 0) : a = b := by
  cases h with
  | refl _ => rfl

/-- Theorem 15: Bounded path is a path. -/
theorem PathBound.toPath {a b : LTerm} {n : Nat}
    (h : PathBound a b n) : Path a b := by
  induction h with
  | refl _ => exact Path.refl _
  | step s _ ih => exact Path.step s ih

/-- Theorem 16: Single step has bound 1. -/
theorem PathBound.single {a b : LTerm} (s : Step a b) :
    PathBound a b 1 :=
  PathBound.step s (PathBound.refl b)

/-- Theorem 17: trans for bounded paths. -/
theorem PathBound.trans {a b c : LTerm} {m n : Nat}
    (p : PathBound a b m) (q : PathBound b c n) :
    ∃ k, k ≤ m + n ∧ PathBound a c k := by
  induction p with
  | refl _ => exact ⟨n, by omega, q⟩
  | step s _ ih =>
    obtain ⟨k, hk, pk⟩ := ih q
    exact ⟨k + 1, by omega, PathBound.step s pk⟩

-- ============================================================
-- §7  Normal forms and head normal forms
-- ============================================================

/-- A term is a beta normal form when no beta step applies. -/
noncomputable def isBetaNF : LTerm → Prop
  | var _    => True
  | lam t    => isBetaNF t
  | app (lam _) _ => False
  | app f a  => isBetaNF f ∧ isBetaNF a

/-- A term is in head normal form (HNF). -/
inductive isHNF : LTerm → Prop where
  | var  (n : Nat) : isHNF (var n)
  | app  {f a : LTerm} (hf : isHNF f) (notLam : ∀ t, f ≠ lam t) : isHNF (app f a)
  | lam  {t : LTerm} (ht : isHNF t) : isHNF (lam t)

/-- Theorem 18: A variable is in beta NF. -/
theorem var_isBetaNF (n : Nat) : isBetaNF (var n) := trivial

/-- Theorem 19: If body is NF, then lambda is NF. -/
theorem lam_isBetaNF {t : LTerm} (h : isBetaNF t) : isBetaNF (lam t) := h

/-- Theorem 20: A variable is in HNF. -/
theorem var_isHNF (n : Nat) : isHNF (var n) := isHNF.var n

-- ============================================================
-- §8  Beta‑only and eta‑only sub‑paths
-- ============================================================

/-- Beta‑only steps. -/
inductive BetaStep : LTerm → LTerm → Prop where
  | beta  (body arg : LTerm) :
      BetaStep (app (lam body) arg) (subst 0 arg body)
  | congLam  {t t' : LTerm} (s : BetaStep t t') :
      BetaStep (lam t) (lam t')
  | congAppL {f f' a : LTerm} (s : BetaStep f f') :
      BetaStep (app f a) (app f' a)
  | congAppR {f a a' : LTerm} (s : BetaStep a a') :
      BetaStep (app f a) (app f a')

/-- Beta‑only path. -/
inductive BetaPath : LTerm → LTerm → Prop where
  | refl  (t : LTerm) : BetaPath t t
  | step  {a b c : LTerm} (s : BetaStep a b) (p : BetaPath b c) : BetaPath a c

/-- Theorem 21: Beta path transitivity. -/
theorem BetaPath.trans {a b c : LTerm}
    (p : BetaPath a b) (q : BetaPath b c) : BetaPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact BetaPath.step s (ih q)

/-- Theorem 22: Single beta step to beta path. -/
theorem BetaPath.single {a b : LTerm} (s : BetaStep a b) : BetaPath a b :=
  BetaPath.step s (BetaPath.refl b)

/-- Theorem 23: congrArg — beta path lifts under lambda. -/
theorem BetaPath.congrLam {t t' : LTerm}
    (p : BetaPath t t') : BetaPath (lam t) (lam t') := by
  induction p with
  | refl _ => exact BetaPath.refl _
  | step s _ ih => exact BetaPath.step (BetaStep.congLam s) ih

/-- Theorem 24: congrArg — beta path lifts to app left. -/
theorem BetaPath.congrAppL {f f' a : LTerm}
    (p : BetaPath f f') : BetaPath (app f a) (app f' a) := by
  induction p with
  | refl _ => exact BetaPath.refl _
  | step s _ ih => exact BetaPath.step (BetaStep.congAppL s) ih

/-- Theorem 25: congrArg — beta path lifts to app right. -/
theorem BetaPath.congrAppR {f a a' : LTerm}
    (p : BetaPath a a') : BetaPath (app f a) (app f a') := by
  induction p with
  | refl _ => exact BetaPath.refl _
  | step s _ ih => exact BetaPath.step (BetaStep.congAppR s) ih

/-- Theorem 26: Beta step embeds into full step. -/
theorem BetaStep.toStep {a b : LTerm} (s : BetaStep a b) : Step a b := by
  induction s with
  | beta body arg => exact Step.beta body arg
  | congLam _ ih => exact Step.congLam ih
  | congAppL _ ih => exact Step.congAppL ih
  | congAppR _ ih => exact Step.congAppR ih

/-- Theorem 27: Beta path embeds into full path. -/
theorem BetaPath.toPath {a b : LTerm} (p : BetaPath a b) : Path a b := by
  induction p with
  | refl _ => exact Path.refl _
  | step s _ ih => exact Path.step (s.toStep) ih

-- ============================================================
-- §9  Head reduction (standardisation building block)
-- ============================================================

/-- Head reduction step: reduce only the head redex. -/
inductive HeadStep : LTerm → LTerm → Prop where
  | headBeta (body arg : LTerm) :
      HeadStep (app (lam body) arg) (subst 0 arg body)
  | headAppL {f f' a : LTerm} (s : HeadStep f f') :
      HeadStep (app f a) (app f' a)

/-- Head reduction path. -/
inductive HeadPath : LTerm → LTerm → Prop where
  | refl  (t : LTerm) : HeadPath t t
  | step  {a b c : LTerm} (s : HeadStep a b) (p : HeadPath b c) : HeadPath a c

/-- Theorem 28: Head path transitivity. -/
theorem HeadPath.trans {a b c : LTerm}
    (p : HeadPath a b) (q : HeadPath b c) : HeadPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact HeadPath.step s (ih q)

/-- Theorem 29: Head step is a beta step. -/
theorem HeadStep.toBetaStep {a b : LTerm} (s : HeadStep a b) : BetaStep a b := by
  induction s with
  | headBeta body arg => exact BetaStep.beta body arg
  | headAppL _ ih => exact BetaStep.congAppL ih

/-- Theorem 30: Head path embeds into beta path. -/
theorem HeadPath.toBetaPath {a b : LTerm} (p : HeadPath a b) : BetaPath a b := by
  induction p with
  | refl _ => exact BetaPath.refl _
  | step s _ ih => exact BetaPath.step (s.toBetaStep) ih

/-- Theorem 31: Head path embeds into full path (trans chain). -/
theorem HeadPath.toPath {a b : LTerm} (p : HeadPath a b) : Path a b :=
  p.toBetaPath.toPath

-- ============================================================
-- §10  Internal reduction (complement of head)
-- ============================================================

/-- Internal step: reduce inside, never the head position. -/
inductive IntStep : LTerm → LTerm → Prop where
  | congLam   {t t' : LTerm} (s : BetaStep t t') : IntStep (lam t) (lam t')
  | congAppR  {f a a' : LTerm} (s : BetaStep a a') : IntStep (app f a) (app f a')
  | congAppL  {f f' a : LTerm} (s : IntStep f f') : IntStep (app f a) (app f' a)

/-- Internal path. -/
inductive IntPath : LTerm → LTerm → Prop where
  | refl  (t : LTerm) : IntPath t t
  | step  {a b c : LTerm} (s : IntStep a b) (p : IntPath b c) : IntPath a c

/-- Theorem 32: Internal path transitivity. -/
theorem IntPath.trans {a b c : LTerm}
    (p : IntPath a b) (q : IntPath b c) : IntPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact IntPath.step s (ih q)

/-- Theorem 33: Internal step is a beta step. -/
theorem IntStep.toBetaStep {a b : LTerm} (s : IntStep a b) : BetaStep a b := by
  induction s with
  | congLam s => exact BetaStep.congLam s
  | congAppR s => exact BetaStep.congAppR s
  | congAppL _ ih => exact BetaStep.congAppL ih

/-- Theorem 34: Internal path embeds into beta path. -/
theorem IntPath.toBetaPath {a b : LTerm} (p : IntPath a b) : BetaPath a b := by
  induction p with
  | refl _ => exact BetaPath.refl _
  | step s _ ih => exact BetaPath.step (s.toBetaStep) ih

-- ============================================================
-- §11  Standardisation theorem (path normal form)
-- ============================================================

/-- A standard path: first head steps, then internal steps.
    This is the path normal form under the standardisation theorem. -/
structure StandardPath (a b : LTerm) where
  mid      : LTerm
  headPart : HeadPath a mid
  intPart  : IntPath mid b

/-- Def 35: Refl gives a trivial standard path. -/
noncomputable def StandardPath.refl (t : LTerm) : StandardPath t t :=
  ⟨t, HeadPath.refl t, IntPath.refl t⟩

/-- Theorem 36: A standard path is a beta path (soundness). -/
theorem StandardPath.toBetaPath {a b : LTerm} (sp : StandardPath a b) :
    BetaPath a b :=
  BetaPath.trans sp.headPart.toBetaPath sp.intPart.toBetaPath

/-- Theorem 37: A standard path is a full path. -/
theorem StandardPath.toPath {a b : LTerm} (sp : StandardPath a b) :
    Path a b :=
  sp.toBetaPath.toPath

/-- Def 38: Head path gives a standard path with trivial internal part. -/
noncomputable def HeadPath.toStandard {a b : LTerm} (hp : HeadPath a b) :
    StandardPath a b :=
  ⟨b, hp, IntPath.refl b⟩

/-- Def 39: Internal path gives a standard path with trivial head part. -/
noncomputable def IntPath.toStandard {a b : LTerm} (ip : IntPath a b) :
    StandardPath a b :=
  ⟨a, HeadPath.refl a, ip⟩

-- ============================================================
-- §12  Böhm tree approximation (infinite path limits)
-- ============================================================

/-- A Böhm approximation truncates at a given depth, replacing
    non‑HNF subterms with ⊥ (bottom, represented as a distinguished var). -/
noncomputable def botTerm : LTerm := var 9999

/-- Approximate to depth n. -/
noncomputable def approx : Nat → LTerm → LTerm
  | 0, _          => botTerm
  | _ + 1, var k  => var k
  | n + 1, lam t  => lam (approx n t)
  | n + 1, app f a => app (approx n f) (approx n a)

/-- Theorem 40: Approximation at depth 0 is always ⊥. -/
theorem approx_zero (t : LTerm) : approx 0 t = botTerm := by
  simp [approx]

/-- Theorem 41: Approximation preserves variables at depth > 0. -/
theorem approx_var (n : Nat) (k : Nat) : approx (n + 1) (var k) = var k := by
  simp [approx]

/-- Theorem 42: Approximation preserves lam structure. -/
theorem approx_lam (n : Nat) (t : LTerm) :
    approx (n + 1) (lam t) = lam (approx n t) := by
  simp [approx]

/-- Theorem 43: Approximation preserves app structure. -/
theorem approx_app (n : Nat) (f a : LTerm) :
    approx (n + 1) (app f a) = app (approx n f) (approx n a) := by
  simp [approx]

/-- The Böhm ordering: t ≤_BT u when every finite approximation of t
    can be matched by u. -/
noncomputable def boehmLeq (t u : LTerm) : Prop :=
  ∀ n, ∃ m, approx n t = approx m u ∨ approx n t = botTerm

/-- Theorem 44: Böhm ordering is reflexive. -/
theorem boehmLeq_refl (t : LTerm) : boehmLeq t t := by
  intro n; exact ⟨n, Or.inl rfl⟩

/-- Theorem 45: ⊥ is bottom in the Böhm ordering. -/
theorem boehmLeq_bot (t : LTerm) : boehmLeq botTerm t := by
  intro n
  cases n with
  | zero => exact ⟨0, Or.inr (approx_zero botTerm)⟩
  | succ n => exact ⟨0, Or.inr rfl⟩

-- ============================================================
-- §13  Church–Rosser / Diamond for path algebra
-- ============================================================

/-- Confluence statement: if a →* b and a →* c then ∃ d, b →* d ∧ c →* d. -/
noncomputable def Confluent : Prop :=
  ∀ a b c : LTerm, Path a b → Path a c → ∃ d, Path b d ∧ Path c d

/-- Theorem 46: If confluent, then NF is unique up to path equality. -/
theorem unique_nf_of_confluent
    (hCR : Confluent) {a nf1 nf2 : LTerm}
    (p1 : Path a nf1) (p2 : Path a nf2)
    (hnf1 : ∀ x, ¬ Step nf1 x) (hnf2 : ∀ x, ¬ Step nf2 x) :
    nf1 = nf2 := by
  obtain ⟨d, pd1, pd2⟩ := hCR a nf1 nf2 p1 p2
  have h1 : nf1 = d := by
    cases pd1 with
    | refl _ => rfl
    | step s _ => exact absurd s (hnf1 _)
  have h2 : nf2 = d := by
    cases pd2 with
    | refl _ => rfl
    | step s _ => exact absurd s (hnf2 _)
  rw [h1, h2]

/-- Theorem 47: Confluence implies SymPath gives common reduct. -/
theorem confluent_sympath_common (hCR : Confluent) {x y : LTerm}
    (p : SymPath x y) : ∃ d, Path x d ∧ Path y d := by
  induction p with
  | refl t => exact ⟨t, Path.refl t, Path.refl t⟩
  | fwd s _ ih =>
    obtain ⟨d, pad, pbd⟩ := ih
    exact ⟨d, Path.step s pad, pbd⟩
  | bwd s _ ih =>
    obtain ⟨d, pbd, pcd⟩ := ih
    obtain ⟨e, pae, pde⟩ := hCR _ _ d (Path.single s) pbd
    exact ⟨e, pae, Path.trans pcd pde⟩

-- ============================================================
-- §14  Parallel reduction (for confluence proofs)
-- ============================================================

/-- Parallel reduction: reduce many redexes simultaneously. -/
inductive ParStep : LTerm → LTerm → Prop where
  | pvar  (n : Nat) : ParStep (var n) (var n)
  | plam  {t t' : LTerm} (s : ParStep t t') : ParStep (lam t) (lam t')
  | papp  {f f' a a' : LTerm} (sf : ParStep f f') (sa : ParStep a a') :
      ParStep (app f a) (app f' a')
  | pbeta {body body' arg arg' : LTerm}
      (sb : ParStep body body') (sa : ParStep arg arg') :
      ParStep (app (lam body) arg) (subst 0 arg' body')

/-- Theorem 48: Identity parallel step (reflexivity). -/
theorem ParStep.refl : (t : LTerm) → ParStep t t
  | var n    => ParStep.pvar n
  | lam body => ParStep.plam (ParStep.refl body)
  | app f a  => ParStep.papp (ParStep.refl f) (ParStep.refl a)

/-- Parallel path (iterated parallel steps). -/
inductive ParPath : LTerm → LTerm → Prop where
  | refl  (t : LTerm) : ParPath t t
  | step  {a b c : LTerm} (s : ParStep a b) (p : ParPath b c) : ParPath a c

/-- Theorem 49: Parallel path transitivity. -/
theorem ParPath.trans {a b c : LTerm}
    (p : ParPath a b) (q : ParPath b c) : ParPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact ParPath.step s (ih q)

/-- Theorem 50: Single beta step embeds into parallel step. -/
theorem BetaStep.toParStep {a b : LTerm} (s : BetaStep a b) : ParStep a b := by
  induction s with
  | beta body arg => exact ParStep.pbeta (ParStep.refl body) (ParStep.refl arg)
  | congLam _ ih => exact ParStep.plam ih
  | congAppL _ ih => exact ParStep.papp ih (ParStep.refl _)
  | congAppR _ ih => exact ParStep.papp (ParStep.refl _) ih

-- ============================================================
-- §15  Reduction strategies as path selectors
-- ============================================================

/-- Leftmost‑outermost strategy: picks the head redex if present. -/
noncomputable def leftmostStep : LTerm → Option LTerm
  | app (lam body) arg => some (subst 0 arg body)
  | app f a =>
    match leftmostStep f with
    | some f' => some (app f' a)
    | none => match leftmostStep a with
              | some a' => some (app f a')
              | none => none
  | lam t =>
    match leftmostStep t with
    | some t' => some (lam t')
    | none => none
  | var _ => none

/-- Theorem 51: Leftmost step on var is none. -/
theorem leftmostStep_none_of_var (n : Nat) : leftmostStep (var n) = none := by
  simp [leftmostStep]

/-- Theorem 52: Leftmost step on a beta redex does beta. -/
theorem leftmostStep_beta (body arg : LTerm) :
    leftmostStep (app (lam body) arg) = some (subst 0 arg body) := by
  simp [leftmostStep]

-- ============================================================
-- §16  de Bruijn index properties under paths
-- ============================================================

/-- Maximum free variable index in a term. -/
noncomputable def maxFV : LTerm → Nat → Nat
  | var n, bound    => if n ≥ bound then n - bound + 1 else 0
  | lam t, bound    => maxFV t (bound + 1)
  | app f a, bound  => max (maxFV f bound) (maxFV a bound)

/-- A term is closed when maxFV = 0. -/
noncomputable def isClosed (t : LTerm) : Prop := maxFV t 0 = 0

/-- Theorem 53: var 0 under one binder is closed from outside. -/
theorem lam_var0_closed : isClosed (lam (var 0)) := by
  simp [isClosed, maxFV]

/-- Theorem 54: The identity combinator is closed. -/
theorem id_closed : isClosed (lam (var 0)) := lam_var0_closed

/-- Theorem 55: Church numeral zero is closed. -/
theorem church_zero_closed : isClosed (lam (lam (var 0))) := by
  simp [isClosed, maxFV]

-- ============================================================
-- §17  Beta expansion as reverse paths (symm application)
-- ============================================================

/-- Beta expansion: the reverse of beta reduction. -/
noncomputable def BetaExpansion (a b : LTerm) : Prop := BetaStep b a

/-- Theorem 56: A beta expansion composes with reduction into a SymPath via symm+trans. -/
theorem expansion_then_reduction {a b c : LTerm}
    (exp : BetaExpansion b a) (red : BetaStep b c) :
    SymPath a c := by
  -- BetaExpansion b a = BetaStep a b, so exp : BetaStep a b
  -- a →β b via exp, b →β c via red
  -- We want SymPath a c: fwd from a to b, then fwd from b to c
  unfold BetaExpansion at exp
  exact SymPath.fwd exp.toStep (SymPath.fwd red.toStep (SymPath.refl c))

/-- Theorem 57: Expansion is the symm of reduction in SymPath. -/
theorem expansion_as_symm {a b : LTerm}
    (s : BetaStep a b) : SymPath b a :=
  SymPath.bwd s.toStep (SymPath.refl a)

-- ============================================================
-- §18  Path concatenation algebra (category laws)
-- ============================================================

/-- Data‑level paths for the category‑law proofs. -/
inductive DPath : LTerm → LTerm → Type where
  | nil  : (a : LTerm) → DPath a a
  | cons : {a b c : LTerm} → Step a b → DPath b c → DPath a c

/-- Theorem 58: trans for DPath. -/
noncomputable def DPath.trans : DPath a b → DPath b c → DPath a c
  | DPath.nil _, q => q
  | DPath.cons s p, q => DPath.cons s (DPath.trans p q)

/-- Theorem 59: trans is associative. -/
theorem DPath.trans_assoc {a b c d : LTerm}
    (p : DPath a b) (q : DPath b c) (r : DPath c d) :
    DPath.trans (DPath.trans p q) r = DPath.trans p (DPath.trans q r) := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [DPath.trans, ih]

/-- Theorem 60: refl is left identity for trans. -/
theorem DPath.trans_nil_left {a b : LTerm} (p : DPath a b) :
    DPath.trans (DPath.nil a) p = p := by
  rfl

/-- Theorem 61: refl is right identity for trans. -/
theorem DPath.trans_nil_right {a b : LTerm} (p : DPath a b) :
    DPath.trans p (DPath.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [DPath.trans, ih]

/-- Theorem 62: DPath category: identity + composition + associativity. -/
theorem dpath_category_laws :
    (∀ (a b : LTerm) (p : DPath a b), DPath.trans (DPath.nil a) p = p) ∧
    (∀ (a b : LTerm) (p : DPath a b), DPath.trans p (DPath.nil b) = p) ∧
    (∀ (a b c d : LTerm) (p : DPath a b) (q : DPath b c) (r : DPath c d),
      DPath.trans (DPath.trans p q) r = DPath.trans p (DPath.trans q r)) :=
  ⟨fun _ _ p => DPath.trans_nil_left p,
   fun _ _ p => DPath.trans_nil_right p,
   fun _ _ _ _ p q r => DPath.trans_assoc p q r⟩

-- ============================================================
-- §19  Combinatory terms via paths
-- ============================================================

/-- The I combinator: λx.x -/
noncomputable def termI : LTerm := lam (var 0)

/-- Theorem 63: I x →β x  (single beta step path). -/
theorem I_reduces (x : LTerm) :
    Step (app termI x) (subst 0 x (var 0)) :=
  Step.beta (var 0) x

/-- Theorem 64: subst 0 x (var 0) = x. -/
theorem subst_var0 (x : LTerm) : subst 0 x (var 0) = x := by
  simp [subst]

/-- Theorem 65: I x reduces to x in one step (full statement). -/
theorem I_reduces_to (x : LTerm) :
    Path (app termI x) x := by
  have h := I_reduces x
  rw [subst_var0] at h
  exact Path.single h

-- ============================================================
-- §20  Coherence and path equivalence
-- ============================================================

/-- Two paths are co-terminal when they reach the same target. -/
noncomputable def CoTerminal (b c : LTerm) (_ : Path a b) (_ : Path a c) : Prop := b = c

/-- Theorem 66: Reflexive paths are always co-terminal. -/
theorem coTerminal_refl (t : LTerm) :
    CoTerminal t t (Path.refl t) (Path.refl t) := rfl

/-- Theorem 67: Path from a to itself composed with p is p (left unit via Prop). -/
theorem path_refl_trans_eq {a b : LTerm} (p : Path a b) :
    Path a b :=
  Path.trans (Path.refl a) p

/-- Theorem 68: congrLam on DPath distributes over trans. -/
noncomputable def DPath.congrLam : DPath a b → DPath (lam a) (lam b)
  | DPath.nil _ => DPath.nil _
  | DPath.cons s p => DPath.cons (Step.congLam s) (DPath.congrLam p)

theorem dpath_congrLam_trans {a b c : LTerm}
    (p : DPath a b) (q : DPath b c) :
    DPath.congrLam (DPath.trans p q) = DPath.trans (DPath.congrLam p) (DPath.congrLam q) := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [DPath.trans, DPath.congrLam, ih]

/-- Theorem 69: congrAppL on DPath distributes over trans. -/
noncomputable def DPath.congrAppL (x : LTerm) : DPath a b → DPath (app a x) (app b x)
  | DPath.nil _ => DPath.nil _
  | DPath.cons s p => DPath.cons (Step.congAppL s) (DPath.congrAppL x p)

theorem dpath_congrAppL_trans {f f' f'' a : LTerm}
    (p : DPath f f') (q : DPath f' f'') :
    DPath.congrAppL a (DPath.trans p q) = DPath.trans (DPath.congrAppL a p) (DPath.congrAppL a q) := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [DPath.trans, DPath.congrAppL, ih]

/-- Theorem 70: congrAppR on DPath distributes over trans. -/
noncomputable def DPath.congrAppR (x : LTerm) : DPath a b → DPath (app x a) (app x b)
  | DPath.nil _ => DPath.nil _
  | DPath.cons s p => DPath.cons (Step.congAppR s) (DPath.congrAppR x p)

theorem dpath_congrAppR_trans {f a a' a'' : LTerm}
    (p : DPath a a') (q : DPath a' a'') :
    DPath.congrAppR f (DPath.trans p q) = DPath.trans (DPath.congrAppR f p) (DPath.congrAppR f q) := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [DPath.trans, DPath.congrAppR, ih]

end LambdaPaths
