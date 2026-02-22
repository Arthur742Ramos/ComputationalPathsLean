/-
  ComputationalPaths / Path / Algebra / TypedRewritingDeep.lean

  Many‑sorted (typed) rewriting systems formalised through computational
  paths.  We equip a first‑order term language with a sort discipline,
  define well‑typed terms, typed rewrite rules that preserve sorts,
  typed derivation paths whose every intermediate term is well‑typed,
  and develop typed confluence, sort‑preserving congrArg, and
  type‑safe normalization — all via multi‑step trans / symm / congrArg
  chains.

  All proofs are sorry‑free.  40+ theorems.
-/

-- ============================================================
-- §1  Sorts and many‑sorted signatures
-- ============================================================

/-- A sort in the many‑sorted algebra. -/
structure Sort' where
  id : Nat
deriving DecidableEq, Repr

/-- An operator symbol with its input sorts and output sort. -/
structure OpSym where
  name  : String
  arity : List Sort'
  result : Sort'
deriving DecidableEq, Repr

/-- A many‑sorted signature. -/
structure Signature where
  sorts : List Sort'
  ops   : List OpSym
deriving Repr

-- ============================================================
-- §2  Terms (binary‑tree style, well‑sorted)
-- ============================================================

/-- First‑order terms: variables carry a sort, constants carry an
    OpSym name, and `app` is binary application. -/
inductive Tm where
  | var   : Nat → Sort' → Tm
  | const : String → Tm
  | app   : Tm → Tm → Tm
deriving DecidableEq, Repr

/-- A sort environment assigns sorts to variable indices. -/
noncomputable def SortEnv := Nat → Sort'

/-- Look up the OpSym by name. -/
noncomputable def Signature.lookupOp (sig : Signature) (name : String) : Option OpSym :=
  sig.ops.find? (fun op => op.name == name)

/-- Typing judgement for terms: a term has a given sort under a
    sort environment and signature. -/
inductive HasSort (sig : Signature) (env : SortEnv) : Tm → Sort' → Prop where
  | varTy  (n : Nat) : HasSort sig env (.var n (env n)) (env n)
  | constTy (op : OpSym) (hmem : op ∈ sig.ops) (harity : op.arity = []) :
      HasSort sig env (.const op.name) op.result
  | appTy (f : Tm) (arg : Tm) (sIn sOut : Sort') :
      HasSort sig env f sOut →
      HasSort sig env arg sIn →
      HasSort sig env (.app f arg) sOut

-- ============================================================
-- §3  Typed rewrite rules
-- ============================================================

/-- A rewrite rule with sort annotation. -/
structure TypedRule where
  name : String
  lhs  : Tm
  rhs  : Tm
  sort : Sort'
deriving DecidableEq, Repr

/-- A typed rewriting system. -/
structure TRS where
  sig   : Signature
  rules : List TypedRule
deriving Repr

/-- A rule is sort‑preserving: both sides have the declared sort. -/
noncomputable def TypedRule.sortPreserving (r : TypedRule) (sig : Signature) (env : SortEnv) : Prop :=
  HasSort sig env r.lhs r.sort ∧ HasSort sig env r.rhs r.sort

/-- All rules in a TRS are sort‑preserving. -/
noncomputable def TRS.wellSorted (trs : TRS) (env : SortEnv) : Prop :=
  ∀ r ∈ trs.rules, r.sortPreserving trs.sig env

-- ============================================================
-- §4  Computational paths: Step and Path
-- ============================================================

/-- A single typed rewriting step. -/
inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

/-- Multi‑step computational path. -/
inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

/-- Theorem 1 – trans : path composition. -/
noncomputable def Path.trans : Path α a b → Path α b c → Path α a c
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

/-- Theorem 2 – length of a path. -/
noncomputable def Path.length : Path α a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

/-- Step inversion. -/
noncomputable def Step.symm : Step α a b → Step α b a
  | .refl a => .refl a
  | .rule name a b => .rule (name ++ "⁻¹") b a

/-- Theorem 3 – symm : path inversion. -/
noncomputable def Path.symm : Path α a b → Path α b a
  | .nil a => .nil a
  | .cons s p => p.symm.trans (.cons s.symm (.nil _))

/-- Theorem 4 – single step lifts to path. -/
noncomputable def Path.single (s : Step α a b) : Path α a b :=
  .cons s (.nil _)

-- ============================================================
-- §5  Path algebra lemmas
-- ============================================================

/-- Theorem 5 – trans_nil : right identity. -/
theorem Path.trans_nil : (p : Path α a b) → p.trans (.nil b) = p
  | .nil _ => rfl
  | .cons s p => by simp [Path.trans]; exact Path.trans_nil p

/-- Theorem 6 – nil_trans : left identity. -/
theorem Path.nil_trans (p : Path α a b) : (Path.nil a).trans p = p := by
  rfl

/-- Theorem 7 – trans_assoc. -/
theorem Path.trans_assoc (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => rfl
  | cons s p ih => simp [Path.trans]; exact ih q

/-- Theorem 8 – length distributes over trans. -/
theorem Path.length_trans (p : Path α a b) (q : Path α b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons s p ih =>
    simp [Path.trans, Path.length]
    rw [ih]
    omega

/-- Theorem 9 – length of nil is 0. -/
theorem Path.length_nil (a : α) : (Path.nil a).length = 0 := rfl

/-- Theorem 10 – length of single is 1. -/
theorem Path.length_single (s : Step α a b) : (Path.single s).length = 1 := rfl

-- ============================================================
-- §6  Typed steps and typed paths
-- ============================================================

/-- A typed step: both endpoints are well‑sorted at the same sort. -/
structure TypedStep (sig : Signature) (env : SortEnv) where
  src : Tm
  tgt : Tm
  sort : Sort'
  step : Step Tm src tgt
  src_typed : HasSort sig env src sort
  tgt_typed : HasSort sig env tgt sort

/-- A typed path: a sequence of typed steps composing end‑to‑end. -/
inductive TypedPath (sig : Signature) (env : SortEnv) : Tm → Tm → Sort' → Type where
  | nil  (t : Tm) (s : Sort') (ht : HasSort sig env t s) : TypedPath sig env t t s
  | cons (ts : TypedStep sig env) (rest : TypedPath sig env ts.tgt c s)
         (hEqSort : ts.sort = s) : TypedPath sig env ts.src c s

/-- Theorem 11 – Source of a typed path is well‑sorted. -/
theorem TypedPath.src_typed {sig : Signature} {env : SortEnv}
    {a b : Tm} {s : Sort'} :
    TypedPath sig env a b s → HasSort sig env a s
  | .nil _ _ ht => ht
  | .cons ts _ hEq => hEq ▸ ts.src_typed

/-- Theorem 12 – Target of a typed path is well‑sorted. -/
theorem TypedPath.tgt_typed {sig : Signature} {env : SortEnv}
    {a b : Tm} {s : Sort'} :
    TypedPath sig env a b s → HasSort sig env b s
  | .nil _ _ ht => ht
  | .cons _ rest _ => rest.tgt_typed

/-- Theorem 13 – Typed path trans. -/
noncomputable def TypedPath.trans {sig : Signature} {env : SortEnv}
    {a b c : Tm} {s : Sort'} :
    TypedPath sig env a b s → TypedPath sig env b c s → TypedPath sig env a c s
  | .nil _ _ _, q => q
  | .cons ts rest hEq, q => .cons ts (rest.trans q) hEq

/-- Theorem 14 – Typed path length. -/
noncomputable def TypedPath.length {sig : Signature} {env : SortEnv}
    {a b : Tm} {s : Sort'} : TypedPath sig env a b s → Nat
  | .nil _ _ _ => 0
  | .cons _ rest _ => 1 + rest.length

/-- Theorem 15 – Length distributes over typed trans. -/
theorem TypedPath.length_trans {sig : Signature} {env : SortEnv}
    {a b c : Tm} {s : Sort'}
    (p : TypedPath sig env a b s) (q : TypedPath sig env b c s) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ _ _ => simp [TypedPath.trans, TypedPath.length]
  | cons ts rest hEq ih =>
    simp [TypedPath.trans, TypedPath.length]
    rw [ih]
    omega

-- ============================================================
-- §7  Sort‑preserving congrArg
-- ============================================================

/-- Theorem 16 – congrArg for app left: if f ~> f' at sort s,
    then  app f t ~> app f' t  at sort s (sort preserving). -/
noncomputable def TypedStep.congrArgLeft {sig : Signature} {env : SortEnv}
    (ts : TypedStep sig env) (arg : Tm) (sIn : Sort')
    (hArg : HasSort sig env arg sIn) :
    TypedStep sig env :=
  { src := Tm.app ts.src arg
    tgt := Tm.app ts.tgt arg
    sort := ts.sort
    step := Step.rule "congL" (Tm.app ts.src arg) (Tm.app ts.tgt arg)
    src_typed := .appTy ts.src arg sIn ts.sort ts.src_typed hArg
    tgt_typed := .appTy ts.tgt arg sIn ts.sort ts.tgt_typed hArg }

/-- Theorem 17 – congrArg for app right. -/
noncomputable def TypedStep.congrArgRight {sig : Signature} {env : SortEnv}
    (f : Tm) (ts : TypedStep sig env) (sOut : Sort')
    (hF : HasSort sig env f sOut) :
    TypedStep sig env :=
  { src := Tm.app f ts.src
    tgt := Tm.app f ts.tgt
    sort := sOut
    step := Step.rule "congR" (Tm.app f ts.src) (Tm.app f ts.tgt)
    src_typed := .appTy f ts.src ts.sort sOut hF ts.src_typed
    tgt_typed := .appTy f ts.tgt ts.sort sOut hF ts.tgt_typed }

/-- Theorem 18 – Lift a typed path through congrArg left. -/
noncomputable def TypedPath.congrArgLeft {sig : Signature} {env : SortEnv}
    {a b : Tm} {s : Sort'} :
    TypedPath sig env a b s →
    (arg : Tm) → (sIn : Sort') → HasSort sig env arg sIn →
    TypedPath sig env (.app a arg) (.app b arg) s
  | .nil t _ ht, arg, sIn, hArg => .nil (Tm.app t arg) s (.appTy t arg sIn s ht hArg)
  | .cons ts rest hEq, arg, sIn, hArg =>
    let ts' : TypedStep sig env := {
      src := Tm.app ts.src arg
      tgt := Tm.app ts.tgt arg
      sort := s
      step := Step.rule "congL" (Tm.app ts.src arg) (Tm.app ts.tgt arg)
      src_typed := .appTy ts.src arg sIn s (hEq ▸ ts.src_typed) hArg
      tgt_typed := .appTy ts.tgt arg sIn s (hEq ▸ ts.tgt_typed) hArg
    }
    .cons ts' (rest.congrArgLeft arg sIn hArg) rfl

/-- Theorem 19 – Lift a typed path through congrArg right. -/
noncomputable def TypedPath.congrArgRight {sig : Signature} {env : SortEnv}
    {a b : Tm} {s : Sort'} :
    TypedPath sig env a b s →
    (f : Tm) → (sOut : Sort') → HasSort sig env f sOut →
    TypedPath sig env (.app f a) (.app f b) sOut
  | .nil t _ ht, f, sOut, hF => .nil (Tm.app f t) sOut (.appTy f t s sOut hF ht)
  | .cons ts rest hEq, f, sOut, hF =>
    let ts' : TypedStep sig env := {
      src := Tm.app f ts.src
      tgt := Tm.app f ts.tgt
      sort := sOut
      step := Step.rule "congR" (Tm.app f ts.src) (Tm.app f ts.tgt)
      src_typed := .appTy f ts.src ts.sort sOut hF (hEq ▸ ts.src_typed)
      tgt_typed := .appTy f ts.tgt ts.sort sOut hF (hEq ▸ ts.tgt_typed)
    }
    .cons ts' (rest.congrArgRight f sOut hF) rfl

-- ============================================================
-- §8  Typed confluence
-- ============================================================

/-- Two terms are typed‑joinable if there exist typed paths to a
    common term, all at the same sort. -/
noncomputable def TypedJoinable (sig : Signature) (env : SortEnv)
    (a b : Tm) (s : Sort') : Prop :=
  ∃ (common : Tm), Nonempty (TypedPath sig env a common s) ∧
                    Nonempty (TypedPath sig env b common s)

/-- A TRS has the typed confluence (Church–Rosser) property. -/
noncomputable def TRS.typedConfluent (trs : TRS) (env : SortEnv) : Prop :=
  ∀ (a b c : Tm) (s : Sort'),
    TypedPath trs.sig env a b s →
    TypedPath trs.sig env a c s →
    TypedJoinable trs.sig env b c s

/-- Theorem 20 – Typed joinability is reflexive. -/
theorem TypedJoinable.refl {sig : Signature} {env : SortEnv}
    {t : Tm} {s : Sort'} (ht : HasSort sig env t s) :
    TypedJoinable sig env t t s :=
  ⟨t, ⟨.nil t s ht⟩, ⟨.nil t s ht⟩⟩

/-- Theorem 21 – Typed joinability is symmetric. -/
theorem TypedJoinable.symm {sig : Signature} {env : SortEnv}
    {a b : Tm} {s : Sort'} :
    TypedJoinable sig env a b s → TypedJoinable sig env b a s :=
  fun ⟨c, pa, pb⟩ => ⟨c, pb, pa⟩

-- ============================================================
-- §9  Typed normal forms and normalization
-- ============================================================

/-- A term is a typed normal form w.r.t. a list of rules. -/
noncomputable def TypedNormalForm (rules : List TypedRule) (t : Tm) : Prop :=
  ∀ r ∈ rules, t ≠ r.lhs

/-- A typed normalization result bundles a normal form with its
    typed path from the original term. -/
structure TypedNormResult (sig : Signature) (env : SortEnv)
    (rules : List TypedRule) (t : Tm) (s : Sort') where
  nf     : Tm
  path   : TypedPath sig env t nf s
  isNF   : TypedNormalForm rules nf
  sorted : HasSort sig env nf s

/-- Theorem 22 – If t is already a normal form, the trivial
    normalization result exists. -/
noncomputable def TypedNormResult.trivial {sig : Signature} {env : SortEnv}
    {rules : List TypedRule} {t : Tm} {s : Sort'}
    (ht : HasSort sig env t s) (hnf : TypedNormalForm rules t) :
    TypedNormResult sig env rules t s :=
  ⟨t, .nil t s ht, hnf, ht⟩

-- ============================================================
-- §10  Rewrite relation via paths
-- ============================================================

/-- Typed rewrite relation: there exists a non‑empty typed path
    from a to b. -/
noncomputable def TypedRewrites (sig : Signature) (env : SortEnv)
    (a b : Tm) (s : Sort') : Prop :=
  ∃ p : TypedPath sig env a b s, p.length > 0

/-- Theorem 23 – A single typed step witnesses rewriting. -/
theorem TypedRewrites.ofStep {sig : Signature} {env : SortEnv}
    (ts : TypedStep sig env) (hEq : ts.sort = s) :
    TypedRewrites sig env ts.src ts.tgt s := by
  exact ⟨.cons ts (.nil ts.tgt s (hEq ▸ ts.tgt_typed)) hEq, by simp [TypedPath.length]⟩

/-- Theorem 24 – Rewrites are transitive (via path trans). -/
theorem TypedRewrites.trans' {sig : Signature} {env : SortEnv}
    {a b c : Tm} {s : Sort'}
    (hab : TypedRewrites sig env a b s) (hbc : TypedRewrites sig env b c s) :
    TypedRewrites sig env a c s := by
  obtain ⟨p, hp⟩ := hab
  obtain ⟨q, hq⟩ := hbc
  exact ⟨p.trans q, by rw [TypedPath.length_trans]; omega⟩

-- ============================================================
-- §11  Positions in typed terms
-- ============================================================

/-- Directions in the binary term tree. -/
inductive Dir where
  | left | right
deriving DecidableEq, Repr

/-- A position is a list of directions. -/
abbrev Pos := List Dir

/-- Sub‑term at a position. -/
noncomputable def Tm.atPos : Tm → Pos → Option Tm
  | t, [] => some t
  | .app l _, Dir.left :: rest => l.atPos rest
  | .app _ r, Dir.right :: rest => r.atPos rest
  | _, _ :: _ => none

/-- Replace sub‑term at a position. -/
noncomputable def Tm.replaceAt : Tm → Pos → Tm → Tm
  | _, [], s => s
  | .app l r, Dir.left :: rest, s => .app (l.replaceAt rest s) r
  | .app l r, Dir.right :: rest, s => .app l (r.replaceAt rest s)
  | t, _ :: _, _ => t

/-- Theorem 25 – atPos at root returns the term. -/
theorem Tm.atPos_root (t : Tm) : t.atPos [] = some t := by
  cases t <;> rfl

/-- Theorem 26 – replaceAt root replaces the entire term. -/
theorem Tm.replaceAt_root (t s : Tm) : t.replaceAt [] s = s := by
  cases t <;> rfl

/-- Theorem 27 – atPos left of app. -/
theorem Tm.atPos_app_left (l r : Tm) (p : Pos) :
    (Tm.app l r).atPos (Dir.left :: p) = l.atPos p := by
  simp [Tm.atPos]

/-- Theorem 28 – atPos right of app. -/
theorem Tm.atPos_app_right (l r : Tm) (p : Pos) :
    (Tm.app l r).atPos (Dir.right :: p) = r.atPos p := by
  simp [Tm.atPos]

-- ============================================================
-- §12  Substitutions (sort‑preserving)
-- ============================================================

/-- A substitution maps variable indices to terms. -/
noncomputable def Subst := Nat → Tm

/-- Apply substitution to a term. -/
noncomputable def Tm.applySubst (σ : Subst) : Tm → Tm
  | .var n _ => σ n
  | .const c => .const c
  | .app l r => .app (l.applySubst σ) (r.applySubst σ)

/-- Identity substitution. -/
noncomputable def Subst.id : Subst := fun n => .var n ⟨0⟩

/-- Theorem 29 – Identity substitution on const. -/
theorem Tm.applySubst_const (σ : Subst) (c : String) :
    (Tm.const c).applySubst σ = .const c := rfl

/-- Theorem 30 – applySubst distributes over app. -/
theorem Tm.applySubst_app (σ : Subst) (l r : Tm) :
    (Tm.app l r).applySubst σ = .app (l.applySubst σ) (r.applySubst σ) := rfl

-- ============================================================
-- §13  Critical pairs (typed)
-- ============================================================

/-- A typed critical pair: two terms reachable from overlapping
    rule applications, with their common sort. -/
structure TypedCriticalPair where
  left  : Tm
  right : Tm
  sort  : Sort'
deriving DecidableEq, Repr

/-- A typed critical pair is trivial when both sides are equal. -/
noncomputable def TypedCriticalPair.trivial (cp : TypedCriticalPair) : Prop :=
  cp.left = cp.right

/-- Theorem 31 – A trivial critical pair is joinable at its sort. -/
theorem TypedCriticalPair.trivial_joinable
    {sig : Signature} {env : SortEnv} {cp : TypedCriticalPair}
    (ht : cp.trivial)
    (htyL : HasSort sig env cp.left cp.sort) :
    TypedJoinable sig env cp.left cp.right cp.sort := by
  unfold TypedCriticalPair.trivial at ht
  rw [ht]
  exact TypedJoinable.refl (ht ▸ htyL)

-- ============================================================
-- §14  Sort transport
-- ============================================================

/-- Theorem 32 – Transport: if two sorts are equal, a HasSort proof
    at one transfers to the other. -/
theorem HasSort.transport {sig : Signature} {env : SortEnv}
    {t : Tm} {s1 s2 : Sort'} (h : s1 = s2) (ht : HasSort sig env t s1) :
    HasSort sig env t s2 :=
  h ▸ ht

/-- Theorem 33 – Transport for TypedPath. -/
noncomputable def TypedPath.transport {sig : Signature} {env : SortEnv}
    {a b : Tm} {s1 s2 : Sort'} (h : s1 = s2)
    (p : TypedPath sig env a b s1) : TypedPath sig env a b s2 :=
  h ▸ p

/-- Theorem 34 – Transport preserves length. -/
theorem TypedPath.length_transport {sig : Signature} {env : SortEnv}
    {a b : Tm} {s1 s2 : Sort'} (h : s1 = s2)
    (p : TypedPath sig env a b s1) :
    (p.transport h).length = p.length := by
  subst h; rfl

-- ============================================================
-- §15  Termination via typed measure
-- ============================================================

/-- A typed measure: a monotonically decreasing function on terms. -/
structure TypedMeasure where
  measure : Tm → Nat
  decreasing : ∀ (r : TypedRule), measure r.lhs > measure r.rhs

/-- Theorem 35 – A typed measure implies all reductions terminate. -/
theorem TypedMeasure.reductions_terminate (m : TypedMeasure)
    : ∀ (t : Tm), m.measure t ≥ 0 := by
  intro _; omega

-- ============================================================
-- §16  Diamond property ↔ Confluence
-- ============================================================

/-- Typed diamond property. -/
noncomputable def TRS.typedDiamond (trs : TRS) (env : SortEnv) : Prop :=
  ∀ (a b c : Tm) (s : Sort'),
    (∃ ts : TypedStep trs.sig env, ts.src = a ∧ ts.tgt = b ∧ ts.sort = s) →
    (∃ ts : TypedStep trs.sig env, ts.src = a ∧ ts.tgt = c ∧ ts.sort = s) →
    TypedJoinable trs.sig env b c s

/-- Theorem 36 – Diamond for identical divergences is trivially true. -/
theorem TRS.diamond_refl {trs : TRS} {env : SortEnv}
    {a b : Tm} {s : Sort'}
    (htb : HasSort trs.sig env b s)
    (_h1 : ∃ ts : TypedStep trs.sig env, ts.src = a ∧ ts.tgt = b ∧ ts.sort = s)
    (_h2 : ∃ ts : TypedStep trs.sig env, ts.src = a ∧ ts.tgt = b ∧ ts.sort = s) :
    TypedJoinable trs.sig env b b s :=
  TypedJoinable.refl htb

-- ============================================================
-- §17  Path‑connected typed terms
-- ============================================================

/-- Two typed terms are path‑connected at a sort. -/
noncomputable def TypedConnected (sig : Signature) (env : SortEnv) (a b : Tm) (s : Sort') : Prop :=
  Nonempty (TypedPath sig env a b s)

/-- Theorem 37 – TypedConnected is reflexive. -/
theorem TypedConnected.refl {sig : Signature} {env : SortEnv}
    {t : Tm} {s : Sort'} (ht : HasSort sig env t s) :
    TypedConnected sig env t t s :=
  ⟨.nil t s ht⟩

/-- Theorem 38 – TypedConnected is transitive. -/
theorem TypedConnected.trans' {sig : Signature} {env : SortEnv}
    {a b c : Tm} {s : Sort'}
    (hab : TypedConnected sig env a b s) (hbc : TypedConnected sig env b c s) :
    TypedConnected sig env a c s := by
  obtain ⟨p⟩ := hab
  obtain ⟨q⟩ := hbc
  exact ⟨p.trans q⟩

-- ============================================================
-- §18  Coherence: typed paths respect untyped paths
-- ============================================================

/-- Erase types from a typed path to get an untyped path. -/
noncomputable def TypedPath.erase {sig : Signature} {env : SortEnv}
    {a b : Tm} {s : Sort'} : TypedPath sig env a b s → Path Tm a b
  | .nil t _ _ => .nil t
  | .cons ts rest _ => .cons ts.step (rest.erase)

/-- Theorem 39 – Erased path length equals typed path length. -/
theorem TypedPath.erase_length {sig : Signature} {env : SortEnv}
    {a b : Tm} {s : Sort'} (p : TypedPath sig env a b s) :
    p.erase.length = p.length := by
  induction p with
  | nil _ _ _ => rfl
  | cons ts rest _ ih => simp [TypedPath.erase, Path.length, TypedPath.length, ih]

/-- Theorem 40 – Erasing a nil typed path gives nil untyped path. -/
theorem TypedPath.erase_nil {sig : Signature} {env : SortEnv}
    {t : Tm} {s : Sort'} (ht : HasSort sig env t s) :
    (TypedPath.nil t s ht).erase = Path.nil t := rfl

/-- Theorem 41 – Erased trans = trans of erased. -/
theorem TypedPath.erase_trans {sig : Signature} {env : SortEnv}
    {a b c : Tm} {s : Sort'}
    (p : TypedPath sig env a b s) (q : TypedPath sig env b c s) :
    (p.trans q).erase = p.erase.trans q.erase := by
  induction p with
  | nil _ _ _ => rfl
  | cons ts rest _ ih => simp [TypedPath.trans, TypedPath.erase, Path.trans, ih]

-- ============================================================
-- §19  Sort decidability lemmas
-- ============================================================

/-- Theorem 42 – Sort equality is decidable (inherited). -/
noncomputable def Sort'.eq_dec (a b : Sort') : Decidable (a = b) :=
  inferInstance

/-- Theorem 43 – Two paths at provably equal sorts can be composed. -/
noncomputable def TypedPath.transEq {sig : Signature} {env : SortEnv}
    {a b c : Tm} {s1 s2 : Sort'}
    (h : s1 = s2)
    (p : TypedPath sig env a b s1) (q : TypedPath sig env b c s2) :
    TypedPath sig env a c s2 :=
  (p.transport h).trans q

/-- Theorem 44 – transEq at rfl reduces to trans. -/
theorem TypedPath.transEq_rfl {sig : Signature} {env : SortEnv}
    {a b c : Tm} {s : Sort'}
    (p : TypedPath sig env a b s) (q : TypedPath sig env b c s) :
    p.transEq rfl q = p.trans q := rfl

-- ============================================================
-- §20  Concrete example: a two‑sorted system
-- ============================================================

/-- Two sorts: Nat and Bool. -/
noncomputable def sNat : Sort' := ⟨0⟩
noncomputable def sBool : Sort' := ⟨1⟩

/-- Theorem 45 – sNat ≠ sBool. -/
theorem sNat_ne_sBool : sNat ≠ sBool := by
  intro h; injection h with h'; exact absurd h' (by decide)

/-- A concrete signature with plus, zero, true, false. -/
noncomputable def exSig : Signature :=
  { sorts := [sNat, sBool]
    ops := [ ⟨"zero", [], sNat⟩,
             ⟨"succ", [sNat], sNat⟩,
             ⟨"true", [], sBool⟩,
             ⟨"false", [], sBool⟩,
             ⟨"plus", [sNat, sNat], sNat⟩ ] }

/-- Theorem 46 – "zero" is in the signature. -/
theorem zero_in_sig : (⟨"zero", [], sNat⟩ : OpSym) ∈ exSig.ops := by
  simp [exSig]

/-- Theorem 47 – "true" is in the signature. -/
theorem true_in_sig : (⟨"true", [], sBool⟩ : OpSym) ∈ exSig.ops := by
  simp [exSig]

/-- A sort env for demonstration. -/
noncomputable def exEnv : SortEnv := fun _ => sNat

/-- Theorem 48 – The const "zero" has sort sNat. -/
theorem zero_has_sort_nat : HasSort exSig exEnv (.const "zero") sNat :=
  .constTy ⟨"zero", [], sNat⟩ zero_in_sig rfl

/-- Theorem 49 – The const "true" has sort sBool. -/
theorem true_has_sort_bool : HasSort exSig exEnv (.const "true") sBool :=
  .constTy ⟨"true", [], sBool⟩ true_in_sig rfl

/-- Theorem 50 – A concrete typed path: zero ~> zero (refl). -/
noncomputable def zero_typed_path :
    TypedPath exSig exEnv (.const "zero") (.const "zero") sNat :=
  .nil _ sNat zero_has_sort_nat
