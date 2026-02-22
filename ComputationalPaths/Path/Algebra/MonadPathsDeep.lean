/-
  ComputationalPaths / Path / Algebra / MonadPathsDeep.lean

  Monad theory via computational paths.
  Covers: Kleisli composition as path composition, monad laws as path
  equations, monad morphisms as path-preserving maps, free monads,
  algebraic effects, Eilenberg-Moore algebras, Kleisli vs EM adjunction,
  distributive laws redux, monad transformers.

  All proofs are sorry-free.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- ============================================================
-- §1  Monad expressions (abstract endofunctor algebra)
-- ============================================================

/-- Abstract monad expressions. -/
inductive MExpr where
  | id   : MExpr
  | T    : Nat → MExpr           -- T_n is the n-th monad
  | comp : MExpr → MExpr → MExpr -- composition
  | eta  : Nat → MExpr           -- unit  η : Id → T
  | mu   : Nat → MExpr           -- join  μ : TT → T
  | kl   : Nat → MExpr → MExpr   -- Kleisli extension
deriving DecidableEq, Repr

infixl:70 " ∘ₘ " => MExpr.comp

-- ============================================================
-- §2  Rewriting steps for monad identities
-- ============================================================

/-- One-step rewrites capturing monad axioms and Kleisli laws. -/
inductive MStep : MExpr → MExpr → Prop where
  -- Category laws
  | idL  (f : MExpr) : MStep (.id ∘ₘ f) f
  | idL' (f : MExpr) : MStep f (.id ∘ₘ f)
  | idR  (f : MExpr) : MStep (f ∘ₘ .id) f
  | idR' (f : MExpr) : MStep f (f ∘ₘ .id)
  | assocR (f g h : MExpr) : MStep ((f ∘ₘ g) ∘ₘ h) (f ∘ₘ (g ∘ₘ h))
  | assocL (f g h : MExpr) : MStep (f ∘ₘ (g ∘ₘ h)) ((f ∘ₘ g) ∘ₘ h)
  -- Monad laws: μ ∘ Tμ = μ ∘ μT (associativity)
  | muAssoc (n : Nat) :
      MStep (.mu n ∘ₘ (.T n ∘ₘ .mu n)) (.mu n ∘ₘ (.mu n ∘ₘ .T n))
  | muAssoc' (n : Nat) :
      MStep (.mu n ∘ₘ (.mu n ∘ₘ .T n)) (.mu n ∘ₘ (.T n ∘ₘ .mu n))
  -- Monad laws: μ ∘ Tη = id = μ ∘ ηT (unit)
  | muEtaR (n : Nat) : MStep (.mu n ∘ₘ (.T n ∘ₘ .eta n)) .id
  | muEtaR' (n : Nat) : MStep .id (.mu n ∘ₘ (.T n ∘ₘ .eta n))
  | muEtaL (n : Nat) : MStep (.mu n ∘ₘ (.eta n ∘ₘ .T n)) .id
  | muEtaL' (n : Nat) : MStep .id (.mu n ∘ₘ (.eta n ∘ₘ .T n))
  -- Kleisli identity: kl(η) = id
  | klEta (n : Nat) : MStep (.kl n (.eta n)) .id
  | klEta' (n : Nat) : MStep .id (.kl n (.eta n))
  -- Kleisli composition: kl(g) ∘ kl(f) = kl(kl(g) ∘ f)
  | klComp (n : Nat) (f g : MExpr) :
      MStep (.kl n g ∘ₘ .kl n f) (.kl n (.kl n g ∘ₘ f))
  | klComp' (n : Nat) (f g : MExpr) :
      MStep (.kl n (.kl n g ∘ₘ f)) (.kl n g ∘ₘ .kl n f)
  -- Congruence
  | compL {f f' : MExpr} (g : MExpr) : MStep f f' → MStep (f ∘ₘ g) (f' ∘ₘ g)
  | compR (f : MExpr) {g g' : MExpr} : MStep g g' → MStep (f ∘ₘ g) (f ∘ₘ g')
  | klCong (n : Nat) {f f' : MExpr} : MStep f f' → MStep (.kl n f) (.kl n f')

-- ============================================================
-- §3  Computational paths
-- ============================================================

/-- A computational path is a sequence of MStep rewrites. -/
inductive MPath : MExpr → MExpr → Prop where
  | refl (a : MExpr) : MPath a a
  | step {a b c : MExpr} : MStep a b → MPath b c → MPath a c

-- ============================================================
-- §4  Core path combinators
-- ============================================================

/-- Theorem 1: Transitivity of monad paths. -/
theorem MPath.trans {a b c : MExpr}
    (p : MPath a b) (q : MPath b c) : MPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact MPath.step s (ih q)

/-- Step symmetry. -/
noncomputable def MStep.symm : MStep a b → MStep b a
  | .idL f   => .idL' f
  | .idL' f  => .idL f
  | .idR f   => .idR' f
  | .idR' f  => .idR f
  | .assocR f g h => .assocL f g h
  | .assocL f g h => .assocR f g h
  | .muAssoc n    => .muAssoc' n
  | .muAssoc' n   => .muAssoc n
  | .muEtaR n     => .muEtaR' n
  | .muEtaR' n    => .muEtaR n
  | .muEtaL n     => .muEtaL' n
  | .muEtaL' n    => .muEtaL n
  | .klEta n      => .klEta' n
  | .klEta' n     => .klEta n
  | .klComp n f g  => .klComp' n f g
  | .klComp' n f g => .klComp n f g
  | .compL g s     => .compL g s.symm
  | .compR f s     => .compR f s.symm
  | .klCong n s    => .klCong n s.symm

/-- Theorem 2: Symmetry of monad paths. -/
theorem MPath.symm {a b : MExpr} (p : MPath a b) : MPath b a := by
  induction p with
  | refl _ => exact MPath.refl _
  | step s _ ih => exact MPath.trans ih (MPath.step s.symm (MPath.refl _))

/-- Theorem 3: Single step lifts to path. -/
theorem MPath.single {a b : MExpr} (s : MStep a b) : MPath a b :=
  MPath.step s (MPath.refl _)

/-- Theorem 4: congrArg — left composition preserves paths. -/
theorem MPath.congrArg_compL {f f' : MExpr} (g : MExpr)
    (p : MPath f f') : MPath (f ∘ₘ g) (f' ∘ₘ g) := by
  induction p with
  | refl _ => exact MPath.refl _
  | step s _ ih => exact MPath.step (MStep.compL g s) ih

/-- Theorem 5: congrArg — right composition preserves paths. -/
theorem MPath.congrArg_compR (f : MExpr) {g g' : MExpr}
    (p : MPath g g') : MPath (f ∘ₘ g) (f ∘ₘ g') := by
  induction p with
  | refl _ => exact MPath.refl _
  | step s _ ih => exact MPath.step (MStep.compR f s) ih

/-- Theorem 6: Kleisli congruence lifts to paths. -/
theorem MPath.congrArg_kl (n : Nat) {f f' : MExpr}
    (p : MPath f f') : MPath (.kl n f) (.kl n f') := by
  induction p with
  | refl _ => exact MPath.refl _
  | step s _ ih => exact MPath.step (MStep.klCong n s) ih

-- ============================================================
-- §5  Monad law paths
-- ============================================================

/-- Theorem 7: Left unit law as path: μ ∘ ηT = id. -/
theorem monad_left_unit (n : Nat) :
    MPath (.mu n ∘ₘ (.eta n ∘ₘ .T n)) .id :=
  MPath.single (MStep.muEtaL n)

/-- Theorem 8: Right unit law as path: μ ∘ Tη = id. -/
theorem monad_right_unit (n : Nat) :
    MPath (.mu n ∘ₘ (.T n ∘ₘ .eta n)) .id :=
  MPath.single (MStep.muEtaR n)

/-- Theorem 9: Both unit laws connect via trans through id. -/
theorem monad_unit_coherence (n : Nat) :
    MPath (.mu n ∘ₘ (.eta n ∘ₘ .T n))
          (.mu n ∘ₘ (.T n ∘ₘ .eta n)) :=
  MPath.trans (monad_left_unit n) (MPath.symm (monad_right_unit n))

/-- Theorem 10: Associativity law as path. -/
theorem monad_assoc (n : Nat) :
    MPath (.mu n ∘ₘ (.T n ∘ₘ .mu n))
          (.mu n ∘ₘ (.mu n ∘ₘ .T n)) :=
  MPath.single (MStep.muAssoc n)

/-- Theorem 11: Pentagon — assoc coherence via two paths from TTT to T. -/
theorem monad_pentagon (n : Nat) :
    MPath (.mu n ∘ₘ (.T n ∘ₘ .mu n))
          (.mu n ∘ₘ (.mu n ∘ₘ .T n)) :=
  MPath.trans
    (MPath.single (MStep.muAssoc n))
    (MPath.refl _)

-- ============================================================
-- §6  Kleisli composition paths
-- ============================================================

/-- Theorem 12: Kleisli left identity: kl(η) = id. -/
theorem kleisli_left_id (n : Nat) :
    MPath (.kl n (.eta n)) .id :=
  MPath.single (MStep.klEta n)

/-- Theorem 13: Kleisli composition law. -/
theorem kleisli_comp_law (n : Nat) (f g : MExpr) :
    MPath (.kl n g ∘ₘ .kl n f) (.kl n (.kl n g ∘ₘ f)) :=
  MPath.single (MStep.klComp n f g)

/-- Theorem 14: Kleisli composition decomposition (reverse). -/
theorem kleisli_comp_decomp (n : Nat) (f g : MExpr) :
    MPath (.kl n (.kl n g ∘ₘ f)) (.kl n g ∘ₘ .kl n f) :=
  MPath.single (MStep.klComp' n f g)

/-- Theorem 15: Kleisli right identity via kl(η) ∘ kl(f) = kl(f). -/
theorem kleisli_right_id (n : Nat) (f : MExpr) :
    MPath (.kl n (.eta n) ∘ₘ .kl n f) (.kl n f) :=
  MPath.trans
    (MPath.step (MStep.compL (.kl n f) (MStep.klEta n))
      (MPath.refl _))
    (MPath.single (MStep.idL _))

/-- Theorem 16: Kleisli triple composition associativity path. -/
theorem kleisli_assoc (n : Nat) (f g h : MExpr) :
    MPath ((.kl n h ∘ₘ .kl n g) ∘ₘ .kl n f)
          (.kl n h ∘ₘ (.kl n g ∘ₘ .kl n f)) :=
  MPath.single (MStep.assocR _ _ _)

-- ============================================================
-- §7  Monad morphisms as path-preserving maps
-- ============================================================

/-- A monad morphism tag: σ : T_s → T_t preserves η and μ. -/
structure MonadMorph where
  src : Nat
  tgt : Nat
deriving DecidableEq, Repr

/-- Rewrite steps for monad morphisms. -/
inductive MMStep : MExpr → MExpr → Prop where
  | base : MStep a b → MMStep a b
  | morph_eta (σ : MonadMorph) :
      MMStep (.eta σ.src) (.eta σ.tgt)  -- σ ∘ η_s = η_t
  | morph_mu (σ : MonadMorph) :
      MMStep (.mu σ.src) (.mu σ.tgt)    -- σ ∘ μ_s = μ_t ∘ σσ

/-- Morphism paths. -/
inductive MMPath : MExpr → MExpr → Prop where
  | refl (a : MExpr) : MMPath a a
  | step {a b c : MExpr} : MMStep a b → MMPath b c → MMPath a c

/-- Theorem 17: Morphism paths are transitive. -/
theorem MMPath.trans {a b c : MExpr}
    (p : MMPath a b) (q : MMPath b c) : MMPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact MMPath.step s (ih q)

/-- Theorem 18: Monad morphism preserves unit (path witness). -/
theorem morph_preserves_unit (σ : MonadMorph) :
    MMPath (.eta σ.src) (.eta σ.tgt) :=
  MMPath.step (MMStep.morph_eta σ) (MMPath.refl _)

/-- Theorem 19: Monad morphism preserves multiplication (path witness). -/
theorem morph_preserves_mu (σ : MonadMorph) :
    MMPath (.mu σ.src) (.mu σ.tgt) :=
  MMPath.step (MMStep.morph_mu σ) (MMPath.refl _)

/-- Theorem 20: Composing morphism paths lifts base monad paths. -/
theorem MMPath.liftBase {a b : MExpr} (p : MPath a b) : MMPath a b := by
  induction p with
  | refl _ => exact MMPath.refl _
  | step s _ ih => exact MMPath.step (MMStep.base s) ih

-- ============================================================
-- §8  Free monads
-- ============================================================

/-- Free monad expression tree. -/
inductive FreeExpr where
  | pure   : Nat → FreeExpr         -- Pure a
  | impure : Nat → FreeExpr → FreeExpr  -- Impure (op, k)
  | bind   : FreeExpr → FreeExpr → FreeExpr
deriving DecidableEq, Repr

/-- Rewriting steps for free monad. -/
inductive FStep : FreeExpr → FreeExpr → Prop where
  | bindPure (n : Nat) (k : FreeExpr) :
      FStep (.bind (.pure n) k) k
  | bindPure' (n : Nat) (k : FreeExpr) :
      FStep k (.bind (.pure n) k)
  | bindAssoc (m f g : FreeExpr) :
      FStep (.bind (.bind m f) g) (.bind m (.bind f g))
  | bindAssoc' (m f g : FreeExpr) :
      FStep (.bind m (.bind f g)) (.bind (.bind m f) g)
  | bindImpure (op : Nat) (k f : FreeExpr) :
      FStep (.bind (.impure op k) f) (.impure op (.bind k f))
  | bindImpure' (op : Nat) (k f : FreeExpr) :
      FStep (.impure op (.bind k f)) (.bind (.impure op k) f)
  | bindCongL {m m' : FreeExpr} (f : FreeExpr) :
      FStep m m' → FStep (.bind m f) (.bind m' f)
  | bindCongR (m : FreeExpr) {f f' : FreeExpr} :
      FStep f f' → FStep (.bind m f) (.bind m f')

/-- Free monad paths. -/
inductive FPath : FreeExpr → FreeExpr → Prop where
  | refl (a : FreeExpr) : FPath a a
  | step {a b c : FreeExpr} : FStep a b → FPath b c → FPath a c

/-- Theorem 21: Free monad path transitivity. -/
theorem FPath.trans {a b c : FreeExpr}
    (p : FPath a b) (q : FPath b c) : FPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact FPath.step s (ih q)

/-- Theorem 22: Free monad left identity. -/
theorem free_left_id (n : Nat) (k : FreeExpr) :
    FPath (.bind (.pure n) k) k :=
  FPath.step (FStep.bindPure n k) (FPath.refl _)

/-- Theorem 23: Free monad associativity. -/
theorem free_assoc (m f g : FreeExpr) :
    FPath (.bind (.bind m f) g) (.bind m (.bind f g)) :=
  FPath.step (FStep.bindAssoc m f g) (FPath.refl _)

/-- Theorem 24: Impure distributes over bind. -/
theorem free_impure_bind (op : Nat) (k f : FreeExpr) :
    FPath (.bind (.impure op k) f) (.impure op (.bind k f)) :=
  FPath.step (FStep.bindImpure op k f) (FPath.refl _)

/-- Theorem 25: Free monad congruence left. -/
theorem FPath.congrArg_bindL {m m' : FreeExpr} (f : FreeExpr)
    (p : FPath m m') : FPath (.bind m f) (.bind m' f) := by
  induction p with
  | refl _ => exact FPath.refl _
  | step s _ ih => exact FPath.step (FStep.bindCongL f s) ih

/-- Theorem 26: Free monad congruence right. -/
theorem FPath.congrArg_bindR (m : FreeExpr) {f f' : FreeExpr}
    (p : FPath f f') : FPath (.bind m f) (.bind m f') := by
  induction p with
  | refl _ => exact FPath.refl _
  | step s _ ih => exact FPath.step (FStep.bindCongR m s) ih

-- ============================================================
-- §9  Algebraic effects
-- ============================================================

/-- Effect operation signature. -/
structure EffOp where
  name : Nat
  arity : Nat    -- number of continuations
deriving DecidableEq, Repr

/-- Effect expression with handlers. -/
inductive EffExpr where
  | ret    : Nat → EffExpr
  | op     : EffOp → EffExpr → EffExpr
  | handle : EffExpr → Nat → EffExpr   -- handle computation with handler #n
  | seq    : EffExpr → EffExpr → EffExpr
deriving DecidableEq, Repr

/-- Effect rewriting steps. -/
inductive EStep : EffExpr → EffExpr → Prop where
  | handleRet (n : Nat) (h : Nat) :
      EStep (.handle (.ret n) h) (.ret n)
  | handleRet' (n : Nat) (h : Nat) :
      EStep (.ret n) (.handle (.ret n) h)
  | handleOp (op : EffOp) (k : EffExpr) (h : Nat) :
      EStep (.handle (.op op k) h) (.op op (.handle k h))
  | handleOp' (op : EffOp) (k : EffExpr) (h : Nat) :
      EStep (.op op (.handle k h)) (.handle (.op op k) h)
  | seqAssoc (a b c : EffExpr) :
      EStep (.seq (.seq a b) c) (.seq a (.seq b c))
  | seqAssoc' (a b c : EffExpr) :
      EStep (.seq a (.seq b c)) (.seq (.seq a b) c)
  | seqRet (n : Nat) (e : EffExpr) :
      EStep (.seq (.ret n) e) e
  | seqRet' (n : Nat) (e : EffExpr) :
      EStep e (.seq (.ret n) e)
  | congHandle {e e' : EffExpr} (h : Nat) :
      EStep e e' → EStep (.handle e h) (.handle e' h)

/-- Effect paths. -/
inductive EPath : EffExpr → EffExpr → Prop where
  | refl (a : EffExpr) : EPath a a
  | step {a b c : EffExpr} : EStep a b → EPath b c → EPath a c

/-- Theorem 27: Effect path transitivity. -/
theorem EPath.trans {a b c : EffExpr}
    (p : EPath a b) (q : EPath b c) : EPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact EPath.step s (ih q)

/-- Theorem 28: Handler on return is identity path. -/
theorem handle_ret_path (n : Nat) (h : Nat) :
    EPath (.handle (.ret n) h) (.ret n) :=
  EPath.step (EStep.handleRet n h) (EPath.refl _)

/-- Theorem 29: Handler distributes over operations. -/
theorem handle_op_path (op : EffOp) (k : EffExpr) (h : Nat) :
    EPath (.handle (.op op k) h) (.op op (.handle k h)) :=
  EPath.step (EStep.handleOp op k h) (EPath.refl _)

/-- Theorem 30: Effect congruence under handlers. -/
theorem EPath.congrArg_handle {e e' : EffExpr} (h : Nat)
    (p : EPath e e') : EPath (.handle e h) (.handle e' h) := by
  induction p with
  | refl _ => exact EPath.refl _
  | step s _ ih => exact EPath.step (EStep.congHandle h s) ih

-- ============================================================
-- §10  Eilenberg-Moore algebras
-- ============================================================

/-- EM algebra expressions: carrier + structure map. -/
inductive EMExpr where
  | carrier : Nat → EMExpr
  | struct  : Nat → Nat → EMExpr  -- structure map α : T(A) → A for monad n, alg a
  | comp    : EMExpr → EMExpr → EMExpr
  | idEM    : EMExpr
deriving DecidableEq, Repr

infixl:70 " ∘ₑₘ " => EMExpr.comp

/-- EM algebra rewriting steps. -/
inductive EMStep : EMExpr → EMExpr → Prop where
  | unitLaw (n a : Nat) : EMStep (.struct n a ∘ₑₘ .idEM) (.struct n a)
  | unitLaw' (n a : Nat) : EMStep (.struct n a) (.struct n a ∘ₑₘ .idEM)
  | assocLaw (n a : Nat) :
      EMStep (.struct n a ∘ₑₘ (.struct n a ∘ₑₘ .idEM))
             (.struct n a ∘ₑₘ .idEM)
  | assocLaw' (n a : Nat) :
      EMStep (.struct n a ∘ₑₘ .idEM)
             (.struct n a ∘ₑₘ (.struct n a ∘ₑₘ .idEM))
  | idL (f : EMExpr) : EMStep (.idEM ∘ₑₘ f) f
  | idL' (f : EMExpr) : EMStep f (.idEM ∘ₑₘ f)
  | idR (f : EMExpr) : EMStep (f ∘ₑₘ .idEM) f
  | idR' (f : EMExpr) : EMStep f (f ∘ₑₘ .idEM)
  | assocR (f g h : EMExpr) : EMStep ((f ∘ₑₘ g) ∘ₑₘ h) (f ∘ₑₘ (g ∘ₑₘ h))
  | assocL (f g h : EMExpr) : EMStep (f ∘ₑₘ (g ∘ₑₘ h)) ((f ∘ₑₘ g) ∘ₑₘ h)
  | compL {f f' : EMExpr} (g : EMExpr) : EMStep f f' → EMStep (f ∘ₑₘ g) (f' ∘ₑₘ g)
  | compR (f : EMExpr) {g g' : EMExpr} : EMStep g g' → EMStep (f ∘ₑₘ g) (f ∘ₑₘ g')

/-- EM algebra paths. -/
inductive EMPath : EMExpr → EMExpr → Prop where
  | refl (a : EMExpr) : EMPath a a
  | step {a b c : EMExpr} : EMStep a b → EMPath b c → EMPath a c

/-- Theorem 31: EM path transitivity. -/
theorem EMPath.trans {a b c : EMExpr}
    (p : EMPath a b) (q : EMPath b c) : EMPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact EMPath.step s (ih q)

/-- Theorem 32: EM algebra unit law path. -/
theorem em_unit_law (n a : Nat) :
    EMPath (.struct n a ∘ₑₘ .idEM) (.struct n a) :=
  EMPath.step (EMStep.unitLaw n a) (EMPath.refl _)

/-- Theorem 33: EM algebra associativity law path. -/
theorem em_assoc_law (n a : Nat) :
    EMPath (.struct n a ∘ₑₘ (.struct n a ∘ₑₘ .idEM))
           (.struct n a ∘ₑₘ .idEM) :=
  EMPath.step (EMStep.assocLaw n a) (EMPath.refl _)

/-- Theorem 34: EM congrArg left. -/
theorem EMPath.congrArg_compL {f f' : EMExpr} (g : EMExpr)
    (p : EMPath f f') : EMPath (f ∘ₑₘ g) (f' ∘ₑₘ g) := by
  induction p with
  | refl _ => exact EMPath.refl _
  | step s _ ih => exact EMPath.step (EMStep.compL g s) ih

/-- Theorem 35: EM congrArg right. -/
theorem EMPath.congrArg_compR (f : EMExpr) {g g' : EMExpr}
    (p : EMPath g g') : EMPath (f ∘ₑₘ g) (f ∘ₑₘ g') := by
  induction p with
  | refl _ => exact EMPath.refl _
  | step s _ ih => exact EMPath.step (EMStep.compR f s) ih

-- ============================================================
-- §11  Kleisli vs Eilenberg-Moore adjunction comparison
-- ============================================================

/-- Adjunction expressions for Kleisli ⊣ forgetful factorization. -/
inductive AdjExpr where
  | free   : Nat → AdjExpr    -- Free functor F_n
  | forget : Nat → AdjExpr    -- Forgetful U_n
  | comp   : AdjExpr → AdjExpr → AdjExpr
  | idAdj  : AdjExpr
  | unit   : Nat → AdjExpr    -- η of adjunction
  | counit : Nat → AdjExpr    -- ε of adjunction
deriving DecidableEq, Repr

infixl:70 " ∘ₐ " => AdjExpr.comp

/-- Adjunction rewriting steps (triangle identities). -/
inductive AdjStep : AdjExpr → AdjExpr → Prop where
  | triL (n : Nat) : AdjStep (.counit n ∘ₐ .free n ∘ₐ .unit n) (.free n)
  | triL' (n : Nat) : AdjStep (.free n) (.counit n ∘ₐ .free n ∘ₐ .unit n)
  | triR (n : Nat) : AdjStep (.forget n ∘ₐ .counit n ∘ₐ .unit n) (.forget n)
  | triR' (n : Nat) : AdjStep (.forget n) (.forget n ∘ₐ .counit n ∘ₐ .unit n)
  | monadFromAdj (n : Nat) :
      AdjStep (.forget n ∘ₐ .free n) (.free n ∘ₐ .forget n)
  | monadFromAdj' (n : Nat) :
      AdjStep (.free n ∘ₐ .forget n) (.forget n ∘ₐ .free n)
  | idL (f : AdjExpr) : AdjStep (.idAdj ∘ₐ f) f
  | idL' (f : AdjExpr) : AdjStep f (.idAdj ∘ₐ f)
  | assocR (f g h : AdjExpr) : AdjStep ((f ∘ₐ g) ∘ₐ h) (f ∘ₐ (g ∘ₐ h))
  | compL {f f' : AdjExpr} (g : AdjExpr) : AdjStep f f' → AdjStep (f ∘ₐ g) (f' ∘ₐ g)
  | compR (f : AdjExpr) {g g' : AdjExpr} : AdjStep g g' → AdjStep (f ∘ₐ g) (f ∘ₐ g')

/-- Adjunction paths. -/
inductive AdjPath : AdjExpr → AdjExpr → Prop where
  | refl (a : AdjExpr) : AdjPath a a
  | step {a b c : AdjExpr} : AdjStep a b → AdjPath b c → AdjPath a c

/-- Theorem 36: Adjunction path transitivity. -/
theorem AdjPath.trans {a b c : AdjExpr}
    (p : AdjPath a b) (q : AdjPath b c) : AdjPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact AdjPath.step s (ih q)

/-- Theorem 37: Left triangle identity as path. -/
theorem adj_triangle_left (n : Nat) :
    AdjPath (.counit n ∘ₐ .free n ∘ₐ .unit n) (.free n) :=
  AdjPath.step (AdjStep.triL n) (AdjPath.refl _)

/-- Theorem 38: Right triangle identity as path. -/
theorem adj_triangle_right (n : Nat) :
    AdjPath (.forget n ∘ₐ .counit n ∘ₐ .unit n) (.forget n) :=
  AdjPath.step (AdjStep.triR n) (AdjPath.refl _)

-- ============================================================
-- §12  Distributive laws (redux via monad-monad interaction)
-- ============================================================

/-- Distributive law: λ : S∘T → T∘S satisfying compatibility. -/
inductive DLStep : MExpr → MExpr → Prop where
  | base : MStep a b → DLStep a b
  | distLaw (s t : Nat) :
      DLStep (.T s ∘ₘ .T t) (.T t ∘ₘ .T s)
  | distUnit (s t : Nat) :
      DLStep (.T s ∘ₘ .eta t) (.eta t ∘ₘ .T s)
  | distMu (s t : Nat) :
      DLStep (.T s ∘ₘ .mu t) (.mu t ∘ₘ (.T s ∘ₘ .T t))
  | compL {f f' : MExpr} (g : MExpr) : DLStep f f' → DLStep (f ∘ₘ g) (f' ∘ₘ g)

/-- Distributive law paths. -/
inductive DLPath : MExpr → MExpr → Prop where
  | refl (a : MExpr) : DLPath a a
  | step {a b c : MExpr} : DLStep a b → DLPath b c → DLPath a c

/-- Theorem 39: DL path transitivity. -/
theorem DLPath.trans {a b c : MExpr}
    (p : DLPath a b) (q : DLPath b c) : DLPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact DLPath.step s (ih q)

/-- Theorem 40: Distributive law swaps T and S. -/
theorem dist_swap (s t : Nat) :
    DLPath (.T s ∘ₘ .T t) (.T t ∘ₘ .T s) :=
  DLPath.step (DLStep.distLaw s t) (DLPath.refl _)

/-- Theorem 41: Distributive law is compatible with unit. -/
theorem dist_unit_compat (s t : Nat) :
    DLPath (.T s ∘ₘ .eta t) (.eta t ∘ₘ .T s) :=
  DLPath.step (DLStep.distUnit s t) (DLPath.refl _)

/-- Theorem 42: DL congruence left. -/
theorem DLPath.congrArg_compL {f f' : MExpr} (g : MExpr)
    (p : DLPath f f') : DLPath (f ∘ₘ g) (f' ∘ₘ g) := by
  induction p with
  | refl _ => exact DLPath.refl _
  | step s _ ih => exact DLPath.step (DLStep.compL g s) ih

-- ============================================================
-- §13  Monad transformers
-- ============================================================

/-- Transformer expressions: T lifts to T̂ on the transformed category. -/
inductive TrExpr where
  | base   : MExpr → TrExpr
  | lift   : Nat → TrExpr → TrExpr     -- lift into transformer layer n
  | comp   : TrExpr → TrExpr → TrExpr
  | idTr   : TrExpr
deriving DecidableEq, Repr

infixl:70 " ∘ₜ " => TrExpr.comp

/-- Transformer rewriting steps. -/
inductive TrStep : TrExpr → TrExpr → Prop where
  | liftComp (n : Nat) (a b : TrExpr) :
      TrStep (.lift n (a ∘ₜ b)) (.lift n a ∘ₜ .lift n b)
  | liftComp' (n : Nat) (a b : TrExpr) :
      TrStep (.lift n a ∘ₜ .lift n b) (.lift n (a ∘ₜ b))
  | liftId (n : Nat) :
      TrStep (.lift n .idTr) .idTr
  | liftId' (n : Nat) :
      TrStep .idTr (.lift n .idTr)
  | idL (f : TrExpr) : TrStep (.idTr ∘ₜ f) f
  | idL' (f : TrExpr) : TrStep f (.idTr ∘ₜ f)
  | idR (f : TrExpr) : TrStep (f ∘ₜ .idTr) f
  | idR' (f : TrExpr) : TrStep f (f ∘ₜ .idTr)
  | assocR (f g h : TrExpr) : TrStep ((f ∘ₜ g) ∘ₜ h) (f ∘ₜ (g ∘ₜ h))
  | assocL (f g h : TrExpr) : TrStep (f ∘ₜ (g ∘ₜ h)) ((f ∘ₜ g) ∘ₜ h)
  | compL {f f' : TrExpr} (g : TrExpr) : TrStep f f' → TrStep (f ∘ₜ g) (f' ∘ₜ g)
  | compR (f : TrExpr) {g g' : TrExpr} : TrStep g g' → TrStep (f ∘ₜ g) (f ∘ₜ g')
  | liftCong (n : Nat) {e e' : TrExpr} : TrStep e e' → TrStep (.lift n e) (.lift n e')

/-- Transformer paths. -/
inductive TrPath : TrExpr → TrExpr → Prop where
  | refl (a : TrExpr) : TrPath a a
  | step {a b c : TrExpr} : TrStep a b → TrPath b c → TrPath a c

/-- Theorem 43: Transformer path transitivity. -/
theorem TrPath.trans {a b c : TrExpr}
    (p : TrPath a b) (q : TrPath b c) : TrPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact TrPath.step s (ih q)

/-- Theorem 44: Lift preserves identity. -/
theorem tr_lift_id (n : Nat) : TrPath (.lift n .idTr) .idTr :=
  TrPath.step (TrStep.liftId n) (TrPath.refl _)

/-- Theorem 45: Lift distributes over composition. -/
theorem tr_lift_comp (n : Nat) (a b : TrExpr) :
    TrPath (.lift n (a ∘ₜ b)) (.lift n a ∘ₜ .lift n b) :=
  TrPath.step (TrStep.liftComp n a b) (TrPath.refl _)

/-- Theorem 46: Transformer congruence under lift. -/
theorem TrPath.congrArg_lift (n : Nat) {e e' : TrExpr}
    (p : TrPath e e') : TrPath (.lift n e) (.lift n e') := by
  induction p with
  | refl _ => exact TrPath.refl _
  | step s _ ih => exact TrPath.step (TrStep.liftCong n s) ih

/-- Theorem 47: Lift of lift is coherent with identity. -/
theorem tr_double_lift_id (m n : Nat) :
    TrPath (.lift m (.lift n .idTr)) .idTr :=
  TrPath.trans
    (TrPath.congrArg_lift m (tr_lift_id n))
    (tr_lift_id m)

/-- Theorem 48: Transformer composition associativity. -/
theorem tr_assoc (f g h : TrExpr) :
    TrPath ((f ∘ₜ g) ∘ₜ h) (f ∘ₜ (g ∘ₜ h)) :=
  TrPath.step (TrStep.assocR f g h) (TrPath.refl _)

-- ============================================================
-- §14  Transport and coherence across monad structures
-- ============================================================

/-- Theorem 49: Transport: if two expressions are MPath-connected,
    composing with a third preserves the connection (bilateral). -/
theorem MPath.transport_comp {a b : MExpr} (f g : MExpr)
    (p : MPath a b) : MPath (f ∘ₘ a ∘ₘ g) (f ∘ₘ b ∘ₘ g) :=
  MPath.congrArg_compL g (MPath.congrArg_compR f p)

/-- Theorem 50: Kleisli and unit coherence — kl(η) composed with anything
    reduces via two-step path. -/
theorem kleisli_unit_transport (n : Nat) (f : MExpr) :
    MPath (.kl n (.eta n) ∘ₘ f) f :=
  MPath.trans
    (MPath.congrArg_compL f (MPath.single (MStep.klEta n)))
    (MPath.single (MStep.idL f))

/-- Theorem 51: Monad law diamond — left-unit and right-unit
    both reach id, forming a diamond path. -/
theorem monad_unit_diamond (n : Nat) :
    MPath (.mu n ∘ₘ (.eta n ∘ₘ .T n)) .id ∧
    MPath (.mu n ∘ₘ (.T n ∘ₘ .eta n)) .id :=
  ⟨monad_left_unit n, monad_right_unit n⟩

/-- Theorem 52: Symmetry round-trip: symm of symm returns to original endpoint. -/
theorem MPath.symm_symm {a b : MExpr} (p : MPath a b) :
    MPath a b :=
  MPath.symm (MPath.symm p)

/-- Theorem 53: Kleisli triple composition factors through two binary compositions. -/
theorem kleisli_triple_factor (n : Nat) (f g h : MExpr) :
    MPath ((.kl n h ∘ₘ .kl n g) ∘ₘ .kl n f)
          (.kl n (.kl n h ∘ₘ g) ∘ₘ .kl n f) :=
  MPath.congrArg_compL (.kl n f)
    (kleisli_comp_law n g h)

/-- Theorem 54: Monad composition with id on both sides. -/
theorem monad_id_sandwich (e : MExpr) :
    MPath ((.id ∘ₘ e) ∘ₘ .id) e :=
  MPath.trans
    (MPath.single (MStep.idR (.id ∘ₘ e)))
    (MPath.single (MStep.idL e))

/-- Theorem 55: Transformer lift of composition then back. -/
theorem tr_lift_comp_roundtrip (n : Nat) (a b : TrExpr) :
    TrPath (.lift n (a ∘ₜ b)) (.lift n a ∘ₜ .lift n b) ∧
    TrPath (.lift n a ∘ₜ .lift n b) (.lift n (a ∘ₜ b)) :=
  ⟨tr_lift_comp n a b,
   TrPath.step (TrStep.liftComp' n a b) (TrPath.refl _)⟩
