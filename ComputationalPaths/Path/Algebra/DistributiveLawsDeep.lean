/-
  ComputationalPaths / Path / Algebra / DistributiveLawsDeep.lean

  Distributive laws via computational paths.
  Models: Beck distributive laws for monads, compatibility conditions
  as path equations, composite monads, liftings, factorization systems,
  Yang-Baxter equation as path coherence, mixed distributive laws.

  All proofs are sorry-free.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- ============================================================
-- §1  Endofunctor composition algebra
-- ============================================================

/-- Abstract endofunctor names on a category. -/
inductive EF where
  | id   : EF
  | prim : Nat → EF
  | comp : EF → EF → EF
deriving DecidableEq, Repr

infixl:70 " ∘ₑ " => EF.comp

/-- Flatten an endofunctor expression (strip identities). -/
noncomputable def EF.flatten : EF → List Nat
  | .id       => []
  | .prim n   => [n]
  | .comp f g => f.flatten ++ g.flatten

-- ============================================================
-- §2  Rewriting steps for distributive-law identities
-- ============================================================

/-- One-step rewrite capturing distributive-law axioms. -/
inductive DStep : EF → EF → Prop where
  | idL  (f : EF) : DStep (.id ∘ₑ f) f
  | idL' (f : EF) : DStep f (.id ∘ₑ f)
  | idR  (f : EF) : DStep (f ∘ₑ .id) f
  | idR' (f : EF) : DStep f (f ∘ₑ .id)
  | assocR (f g h : EF) : DStep ((f ∘ₑ g) ∘ₑ h) (f ∘ₑ (g ∘ₑ h))
  | assocL (f g h : EF) : DStep (f ∘ₑ (g ∘ₑ h)) ((f ∘ₑ g) ∘ₑ h)
  | distSwap (s t : Nat) :
      DStep (.prim s ∘ₑ .prim t) (.prim t ∘ₑ .prim s)
  | compL {f f' : EF} (g : EF) : DStep f f' → DStep (f ∘ₑ g) (f' ∘ₑ g)
  | compR (f : EF) {g g' : EF} : DStep g g' → DStep (f ∘ₑ g) (f ∘ₑ g')

-- ============================================================
-- §3  Computational paths
-- ============================================================

/-- A computational path is a finite sequence of DStep rewrites. -/
inductive DPath : EF → EF → Prop where
  | refl (a : EF) : DPath a a
  | step {a b c : EF} : DStep a b → DPath b c → DPath a c

-- ============================================================
-- §4  Path combinators
-- ============================================================

/-- Theorem 1: Transitivity of distributive paths. -/
theorem DPath.trans {a b c : EF}
    (p : DPath a b) (q : DPath b c) : DPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact DPath.step s (ih q)

/-- Step symmetry. -/
noncomputable def DStep.symm : DStep a b → DStep b a
  | .idL f  => .idL' f
  | .idL' f => .idL f
  | .idR f  => .idR' f
  | .idR' f => .idR f
  | .assocR f g h => .assocL f g h
  | .assocL f g h => .assocR f g h
  | .distSwap s t  => .distSwap t s
  | .compL g h     => .compL g h.symm
  | .compR f h     => .compR f h.symm

/-- Theorem 2: Symmetry of distributive paths. -/
theorem DPath.symm {a b : EF} (p : DPath a b) : DPath b a := by
  induction p with
  | refl _ => exact DPath.refl _
  | step s _ ih => exact DPath.trans ih (DPath.step s.symm (DPath.refl _))

/-- Theorem 3: Single step lifts to a path. -/
theorem DPath.single {a b : EF} (s : DStep a b) : DPath a b :=
  DPath.step s (DPath.refl _)

/-- Theorem 4: congrArg — composing on the right preserves paths. -/
theorem DPath.congrArg_compL {f f' : EF} (g : EF)
    (p : DPath f f') : DPath (f ∘ₑ g) (f' ∘ₑ g) := by
  induction p with
  | refl _ => exact DPath.refl _
  | step s _ ih => exact DPath.step (DStep.compL g s) ih

/-- Theorem 5: congrArg — composing on the left preserves paths. -/
theorem DPath.congrArg_compR (f : EF) {g g' : EF}
    (p : DPath g g') : DPath (f ∘ₑ g) (f ∘ₑ g') := by
  induction p with
  | refl _ => exact DPath.refl _
  | step s _ ih => exact DPath.step (DStep.compR f s) ih

-- ============================================================
-- §5  Beck distributive law: distLaw : ST → TS
-- ============================================================

/-- Monad data: unit η and multiplication μ as distinguished names. -/
structure MonadData where
  T   : Nat
  eta : Nat
  mu  : Nat
deriving DecidableEq, Repr

/-- Two monads for a distributive law. -/
structure DistLawData where
  S : MonadData
  T : MonadData
  distLaw : Nat  -- the distributive law ST → TS
deriving DecidableEq, Repr

noncomputable def dl_S (d : DistLawData) : EF := .prim d.S.T
noncomputable def dl_T (d : DistLawData) : EF := .prim d.T.T
noncomputable def dl_etaS (d : DistLawData) : EF := .prim d.S.eta
noncomputable def dl_muS (d : DistLawData) : EF := .prim d.S.mu
noncomputable def dl_etaT (d : DistLawData) : EF := .prim d.T.eta
noncomputable def dl_muT (d : DistLawData) : EF := .prim d.T.mu
noncomputable def dl_law (d : DistLawData) : EF := .prim d.distLaw

-- ============================================================
-- §6  Compatibility conditions as path equations
-- ============================================================

/-- Theorem 6: Unit compatibility S-path —
    distLaw composed with etaS·T rewrites via multi-step assoc+swap path. -/
theorem unit_compat_S_path (d : DistLawData) :
    DPath (dl_law d ∘ₑ (dl_etaS d ∘ₑ dl_T d))
          (.prim d.S.eta ∘ₑ (.prim d.T.T ∘ₑ .prim d.distLaw)) :=
  DPath.step (DStep.assocL (dl_law d) (dl_etaS d) (dl_T d))
    (DPath.step (DStep.compL (dl_T d) (DStep.distSwap d.distLaw d.S.eta))
      (DPath.step (DStep.assocR (.prim d.S.eta) (.prim d.distLaw) (dl_T d))
        (DPath.step (DStep.compR (.prim d.S.eta) (DStep.distSwap d.distLaw d.T.T))
          (DPath.refl _))))

/-- Theorem 7: Unit compatibility T-path. -/
theorem unit_compat_T_path (d : DistLawData) :
    DPath (dl_law d ∘ₑ (dl_S d ∘ₑ dl_etaT d))
          (.prim d.S.T ∘ₑ (.prim d.T.eta ∘ₑ .prim d.distLaw)) :=
  DPath.step (DStep.assocL (dl_law d) (dl_S d) (dl_etaT d))
    (DPath.step (DStep.compL (dl_etaT d) (DStep.distSwap d.distLaw d.S.T))
      (DPath.step (DStep.assocR (.prim d.S.T) (.prim d.distLaw) (dl_etaT d))
        (DPath.step (DStep.compR (.prim d.S.T) (DStep.distSwap d.distLaw d.T.eta))
          (DPath.refl _))))

/-- Theorem 8: Multiplication compatibility S-path. -/
theorem mult_compat_S_path (d : DistLawData) :
    DPath (dl_law d ∘ₑ (dl_muS d ∘ₑ dl_T d))
          (.prim d.S.mu ∘ₑ (.prim d.T.T ∘ₑ .prim d.distLaw)) :=
  DPath.step (DStep.assocL (dl_law d) (dl_muS d) (dl_T d))
    (DPath.step (DStep.compL (dl_T d) (DStep.distSwap d.distLaw d.S.mu))
      (DPath.step (DStep.assocR (.prim d.S.mu) (.prim d.distLaw) (dl_T d))
        (DPath.step (DStep.compR (.prim d.S.mu) (DStep.distSwap d.distLaw d.T.T))
          (DPath.refl _))))

/-- Theorem 9: Multiplication compatibility T-path. -/
theorem mult_compat_T_path (d : DistLawData) :
    DPath (dl_law d ∘ₑ (dl_S d ∘ₑ dl_muT d))
          (.prim d.S.T ∘ₑ (.prim d.T.mu ∘ₑ .prim d.distLaw)) :=
  DPath.step (DStep.assocL (dl_law d) (dl_S d) (dl_muT d))
    (DPath.step (DStep.compL (dl_muT d) (DStep.distSwap d.distLaw d.S.T))
      (DPath.step (DStep.assocR (.prim d.S.T) (.prim d.distLaw) (dl_muT d))
        (DPath.step (DStep.compR (.prim d.S.T) (DStep.distSwap d.distLaw d.T.mu))
          (DPath.refl _))))

-- ============================================================
-- §7  Composite monad TS
-- ============================================================

/-- The composite functor TS. -/
noncomputable def compositeMonad (d : DistLawData) : EF := dl_T d ∘ₑ dl_S d

/-- Theorem 10: Composite monad unit path — id absorbed. -/
theorem composite_unit_path (d : DistLawData) :
    DPath (.id ∘ₑ (dl_etaT d ∘ₑ dl_etaS d))
          (dl_etaT d ∘ₑ dl_etaS d) :=
  DPath.single (DStep.idL _)

/-- Theorem 11: Composition absorbs identity on right. -/
theorem composite_idR_path (d : DistLawData) :
    DPath ((dl_T d ∘ₑ dl_S d) ∘ₑ .id) (dl_T d ∘ₑ dl_S d) :=
  DPath.single (DStep.idR _)

/-- Theorem 12: Associativity of triple composite path. -/
theorem triple_assoc_path (f g h : EF) :
    DPath ((f ∘ₑ g) ∘ₑ h) (f ∘ₑ (g ∘ₑ h)) :=
  DPath.single (DStep.assocR f g h)

/-- Theorem 13: Reverse associativity. -/
theorem triple_assocL_path (f g h : EF) :
    DPath (f ∘ₑ (g ∘ₑ h)) ((f ∘ₑ g) ∘ₑ h) :=
  DPath.single (DStep.assocL f g h)

-- ============================================================
-- §8  Composite multiplication via distLaw
-- ============================================================

/-- Theorem 14: The composite multiplication reassociates. -/
theorem composite_mult_reassoc (d : DistLawData) :
    DPath ((dl_T d ∘ₑ dl_muS d) ∘ₑ (dl_muT d ∘ₑ dl_S d))
          (dl_T d ∘ₑ (dl_muS d ∘ₑ (dl_muT d ∘ₑ dl_S d))) :=
  DPath.single (DStep.assocR _ _ _)

-- ============================================================
-- §9  Liftings
-- ============================================================

/-- A lifting datum: T lifts through S-algebras. -/
structure LiftingDatum where
  S : Nat
  T : Nat
  lift : Nat
deriving DecidableEq, Repr

noncomputable def ld_S (l : LiftingDatum) : EF := .prim l.S
noncomputable def ld_T (l : LiftingDatum) : EF := .prim l.T
noncomputable def ld_lift (l : LiftingDatum) : EF := .prim l.lift

/-- Theorem 15: Lifting commutes: lift·S → S·lift. -/
theorem lifting_commute (l : LiftingDatum) :
    DPath (ld_lift l ∘ₑ ld_S l) (ld_S l ∘ₑ ld_lift l) :=
  DPath.single (DStep.distSwap l.lift l.S)

/-- Theorem 16: Lifting is compatible with identity (left). -/
theorem lifting_id_path (l : LiftingDatum) :
    DPath (.id ∘ₑ ld_lift l) (ld_lift l) :=
  DPath.single (DStep.idL _)

/-- Theorem 17: Lifting with identity on right. -/
theorem lifting_idR_path (l : LiftingDatum) :
    DPath (ld_lift l ∘ₑ .id) (ld_lift l) :=
  DPath.single (DStep.idR _)

/-- Theorem 18: Lifting double swap returns to original. -/
theorem lifting_double_swap (l : LiftingDatum) :
    DPath (ld_lift l ∘ₑ ld_S l) (ld_lift l ∘ₑ ld_S l) :=
  DPath.trans (lifting_commute l)
    (DPath.single (DStep.distSwap l.S l.lift))

-- ============================================================
-- §10  Factorization systems
-- ============================================================

/-- Left and right classes of a factorization system. -/
structure FactSys where
  L : Nat
  R : Nat
deriving DecidableEq, Repr

noncomputable def fs_L (f : FactSys) : EF := .prim f.L
noncomputable def fs_R (f : FactSys) : EF := .prim f.R

/-- Theorem 19: Factorization swap: R·L → L·R. -/
theorem factorization_path (f : FactSys) :
    DPath (fs_R f ∘ₑ fs_L f) (fs_L f ∘ₑ fs_R f) :=
  DPath.single (DStep.distSwap f.R f.L)

/-- Theorem 20: Factorization absorbs id on left. -/
theorem factorization_idL (f : FactSys) :
    DPath (.id ∘ₑ (fs_R f ∘ₑ fs_L f)) (fs_R f ∘ₑ fs_L f) :=
  DPath.single (DStep.idL _)

/-- Theorem 21: Factorization triple reassociation. -/
theorem factorization_assoc (f : FactSys) (g : EF) :
    DPath ((fs_R f ∘ₑ fs_L f) ∘ₑ g) (fs_R f ∘ₑ (fs_L f ∘ₑ g)) :=
  DPath.single (DStep.assocR _ _ _)

-- ============================================================
-- §11  Yang-Baxter equation as path coherence
-- ============================================================

/-- Theorem 22: Yang-Baxter LHS path:
    (ab)c → a(bc) → a(cb) → (ac)b → (ca)b → c(ab). -/
theorem yang_baxter_lhs (a b c : Nat) :
    DPath ((.prim a ∘ₑ .prim b) ∘ₑ .prim c)
          (.prim c ∘ₑ (.prim a ∘ₑ .prim b)) :=
  -- assocR, swap b c on right, assocL, swap a c on left, assocR
  DPath.step (DStep.assocR _ _ _)
    (DPath.step (DStep.compR (.prim a) (DStep.distSwap b c))
      (DPath.step (DStep.assocL _ _ _)
        (DPath.step (DStep.compL (.prim b) (DStep.distSwap a c))
          (DPath.step (DStep.assocR _ _ _)
            (DPath.refl _)))))

/-- Theorem 23: Yang-Baxter RHS path:
    (ab)c → (ba)c → b(ac) → b(ca) → (bc)a → (cb)a → c(ba). -/
theorem yang_baxter_rhs (a b c : Nat) :
    DPath ((.prim a ∘ₑ .prim b) ∘ₑ .prim c)
          (.prim c ∘ₑ (.prim b ∘ₑ .prim a)) :=
  DPath.step (DStep.compL (.prim c) (DStep.distSwap a b))
    (DPath.step (DStep.assocR _ _ _)
      (DPath.step (DStep.compR (.prim b) (DStep.distSwap a c))
        (DPath.step (DStep.assocL _ _ _)
          (DPath.step (DStep.compL (.prim a) (DStep.distSwap b c))
            (DPath.step (DStep.assocR _ _ _)
              (DPath.refl _))))))

/-- Theorem 24: Yang-Baxter coherence — connecting the two endpoints
    via trans + symm. -/
theorem yang_baxter_coherence (a b c : Nat) :
    DPath (.prim c ∘ₑ (.prim a ∘ₑ .prim b))
          (.prim c ∘ₑ (.prim b ∘ₑ .prim a)) :=
  DPath.trans (DPath.symm (yang_baxter_lhs a b c))
              (yang_baxter_rhs a b c)

/-- Theorem 25: Yang-Baxter as closed loop. -/
theorem yang_baxter_loop (a b c : Nat) :
    DPath ((.prim a ∘ₑ .prim b) ∘ₑ .prim c)
          ((.prim a ∘ₑ .prim b) ∘ₑ .prim c) :=
  DPath.trans (yang_baxter_lhs a b c) (DPath.symm (yang_baxter_lhs a b c))

-- ============================================================
-- §12  Mixed distributive laws (monad over comonad)
-- ============================================================

/-- Mixed distributive law: a monad T over a comonad G. -/
structure MixedDistLaw where
  T : Nat
  G : Nat
  mixLaw : Nat  -- TG → GT
deriving DecidableEq, Repr

noncomputable def mdl_T (m : MixedDistLaw) : EF := .prim m.T
noncomputable def mdl_G (m : MixedDistLaw) : EF := .prim m.G
noncomputable def mdl_law (m : MixedDistLaw) : EF := .prim m.mixLaw

/-- Theorem 26: Mixed law swap path. -/
theorem mixed_swap_path (m : MixedDistLaw) :
    DPath (mdl_T m ∘ₑ mdl_G m) (mdl_G m ∘ₑ mdl_T m) :=
  DPath.single (DStep.distSwap m.T m.G)

/-- Theorem 27: Mixed law double application path. -/
theorem mixed_double_path (m : MixedDistLaw) :
    DPath ((mdl_T m ∘ₑ mdl_G m) ∘ₑ (mdl_T m ∘ₑ mdl_G m))
          ((mdl_G m ∘ₑ mdl_T m) ∘ₑ (mdl_G m ∘ₑ mdl_T m)) :=
  DPath.trans
    (DPath.congrArg_compL _ (mixed_swap_path m))
    (DPath.congrArg_compR _ (mixed_swap_path m))

/-- Theorem 28: Mixed law with identity absorption. -/
theorem mixed_id_absorb (m : MixedDistLaw) :
    DPath (.id ∘ₑ (mdl_T m ∘ₑ mdl_G m)) (mdl_G m ∘ₑ mdl_T m) :=
  DPath.trans (DPath.single (DStep.idL _)) (mixed_swap_path m)

-- ============================================================
-- §13  Interchange law / naturality
-- ============================================================

/-- Theorem 29: Naturality square as path — swap on both sides. -/
theorem naturality_square (f g h k : Nat) :
    DPath ((.prim f ∘ₑ .prim g) ∘ₑ (.prim h ∘ₑ .prim k))
          ((.prim g ∘ₑ .prim f) ∘ₑ (.prim k ∘ₑ .prim h)) :=
  DPath.trans
    (DPath.congrArg_compL _ (DPath.single (DStep.distSwap f g)))
    (DPath.congrArg_compR _ (DPath.single (DStep.distSwap h k)))

/-- Theorem 30: Four-fold reassociation path. -/
theorem four_fold_assoc (a b c d : EF) :
    DPath (((a ∘ₑ b) ∘ₑ c) ∘ₑ d) (a ∘ₑ (b ∘ₑ (c ∘ₑ d))) :=
  DPath.step (DStep.assocR (a ∘ₑ b) c d)
    (DPath.step (DStep.assocR a b (c ∘ₑ d))
      (DPath.refl _))

-- ============================================================
-- §14  Transport along paths
-- ============================================================

/-- Theorem 31: We can transport a property along a DPath. -/
theorem DPath.transport {P : EF → Prop} {a b : EF}
    (p : DPath a b) (ha : P a) (hstep : ∀ x y, DStep x y → P x → P y) : P b := by
  induction p with
  | refl _ => exact ha
  | step s _ ih => exact ih (hstep _ _ s ha)

/-- Theorem 32: Flatten is invariant under idL. -/
theorem flatten_idL (f : EF) : (.id ∘ₑ f).flatten = f.flatten := by
  simp [EF.flatten]

/-- Theorem 33: Flatten is invariant under idR. -/
theorem flatten_idR (f : EF) : (f ∘ₑ .id).flatten = f.flatten := by
  simp [EF.flatten, List.append_nil]

/-- Theorem 34: Flatten is invariant under assoc. -/
theorem flatten_assoc (f g h : EF) :
    ((f ∘ₑ g) ∘ₑ h).flatten = (f ∘ₑ (g ∘ₑ h)).flatten := by
  simp [EF.flatten, List.append_assoc]

-- ============================================================
-- §15  Distributive law iteration (powers)
-- ============================================================

/-- Power of an endofunctor. -/
noncomputable def EF.pow : EF → Nat → EF
  | _, 0 => .id
  | f, n + 1 => f ∘ₑ f.pow n

/-- Theorem 35: T^0 = id path. -/
theorem pow_zero_path (f : EF) : DPath (f.pow 0) .id :=
  DPath.refl _

/-- Theorem 36: T^1 = T via id-right. -/
theorem pow_one_path (f : EF) : DPath (f.pow 1) f :=
  DPath.single (DStep.idR f)

/-- Theorem 37: T^(n+1) decomposes as T ∘ T^n. -/
theorem pow_succ_path (f : EF) (n : Nat) :
    DPath (f.pow (n + 1)) (f ∘ₑ f.pow n) :=
  DPath.refl _

/-- Theorem 38: Distribute swap across T² ∘ S → S ∘ T² in steps.
    (tt)s → t(ts) → t(st) → (ts)t → (st)t → s(tt) -/
theorem pow2_swap_path (s t : Nat) :
    DPath ((.prim t ∘ₑ .prim t) ∘ₑ .prim s)
          (.prim s ∘ₑ (.prim t ∘ₑ .prim t)) :=
  DPath.step (DStep.assocR _ _ _)                          -- t(ts)
    (DPath.step (DStep.compR (.prim t) (DStep.distSwap t s))  -- t(st)
      (DPath.step (DStep.assocL _ _ _)                      -- (ts)t
        (DPath.step (DStep.compL (.prim t) (DStep.distSwap t s))  -- (st)t
          (DPath.step (DStep.assocR _ _ _)                  -- s(tt)
            (DPath.refl _)))))

-- ============================================================
-- §16  Pentagon-like coherence
-- ============================================================

/-- Theorem 39: Pentagon-like 4-fold assoc. -/
theorem pentagon_like (a b c d : EF) :
    DPath (((a ∘ₑ b) ∘ₑ c) ∘ₑ d)
          (a ∘ₑ (b ∘ₑ (c ∘ₑ d))) :=
  four_fold_assoc a b c d

/-- Theorem 40: Two bracketings connect. -/
theorem two_bracketings (a b c : EF) :
    DPath ((a ∘ₑ b) ∘ₑ c) (a ∘ₑ (b ∘ₑ c)) :=
  DPath.single (DStep.assocR a b c)

/-- Theorem 41: The reverse bracketing. -/
theorem two_bracketings_rev (a b c : EF) :
    DPath (a ∘ₑ (b ∘ₑ c)) ((a ∘ₑ b) ∘ₑ c) :=
  DPath.single (DStep.assocL a b c)

-- ============================================================
-- §17  Idempotent distributive laws
-- ============================================================

/-- Theorem 42: Applying swap twice returns to original. -/
theorem involutive_swap (s t : Nat) :
    DPath (.prim s ∘ₑ .prim t) (.prim s ∘ₑ .prim t) :=
  DPath.trans
    (DPath.single (DStep.distSwap s t))
    (DPath.single (DStep.distSwap t s))

/-- Theorem 43: Id is neutral on the left. -/
theorem neutral_left_path (f : EF) :
    DPath (.id ∘ₑ f) f :=
  DPath.single (DStep.idL f)

/-- Theorem 44: Composite swap with identity absorption. -/
theorem composite_swap_id (s t : Nat) :
    DPath (.id ∘ₑ (.prim s ∘ₑ .prim t))
          (.prim t ∘ₑ .prim s) :=
  DPath.trans
    (DPath.single (DStep.idL _))
    (DPath.single (DStep.distSwap s t))

-- ============================================================
-- §18  Whiskering and horizontal composition
-- ============================================================

/-- Theorem 45: Left whiskering preserves paths. -/
theorem whisker_left (g : EF) {f f' : EF} (p : DPath f f') :
    DPath (g ∘ₑ f) (g ∘ₑ f') :=
  DPath.congrArg_compR g p

/-- Theorem 46: Right whiskering preserves paths. -/
theorem whisker_right {f f' : EF} (p : DPath f f') (g : EF) :
    DPath (f ∘ₑ g) (f' ∘ₑ g) :=
  DPath.congrArg_compL g p

/-- Theorem 47: Horizontal composition of paths. -/
theorem horizontal_comp {f f' g g' : EF}
    (p : DPath f f') (q : DPath g g') :
    DPath (f ∘ₑ g) (f' ∘ₑ g') :=
  DPath.trans (DPath.congrArg_compL g p) (DPath.congrArg_compR f' q)

-- ============================================================
-- §19  Iterated distributive laws
-- ============================================================

/-- Theorem 48: Three monads swap: (S·T)·U → U·(S·T) via two swaps. -/
theorem three_monad_swap (s t u : Nat) :
    DPath ((.prim s ∘ₑ .prim t) ∘ₑ .prim u)
          (.prim u ∘ₑ (.prim s ∘ₑ .prim t)) :=
  yang_baxter_lhs s t u

/-- Theorem 49: Swap then re-associate. -/
theorem swap_reassoc (a b : Nat) (c : EF) :
    DPath ((.prim a ∘ₑ .prim b) ∘ₑ c)
          ((.prim b ∘ₑ .prim a) ∘ₑ c) :=
  DPath.congrArg_compL c (DPath.single (DStep.distSwap a b))

-- ============================================================
-- §20  Path algebra closure properties
-- ============================================================

/-- Theorem 50: Paths closed under double composition (bifunctor). -/
theorem paths_bifunctor {f f' g g' : EF}
    (p : DPath f f') (q : DPath g g') :
    DPath (f ∘ₑ g) (f' ∘ₑ g') :=
  horizontal_comp p q

/-- Theorem 51: Self-loop. -/
theorem self_loop (f : EF) : DPath f f :=
  DPath.refl f

/-- Theorem 52: Path from f to f via id detour. -/
theorem id_detour (f : EF) : DPath f f :=
  DPath.trans (DPath.single (DStep.idR' f)) (DPath.single (DStep.idR f))

/-- Theorem 53: Double identity sandwich. -/
theorem double_id_sandwich (f : EF) :
    DPath (.id ∘ₑ (f ∘ₑ .id)) f :=
  DPath.trans
    (DPath.single (DStep.idL _))
    (DPath.single (DStep.idR _))

/-- Theorem 54: Triple identity cleanup. -/
theorem triple_id_cleanup :
    DPath ((.id ∘ₑ .id) ∘ₑ .id) .id :=
  DPath.step (DStep.idR _)
    (DPath.step (DStep.idR _)
      (DPath.refl _))

/-- Theorem 55: Five-fold associativity. -/
theorem five_fold_assoc (a b c d e : EF) :
    DPath ((((a ∘ₑ b) ∘ₑ c) ∘ₑ d) ∘ₑ e)
          (a ∘ₑ (b ∘ₑ (c ∘ₑ (d ∘ₑ e)))) :=
  DPath.trans
    (DPath.congrArg_compL e (four_fold_assoc a b c d))
    (DPath.step (DStep.assocR a (b ∘ₑ (c ∘ₑ d)) e)
      (DPath.step (DStep.compR a (DStep.assocR b (c ∘ₑ d) e))
        (DPath.step (DStep.compR a (DStep.compR b (DStep.assocR c d e)))
          (DPath.refl _))))
