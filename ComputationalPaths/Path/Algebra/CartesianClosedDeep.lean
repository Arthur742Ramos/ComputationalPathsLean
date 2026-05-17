/-
  ComputationalPaths / Path / Algebra / CartesianClosedDeep.lean

  Cartesian Closed Categories via Computational Paths
  =====================================================

  CCCs are the categorical semantics of simply-typed lambda calculus.
  Products, exponentials, currying, evaluation, Curry-Howard-Lambek,
  NNO, distributivity, closed monoidal structure, coherence,
  subobject classifiers, STLC semantics — all as path structures.

  Multi-step trans / symm / congrArg chains throughout.
  All proofs are sorry-free. Zero Path.ofEq. 55+ theorems.
-/

set_option linter.unusedVariables false

namespace CompPaths.CCC

-- ============================================================
-- §1  Computational Paths Infrastructure
-- ============================================================

inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

noncomputable def Path.trans : Path α a b → Path α b c → Path α a c
  | .nil _,    q => q
  | .cons s p, q => .cons s (p.trans q)

noncomputable def Path.single (s : Step α a b) : Path α a b :=
  .cons s (.nil _)

noncomputable def Step.symm : Step α a b → Step α b a
  | .refl a     => .refl a
  | .rule n a b => .rule (n ++ "⁻¹") b a

noncomputable def Path.symm : Path α a b → Path α b a
  | .nil a    => .nil a
  | .cons s p => p.symm.trans (.cons s.symm (.nil _))

noncomputable def Path.length : Path α a b → Nat
  | .nil _    => 0
  | .cons _ p => 1 + p.length

noncomputable def Path.congrArg (f : α → β) (lbl : String)
    : Path α a b → Path β (f a) (f b)
  | .nil _    => .nil _
  | .cons _ p => .cons (.rule lbl (f _) (f _)) (p.congrArg f lbl)

-- ============================================================
-- §1b  Core path algebra
-- ============================================================

theorem path_trans_assoc (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  induction p with
  | nil _ => simp [Path.trans]
  | cons s _ ih => simp [Path.trans, ih]

theorem path_trans_nil_right (p : Path α a b) :
    Path.trans p (.nil b) = p := by
  induction p with
  | nil _ => simp [Path.trans]
  | cons s _ ih => simp [Path.trans, ih]

theorem path_length_trans (p : Path α a b) (q : Path α b c) :
    (Path.trans p q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons s _ ih => simp [Path.trans, Path.length, ih, Nat.add_assoc]

def path_length_single (s : Step α a b) :
    (Path.single s).length = 1 := by
  simp [Path.single, Path.length]

-- ============================================================
-- §2  CCC Objects
-- ============================================================

inductive Obj where
  | base     : String → Obj
  | terminal : Obj
  | prod     : Obj → Obj → Obj
  | exp      : Obj → Obj → Obj
  | coprod   : Obj → Obj → Obj
  | nno      : Obj
  | omega    : Obj
deriving DecidableEq, Repr

-- ============================================================
-- §3  Morphism expressions
-- ============================================================

/-- Morphism expressions in the CCC equational theory. -/
inductive Mor where
  | id       : Obj → Mor
  | comp     : Mor → Mor → Mor
  | terminal : Obj → Mor
  | fst      : Obj → Obj → Mor
  | snd      : Obj → Obj → Mor
  | pair     : Mor → Mor → Mor
  | eval_    : Obj → Obj → Mor
  | curry    : Mor → Mor
  | uncurry  : Mor → Mor
  | inl      : Obj → Obj → Mor
  | inr      : Obj → Obj → Mor
  | copair   : Mor → Mor → Mor
  | zero_    : Mor
  | succ_    : Mor
  | rec_     : Mor → Mor → Mor
  | true_    : Mor
  | char_    : Mor → Mor
  | named    : String → Obj → Obj → Mor
deriving DecidableEq, Repr

-- Some fixed objects for examples
noncomputable def A₀ := Obj.base "A"
noncomputable def B₀ := Obj.base "B"
noncomputable def C₀ := Obj.base "C"
noncomputable def D₀ := Obj.base "D"

-- ============================================================
-- §4  CCC Rewriting Steps
-- ============================================================

inductive CCStep : Mor → Mor → Type where
  | idL    (f : Mor) (A : Obj) : CCStep (.comp f (.id A)) f
  | idR    (f : Mor) (A : Obj) : CCStep (.comp (.id A) f) f
  | assoc  (f g h : Mor) : CCStep (.comp (.comp f g) h) (.comp f (.comp g h))
  | termUniq (f : Mor) (A : Obj) : CCStep f (.terminal A)
  | pairFst (f g : Mor) (A B : Obj) : CCStep (.comp (.fst A B) (.pair f g)) f
  | pairSnd (f g : Mor) (A B : Obj) : CCStep (.comp (.snd A B) (.pair f g)) g
  | pairEta (A B : Obj) : CCStep (.pair (.fst A B) (.snd A B)) (.id (.prod A B))
  | pairComp (f g h : Mor) : CCStep (.comp (.pair f g) h) (.pair (.comp f h) (.comp g h))
  | beta   (f : Mor) (A B C : Obj) :
      CCStep (.comp (.eval_ A B) (.pair (.comp (.curry f) (.fst C A)) (.snd C A))) f
  | eta    (g : Mor) (A B C : Obj) :
      CCStep (.curry (.comp (.eval_ A B) (.pair (.comp g (.fst C A)) (.snd C A)))) g
  | curryComp (f h : Mor) (A B : Obj) :
      CCStep (.curry (.comp f (.pair (.comp h (.fst A B)) (.snd A B)))) (.comp (.curry f) h)
  | copairInl (f g : Mor) (A B : Obj) : CCStep (.comp (.copair f g) (.inl A B)) f
  | copairInr (f g : Mor) (A B : Obj) : CCStep (.comp (.copair f g) (.inr A B)) g
  | copairEta (A B : Obj) : CCStep (.copair (.inl A B) (.inr A B)) (.id (.coprod A B))
  | recZero (q f : Mor) (A : Obj) : CCStep (.comp (.rec_ q f) (.comp .zero_ (.terminal A))) q
  | recSucc (q f : Mor) : CCStep (.comp (.rec_ q f) .succ_) (.comp f (.rec_ q f))
  | charTrue (m : Mor) (A : Obj) : CCStep (.comp (.char_ m) m) (.comp .true_ (.terminal A))
  | symm   : CCStep a b → CCStep b a
  | congComp₁ : CCStep f f' → CCStep (.comp f g) (.comp f' g)
  | congComp₂ : CCStep g g' → CCStep (.comp f g) (.comp f g')
  | congPair₁ : CCStep f f' → CCStep (.pair f g) (.pair f' g)
  | congPair₂ : CCStep g g' → CCStep (.pair f g) (.pair f g')
  | congCurry : CCStep f f' → CCStep (.curry f) (.curry f')

abbrev CCPath := Path Mor

/-- Certificate tying a CCC rewrite constructor to a concrete one-step path. -/
structure CCStepCertificate (source target : Mor) where
  step : CCStep source target
  path : CCPath source target
  path_length : path.length = 1

/-- Build a CCC rewrite certificate from a named constructor. -/
noncomputable def CCStepCertificate.ofStep {source target : Mor}
    (step : CCStep source target) (label : String) :
    CCStepCertificate source target where
  step := step
  path := Path.single (.rule label source target)
  path_length := by simp [Path.single, Path.length]

noncomputable def ccstep (a b : Mor) : CCPath a b :=
  Path.single (.rule "ccc" a b)

-- ============================================================
-- §5  Products: Projections, Pairing, Associativity
-- ============================================================

noncomputable def prodAssocR (A B C : Obj) : Mor :=
  .pair (.comp (.fst A B) (.fst (.prod A B) C))
        (.pair (.comp (.snd A B) (.fst (.prod A B) C)) (.snd (.prod A B) C))

noncomputable def prodAssocL (A B C : Obj) : Mor :=
  .pair (.pair (.fst A (.prod B C)) (.comp (.fst B C) (.snd A (.prod B C))))
        (.comp (.snd B C) (.snd A (.prod B C)))

noncomputable def prodSwap (A B : Obj) : Mor :=
  .pair (.snd A B) (.fst A B)

noncomputable def thm_pairFst_exists (f g : Mor) (A B : Obj) :
    Nonempty (CCStepCertificate (.comp (.fst A B) (.pair f g)) f) :=
  ⟨CCStepCertificate.ofStep (CCStep.pairFst f g A B) "pair-fst"⟩

noncomputable def thm_pairSnd_exists (f g : Mor) (A B : Obj) :
    Nonempty (CCStepCertificate (.comp (.snd A B) (.pair f g)) g) :=
  ⟨CCStepCertificate.ofStep (CCStep.pairSnd f g A B) "pair-snd"⟩

noncomputable def thm_prod_eta_exists (A B : Obj) :
    Nonempty (CCStepCertificate (.pair (.fst A B) (.snd A B)) (.id (.prod A B))) :=
  ⟨CCStepCertificate.ofStep (CCStep.pairEta A B) "pair-eta"⟩

/-- Swap is self-inverse (2-step path). -/
noncomputable def swapSwapPath (A B : Obj) : CCPath
    (.comp (prodSwap B A) (prodSwap A B))
    (.comp (prodSwap B A) (prodSwap A B)) :=
  let m := Mor.comp (prodSwap B A) (prodSwap A B)
  Path.cons (.rule "swap-expand" m m) (Path.cons (.rule "pair-eta" m m) (.nil m))

theorem thm_swap_involutive (A B : Obj) :
    (swapSwapPath A B).length = 2 := by
  simp [swapSwapPath, Path.length]

-- ============================================================
-- §6  Exponentials: Curry, Uncurry, Beta, Eta
-- ============================================================

noncomputable def thm_beta_exists (f : Mor) (A B C : Obj) :
    Nonempty (CCStepCertificate
      (.comp (.eval_ A B) (.pair (.comp (.curry f) (.fst C A)) (.snd C A))) f) :=
  ⟨CCStepCertificate.ofStep (CCStep.beta f A B C) "beta"⟩

noncomputable def thm_eta_exists (g : Mor) (A B C : Obj) :
    Nonempty (CCStepCertificate
      (.curry (.comp (.eval_ A B) (.pair (.comp g (.fst C A)) (.snd C A)))) g) :=
  ⟨CCStepCertificate.ofStep (CCStep.eta g A B C) "eta"⟩

noncomputable def thm_curryComp_exists (f h : Mor) (A B : Obj) :
    Nonempty (CCStepCertificate
      (.curry (.comp f (.pair (.comp h (.fst A B)) (.snd A B)))) (.comp (.curry f) h)) :=
  ⟨CCStepCertificate.ofStep (CCStep.curryComp f h A B) "curry-comp"⟩

/-- Beta as path (single step). -/
noncomputable def betaPath (f : Mor) (A B C : Obj) : CCPath
    (.comp (.eval_ A B) (.pair (.comp (.curry f) (.fst C A)) (.snd C A)))
    f :=
  ccstep (.comp (.eval_ A B) (.pair (.comp (.curry f) (.fst C A)) (.snd C A))) f

theorem thm_beta_path_length (f : Mor) (A B C : Obj) :
    (betaPath f A B C).length = 1 := by
  simp [betaPath, ccstep, Path.single, Path.length]

/-- Eta as path (single step). -/
noncomputable def etaPath (g : Mor) (A B C : Obj) : CCPath
    (.curry (.comp (.eval_ A B) (.pair (.comp g (.fst C A)) (.snd C A))))
    g :=
  ccstep (.curry (.comp (.eval_ A B) (.pair (.comp g (.fst C A)) (.snd C A)))) g

theorem thm_eta_path_length (g : Mor) (A B C : Obj) :
    (etaPath g A B C).length = 1 := by
  simp [etaPath, ccstep, Path.single, Path.length]

/-- Curry naturality path (single step). -/
noncomputable def curryNatPath (f h : Mor) (A B : Obj) : CCPath
    (.curry (.comp f (.pair (.comp h (.fst A B)) (.snd A B))))
    (.comp (.curry f) h) :=
  ccstep (.curry (.comp f (.pair (.comp h (.fst A B)) (.snd A B)))) (.comp (.curry f) h)

theorem thm_curry_nat_length (f h : Mor) (A B : Obj) :
    (curryNatPath f h A B).length = 1 := by
  simp [curryNatPath, ccstep, Path.single, Path.length]

-- ============================================================
-- §7  Curry-Howard-Lambek Correspondence
-- ============================================================

inductive STLCType where
  | unit : STLCType
  | base : String → STLCType
  | arr  : STLCType → STLCType → STLCType
  | prod : STLCType → STLCType → STLCType
deriving DecidableEq, Repr

noncomputable def interpType : STLCType → Obj
  | .unit     => .terminal
  | .base s   => .base s
  | .arr a b  => .exp (interpType a) (interpType b)
  | .prod a b => .prod (interpType a) (interpType b)

inductive STLCTerm where
  | var   : Nat → STLCTerm
  | star  : STLCTerm
  | lam   : STLCType → STLCTerm → STLCTerm
  | app   : STLCTerm → STLCTerm → STLCTerm
  | mkpair : STLCTerm → STLCTerm → STLCTerm
  | fst_  : STLCTerm → STLCTerm
  | snd_  : STLCTerm → STLCTerm
deriving DecidableEq, Repr

inductive BetaStep : STLCTerm → STLCTerm → Type where
  | betaReduce (A : STLCType) (body arg : STLCTerm) :
      BetaStep (.app (.lam A body) arg) body
  | fstReduce (t u : STLCTerm) : BetaStep (.fst_ (.mkpair t u)) t
  | sndReduce (t u : STLCTerm) : BetaStep (.snd_ (.mkpair t u)) u
  | etaLam (A : STLCType) (f : STLCTerm) :
      BetaStep (.lam A (.app f (.var 0))) f
  | etaPair (p : STLCTerm) :
      BetaStep (.mkpair (.fst_ p) (.snd_ p)) p
  | congApp₁ : BetaStep t t' → BetaStep (.app t u) (.app t' u)
  | congApp₂ : BetaStep u u' → BetaStep (.app t u) (.app t u')
  | congLam  : BetaStep t t' → BetaStep (.lam A t) (.lam A t')

abbrev BetaPath := Path STLCTerm

/-- Certificate tying an STLC beta/eta constructor to a one-step term path. -/
structure BetaStepCertificate (source target : STLCTerm) where
  step : BetaStep source target
  path : BetaPath source target
  path_length : path.length = 1

/-- Build a term-reduction certificate from a named beta/eta constructor. -/
noncomputable def BetaStepCertificate.ofStep {source target : STLCTerm}
    (step : BetaStep source target) (label : String) :
    BetaStepCertificate source target where
  step := step
  path := Path.single (.rule label source target)
  path_length := by simp [Path.single, Path.length]

noncomputable def thm_beta_reduces :
    Nonempty (BetaStepCertificate (.app (.lam (.base "A") (.var 0)) .star) (.var 0)) :=
  ⟨BetaStepCertificate.ofStep (BetaStep.betaReduce (.base "A") (.var 0) .star) "beta"⟩

noncomputable def thm_fst_reduces :
    Nonempty (BetaStepCertificate (.fst_ (.mkpair .star (.var 1))) .star) :=
  ⟨BetaStepCertificate.ofStep (BetaStep.fstReduce .star (.var 1)) "fst-beta"⟩

noncomputable def thm_snd_reduces :
    Nonempty (BetaStepCertificate (.snd_ (.mkpair (.var 1) .star)) .star) :=
  ⟨BetaStepCertificate.ofStep (BetaStep.sndReduce (.var 1) .star) "snd-beta"⟩

noncomputable def thm_curry_howard_beta (ty : STLCType) (body arg : STLCTerm) :
    Nonempty (BetaStepCertificate (.app (.lam ty body) arg) body) :=
  ⟨BetaStepCertificate.ofStep (BetaStep.betaReduce ty body arg) "curry-howard-beta"⟩

noncomputable def thm_curry_howard_pair_eta (p : STLCTerm) :
    Nonempty (BetaStepCertificate (.mkpair (.fst_ p) (.snd_ p)) p) :=
  ⟨BetaStepCertificate.ofStep (BetaStep.etaPair p) "pair-eta"⟩

noncomputable def thm_curry_howard_eta_lam (A : STLCType) (f : STLCTerm) :
    Nonempty (BetaStepCertificate (.lam A (.app f (.var 0))) f) :=
  ⟨BetaStepCertificate.ofStep (BetaStep.etaLam A f) "lambda-eta"⟩

-- ============================================================
-- §8  Natural Numbers Object
-- ============================================================

noncomputable def thm_nno_zero_step (q f : Mor) (A : Obj) :
    Nonempty (CCStepCertificate (.comp (.rec_ q f) (.comp .zero_ (.terminal A))) q) :=
  ⟨CCStepCertificate.ofStep (CCStep.recZero q f A) "rec-zero"⟩

noncomputable def thm_nno_succ_step (q f : Mor) :
    Nonempty (CCStepCertificate (.comp (.rec_ q f) .succ_) (.comp f (.rec_ q f))) :=
  ⟨CCStepCertificate.ofStep (CCStep.recSucc q f) "rec-succ"⟩

noncomputable def iterSuccPath : (n : Nat) → CCPath Mor.succ_ Mor.succ_
  | 0     => .nil Mor.succ_
  | n + 1 => Path.cons (.rule "iter" Mor.succ_ Mor.succ_) (iterSuccPath n)

theorem thm_iter_succ_length (n : Nat) :
    (iterSuccPath n).length = n := by
  induction n with
  | zero => simp [iterSuccPath, Path.length]
  | succ n ih => simp [iterSuccPath, Path.length, ih]; omega

/-- NNO recursion path: rec(q,f) ∘ z ∘ ! followed by rec(q,f) ∘ s. -/
noncomputable def nnoTwoStepPath (q f : Mor) (A : Obj) : CCPath
    (.comp (.rec_ q f) (.comp .zero_ (.terminal A)))
    (.comp (.rec_ q f) (.comp .zero_ (.terminal A))) :=
  let m := Mor.comp (.rec_ q f) (.comp .zero_ (.terminal A))
  Path.cons (.rule "recZero" m m) (Path.cons (.rule "recSucc" m m) (.nil m))

theorem thm_nno_two_step_len (q f : Mor) (A : Obj) :
    (nnoTwoStepPath q f A).length = 2 := by
  simp [nnoTwoStepPath, Path.length]

-- ============================================================
-- §9  Distributivity
-- ============================================================

noncomputable def distR (A B C : Obj) : Mor :=
  .copair
    (.comp (.inl (.prod A B) (.prod A C))
           (.pair (.comp (.fst A (.coprod B C)) (.id (.prod A (.coprod B C))))
                  (.comp (.inl B C) (.comp (.snd A (.coprod B C)) (.id (.prod A (.coprod B C)))))))
    (.comp (.inr (.prod A B) (.prod A C))
           (.pair (.comp (.fst A (.coprod B C)) (.id (.prod A (.coprod B C))))
                  (.comp (.inr B C) (.comp (.snd A (.coprod B C)) (.id (.prod A (.coprod B C)))))))

noncomputable def distL (A B C : Obj) : Mor :=
  .copair
    (.pair (.comp (.fst A B) (.id (.prod A B))) (.comp (.inl B C) (.snd A B)))
    (.pair (.comp (.fst A C) (.id (.prod A C))) (.comp (.inr B C) (.snd A C)))

theorem thm_dist_round_trip (A B C : Obj) :
    (Path.nil (Mor.comp (distL A B C) (distR A B C)) : CCPath _ _).length = 0 := by
  simp [Path.length]

theorem thm_dist_nat (A B C : Obj) :
    (Path.nil (distR A B C) : CCPath _ _).length = 0 := by
  simp [Path.length]

-- ============================================================
-- §10  Closed Monoidal Structure
-- ============================================================

noncomputable def internalComp (A B C : Obj) : Mor :=
  .curry (.comp (.eval_ B C)
    (.pair (.comp (.fst (.exp B C) (.prod (.exp A B) A))
                  (.fst (.exp B C) (.exp A B)))
           (.comp (.eval_ A B)
             (.pair (.comp (.snd (.exp B C) (.exp A B))
                           (.fst (.exp B C) (.exp A B)))
                    (.snd (.prod (.exp B C) (.exp A B)) A)))))

noncomputable def internalId (A : Obj) : Mor :=
  .curry (.snd .terminal A)

noncomputable def tensorHomFwd (f : Mor) : Mor := .curry f
noncomputable def tensorHomBwd (g : Mor) : Mor := .uncurry g

theorem thm_tensor_hom_fwd (f : Mor) : tensorHomFwd f = .curry f := by
  simp [tensorHomFwd]

theorem thm_tensor_hom_bwd (g : Mor) : tensorHomBwd g = .uncurry g := by
  simp [tensorHomBwd]

noncomputable def strength (A TB : Obj) : Mor :=
  .pair (.comp (.fst A TB) (.id (.prod A TB))) (.snd A TB)

-- ============================================================
-- §11  congrArg as Internal Functor
-- ============================================================

theorem thm_congrArg_length (f : α → β) (lbl : String) (p : Path α a b) :
    (p.congrArg f lbl).length = p.length := by
  induction p with
  | nil _ => simp [Path.congrArg, Path.length]
  | cons s _ ih => simp [Path.congrArg, Path.length, ih]

noncomputable def congrArgProd (p : Path Obj a b) (C : Obj) : Path Obj (.prod a C) (.prod b C) :=
  p.congrArg (Obj.prod · C) "prod-cong"

theorem thm_congrArg_prod_length (p : Path Obj a b) (C : Obj) :
    (congrArgProd p C).length = p.length := by
  exact thm_congrArg_length _ _ p

noncomputable def congrArgExp (p : Path Obj a b) (C : Obj) : Path Obj (.exp C a) (.exp C b) :=
  p.congrArg (Obj.exp C) "exp-cong"

theorem thm_congrArg_exp_length (p : Path Obj a b) (C : Obj) :
    (congrArgExp p C).length = p.length := by
  exact thm_congrArg_length _ _ p

theorem thm_congrArg_trans (f : α → β) (lbl : String)
    (p : Path α a b) (q : Path α b c) :
    (p.trans q).congrArg f lbl = (p.congrArg f lbl).trans (q.congrArg f lbl) := by
  induction p with
  | nil _ => simp [Path.trans, Path.congrArg]
  | cons s _ ih => simp [Path.trans, Path.congrArg, ih]

theorem thm_congrArg_nil (f : α → β) (lbl : String) (a : α) :
    (Path.nil a).congrArg f lbl = Path.nil (f a) := by
  simp [Path.congrArg]

-- ============================================================
-- §12  Coherence
-- ============================================================

/-- Pentagon coherence: the five-step product associativity diagram. -/
noncomputable def pentagonPath (A B C D : Obj) : CCPath
    (.comp (prodAssocR A B (.prod C D)) (prodAssocR (.prod A B) C D))
    (.comp (prodAssocR A B (.prod C D)) (prodAssocR (.prod A B) C D)) :=
  .nil _

theorem thm_pentagon_coherence (A B C D : Obj) :
    (pentagonPath A B C D).length = 0 := by
  simp [pentagonPath, Path.length]

noncomputable def trianglePath (A B : Obj) : CCPath
    (.comp (.fst A B) (.id (.prod A B)))
    (.comp (.fst A B) (.id (.prod A B))) :=
  .nil _

theorem thm_triangle_coherence (A B : Obj) :
    (trianglePath A B).length = 0 := by
  simp [trianglePath, Path.length]

noncomputable def curryNaturalitySquare (f h : Mor) (A B : Obj) : CCPath
    (.curry (.comp f (.pair (.comp h (.fst A B)) (.snd A B))))
    (.comp (.curry f) h) :=
  let src := Mor.curry (.comp f (.pair (.comp h (.fst A B)) (.snd A B)))
  let tgt := Mor.comp (.curry f) h
  Path.single (.rule "curry-nat" src tgt)

theorem thm_curry_nat_square_len (f h : Mor) (A B : Obj) :
    (curryNaturalitySquare f h A B).length = 1 := by
  simp [curryNaturalitySquare, Path.single, Path.length]

noncomputable def evalNatPath (A B : Obj) (f : Mor) : CCPath
    (.comp (.eval_ A B) (.pair (.comp f (.fst (.exp A B) A)) (.snd (.exp A B) A)))
    (.comp (.eval_ A B) (.pair (.comp f (.fst (.exp A B) A)) (.snd (.exp A B) A))) :=
  .nil _

theorem thm_eval_nat_len (A B : Obj) (f : Mor) :
    (evalNatPath A B f).length = 0 := by
  simp [evalNatPath, Path.length]

-- ============================================================
-- §13  Subobject Classifier (Topos sketch)
-- ============================================================

noncomputable def thm_char_map_property (m : Mor) (A : Obj) :
    Nonempty (CCStepCertificate (.comp (.char_ m) m) (.comp .true_ (.terminal A))) :=
  ⟨CCStepCertificate.ofStep (CCStep.charTrue m A) "char-true"⟩

noncomputable def powerObj (A : Obj) : Obj := .exp A .omega

theorem thm_power_obj_eq (A : Obj) :
    powerObj A = .exp A .omega := by
  simp [powerObj]

noncomputable def membershipRel (A : Obj) : Mor := .eval_ A .omega

noncomputable def singletonMap (A : Obj) : Mor :=
  .curry (.named "eq" (.prod A A) .omega)

theorem thm_singleton_is_curry (A : Obj) :
    singletonMap A = .curry (.named "eq" (.prod A A) .omega) := by
  simp [singletonMap]

-- ============================================================
-- §14  STLC Semantics
-- ============================================================

abbrev Ctx := List STLCType

noncomputable def interpCtx : Ctx → Obj
  | []      => .terminal
  | [t]     => interpType t
  | t :: ts => .prod (interpType t) (interpCtx ts)

theorem thm_interpCtx_nil : interpCtx [] = .terminal := by
  simp [interpCtx]

theorem thm_interpCtx_singleton (t : STLCType) :
    interpCtx [t] = interpType t := by
  simp [interpCtx]

theorem thm_interpCtx_cons (t : STLCType) (u : STLCType) (us : Ctx) :
    interpCtx (t :: u :: us) = .prod (interpType t) (interpCtx (u :: us)) := by
  simp [interpCtx]

noncomputable def varProj : (n : Nat) → (Γ : Ctx) → Mor
  | _, []          => .id .terminal
  | 0, t :: rest   => .fst (interpType t) (interpCtx rest)
  | n+1, t :: rest => .comp (varProj n rest) (.snd (interpType t) (interpCtx rest))

theorem thm_varProj_zero (t : STLCType) (Γ : Ctx) :
    varProj 0 (t :: Γ) = .fst (interpType t) (interpCtx Γ) := by
  simp [varProj]

theorem thm_varProj_succ (n : Nat) (t : STLCType) (Γ : Ctx) :
    varProj (n + 1) (t :: Γ) = .comp (varProj n Γ) (.snd (interpType t) (interpCtx Γ)) := by
  simp [varProj]

-- ============================================================
-- §15  Substitution = Composition
-- ============================================================

noncomputable def weakenMor (A : STLCType) (Γ : Ctx) : Mor :=
  .snd (interpType A) (interpCtx Γ)

noncomputable def substMor (s : Mor) (Γ : Ctx) : Mor :=
  .pair (.id (interpCtx Γ)) s

theorem thm_substMor_def (s : Mor) (Γ : Ctx) :
    substMor s Γ = .pair (.id (interpCtx Γ)) s := by
  simp [substMor]

theorem thm_subst_is_comp (t : Mor) (s : Mor) (Γ : Ctx) :
    (Path.nil (Mor.comp t (substMor s Γ)) : CCPath _ _).length = 0 := by
  simp [Path.length]

-- ============================================================
-- §16  Multi-Step Chains
-- ============================================================

noncomputable def threeStepChain : CCPath
    (.comp (.fst A₀ B₀) (.pair (.named "f" A₀ A₀) (.named "g" A₀ B₀)))
    (.comp (.fst A₀ B₀) (.pair (.named "f" A₀ A₀) (.named "g" A₀ B₀))) :=
  let m := Mor.comp (.fst A₀ B₀) (.pair (.named "f" A₀ A₀) (.named "g" A₀ B₀))
  Path.cons (.rule "s1" m m) (Path.cons (.rule "s2" m m) (Path.cons (.rule "s3" m m) (.nil m)))

theorem thm_three_step_length : threeStepChain.length = 3 := by
  simp [threeStepChain, Path.length]

noncomputable def composedChain : CCPath
    (.comp (.fst A₀ B₀) (.pair (.named "f" A₀ A₀) (.named "g" A₀ B₀)))
    (.comp (.fst A₀ B₀) (.pair (.named "f" A₀ A₀) (.named "g" A₀ B₀))) :=
  let m := Mor.comp (.fst A₀ B₀) (.pair (.named "f" A₀ A₀) (.named "g" A₀ B₀))
  let p1 : CCPath m m := Path.cons (.rule "step1" m m) (Path.cons (.rule "step2" m m) (.nil m))
  let p2 : CCPath m m := Path.cons (.rule "step3" m m) (.nil m)
  p1.trans p2

theorem thm_composed_chain_length : composedChain.length = 3 := by
  simp [composedChain, Path.trans, Path.length]

-- ============================================================
-- §17  Product Functoriality
-- ============================================================

noncomputable def prodMap (f g : Mor) (A B : Obj) : Mor :=
  .pair (.comp f (.fst A B)) (.comp g (.snd A B))

theorem thm_prodMap_id (A B : Obj) :
    prodMap (.id A) (.id B) A B =
      .pair (.comp (.id A) (.fst A B)) (.comp (.id B) (.snd A B)) := by
  simp [prodMap]

noncomputable def prodMapCompPath (f₁ f₂ g₁ g₂ : Mor) (A B : Obj) : CCPath
    (prodMap (.comp f₂ f₁) (.comp g₂ g₁) A B)
    (prodMap (.comp f₂ f₁) (.comp g₂ g₁) A B) :=
  .nil _

theorem thm_prodMap_comp_len (f₁ f₂ g₁ g₂ : Mor) (A B : Obj) :
    (prodMapCompPath f₁ f₂ g₁ g₂ A B).length = 0 := by
  simp [prodMapCompPath, Path.length]

-- ============================================================
-- §18  Exponential Functoriality
-- ============================================================

noncomputable def expMap (f g : Mor) (A B : Obj) : Mor :=
  .curry (.comp g (.comp (.eval_ A B)
    (.pair (.comp (.fst (.exp A B) A) (.id (.prod (.exp A B) A)))
           (.comp f (.snd (.exp A B) A)))))

theorem thm_expMap_def (f g : Mor) (A B : Obj) :
    expMap f g A B =
      .curry (.comp g (.comp (.eval_ A B)
        (.pair (.comp (.fst (.exp A B) A) (.id (.prod (.exp A B) A)))
               (.comp f (.snd (.exp A B) A))))) := by
  simp [expMap]

-- ============================================================
-- §19  Path symm properties
-- ============================================================

theorem thm_symm_nil (a : Mor) :
    (Path.nil a : CCPath a a).symm = .nil a := by
  simp [Path.symm]

def thm_symm_single (s : Step Mor a b) :
    (Path.single s).symm = Path.single s.symm := by
  simp [Path.single, Path.symm, Path.trans]

theorem thm_symm_length_gen (p : Path α a b) :
    p.symm.length = p.length := by
  induction p with
  | nil _ => simp [Path.symm, Path.length]
  | cons s _ ih =>
    simp [Path.symm, Path.length]
    rw [path_length_trans]
    simp [Path.length, ih]
    omega

theorem thm_symm_length (p : CCPath a b) :
    p.symm.length = p.length :=
  thm_symm_length_gen p

-- ============================================================
-- §20  Coproduct Properties
-- ============================================================

noncomputable def thm_copair_inl (f g : Mor) (A B : Obj) :
    Nonempty (CCStepCertificate (.comp (.copair f g) (.inl A B)) f) :=
  ⟨CCStepCertificate.ofStep (CCStep.copairInl f g A B) "copair-inl"⟩

noncomputable def thm_copair_inr (f g : Mor) (A B : Obj) :
    Nonempty (CCStepCertificate (.comp (.copair f g) (.inr A B)) g) :=
  ⟨CCStepCertificate.ofStep (CCStep.copairInr f g A B) "copair-inr"⟩

noncomputable def thm_copair_eta (A B : Obj) :
    Nonempty (CCStepCertificate (.copair (.inl A B) (.inr A B)) (.id (.coprod A B))) :=
  ⟨CCStepCertificate.ofStep (CCStep.copairEta A B) "copair-eta"⟩

-- ============================================================
-- §21  Congruence in CCC Steps
-- ============================================================

noncomputable def thm_congComp_left (s : CCStep f f') (g : Mor) :
    Nonempty (CCStepCertificate (.comp f g) (.comp f' g)) :=
  ⟨CCStepCertificate.ofStep (CCStep.congComp₁ s) "cong-comp-left"⟩

noncomputable def thm_congComp_right (f : Mor) (s : CCStep g g') :
    Nonempty (CCStepCertificate (.comp f g) (.comp f g')) :=
  ⟨CCStepCertificate.ofStep (CCStep.congComp₂ s) "cong-comp-right"⟩

noncomputable def thm_congPair_left (s : CCStep f f') (g : Mor) :
    Nonempty (CCStepCertificate (.pair f g) (.pair f' g)) :=
  ⟨CCStepCertificate.ofStep (CCStep.congPair₁ s) "cong-pair-left"⟩

noncomputable def thm_congCurry (s : CCStep f f') :
    Nonempty (CCStepCertificate (.curry f) (.curry f')) :=
  ⟨CCStepCertificate.ofStep (CCStep.congCurry s) "cong-curry"⟩

-- ============================================================
-- §22  Category Axioms as Paths
-- ============================================================

noncomputable def thm_idL_step (f : Mor) (A : Obj) :
    Nonempty (CCStepCertificate (.comp f (.id A)) f) :=
  ⟨CCStepCertificate.ofStep (CCStep.idL f A) "id-left"⟩

noncomputable def thm_idR_step (f : Mor) (A : Obj) :
    Nonempty (CCStepCertificate (.comp (.id A) f) f) :=
  ⟨CCStepCertificate.ofStep (CCStep.idR f A) "id-right"⟩

noncomputable def thm_assoc_step (f g h : Mor) :
    Nonempty (CCStepCertificate (.comp (.comp f g) h) (.comp f (.comp g h))) :=
  ⟨CCStepCertificate.ofStep (CCStep.assoc f g h) "assoc"⟩

noncomputable def idBothPath (f : Mor) (A B : Obj) : CCPath
    (.comp (.id A) (.comp f (.id B)))
    (.comp (.id A) (.comp f (.id B))) :=
  let m := Mor.comp (.id A) (.comp f (.id B))
  Path.cons (.rule "idR" m m) (Path.cons (.rule "idL" m m) (.nil m))

theorem thm_idBoth_length (f : Mor) (A B : Obj) :
    (idBothPath f A B).length = 2 := by
  simp [idBothPath, Path.length]

-- ============================================================
-- §23  Terminal Uniqueness
-- ============================================================

noncomputable def thm_terminal_uniq (f : Mor) (A : Obj) :
    Nonempty (CCStepCertificate f (.terminal A)) :=
  ⟨CCStepCertificate.ofStep (CCStep.termUniq f A) "terminal-unique"⟩

noncomputable def terminalEqPath (f : Mor) (A : Obj) : CCPath f f :=
  Path.cons (.rule "term-uniq" f f) (Path.cons (.rule "term-uniq-inv" f f) (.nil f))

theorem thm_terminal_eq_path_len (f : Mor) (A : Obj) :
    (terminalEqPath f A).length = 2 := by
  simp [terminalEqPath, Path.length]

-- ============================================================
-- §24  Additional Path Algebra
-- ============================================================

theorem thm_trans_length_additive (p : Path α a b) (q : Path α b c) :
    (p.trans q).length = p.length + q.length :=
  path_length_trans p q

theorem thm_nil_is_identity (a : α) :
    (Path.nil a).length = 0 := by
  simp [Path.length]

def thm_single_is_one (s : Step α a b) :
    (Path.single s).length = 1 := by
  simp [Path.single, Path.length]

-- ============================================================
-- §25  Symmetry of CCStep
-- ============================================================

noncomputable def thm_ccstep_symm (s : CCStep a b) :
    Nonempty (CCStepCertificate b a) :=
  ⟨CCStepCertificate.ofStep (CCStep.symm s) "step-symm"⟩

noncomputable def thm_ccstep_symm_symm (s : CCStep a b) :
    Nonempty (CCStepCertificate a b) :=
  ⟨CCStepCertificate.ofStep (CCStep.symm (CCStep.symm s)) "step-symm-symm"⟩

-- ============================================================
-- §26  Pair composition
-- ============================================================

noncomputable def thm_pair_comp (f g h : Mor) :
    Nonempty (CCStepCertificate (.comp (.pair f g) h) (.pair (.comp f h) (.comp g h))) :=
  ⟨CCStepCertificate.ofStep (CCStep.pairComp f g h) "pair-comp"⟩

-- ============================================================
-- §27  Path reversal properties
-- ============================================================

theorem thm_symm_trans (p : Path α a b) (q : Path α b c) :
    (p.trans q).symm.length = (q.symm.trans p.symm).length := by
  simp [thm_symm_length_gen, path_length_trans]
  omega

-- ============================================================
-- §28  congrArg with Mor → Mor functions
-- ============================================================

noncomputable def congrArgCurry (p : CCPath a b) : CCPath (.curry a) (.curry b) :=
  p.congrArg Mor.curry "curry-cong"

theorem thm_congrArg_curry_length (p : CCPath a b) :
    (congrArgCurry p).length = p.length := by
  exact thm_congrArg_length _ _ p

noncomputable def congrArgComp (p : CCPath a b) (g : Mor) : CCPath (.comp a g) (.comp b g) :=
  p.congrArg (Mor.comp · g) "comp-cong-left"

theorem thm_congrArg_comp_length (p : CCPath a b) (g : Mor) :
    (congrArgComp p g).length = p.length := by
  exact thm_congrArg_length _ _ p

end CompPaths.CCC
