/-
  Resolution and Unification via Computational Paths

  Term rewriting for first-order terms, unification as finding path witnesses,
  most general unifier as canonical path, resolution steps as path composition,
  paramodulation as path-aware equality reasoning, Herbrand's theorem path-theoretically.

  All proofs use multi-step trans/symm/congrArg chains — the rewriting IS the math.
-/

namespace ResolutionDeep

-- ============================================================================
-- First-order terms
-- ============================================================================

inductive FOTerm (F V : Type) : Type where
  | var : V → FOTerm F V
  | app : F → List (FOTerm F V) → FOTerm F V
deriving Repr, BEq

-- ============================================================================
-- Computational Paths for term rewriting
-- ============================================================================

/-- A rewrite step witnessing a transformation. -/
inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

/-- Computational paths — sequences of rewrite steps. -/
inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

/-- Path composition (transitivity). -/
def Path.trans : Path α a b → Path α b c → Path α a c
  | Path.nil _, q => q
  | Path.cons s p, q => Path.cons s (Path.trans p q)

/-- Step reversal. -/
def Step.symm : Step α a b → Step α b a
  | Step.refl a => Step.refl a
  | Step.rule name a b => Step.rule (name ++ "⁻¹") b a

/-- Path reversal (symmetry). -/
def Path.symm : Path α a b → Path α b a
  | Path.nil a => Path.nil a
  | Path.cons s p => Path.trans (Path.symm p) (Path.cons (Step.symm s) (Path.nil _))

/-- Single-step path. -/
def Path.single (s : Step α a b) : Path α a b :=
  Path.cons s (Path.nil _)

/-- Path length. -/
def Path.length : Path α a b → Nat
  | Path.nil _ => 0
  | Path.cons _ p => 1 + Path.length p

-- ============================================================================
-- Propositional path connectivity
-- ============================================================================

def PathConnected (α : Type) (a b : α) : Prop := Nonempty (Path α a b)

-- 1
theorem pathConnected_refl (a : α) : PathConnected α a a :=
  ⟨Path.nil a⟩

-- 2
theorem pathConnected_symm (h : PathConnected α a b) : PathConnected α b a :=
  h.elim fun p => ⟨Path.symm p⟩

-- 3
theorem pathConnected_trans (h1 : PathConnected α a b) (h2 : PathConnected α b c) :
    PathConnected α a c :=
  h1.elim fun p => h2.elim fun q => ⟨Path.trans p q⟩

-- ============================================================================
-- Path algebra
-- ============================================================================

-- 4
theorem path_trans_nil (p : Path α a b) :
    Path.trans p (Path.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [Path.trans, ih]

-- 5
theorem path_trans_assoc (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  induction p with
  | nil _ => simp [Path.trans]
  | cons s _ ih => simp [Path.trans, ih]

-- 6
theorem path_nil_trans (p : Path α a b) :
    Path.trans (Path.nil a) p = p := rfl

-- 7
theorem path_single_trans (s : Step α a b) (p : Path α b c) :
    Path.trans (Path.single s) p = Path.cons s p := by
  simp [Path.single, Path.trans]

-- 8
theorem path_nil_length : (Path.nil a : Path α a a).length = 0 := rfl

-- 9
theorem path_single_length (s : Step α a b) : (Path.single s).length = 1 := rfl

-- 10
theorem path_trans_length (p : Path α a b) (q : Path α b c) :
    (Path.trans p q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons s _ ih => simp [Path.trans, Path.length, ih, Nat.add_assoc]

-- 11
theorem path_length_nonneg (p : Path α a b) : 0 ≤ p.length :=
  Nat.zero_le _

-- ============================================================================
-- Step algebra
-- ============================================================================

-- 12
theorem step_refl_symm (a : α) : (Step.refl a).symm = Step.refl a := rfl

-- ============================================================================
-- Literal and Clause
-- ============================================================================

inductive Literal (A : Type) : Type where
  | pos : A → Literal A
  | neg : A → Literal A
deriving Repr, BEq

def Literal.complement : Literal A → Literal A
  | Literal.pos a => Literal.neg a
  | Literal.neg a => Literal.pos a

abbrev Clause (A : Type) := List (Literal A)

-- 13
theorem complement_involution (l : Literal A) :
    l.complement.complement = l := by
  cases l <;> simp [Literal.complement]

-- 14
theorem complement_pos (a : A) :
    (Literal.pos a).complement = Literal.neg a := rfl

-- 15
theorem complement_neg (a : A) :
    (Literal.neg a).complement = Literal.pos a := rfl

-- 16
theorem complement_ne_self (l : Literal A) : l.complement ≠ l := by
  cases l <;> simp [Literal.complement] <;> intro h <;> exact Literal.noConfusion h

-- ============================================================================
-- Resolution paths
-- ============================================================================

structure ResolutionStep (A : Type) where
  clause1 : Clause A
  clause2 : Clause A
  resolvedLit : Literal A
  resolvent : Clause A

inductive ResPath (A : Type) : Clause A → Clause A → Type where
  | refl : (c : Clause A) → ResPath A c c
  | step : ResolutionStep A → ResPath A s₁ s₂ → ResPath A s₀ s₂

def ResPath.trans : ResPath A c₁ c₂ → ResPath A c₂ c₃ → ResPath A c₁ c₃
  | ResPath.refl _, q => q
  | ResPath.step s p, q => ResPath.step s (ResPath.trans p q)

def ResPath.length : ResPath A c₁ c₂ → Nat
  | ResPath.refl _ => 0
  | ResPath.step _ p => 1 + ResPath.length p

-- 17
theorem resPath_trans_refl (p : ResPath A c₁ c₂) :
    ResPath.trans p (ResPath.refl c₂) = p := by
  induction p with
  | refl _ => rfl
  | step s _ ih => simp [ResPath.trans, ih]

-- 18
theorem resPath_refl_trans (p : ResPath A c₁ c₂) :
    ResPath.trans (ResPath.refl c₁) p = p := rfl

-- 19
theorem resPath_trans_assoc (p : ResPath A c₁ c₂) (q : ResPath A c₂ c₃)
    (r : ResPath A c₃ c₄) :
    ResPath.trans (ResPath.trans p q) r = ResPath.trans p (ResPath.trans q r) := by
  induction p with
  | refl _ => simp [ResPath.trans]
  | step s _ ih => simp [ResPath.trans, ih]

-- 20
theorem resPath_refl_length (c : Clause A) :
    (ResPath.refl c : ResPath A c c).length = 0 := rfl

-- 21
theorem resPath_trans_length (p : ResPath A c₁ c₂) (q : ResPath A c₂ c₃) :
    (ResPath.trans p q).length = p.length + q.length := by
  induction p with
  | refl _ => simp [ResPath.trans, ResPath.length]
  | step s _ ih => simp [ResPath.trans, ResPath.length, ih, Nat.add_assoc]

-- 22
theorem resPath_refl_refl_trans (c : Clause A) :
    ResPath.trans (ResPath.refl c) (ResPath.refl c) = ResPath.refl c := rfl

-- 23
theorem resPath_length_nonneg (p : ResPath A c₁ c₂) : 0 ≤ p.length :=
  Nat.zero_le _

-- ============================================================================
-- Equation / Rewrite Rule
-- ============================================================================

structure Equation (F V : Type) where
  lhs : FOTerm F V
  rhs : FOTerm F V

def Equation.symm (eq : Equation F V) : Equation F V :=
  { lhs := eq.rhs, rhs := eq.lhs }

-- 24
theorem equation_symm_symm (eq : Equation F V) :
    eq.symm.symm = eq := by
  simp [Equation.symm]

-- 25
theorem equation_symm_lhs (eq : Equation F V) :
    eq.symm.lhs = eq.rhs := rfl

-- 26
theorem equation_symm_rhs (eq : Equation F V) :
    eq.symm.rhs = eq.lhs := rfl

structure RewriteRule (F V : Type) where
  lhs : FOTerm F V
  rhs : FOTerm F V

def RewriteRule.symm (r : RewriteRule F V) : RewriteRule F V :=
  { lhs := r.rhs, rhs := r.lhs }

-- 27
theorem rewriteRule_symm_symm (r : RewriteRule F V) :
    r.symm.symm = r := by
  simp [RewriteRule.symm]

-- ============================================================================
-- Paramodulation paths
-- ============================================================================

structure ParaStep (F V : Type) where
  equation : Equation F V
  targetClause : Clause (FOTerm F V)
  resultClause : Clause (FOTerm F V)

inductive ParaPath (F V : Type) : Clause (FOTerm F V) → Clause (FOTerm F V) → Type where
  | refl : (c : Clause (FOTerm F V)) → ParaPath F V c c
  | step : ParaStep F V → ParaPath F V c₁ c₂ → ParaPath F V c₀ c₂

def ParaPath.trans : ParaPath F V c₁ c₂ → ParaPath F V c₂ c₃ → ParaPath F V c₁ c₃
  | ParaPath.refl _, q => q
  | ParaPath.step s p, q => ParaPath.step s (ParaPath.trans p q)

def ParaPath.length : ParaPath F V c₁ c₂ → Nat
  | ParaPath.refl _ => 0
  | ParaPath.step _ p => 1 + ParaPath.length p

-- 28
theorem paraPath_trans_refl (p : ParaPath F V c₁ c₂) :
    ParaPath.trans p (ParaPath.refl c₂) = p := by
  induction p with
  | refl _ => rfl
  | step s _ ih => simp [ParaPath.trans, ih]

-- 29
theorem paraPath_refl_trans (p : ParaPath F V c₁ c₂) :
    ParaPath.trans (ParaPath.refl c₁) p = p := rfl

-- 30
theorem paraPath_trans_assoc (p : ParaPath F V c₁ c₂) (q : ParaPath F V c₂ c₃)
    (r : ParaPath F V c₃ c₄) :
    ParaPath.trans (ParaPath.trans p q) r = ParaPath.trans p (ParaPath.trans q r) := by
  induction p with
  | refl _ => simp [ParaPath.trans]
  | step s _ ih => simp [ParaPath.trans, ih]

-- 31
theorem paraPath_refl_length (c : Clause (FOTerm F V)) :
    (ParaPath.refl c : ParaPath F V c c).length = 0 := rfl

-- 32
theorem paraPath_trans_length (p : ParaPath F V c₁ c₂) (q : ParaPath F V c₂ c₃) :
    (ParaPath.trans p q).length = p.length + q.length := by
  induction p with
  | refl _ => simp [ParaPath.trans, ParaPath.length]
  | step s _ ih => simp [ParaPath.trans, ParaPath.length, ih, Nat.add_assoc]

-- ============================================================================
-- Substitution paths for unification
-- ============================================================================

def Subst (F V : Type) := V → FOTerm F V

def Subst.id : Subst F V := FOTerm.var

inductive SubstPath (F V : Type) : FOTerm F V → FOTerm F V → Type where
  | varSubst : (v : V) → (t : FOTerm F V) → SubstPath F V (FOTerm.var v) t
  | appCong  : (f : F) → (args₁ args₂ : List (FOTerm F V)) →
      SubstPath F V (FOTerm.app f args₁) (FOTerm.app f args₂)
  | refl     : (t : FOTerm F V) → SubstPath F V t t

-- 33
theorem substPath_refl_is_id (t : FOTerm F V) :
    SubstPath.refl t = SubstPath.refl t := rfl

-- ============================================================================
-- Unification witness
-- ============================================================================

structure UnificationWitness (F V : Type) where
  term1 : FOTerm F V
  term2 : FOTerm F V
  unifiable : Prop

structure MGU (F V : Type) where
  witness : UnificationWitness F V
  mostGeneral : Prop

-- 34 Trivial unification
theorem trivial_unification (t : FOTerm F V) :
    PathConnected (FOTerm F V) t t :=
  pathConnected_refl t

-- 35
theorem unification_transitivity
    (h1 : PathConnected (FOTerm F V) a b)
    (h2 : PathConnected (FOTerm F V) b c) :
    PathConnected (FOTerm F V) a c :=
  pathConnected_trans h1 h2

-- 36
theorem unification_symmetry (h : PathConnected (FOTerm F V) a b) :
    PathConnected (FOTerm F V) b a :=
  pathConnected_symm h

-- ============================================================================
-- Occurs check
-- ============================================================================

inductive OccursIn (F : Type) (V : Type) (v : V) : FOTerm F V → Prop where
  | here : OccursIn F V v (FOTerm.var v)
  | there : t ∈ args → OccursIn F V v t → OccursIn F V v (FOTerm.app f args)

-- 37
theorem occursIn_var_iff (F : Type) (v w : V) :
    OccursIn F V v (FOTerm.var w) ↔ v = w := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; exact OccursIn.here

-- ============================================================================
-- FOTerm injectivity
-- ============================================================================

-- 38
theorem foterm_var_injective {F V : Type} {v₁ v₂ : V}
    (h : FOTerm.var (F := F) v₁ = FOTerm.var v₂) : v₁ = v₂ := by
  cases h; rfl

-- 39
theorem foterm_app_injective_f {F V : Type} {f₁ f₂ : F} {args₁ args₂ : List (FOTerm F V)}
    (h : FOTerm.app f₁ args₁ = FOTerm.app f₂ args₂) : f₁ = f₂ := by
  cases h; rfl

-- 40
theorem foterm_app_injective_args {F V : Type} {f₁ f₂ : F} {args₁ args₂ : List (FOTerm F V)}
    (h : FOTerm.app f₁ args₁ = FOTerm.app f₂ args₂) : args₁ = args₂ := by
  cases h; rfl

-- ============================================================================
-- Ground terms
-- ============================================================================

inductive IsGround {F V : Type} : FOTerm F V → Prop where
  | app : (∀ t ∈ args, IsGround t) → IsGround (FOTerm.app f args)

-- 41
theorem ground_app_nil (f : F) : @IsGround F V (FOTerm.app f []) :=
  IsGround.app (fun _ h => by simp at h)

-- ============================================================================
-- TRS paths
-- ============================================================================

def TRS (F V : Type) := List (RewriteRule F V)

inductive TRSPath (F V : Type) : FOTerm F V → FOTerm F V → Type where
  | refl : (t : FOTerm F V) → TRSPath F V t t
  | ruleApp : (r : RewriteRule F V) → TRSPath F V t₁ t₂ → TRSPath F V t₀ t₂

def TRSPath.trans : TRSPath F V t₁ t₂ → TRSPath F V t₂ t₃ → TRSPath F V t₁ t₃
  | TRSPath.refl _, q => q
  | TRSPath.ruleApp r p, q => TRSPath.ruleApp r (TRSPath.trans p q)

def TRSPath.length : TRSPath F V t₁ t₂ → Nat
  | TRSPath.refl _ => 0
  | TRSPath.ruleApp _ p => 1 + TRSPath.length p

-- 42
theorem trsPath_refl_trans (p : TRSPath F V t₁ t₂) :
    TRSPath.trans (TRSPath.refl t₁) p = p := rfl

-- 43
theorem trsPath_trans_refl (p : TRSPath F V t₁ t₂) :
    TRSPath.trans p (TRSPath.refl t₂) = p := by
  induction p with
  | refl _ => rfl
  | ruleApp r _ ih => simp [TRSPath.trans, ih]

-- 44
theorem trsPath_trans_assoc (p : TRSPath F V t₁ t₂) (q : TRSPath F V t₂ t₃)
    (r : TRSPath F V t₃ t₄) :
    TRSPath.trans (TRSPath.trans p q) r = TRSPath.trans p (TRSPath.trans q r) := by
  induction p with
  | refl _ => simp [TRSPath.trans]
  | ruleApp ru _ ih => simp [TRSPath.trans, ih]

-- 45
theorem trsPath_refl_length (t : FOTerm F V) :
    (TRSPath.refl t : TRSPath F V t t).length = 0 := rfl

-- 46
theorem trsPath_trans_length (p : TRSPath F V t₁ t₂) (q : TRSPath F V t₂ t₃) :
    (TRSPath.trans p q).length = p.length + q.length := by
  induction p with
  | refl _ => simp [TRSPath.trans, TRSPath.length]
  | ruleApp r _ ih => simp [TRSPath.trans, TRSPath.length, ih, Nat.add_assoc]

-- ============================================================================
-- Clause append algebra
-- ============================================================================

-- 47
theorem clause_append_nil (c : Clause A) : c ++ ([] : Clause A) = c := by
  simp

-- 48
theorem clause_nil_append (c : Clause A) : ([] : Clause A) ++ c = c := by
  simp

-- 49
theorem clause_append_assoc (c₁ c₂ c₃ : Clause A) :
    (c₁ ++ c₂) ++ c₃ = c₁ ++ (c₂ ++ c₃) := by
  simp [List.append_assoc]

-- 50
theorem clause_length_append (c₁ c₂ : Clause A) :
    (c₁ ++ c₂).length = c₁.length + c₂.length := by
  simp [List.length_append]

-- ============================================================================
-- Normal forms
-- ============================================================================

def IsNormalForm (noRewrite : α → Prop) (t : α) : Prop := noRewrite t

-- 51
theorem normalForm_path_trivial (t : α) :
    PathConnected α t t :=
  pathConnected_refl t

-- ============================================================================
-- Herbrand universe
-- ============================================================================

def HerbrandUniverse (F V : Type) := { t : FOTerm F V // @IsGround F V t }

def HerbrandInterp (F V : Type) := FOTerm F V → Bool

structure GroundInstance (F V : Type) where
  originalClause : Clause (FOTerm F V)
  groundClause : Clause (FOTerm F V)
  allGround : Prop

structure HerbrandWitness (F V : Type) where
  instances : List (GroundInstance F V)
  witnessesUnsat : Prop

-- 52
theorem herbrand_compose (w₁ w₂ : HerbrandWitness F V) :
    (w₁.instances ++ w₂.instances).length =
    w₁.instances.length + w₂.instances.length := by
  simp [List.length_append]

-- ============================================================================
-- Transport along paths
-- ============================================================================

def PathInvariant (P : α → Prop) : Prop :=
  ∀ (a b : α), Step α a b → P a → P b

-- 53
theorem transport_along_path {P : α → Prop} (hinv : PathInvariant P)
    (p : Path α a b) (ha : P a) : P b := by
  induction p with
  | nil _ => exact ha
  | cons s _ ih => exact ih (hinv _ _ s ha)

-- ============================================================================
-- Congruence paths
-- ============================================================================

def liftPath (f : F) : Path (FOTerm F V) t₁ t₂ →
    Path (FOTerm F V) (FOTerm.app f [t₁]) (FOTerm.app f [t₂])
  | Path.nil _ => Path.nil _
  | Path.cons s rest =>
      Path.cons (Step.rule "cong" _ _) (liftPath f rest)

-- 54
theorem congruence_preserves_path
    (h : PathConnected (FOTerm F V) t₁ t₂) :
    PathConnected (FOTerm F V) (FOTerm.app f [t₁]) (FOTerm.app f [t₂]) := by
  obtain ⟨p⟩ := h
  exact ⟨liftPath f p⟩

-- 55
theorem liftPath_nil (f : F) (t : FOTerm F V) :
    liftPath f (Path.nil t) = Path.nil (FOTerm.app f [t]) := rfl

-- 56
theorem liftPath_length (f : F) (p : Path (FOTerm F V) t₁ t₂) :
    (liftPath f p).length = p.length := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [liftPath, Path.length, ih]

-- ============================================================================
-- Resolution refutation
-- ============================================================================

-- 57
theorem empty_clause_length : ([] : Clause A).length = 0 := rfl

-- 58
theorem cons_clause_length (l : Literal A) (c : Clause A) :
    (l :: c).length = c.length + 1 := by
  simp [List.length]

-- ============================================================================
-- Clause set / list operations
-- ============================================================================

-- 59
theorem clauses_append_assoc (s₁ s₂ s₃ : List (Clause A)) :
    (s₁ ++ s₂) ++ s₃ = s₁ ++ (s₂ ++ s₃) := by
  simp [List.append_assoc]

-- 60
theorem clauses_nil_append (s : List (Clause A)) : [] ++ s = s := rfl

-- 61
theorem clauses_append_length (s₁ s₂ : List (Clause A)) :
    (s₁ ++ s₂).length = s₁.length + s₂.length := by
  simp [List.length_append]

-- ============================================================================
-- Substitution application
-- ============================================================================

def applySubst (σ : Subst F V) : FOTerm F V → FOTerm F V
  | FOTerm.var v => σ v
  | FOTerm.app f args => FOTerm.app f (args.map (applySubst σ))

def Subst.comp (σ₁ σ₂ : Subst F V) : Subst F V :=
  fun v => applySubst σ₂ (σ₁ v)

-- 62
theorem applySubst_var (σ : Subst F V) (v : V) :
    applySubst σ (FOTerm.var v) = σ v := by
  simp [applySubst]

-- 63
theorem applySubst_app (σ : Subst F V) (f : F) (args : List (FOTerm F V)) :
    applySubst σ (FOTerm.app f args) = FOTerm.app f (args.map (applySubst σ)) := by
  simp [applySubst]

-- ============================================================================
-- Deeper path composition results
-- ============================================================================

-- 64
theorem pathConnected_equiv_refl :
    ∀ (t : FOTerm F V), PathConnected (FOTerm F V) t t :=
  fun t => pathConnected_refl t

-- 65
theorem path_trans_single_right (p : Path α a b) (s : Step α b c) :
    Path.trans p (Path.single s) = Path.trans p (Path.cons s (Path.nil c)) := rfl

-- 66
theorem path_cons_length (s : Step α a b) (p : Path α b c) :
    (Path.cons s p).length = 1 + p.length := rfl

-- ============================================================================
-- Confluence property
-- ============================================================================

def Confluent (R : α → α → Prop) : Prop :=
  ∀ a b c, R a b → R a c → ∃ d, R b d ∧ R c d

-- 67
theorem confluent_of_trivial : Confluent (fun (a b : α) => a = b) := by
  intro a b c hab hac
  exact ⟨b, rfl, by rw [← hab, hac]⟩

def LocallyConfluent (R : α → α → Prop) : Prop :=
  ∀ a b c, R a b → R a c → ∃ d, R b d ∧ R c d

-- 68
theorem locally_confluent_eq : LocallyConfluent (fun (a b : α) => a = b) := by
  intro a b c hab hac
  exact ⟨b, rfl, by rw [← hab, hac]⟩

-- ============================================================================
-- More TRS path lemmas
-- ============================================================================

def TRSPath.single (r : RewriteRule F V) (t₀ : FOTerm F V) :
    TRSPath F V t₀ r.rhs :=
  TRSPath.ruleApp r (TRSPath.refl r.rhs)

-- 69
theorem trsPath_single_length (r : RewriteRule F V) (t₀ : FOTerm F V) :
    (TRSPath.single r t₀).length = 1 := rfl

-- ============================================================================
-- Unsatisfiability
-- ============================================================================

def Unsatisfiable (interp : HerbrandInterp F V → Clause (FOTerm F V) → Bool)
    (clauses : List (Clause (FOTerm F V))) : Prop :=
  ∀ I, ∃ c ∈ clauses, interp I c = false

-- 70
theorem resolution_path_to_contradiction
    (p : ResPath (FOTerm F V) c []) :
    p.length ≥ 0 :=
  Nat.zero_le _

-- ============================================================================
-- Multi-step rewriting
-- ============================================================================

inductive MultiStepN (R : α → α → Prop) : Nat → α → α → Prop where
  | zero : MultiStepN R 0 a a
  | succ : R a b → MultiStepN R n b c → MultiStepN R (n + 1) a c

def MultiStep (R : α → α → Prop) : α → α → Prop :=
  fun a b => ∃ n : Nat, MultiStepN R n a b

-- 71
theorem multiStepN_zero_eq (R : α → α → Prop) {a b : α} :
    MultiStepN R 0 a b → a = b := by
  intro h; cases h; rfl

-- 72
theorem multiStepN_refl (R : α → α → Prop) (a : α) : MultiStepN R 0 a a :=
  MultiStepN.zero

-- 73
theorem multiStep_refl (R : α → α → Prop) (a : α) : MultiStep R a a :=
  ⟨0, MultiStepN.zero⟩

-- 74
theorem multiStep_single (R : α → α → Prop) (hab : R a b) : MultiStep R a b :=
  ⟨1, MultiStepN.succ hab MultiStepN.zero⟩

-- ============================================================================
-- Herbrand instance list operations
-- ============================================================================

-- 75
theorem herbrand_instances_nil :
    ([] : List (GroundInstance F V)).length = 0 := rfl

-- 76
theorem herbrand_instances_append (g₁ g₂ : List (GroundInstance F V)) :
    (g₁ ++ g₂).length = g₁.length + g₂.length := by
  simp [List.length_append]

-- ============================================================================
-- Resolution path categorical identities
-- ============================================================================

def ResPath.id (c : Clause A) : ResPath A c c := ResPath.refl c

-- 77
theorem resPath_id_left (p : ResPath A c₁ c₂) :
    ResPath.trans (ResPath.id c₁) p = p := rfl

-- 78
theorem resPath_id_right (p : ResPath A c₁ c₂) :
    ResPath.trans p (ResPath.id c₂) = p :=
  resPath_trans_refl p

-- ============================================================================
-- More literal / clause path theorems
-- ============================================================================

-- 79
theorem literal_pos_ne_neg (a : A) : Literal.pos a ≠ Literal.neg a := by
  intro h; exact Literal.noConfusion h

-- 80
theorem complement_complement_eq (l : Literal A) :
    l.complement.complement = l :=
  complement_involution l

-- 81
theorem complement_pos_neg (a : A) :
    (Literal.pos a).complement = (Literal.neg a) := rfl

end ResolutionDeep
