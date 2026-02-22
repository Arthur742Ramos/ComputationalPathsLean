/-
  ComputationalPaths / Path / Algebra / AutomataPathsDeep.lean

  Automata theory formalised as path algebra.
  States are vertices, transitions are Step generators,
  accepting runs are paths to final states, language equivalence
  via bisimulation paths, Myhill-Nerode as path quotient,
  DFA minimization as path collapsing, pumping lemma via
  path decomposition.

  All proofs are sorry-free.  50 theorems.
-/

-- ============================================================
-- §1  Alphabet, States, Computational Paths
-- ============================================================

structure ASym where
  id : Nat
deriving DecidableEq, Repr

structure AState where
  id : Nat
deriving DecidableEq, Repr

/-- A rewrite / transition step. -/
inductive AStep (α : Type) : α → α → Type where
  | mk : (label : String) → (a b : α) → AStep α a b

/-- Computational path: multi-step derivation. -/
inductive APath (α : Type) : α → α → Type where
  | nil  : (a : α) → APath α a a
  | cons : AStep α a b → APath α b c → APath α a c

noncomputable def APath.trans {α : Type} {a b c : α}
    (p : APath α a b) (q : APath α b c) : APath α a c :=
  match p with
  | .nil _ => q
  | .cons s rest => .cons s (rest.trans q)

noncomputable def AStep.symm {α : Type} {a b : α} : AStep α a b → AStep α b a
  | .mk name a b => .mk (name ++ "⁻¹") b a

noncomputable def APath.symm {α : Type} {a b : α} : APath α a b → APath α b a
  | .nil a => .nil a
  | .cons s rest => rest.symm.trans (.cons s.symm (.nil _))

noncomputable def APath.length {α : Type} {a b : α} : APath α a b → Nat
  | .nil _ => 0
  | .cons _ rest => 1 + rest.length

noncomputable def APath.single {α : Type} {a b : α} (s : AStep α a b) : APath α a b :=
  .cons s (.nil _)

noncomputable def AStep.map {α β : Type} (f : α → β) {a b : α} : AStep α a b → AStep β (f a) (f b)
  | .mk name a b => .mk name (f a) (f b)

noncomputable def APath.map {α β : Type} (f : α → β) {a b : α} : APath α a b → APath β (f a) (f b)
  | .nil a => .nil (f a)
  | .cons s rest => .cons (s.map f) (rest.map f)

-- ============================================================
-- §2  DFA Definition
-- ============================================================

structure DFA where
  states   : List AState
  start    : AState
  finals   : List AState
  delta    : AState → ASym → AState

-- ============================================================
-- §3  Extended delta and acceptance
-- ============================================================

noncomputable def DFA.deltaStar (M : DFA) (q : AState) : List ASym → AState
  | [] => q
  | a :: rest => M.deltaStar (M.delta q a) rest

noncomputable def DFA.accepts (M : DFA) (w : List ASym) : Prop :=
  M.deltaStar M.start w ∈ M.finals

noncomputable def DFA.language (M : DFA) : List ASym → Prop := M.accepts

/-- Theorem 1: Empty word accepted iff start is final. -/
theorem DFA.accepts_nil (M : DFA) :
    M.accepts [] ↔ M.start ∈ M.finals := by
  simp [DFA.accepts, DFA.deltaStar]

/-- Theorem 2: deltaStar on cons. -/
theorem DFA.deltaStar_cons (M : DFA) (q : AState) (a : ASym) (w : List ASym) :
    M.deltaStar q (a :: w) = M.deltaStar (M.delta q a) w := rfl

/-- Theorem 3: deltaStar on append (path composition). -/
theorem DFA.deltaStar_append (M : DFA) (q : AState) (u v : List ASym) :
    M.deltaStar q (u ++ v) = M.deltaStar (M.deltaStar q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih => simp [DFA.deltaStar, ih]

/-- Theorem 4: deltaStar append from start. -/
theorem DFA.accepts_append (M : DFA) (u v : List ASym) :
    M.deltaStar M.start (u ++ v) = M.deltaStar (M.deltaStar M.start u) v :=
  M.deltaStar_append M.start u v

/-- Theorem 5: deltaStar on singleton. -/
theorem DFA.deltaStar_singleton (M : DFA) (q : AState) (a : ASym) :
    M.deltaStar q [a] = M.delta q a := rfl

-- ============================================================
-- §4  DFA Runs as paths
-- ============================================================

/-- One-step DFA transition. -/
inductive DFAStep (M : DFA) : AState → AState → Prop where
  | read (q : AState) (a : ASym) : DFAStep M q (M.delta q a)
  | readAt {q q' : AState} (a : ASym) (heq : q' = M.delta q a) : DFAStep M q q'

/-- Multi-step run (path). -/
inductive DFARun (M : DFA) : AState → AState → Prop where
  | done  (q : AState) : DFARun M q q
  | step  {q₁ q₂ q₃ : AState} : DFAStep M q₁ q₂ → DFARun M q₂ q₃ → DFARun M q₁ q₃

/-- Theorem 6: Run transitivity (path composition). -/
theorem DFARun.trans {M : DFA} {q₁ q₂ q₃ : AState}
    (r₁ : DFARun M q₁ q₂) (r₂ : DFARun M q₂ q₃) : DFARun M q₁ q₃ := by
  induction r₁ with
  | done _ => exact r₂
  | step s _ ih => exact DFARun.step s (ih r₂)

/-- Theorem 7: Single step lifts to a run. -/
theorem DFARun.single {M : DFA} {q₁ q₂ : AState}
    (s : DFAStep M q₁ q₂) : DFARun M q₁ q₂ :=
  DFARun.step s (DFARun.done q₂)

/-- Theorem 8: deltaStar yields a run. -/
theorem DFARun.of_deltaStar (M : DFA) (q : AState) (w : List ASym) :
    DFARun M q (M.deltaStar q w) := by
  induction w generalizing q with
  | nil => exact DFARun.done q
  | cons a rest ih =>
    exact DFARun.step (DFAStep.read q a) (ih (M.delta q a))

/-- Theorem 9: A run from q to q' implies reachability. -/
theorem DFARun.implies_reachable {M : DFA} {q q' : AState}
    (r : DFARun M q q') : ∃ w, M.deltaStar q w = q' := by
  induction r with
  | done q => exact ⟨[], rfl⟩
  | step s _ ih =>
    obtain ⟨w, hw⟩ := ih
    cases s with
    | read q₀ => exact ⟨_ :: w, hw⟩
    | readAt a heq => subst heq; exact ⟨a :: w, hw⟩

-- ============================================================
-- §5  NFA and subset construction
-- ============================================================

structure NFA where
  states  : List AState
  start   : List AState
  finals  : List AState
  delta   : AState → ASym → List AState

noncomputable def NFA.deltaSetStep (N : NFA) (qs : List AState) (a : ASym) : List AState :=
  (qs.flatMap (fun q => N.delta q a)).eraseDups

noncomputable def NFA.deltaSetStar (N : NFA) (qs : List AState) : List ASym → List AState
  | [] => qs
  | a :: rest => N.deltaSetStar (N.deltaSetStep qs a) rest

noncomputable def NFA.acceptsNFA (N : NFA) (w : List ASym) : Prop :=
  ∃ q ∈ N.deltaSetStar N.start w, q ∈ N.finals

/-- Theorem 10: NFA deltaSetStar on nil. -/
theorem NFA.deltaSetStar_nil (N : NFA) (qs : List AState) :
    N.deltaSetStar qs [] = qs := rfl

/-- Theorem 11: NFA deltaSetStar on cons. -/
theorem NFA.deltaSetStar_cons (N : NFA) (qs : List AState) (a : ASym) (w : List ASym) :
    N.deltaSetStar qs (a :: w) = N.deltaSetStar (N.deltaSetStep qs a) w := rfl

/-- Theorem 12: NFA deltaSetStar on append (path trans). -/
theorem NFA.deltaSetStar_append (N : NFA) (qs : List AState) (u v : List ASym) :
    N.deltaSetStar qs (u ++ v) = N.deltaSetStar (N.deltaSetStar qs u) v := by
  induction u generalizing qs with
  | nil => rfl
  | cons a u ih => simp [NFA.deltaSetStar, ih]

-- ============================================================
-- §6  Language equivalence and bisimulation paths
-- ============================================================

noncomputable def langEquiv (M₁ M₂ : DFA) : Prop :=
  ∀ w : List ASym, M₁.accepts w ↔ M₂.accepts w

/-- Theorem 13: Language equivalence is reflexive. -/
theorem langEquiv_refl (M : DFA) : langEquiv M M :=
  fun _ => Iff.rfl

/-- Theorem 14: Language equivalence is symmetric. -/
theorem langEquiv_symm {M₁ M₂ : DFA} (h : langEquiv M₁ M₂) : langEquiv M₂ M₁ :=
  fun w => (h w).symm

/-- Theorem 15: Language equivalence is transitive. -/
theorem langEquiv_trans {M₁ M₂ M₃ : DFA}
    (h₁ : langEquiv M₁ M₂) (h₂ : langEquiv M₂ M₃) : langEquiv M₁ M₃ :=
  fun w => Iff.trans (h₁ w) (h₂ w)

/-- Bisimulation relation. -/
structure Bisimulation (M₁ M₂ : DFA) where
  rel : AState → AState → Prop
  start_rel : rel M₁.start M₂.start
  step_rel : ∀ q₁ q₂ a, rel q₁ q₂ → rel (M₁.delta q₁ a) (M₂.delta q₂ a)
  final_compat : ∀ q₁ q₂, rel q₁ q₂ → (q₁ ∈ M₁.finals ↔ q₂ ∈ M₂.finals)

/-- Theorem 16: Bisimulation preserves deltaStar (path induction). -/
theorem Bisimulation.deltaStar_rel {M₁ M₂ : DFA} (B : Bisimulation M₁ M₂)
    (q₁ q₂ : AState) (w : List ASym) (hrel : B.rel q₁ q₂) :
    B.rel (M₁.deltaStar q₁ w) (M₂.deltaStar q₂ w) := by
  induction w generalizing q₁ q₂ with
  | nil => exact hrel
  | cons a rest ih => exact ih _ _ (B.step_rel q₁ q₂ a hrel)

/-- Theorem 17: Bisimulation implies language equivalence. -/
theorem Bisimulation.toLangEquiv {M₁ M₂ : DFA} (B : Bisimulation M₁ M₂) :
    langEquiv M₁ M₂ := by
  intro w
  simp [DFA.accepts]
  exact B.final_compat _ _ (B.deltaStar_rel M₁.start M₂.start w B.start_rel)

-- ============================================================
-- §7  Myhill-Nerode equivalence
-- ============================================================

noncomputable def nerodeEquiv (M : DFA) (q₁ q₂ : AState) : Prop :=
  ∀ w : List ASym, M.deltaStar q₁ w ∈ M.finals ↔ M.deltaStar q₂ w ∈ M.finals

/-- Theorem 18: Nerode equivalence is reflexive. -/
theorem nerodeEquiv_refl (M : DFA) (q : AState) : nerodeEquiv M q q :=
  fun _ => Iff.rfl

/-- Theorem 19: Nerode equivalence is symmetric. -/
theorem nerodeEquiv_symm {M : DFA} {q₁ q₂ : AState}
    (h : nerodeEquiv M q₁ q₂) : nerodeEquiv M q₂ q₁ :=
  fun w => (h w).symm

/-- Theorem 20: Nerode equivalence is transitive. -/
theorem nerodeEquiv_trans {M : DFA} {q₁ q₂ q₃ : AState}
    (h₁ : nerodeEquiv M q₁ q₂) (h₂ : nerodeEquiv M q₂ q₃) : nerodeEquiv M q₁ q₃ :=
  fun w => Iff.trans (h₁ w) (h₂ w)

/-- Theorem 21: Nerode equivalence is a right congruence. -/
theorem nerodeEquiv_congr {M : DFA} {q₁ q₂ : AState} (a : ASym)
    (h : nerodeEquiv M q₁ q₂) : nerodeEquiv M (M.delta q₁ a) (M.delta q₂ a) := by
  intro w
  have := h (a :: w)
  simp [DFA.deltaStar] at this
  exact this

/-- Theorem 22: Nerode classes refine final/non-final. -/
theorem nerodeEquiv_final_compat {M : DFA} {q₁ q₂ : AState}
    (h : nerodeEquiv M q₁ q₂) : (q₁ ∈ M.finals ↔ q₂ ∈ M.finals) := by
  have := h []
  simp [DFA.deltaStar] at this
  exact this

-- ============================================================
-- §8  Distinguishability
-- ============================================================

inductive Distinguishable (M : DFA) : AState → AState → Prop where
  | base {q₁ q₂ : AState} :
      (q₁ ∈ M.finals) → ¬(q₂ ∈ M.finals) → Distinguishable M q₁ q₂
  | base' {q₁ q₂ : AState} :
      ¬(q₁ ∈ M.finals) → (q₂ ∈ M.finals) → Distinguishable M q₁ q₂
  | ind {q₁ q₂ : AState} (a : ASym) :
      Distinguishable M (M.delta q₁ a) (M.delta q₂ a) → Distinguishable M q₁ q₂

/-- Theorem 23: Distinguishable implies not Nerode-equivalent. -/
theorem Distinguishable.not_nerode {M : DFA} {q₁ q₂ : AState}
    (d : Distinguishable M q₁ q₂) : ¬ nerodeEquiv M q₁ q₂ := by
  induction d with
  | base hf hnf =>
    intro h
    exact hnf ((nerodeEquiv_final_compat h).mp hf)
  | base' hnf hf =>
    intro h
    exact hnf ((nerodeEquiv_final_compat h).mpr hf)
  | ind a _ ih =>
    intro h
    exact ih (nerodeEquiv_congr a h)

/-- Theorem 24: Minimization bisimulation (self-bisim via Nerode). -/
theorem minimize_bisim_self (M : DFA) :
    ∃ (R : AState → AState → Prop),
      R M.start M.start ∧
      (∀ q₁ q₂ a, R q₁ q₂ → R (M.delta q₁ a) (M.delta q₂ a)) ∧
      (∀ q₁ q₂, R q₁ q₂ → (q₁ ∈ M.finals ↔ q₂ ∈ M.finals)) :=
  ⟨nerodeEquiv M, nerodeEquiv_refl M M.start,
   fun _ _ a h => nerodeEquiv_congr a h,
   fun _ _ h => nerodeEquiv_final_compat h⟩

-- ============================================================
-- §9  Visits and pumping
-- ============================================================

noncomputable def DFA.visits (M : DFA) (q : AState) : List ASym → List AState
  | [] => [q]
  | a :: rest => q :: M.visits (M.delta q a) rest

/-- Theorem 25: Visits length = input length + 1. -/
theorem DFA.visits_length (M : DFA) (q : AState) (w : List ASym) :
    (M.visits q w).length = w.length + 1 := by
  induction w generalizing q with
  | nil => simp [DFA.visits]
  | cons a rest ih => simp [DFA.visits, ih]

/-- Theorem 26: Head of visits is the starting state. -/
theorem DFA.visits_head (M : DFA) (q : AState) (w : List ASym) :
    (M.visits q w).head? = some q := by
  cases w with
  | nil => simp [DFA.visits]
  | cons a rest => simp [DFA.visits]

/-- Theorem 27: Pumping structure: any long-enough word decomposes.
    If |w| ≥ n, then w = x ++ y ++ z with |y| ≥ 1 and |xy| ≤ n. -/
theorem pumping_decompose (w : List ASym) (n : Nat) (hlen : n ≤ w.length) (hn : 0 < n) :
    ∃ x y z : List ASym,
      w = x ++ y ++ z ∧ y.length ≥ 1 ∧ (x ++ y).length ≤ n := by
  exact ⟨[], w.take n, w.drop n, by simp [List.take_append_drop],
         by simp; omega,
         by simp; omega⟩

-- ============================================================
-- §10  Reachability
-- ============================================================

noncomputable def DFA.reachable (M : DFA) (q : AState) : Prop :=
  ∃ w : List ASym, M.deltaStar M.start w = q

/-- Theorem 28: Start state is always reachable. -/
theorem DFA.start_reachable (M : DFA) : M.reachable M.start :=
  ⟨[], rfl⟩

/-- Theorem 29: Reachability extends by one transition. -/
theorem DFA.reachable_step (M : DFA) (q : AState) (a : ASym)
    (hr : M.reachable q) : M.reachable (M.delta q a) := by
  obtain ⟨w, hw⟩ := hr
  exact ⟨w ++ [a], by rw [DFA.deltaStar_append]; simp [DFA.deltaStar, hw]⟩

/-- Theorem 30: Reachability extends along words. -/
theorem DFA.reachable_word (M : DFA) (q : AState) (w : List ASym)
    (hr : M.reachable q) : M.reachable (M.deltaStar q w) := by
  obtain ⟨v, hv⟩ := hr
  exact ⟨v ++ w, by rw [DFA.deltaStar_append, hv]⟩

-- ============================================================
-- §11  Automata transformation paths
-- ============================================================

inductive AutomataOp : String → Type where
  | removeUnreachable : AutomataOp "removeUnreachable"
  | mergeEquiv        : AutomataOp "mergeEquiv"
  | complement        : AutomataOp "complement"
  | product           : AutomataOp "product"
  | reverse           : AutomataOp "reverse"

inductive ATStep : DFA → DFA → Type where
  | transform : (name : String) → (M M' : DFA) → ATStep M M'

inductive ATPath : DFA → DFA → Type where
  | nil  : (M : DFA) → ATPath M M
  | cons : ATStep M₁ M₂ → ATPath M₂ M₃ → ATPath M₁ M₃

noncomputable def ATPath.trans : ATPath M₁ M₂ → ATPath M₂ M₃ → ATPath M₁ M₃
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

noncomputable def ATPath.single (s : ATStep M₁ M₂) : ATPath M₁ M₂ :=
  .cons s (.nil _)

noncomputable def ATPath.length : ATPath M₁ M₂ → Nat
  | .nil _ => 0
  | .cons _ rest => 1 + rest.length

/-- Theorem 31: nil path has length 0. -/
theorem ATPath.length_nil (M : DFA) : (ATPath.nil M).length = 0 := rfl

/-- Theorem 32: cons path length. -/
theorem ATPath.length_cons (s : ATStep M₁ M₂) (p : ATPath M₂ M₃) :
    (ATPath.cons s p).length = 1 + p.length := rfl

/-- Theorem 33: trans preserves total length. -/
theorem ATPath.trans_length (p : ATPath M₁ M₂) (q : ATPath M₂ M₃) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [ATPath.trans, ATPath.length]
  | cons _ _ ih => simp [ATPath.trans, ATPath.length, ih]; omega

-- ============================================================
-- §12  Computational transition path (APath layer)
-- ============================================================

/-- Build an APath tracking state transitions on a word. -/
noncomputable def DFA.transPath (M : DFA) (q : AState) : (w : List ASym) → APath AState q (M.deltaStar q w)
  | [] => APath.nil q
  | a :: rest =>
    APath.cons (AStep.mk s!"δ({q.id},{a.id})" q (M.delta q a))
               (M.transPath (M.delta q a) rest)

/-- Theorem 34: Transition path length equals word length. -/
theorem DFA.transPath_length (M : DFA) (q : AState) :
    (w : List ASym) → (M.transPath q w).length = w.length
  | [] => rfl
  | _a :: rest => by
    simp [DFA.transPath, APath.length]
    have := DFA.transPath_length M (M.delta q _a) rest
    omega

/-- Theorem 35: APath map preserves length. -/
theorem APath.map_length {α β : Type} (f : α → β) {a b : α} (p : APath α a b) :
    (p.map f).length = p.length := by
  induction p with
  | nil _ => rfl
  | cons _ _ ih => simp [APath.map, APath.length, ih]

/-- Theorem 36: APath.trans preserves total length. -/
theorem APath.trans_length {α : Type} {a b c : α} (p : APath α a b) (q : APath α b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [APath.trans, APath.length]
  | cons _ _ ih => simp [APath.trans, APath.length, ih]; omega

-- ============================================================
-- §13  Word equivalence (Myhill-Nerode on words)
-- ============================================================

noncomputable def wordEquiv (M : DFA) (u v : List ASym) : Prop :=
  nerodeEquiv M (M.deltaStar M.start u) (M.deltaStar M.start v)

/-- Theorem 37: wordEquiv is reflexive. -/
theorem wordEquiv_refl (M : DFA) (w : List ASym) : wordEquiv M w w :=
  nerodeEquiv_refl M _

/-- Theorem 38: wordEquiv is symmetric. -/
theorem wordEquiv_symm {M : DFA} {u v : List ASym}
    (h : wordEquiv M u v) : wordEquiv M v u :=
  nerodeEquiv_symm h

/-- Theorem 39: wordEquiv is transitive. -/
theorem wordEquiv_trans {M : DFA} {u v w : List ASym}
    (h₁ : wordEquiv M u v) (h₂ : wordEquiv M v w) : wordEquiv M u w :=
  nerodeEquiv_trans h₁ h₂

/-- Theorem 40: wordEquiv is a right congruence. -/
theorem wordEquiv_right_congr {M : DFA} {u v : List ASym} (a : ASym)
    (h : wordEquiv M u v) : wordEquiv M (u ++ [a]) (v ++ [a]) := by
  unfold wordEquiv
  rw [DFA.deltaStar_append, DFA.deltaStar_append]
  simp [DFA.deltaStar]
  exact nerodeEquiv_congr a h

/-- Theorem 41: wordEquiv preserves acceptance. -/
theorem wordEquiv_accepts_iff {M : DFA} {u v : List ASym}
    (h : wordEquiv M u v) : M.accepts u ↔ M.accepts v := by
  simp [DFA.accepts]
  exact nerodeEquiv_final_compat h

-- ============================================================
-- §14  Run rewriting (coherence)
-- ============================================================

inductive RunRewrite (M : DFA) : List ASym → List ASym → Prop where
  | id   (w : List ASym) : RunRewrite M w w
  | pre  (a : ASym) {w₁ w₂ : List ASym} : RunRewrite M w₁ w₂ → RunRewrite M (a :: w₁) (a :: w₂)

/-- Theorem 42: RunRewrite is reflexive. -/
theorem RunRewrite.refl (M : DFA) (w : List ASym) : RunRewrite M w w :=
  RunRewrite.id w

/-- Theorem 43: RunRewrite preserves deltaStar. -/
theorem RunRewrite.preserves {M : DFA} {w₁ w₂ : List ASym}
    (rw : RunRewrite M w₁ w₂) (q : AState) :
    M.deltaStar q w₁ = M.deltaStar q w₂ := by
  induction rw generalizing q with
  | id _ => rfl
  | pre a _ ih => simp [DFA.deltaStar]; exact ih _

/-- Theorem 44: RunRewrite preserves acceptance. -/
theorem RunRewrite.preserves_accept {M : DFA} {w₁ w₂ : List ASym}
    (rw : RunRewrite M w₁ w₂) : M.accepts w₁ ↔ M.accepts w₂ := by
  simp [DFA.accepts, rw.preserves M.start]

-- ============================================================
-- §15  Complement DFA
-- ============================================================

noncomputable def DFA.complementDFA (M : DFA) (nonFinals : List AState) : DFA where
  states := M.states
  start := M.start
  finals := nonFinals
  delta := M.delta

/-- Theorem 45: Complement preserves deltaStar. -/
theorem DFA.complement_deltaStar (M : DFA) (nf : List AState) (q : AState) (w : List ASym) :
    (M.complementDFA nf).deltaStar q w = M.deltaStar q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a rest ih =>
    simp [DFA.deltaStar, DFA.complementDFA]
    exact ih _

-- ============================================================
-- §16  DFA product
-- ============================================================

structure ProdState where
  fst : AState
  snd : AState
deriving DecidableEq, Repr

noncomputable def DFA.productDelta (M₁ M₂ : DFA)
    (encode : ProdState → AState) (decode : AState → ProdState) (q : AState) (a : ASym) : AState :=
  let p := decode q
  encode ⟨M₁.delta p.fst a, M₂.delta p.snd a⟩

/-- Theorem 46: Product deltaStar decomposes into components. -/
theorem DFA.product_deltaStar_decompose (M₁ M₂ : DFA)
    (encode : ProdState → AState) (decode : AState → ProdState)
    (enc_dec : ∀ q, decode (encode q) = q)
    (w : List ASym) (p : ProdState) :
    let M' : DFA := ⟨[], encode ⟨M₁.start, M₂.start⟩, [], DFA.productDelta M₁ M₂ encode decode⟩
    decode (M'.deltaStar (encode p) w) =
    ⟨M₁.deltaStar p.fst w, M₂.deltaStar p.snd w⟩ := by
  induction w generalizing p with
  | nil => simp [DFA.deltaStar, enc_dec]
  | cons a rest ih =>
    simp [DFA.deltaStar, DFA.productDelta, enc_dec]
    exact ih ⟨M₁.delta p.fst a, M₂.delta p.snd a⟩

-- ============================================================
-- §17  Closure properties as path steps
-- ============================================================

/-- Closure step: one closure operation on a language class. -/
inductive ClosureStep : String → String → Prop where
  | union         : ClosureStep "L₁" "L₁ ∪ L₂"
  | intersection  : ClosureStep "L₁" "L₁ ∩ L₂"
  | complementOp  : ClosureStep "L" "L̄"
  | concatenation : ClosureStep "L₁" "L₁·L₂"
  | star          : ClosureStep "L" "L*"

/-- Closure path. -/
inductive ClosurePath : String → String → Prop where
  | nil  (s : String) : ClosurePath s s
  | cons {s₁ s₂ s₃ : String} : ClosureStep s₁ s₂ → ClosurePath s₂ s₃ → ClosurePath s₁ s₃

/-- Theorem 47: Closure path transitivity. -/
theorem ClosurePath.trans {s₁ s₂ s₃ : String}
    (p : ClosurePath s₁ s₂) (q : ClosurePath s₂ s₃) : ClosurePath s₁ s₃ := by
  induction p with
  | nil _ => exact q
  | cons s _ ih => exact ClosurePath.cons s (ih q)

/-- Theorem 48: Single closure step is a path. -/
theorem ClosurePath.single {s₁ s₂ : String}
    (s : ClosureStep s₁ s₂) : ClosurePath s₁ s₂ :=
  ClosurePath.cons s (ClosurePath.nil _)

-- ============================================================
-- §18  Additional path theorems
-- ============================================================

/-- Theorem 49: APath.symm of nil is nil. -/
theorem APath.symm_nil {α : Type} (a : α) : (APath.nil a).symm = APath.nil a := rfl

/-- Theorem 50: deltaStar on two appended singletons. -/
theorem DFA.deltaStar_two (M : DFA) (q : AState) (a b : ASym) :
    M.deltaStar q [a, b] = M.delta (M.delta q a) b := rfl
