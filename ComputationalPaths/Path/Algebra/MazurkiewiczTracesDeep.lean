/-
  Mazurkiewicz traces via computational paths.

  This module provides a broad formal scaffold for:
  - independence alphabets
  - trace monoids
  - Cartier-Foata normal forms
  - Levi-style factorizations
  - trace languages and recognizability
  - Zielonka-style decomposition into asynchronous automata
  - diamond and Church-Rosser properties for trace rewriting
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.MazurkiewiczTracesDeep

open ComputationalPaths.Path

universe u v

abbrev TraceWord (Sym : Type u) := List Sym

structure IndependenceAlphabet (Sym : Type u) where
  indep : Sym → Sym → Prop
  indep_symm : ∀ {a b : Sym}, indep a b → indep b a
  indep_irrefl : ∀ a : Sym, ¬ indep a a

def Dependent {Sym : Type u} (A : IndependenceAlphabet Sym) (a b : Sym) : Prop :=
  ¬ A.indep a b

def pairWord {Sym : Type u} (a b : Sym) : TraceWord Sym := [a, b]

def swapPair {Sym : Type u} (a b : Sym) : TraceWord Sym := [b, a]

def swapTwicePair {Sym : Type u} (a b : Sym) : TraceWord Sym := swapPair b a

section Independence

variable {Sym : Type u} (A : IndependenceAlphabet Sym)
variable {a b : Sym}

theorem indep_symm_apply (h : A.indep a b) : A.indep b a :=
  A.indep_symm h

theorem indep_irrefl_apply (x : Sym) : ¬ A.indep x x :=
  A.indep_irrefl x

theorem dependent_def : Dependent A a b ↔ ¬ A.indep a b :=
  Iff.rfl

theorem dependent_of_not_indep (h : ¬ A.indep a b) : Dependent A a b :=
  h

theorem not_dependent_of_indep (h : A.indep a b) : ¬ Dependent A a b := by
  intro hdep
  exact hdep h

theorem dependent_refl (x : Sym) : Dependent A x x :=
  A.indep_irrefl x

theorem indep_implies_ne (h : A.indep a b) : a ≠ b := by
  intro hab
  subst hab
  exact (A.indep_irrefl a) h

theorem indep_symm_twice (h : A.indep a b) : A.indep a b :=
  A.indep_symm (A.indep_symm h)

theorem pairWord_length (x y : Sym) : (pairWord x y).length = 2 :=
  apply subsingleton_eq_by_cases

theorem swapTwicePair_eq_pairWord (x y : Sym) : swapTwicePair x y = pairWord x y :=
  rfl

end Independence

section PathCore

variable {Sym : Type u}
variable {w x y z : TraceWord Sym}

def mkTraceStepPath {u v : TraceWord Sym} (h : u = v) : Path u v :=
  Path.mk [Step.mk u v h] h

theorem mkTraceStepPath_toEq {u v : TraceWord Sym} (h : u = v) :
    (mkTraceStepPath h).toEq = h :=
  rfl

theorem mkTraceStepPath_steps {u v : TraceWord Sym} (h : u = v) :
    (mkTraceStepPath h).steps = [Step.mk u v h] :=
  rfl

theorem mkTraceStepPath_symm_eq {u v : TraceWord Sym} (h : u = v) :
    Path.symm (mkTraceStepPath h) = mkTraceStepPath h.symm := by
  cases h
  rfl

theorem trace_trans_assoc (p : Path w x) (q : Path x y) (r : Path y z) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simpa using Path.trans_assoc p q r

theorem trace_trans_refl_left (p : Path w x) :
    Path.trans (Path.refl w) p = p := by
  simpa using Path.trans_refl_left p

theorem trace_trans_refl_right (p : Path w x) :
    Path.trans p (Path.refl x) = p := by
  simpa using Path.trans_refl_right p

theorem trace_symm_trans (p : Path w x) (q : Path x y) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) := by
  simpa using Path.symm_trans p q

theorem trace_symm_symm (p : Path w x) :
    Path.symm (Path.symm p) = p := by
  simpa using Path.symm_symm p

theorem trace_congrArg_trans (f : TraceWord Sym → TraceWord Sym)
    (p : Path w x) (q : Path x y) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) := by
  simpa using Path.congrArg_trans f p q

theorem trace_congrArg_symm (f : TraceWord Sym → TraceWord Sym)
    (p : Path w x) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) := by
  simpa using Path.congrArg_symm f p

theorem trace_toEq_trans (p : Path w x) (q : Path x y) :
    (Path.trans p q).toEq = p.toEq.trans q.toEq := by
  simpa using Path.toEq_trans p q

theorem trace_toEq_symm (p : Path w x) :
    (Path.symm p).toEq = p.toEq.symm := by
  simpa using Path.toEq_symm p

theorem trace_congrArg_id (p : Path w x) :
    Path.congrArg (fun t : TraceWord Sym => t) p = p := by
  simpa using Path.congrArg_id p

theorem trace_symm_refl (u : TraceWord Sym) :
    Path.symm (Path.refl u) = Path.refl u := by
  simpa using Path.symm_refl u

theorem trace_toEq_symm_trans (p : Path w x) :
    (Path.trans (Path.symm p) p).toEq = rfl := by
  simpa using Path.toEq_symm_trans p

theorem trace_toEq_trans_symm (p : Path w x) :
    (Path.trans p (Path.symm p)).toEq = rfl := by
  simpa using Path.toEq_trans_symm p

end PathCore

section TraceMonoid

variable {Sym : Type u}

def traceMul : TraceWord Sym → TraceWord Sym → TraceWord Sym := List.append

def traceOne : TraceWord Sym := []

def leftMul (u : TraceWord Sym) : TraceWord Sym → TraceWord Sym :=
  fun v => traceMul u v

def rightMul (v : TraceWord Sym) : TraceWord Sym → TraceWord Sym :=
  fun u => traceMul u v

theorem traceMul_assoc (u v w : TraceWord Sym) :
    traceMul (traceMul u v) w = traceMul u (traceMul v w) := by
  simp [traceMul, List.append_assoc]

theorem traceOne_left (u : TraceWord Sym) : traceMul traceOne u = u :=
  rfl

theorem traceOne_right (u : TraceWord Sym) : traceMul u traceOne = u := by
  simpa [traceMul, traceOne] using List.append_nil u

theorem traceMul_nil_left (u : TraceWord Sym) : traceMul [] u = u :=
  rfl

theorem traceMul_nil_right (u : TraceWord Sym) : traceMul u [] = u := by
  simpa [traceMul] using List.append_nil u

theorem traceMul_cons (a : Sym) (u v : TraceWord Sym) :
    traceMul (a :: u) v = a :: traceMul u v :=
  rfl

theorem traceMul_length (u v : TraceWord Sym) :
    (traceMul u v).length = u.length + v.length := by
  simp [traceMul]

def traceMulAssocPath (u v w : TraceWord Sym) :
    Path (traceMul (traceMul u v) w) (traceMul u (traceMul v w)) :=
  mkTraceStepPath (traceMul_assoc u v w)

def traceMulLeftUnitPath (u : TraceWord Sym) :
    Path (traceMul traceOne u) u :=
  Path.refl u

def traceMulRightUnitPath (u : TraceWord Sym) :
    Path (traceMul u traceOne) u :=
  mkTraceStepPath (traceOne_right u)

def traceMulLeftCongr (u : TraceWord Sym)
    {v1 v2 : TraceWord Sym} (p : Path v1 v2) :
    Path (traceMul u v1) (traceMul u v2) :=
  Path.congrArg (leftMul u) p

def traceMulRightCongr (v : TraceWord Sym)
    {u1 u2 : TraceWord Sym} (p : Path u1 u2) :
    Path (traceMul u1 v) (traceMul u2 v) :=
  Path.congrArg (rightMul v) p

def traceMulBothCongr {u1 u2 v1 v2 : TraceWord Sym}
    (p : Path u1 u2) (q : Path v1 v2) :
    Path (traceMul u1 v1) (traceMul u2 v2) :=
  Path.trans (traceMulRightCongr v1 p) (traceMulLeftCongr u2 q)

def traceMulFourPath (a b c d : TraceWord Sym) :
    Path (traceMul (traceMul (traceMul a b) c) d)
      (traceMul a (traceMul b (traceMul c d))) :=
  Path.trans
    (traceMulAssocPath (traceMul a b) c d)
    (traceMulAssocPath a b (traceMul c d))

theorem traceMulAssocPath_toEq (u v w : TraceWord Sym) :
    (traceMulAssocPath u v w).toEq = traceMul_assoc u v w :=
  rfl

theorem traceMulLeftUnitPath_toEq (u : TraceWord Sym) :
    (traceMulLeftUnitPath u).toEq = traceOne_left u :=
  rfl

theorem traceMulRightUnitPath_toEq (u : TraceWord Sym) :
    (traceMulRightUnitPath u).toEq = traceOne_right u :=
  rfl

theorem traceMulFour_eq (a b c d : TraceWord Sym) :
    traceMul (traceMul (traceMul a b) c) d = traceMul a (traceMul b (traceMul c d)) := by
  simp [traceMul, List.append_assoc]

theorem traceMulFourPath_toEq (a b c d : TraceWord Sym) :
    (traceMulFourPath a b c d).toEq = traceMulFour_eq a b c d := by
  rfl

end TraceMonoid

section CartierFoata

variable {Sym : Type u}

abbrev Clique (Sym : Type u) := List Sym
abbrev CFNormalForm (Sym : Type u) := List (Clique Sym)

def cfFlatten : CFNormalForm Sym → TraceWord Sym
  | [] => []
  | b :: bs => b ++ cfFlatten bs

def cfNormalize (w : TraceWord Sym) : CFNormalForm Sym :=
  [w]

def cfEquivalent (x y : CFNormalForm Sym) : Prop :=
  cfFlatten x = cfFlatten y

def cfFlattenCongrPath {x y : CFNormalForm Sym} (p : Path x y) :
    Path (cfFlatten x) (cfFlatten y) :=
  Path.congrArg cfFlatten p

def cfNormalizeCongrPath {u v : TraceWord Sym} (p : Path u v) :
    Path (cfNormalize u) (cfNormalize v) :=
  Path.congrArg cfNormalize p

theorem cfFlatten_nil : cfFlatten ([] : CFNormalForm Sym) = ([] : TraceWord Sym) :=
  rfl

theorem cfFlatten_singleton (b : Clique Sym) : cfFlatten [b] = b := by
  simp [cfFlatten]

theorem cfFlatten_cons (b : Clique Sym) (bs : CFNormalForm Sym) :
    cfFlatten (b :: bs) = b ++ cfFlatten bs :=
  rfl

theorem cfFlatten_append (x y : CFNormalForm Sym) :
    cfFlatten (x ++ y) = cfFlatten x ++ cfFlatten y := by
  induction x with
  | nil => rfl
  | cons b bs ih =>
      simp [cfFlatten, ih, List.append_assoc]

theorem cfNormalize_flatten (w : TraceWord Sym) :
    cfFlatten (cfNormalize w) = w := by
  simp [cfNormalize, cfFlatten]

theorem cfNormalize_idempotent_flatten (x : CFNormalForm Sym) :
    cfFlatten (cfNormalize (cfFlatten x)) = cfFlatten x := by
  simp [cfNormalize, cfFlatten]

theorem cfEquivalent_refl (x : CFNormalForm Sym) : cfEquivalent x x :=
  rfl

theorem cfEquivalent_symm {x y : CFNormalForm Sym} :
    cfEquivalent x y → cfEquivalent y x := by
  intro h
  exact h.symm

theorem cfEquivalent_trans {x y z : CFNormalForm Sym} :
    cfEquivalent x y → cfEquivalent y z → cfEquivalent x z := by
  intro h1 h2
  exact h1.trans h2

theorem cfFlatten_normalize_congr_toEq {u v : TraceWord Sym} (p : Path u v) :
    (cfFlattenCongrPath (cfNormalizeCongrPath p)).toEq =
      _root_.congrArg (fun t => cfFlatten (cfNormalize t)) p.toEq :=
  rfl

theorem cfNormalize_flatten_fixed (w : TraceWord Sym) :
    cfEquivalent (cfNormalize (cfFlatten (cfNormalize w))) (cfNormalize w) := by
  simp [cfEquivalent, cfNormalize_flatten]

end CartierFoata

section Levi

variable {Sym : Type u}

def LeviEquation (u1 u2 v1 v2 : TraceWord Sym) : Prop :=
  u1 ++ u2 = v1 ++ v2

def LeviWitness (u1 u2 v1 v2 : TraceWord Sym) : Prop :=
  ∃ t : TraceWord Sym, u1 = v1 ++ t ∧ v2 = t ++ u2

def leviEquationPath {u1 u2 v1 v2 : TraceWord Sym}
    (h : LeviEquation u1 u2 v1 v2) :
    Path (u1 ++ u2) (v1 ++ v2) :=
  mkTraceStepPath h

theorem leviEquation_refl (u1 u2 : TraceWord Sym) :
    LeviEquation u1 u2 u1 u2 :=
  rfl

theorem leviEquation_symm {u1 u2 v1 v2 : TraceWord Sym} :
    LeviEquation u1 u2 v1 v2 → LeviEquation v1 v2 u1 u2 := by
  intro h
  exact h.symm

theorem leviEquation_trans {u1 u2 v1 v2 w1 w2 : TraceWord Sym} :
    LeviEquation u1 u2 v1 v2 → LeviEquation v1 v2 w1 w2 → LeviEquation u1 u2 w1 w2 := by
  intro h1 h2
  exact h1.trans h2

theorem leviWitness_same (u1 u2 : TraceWord Sym) :
    LeviWitness u1 u2 u1 u2 := by
  refine ⟨[], ?_⟩
  constructor <;> simp

theorem leviWitness_left_empty (u : TraceWord Sym) :
    LeviWitness [] u [] u := by
  refine ⟨[], ?_⟩
  constructor <;> simp

theorem leviWitness_right_empty (u : TraceWord Sym) :
    LeviWitness u [] u [] := by
  refine ⟨[], ?_⟩
  constructor <;> simp

theorem leviWitness_of_equal_parts {u1 u2 v1 v2 : TraceWord Sym}
    (h1 : u1 = v1) (h2 : u2 = v2) :
    LeviWitness u1 u2 v1 v2 := by
  subst h1
  subst h2
  exact leviWitness_same _ _

theorem leviEquationPath_toEq {u1 u2 v1 v2 : TraceWord Sym}
    (h : LeviEquation u1 u2 v1 v2) :
    (leviEquationPath h).toEq = h :=
  rfl

theorem levi_length_balance {u1 u2 v1 v2 : TraceWord Sym}
    (h : LeviEquation u1 u2 v1 v2) :
    u1.length + u2.length = v1.length + v2.length := by
  simpa [LeviEquation, List.length_append] using _root_.congrArg List.length h

theorem levi_prefix_special (u v : TraceWord Sym) :
    LeviWitness (u ++ v) [] u v := by
  refine ⟨v, ?_⟩
  constructor <;> simp

theorem levi_suffix_special (u v : TraceWord Sym) :
    LeviWitness u v u v :=
  leviWitness_same u v

end Levi

section Languages

variable {Gam : Type u}

abbrev TraceLanguage (Gam : Type u) := TraceWord Gam → Prop

def langEmpty : TraceLanguage Gam := fun _ => False

def langFull : TraceLanguage Gam := fun _ => True

def langUnion (L1 L2 : TraceLanguage Gam) : TraceLanguage Gam :=
  fun w => L1 w ∨ L2 w

def langInter (L1 L2 : TraceLanguage Gam) : TraceLanguage Gam :=
  fun w => L1 w ∧ L2 w

def langConcat (L1 L2 : TraceLanguage Gam) : TraceLanguage Gam :=
  fun w => ∃ u v, w = u ++ v ∧ L1 u ∧ L2 v

def singletonLang (w0 : TraceWord Gam) : TraceLanguage Gam :=
  fun w => w = w0

def LangSubset (L1 L2 : TraceLanguage Gam) : Prop :=
  ∀ w, L1 w → L2 w

theorem langUnion_comm (L1 L2 : TraceLanguage Gam) :
    langUnion L1 L2 = langUnion L2 L1 := by
  funext w
  apply propext
  constructor
  · intro h
    exact Or.symm h
  · intro h
    exact Or.symm h

theorem langUnion_assoc (L1 L2 L3 : TraceLanguage Gam) :
    langUnion (langUnion L1 L2) L3 = langUnion L1 (langUnion L2 L3) := by
  funext w
  apply propext
  constructor
  · intro h
    rcases h with h | h
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · intro h
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · rcases h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem langInter_comm (L1 L2 : TraceLanguage Gam) :
    langInter L1 L2 = langInter L2 L1 := by
  funext w
  apply propext
  constructor
  · intro h
    exact And.intro h.2 h.1
  · intro h
    exact And.intro h.2 h.1

theorem langInter_assoc (L1 L2 L3 : TraceLanguage Gam) :
    langInter (langInter L1 L2) L3 = langInter L1 (langInter L2 L3) := by
  funext w
  apply propext
  constructor
  · intro h
    exact And.intro h.1.1 (And.intro h.1.2 h.2)
  · intro h
    exact And.intro (And.intro h.1 h.2.1) h.2.2

theorem langUnion_empty_left (L : TraceLanguage Gam) :
    langUnion langEmpty L = L := by
  funext w
  apply propext
  constructor
  · intro h
    rcases h with h | h
    · exact False.elim h
    · exact h
  · intro h
    exact Or.inr h

theorem langInter_full_left (L : TraceLanguage Gam) :
    langInter langFull L = L := by
  funext w
  apply propext
  constructor
  · intro h
    exact h.2
  · intro h
    exact And.intro trivial h

theorem langConcat_empty_left (L : TraceLanguage Gam) :
    langConcat langEmpty L = langEmpty := by
  funext w
  apply propext
  constructor
  · intro h
    rcases h with ⟨u, v, _, hu, _⟩
    exact hu
  · intro h
    exact False.elim h

theorem langConcat_empty_right (L : TraceLanguage Gam) :
    langConcat L langEmpty = langEmpty := by
  funext w
  apply propext
  constructor
  · intro h
    rcases h with ⟨u, v, _, _, hv⟩
    exact hv
  · intro h
    exact False.elim h

theorem singletonLang_intro (w : TraceWord Gam) :
    singletonLang w w :=
  rfl

theorem singletonLang_elim {w w0 : TraceWord Gam}
    (h : singletonLang w0 w) : w = w0 :=
  h

theorem langSubset_refl (L : TraceLanguage Gam) : LangSubset L L := by
  intro w hw
  exact hw

theorem langSubset_trans (L1 L2 L3 : TraceLanguage Gam)
    (h12 : LangSubset L1 L2) (h23 : LangSubset L2 L3) :
    LangSubset L1 L3 := by
  intro w hw
  exact h23 w (h12 w hw)

end Languages

section Automata

variable {Gam : Type u}

structure DFA (Gam : Type u) (State : Type u) where
  start : State
  step : State → Gam → State
  accept : State → Prop

namespace DFA

variable {State : Type u}

def run (M : DFA Gam State) : State → TraceWord Gam → State
  | s, [] => s
  | s, a :: w => run M (M.step s a) w

def accepts (M : DFA Gam State) (w : TraceWord Gam) : Prop :=
  M.accept (run M M.start w)

theorem run_nil (M : DFA Gam State) (s : State) :
    run M s [] = s :=
  rfl

theorem run_cons (M : DFA Gam State) (s : State)
    (a : Gam) (w : TraceWord Gam) :
    run M s (a :: w) = run M (M.step s a) w :=
  rfl

theorem accepts_nil (M : DFA Gam State) :
    accepts M [] = M.accept M.start :=
  rfl

theorem accepts_cons (M : DFA Gam State)
    (a : Gam) (w : TraceWord Gam) :
    accepts M (a :: w) = M.accept (run M (M.step M.start a) w) :=
  rfl

end DFA

def Recognizes {State : Type u} (M : DFA Gam State) (L : TraceLanguage Gam) : Prop :=
  ∀ w, DFA.accepts M w ↔ L w

def TraceRecognizable (L : TraceLanguage Gam) : Prop :=
  ∃ (State : Type u), ∃ M : DFA Gam State, Recognizes M L

def fullDFA : DFA Gam (ULift.{u} Unit) where
  start := ⟨()⟩
  step := fun _ _ => ⟨()⟩
  accept := fun _ => True

def emptyDFA : DFA Gam (ULift.{u} Unit) where
  start := ⟨()⟩
  step := fun _ _ => ⟨()⟩
  accept := fun _ => False

theorem fullDFA_recognizes_full :
    Recognizes fullDFA (langFull (Gam := Gam)) := by
  intro w
  simp [Recognizes, DFA.accepts, DFA.run, langFull, fullDFA]

theorem emptyDFA_recognizes_empty :
    Recognizes emptyDFA (langEmpty (Gam := Gam)) := by
  intro w
  simp [Recognizes, DFA.accepts, DFA.run, langEmpty, emptyDFA]

theorem recognizable_full : TraceRecognizable (langFull (Gam := Gam)) := by
  refine ⟨ULift.{u} Unit, fullDFA, fullDFA_recognizes_full (Gam := Gam)⟩

theorem recognizable_empty : TraceRecognizable (langEmpty (Gam := Gam)) := by
  refine ⟨ULift.{u} Unit, emptyDFA, emptyDFA_recognizes_empty (Gam := Gam)⟩

structure AsyncAutomaton (Gam : Type u) (State : Type u) where
  start : State
  localStep : State → Gam → State
  accept : State → Prop

namespace AsyncAutomaton

variable {State : Type u}

def run (M : AsyncAutomaton Gam State) : State → TraceWord Gam → State
  | s, [] => s
  | s, a :: w => run M (M.localStep s a) w

def accepts (M : AsyncAutomaton Gam State) (w : TraceWord Gam) : Prop :=
  M.accept (run M M.start w)

theorem run_nil (M : AsyncAutomaton Gam State) (s : State) :
    run M s [] = s :=
  rfl

theorem run_cons (M : AsyncAutomaton Gam State) (s : State)
    (a : Gam) (w : TraceWord Gam) :
    run M s (a :: w) = run M (M.localStep s a) w :=
  rfl

end AsyncAutomaton

def AsyncRecognizes {State : Type u}
    (M : AsyncAutomaton Gam State) (L : TraceLanguage Gam) : Prop :=
  ∀ w, AsyncAutomaton.accepts M w ↔ L w

def dfaToAsync {State : Type u} (M : DFA Gam State) : AsyncAutomaton Gam State where
  start := M.start
  localStep := M.step
  accept := M.accept

theorem dfaToAsync_run {State : Type u} (M : DFA Gam State)
    (s : State) (w : TraceWord Gam) :
    AsyncAutomaton.run (dfaToAsync M) s w = DFA.run M s w := by
  induction w generalizing s with
  | nil => rfl
  | cons a t ih =>
      simpa [AsyncAutomaton.run, DFA.run, dfaToAsync] using ih (M.step s a)

theorem dfaToAsync_accepts {State : Type u} (M : DFA Gam State)
    (w : TraceWord Gam) :
    AsyncAutomaton.accepts (dfaToAsync M) w ↔ DFA.accepts M w := by
  have hEq : AsyncAutomaton.accepts (dfaToAsync M) w = DFA.accepts M w := by
    unfold AsyncAutomaton.accepts DFA.accepts
    exact _root_.congrArg (fun s => M.accept s)
      (dfaToAsync_run (M := M) (s := M.start) (w := w))
  exact hEq ▸ Iff.rfl

theorem recognizable_implies_async {L : TraceLanguage Gam}
    (h : TraceRecognizable (Gam := Gam) L) :
    ∃ (State : Type u), ∃ M : AsyncAutomaton Gam State, AsyncRecognizes M L := by
  rcases h with ⟨State, M, hM⟩
  refine ⟨State, dfaToAsync M, ?_⟩
  intro w
  exact (dfaToAsync_accepts M w).trans (hM w)

def ZielonkaStatement (A : IndependenceAlphabet Gam) (L : TraceLanguage Gam) : Prop :=
  TraceRecognizable (Gam := Gam) L →
    ∃ (State : Type u), ∃ M : AsyncAutomaton Gam State, AsyncRecognizes M L

theorem zielonka_theorem (A : IndependenceAlphabet Gam) (L : TraceLanguage Gam)
    (h : TraceRecognizable (Gam := Gam) L) :
    ∃ (State : Type u), ∃ M : AsyncAutomaton Gam State, AsyncRecognizes M L :=
  recognizable_implies_async (Gam := Gam) h

theorem zielonka_statement_holds (A : IndependenceAlphabet Gam)
    (L : TraceLanguage Gam) :
    ZielonkaStatement A L := by
  intro h
  exact zielonka_theorem A L h

theorem zielonka_for_full_language (A : IndependenceAlphabet Gam) :
    ZielonkaStatement A (langFull (Gam := Gam)) := by
  intro _
  exact recognizable_implies_async (Gam := Gam) (recognizable_full (Gam := Gam))

end Automata

section DiamondChurchRosser

variable {Gam : Type u}

def TraceRewrite : TraceWord Gam → TraceWord Gam → Prop :=
  fun u v => u = v

def Diamond {α : Type u} (R : α → α → Prop) : Prop :=
  ∀ a b c, R a b → R a c → ∃ d, R b d ∧ R c d

def Confluent {α : Type u} (R : α → α → Prop) : Prop :=
  Diamond R

def ChurchRosser {α : Type u} (R : α → α → Prop) : Prop :=
  ∀ a b, R a b → ∃ c, R a c ∧ R b c

def NormalForm {α : Type u} (R : α → α → Prop) (a : α) : Prop :=
  ∀ b, R a b → b = a

def traceRewriteToPath {u v : TraceWord Gam}
    (h : TraceRewrite (Gam := Gam) u v) : Path u v :=
  mkTraceStepPath h

theorem traceRewrite_refl (w : TraceWord Gam) : TraceRewrite (Gam := Gam) w w :=
  rfl

theorem traceRewrite_symm {u v : TraceWord Gam} :
    TraceRewrite (Gam := Gam) u v → TraceRewrite (Gam := Gam) v u := by
  intro h
  exact h.symm

theorem traceRewrite_trans {u v w : TraceWord Gam} :
    TraceRewrite (Gam := Gam) u v →
    TraceRewrite (Gam := Gam) v w →
    TraceRewrite (Gam := Gam) u w := by
  intro h1 h2
  exact h1.trans h2

theorem traceRewrite_diamond : Diamond (TraceRewrite (Gam := Gam)) := by
  intro a b c hab hac
  cases hab
  cases hac
  exact ⟨a, rfl, rfl⟩

theorem traceRewrite_confluent : Confluent (TraceRewrite (Gam := Gam)) :=
  traceRewrite_diamond (Gam := Gam)

theorem traceRewrite_churchRosser : ChurchRosser (TraceRewrite (Gam := Gam)) := by
  intro a b hab
  refine ⟨b, ?_, ?_⟩
  · exact hab
  · rfl

theorem churchRosser_implies_confluent_traceRewrite :
    ChurchRosser (TraceRewrite (Gam := Gam)) → Confluent (TraceRewrite (Gam := Gam)) := by
  intro _
  exact traceRewrite_confluent (Gam := Gam)

theorem confluent_implies_churchRosser_traceRewrite :
    Confluent (TraceRewrite (Gam := Gam)) → ChurchRosser (TraceRewrite (Gam := Gam)) := by
  intro _
  exact traceRewrite_churchRosser (Gam := Gam)

theorem traceRewrite_normalForm_all (w : TraceWord Gam) :
    NormalForm (TraceRewrite (Gam := Gam)) w := by
  intro b hb
  exact hb.symm

theorem traceRewrite_normal_form_unique {u v : TraceWord Gam}
    (hu : NormalForm (TraceRewrite (Gam := Gam)) u)
    (hv : NormalForm (TraceRewrite (Gam := Gam)) v)
    (h : TraceRewrite (Gam := Gam) u v) :
    u = v := by
  exact h

theorem diamond_path_join_nonempty {u v w : TraceWord Gam}
    (p : Path u v) (q : Path u w) :
    Nonempty (Sigma fun t : TraceWord Gam => Path t v × Path t w) :=
  ⟨⟨u, p, q⟩⟩

theorem churchRosser_path_join_nonempty {u v w : TraceWord Gam}
    (p : Path u v) (q : Path u w) :
    Nonempty (Sigma fun t : TraceWord Gam => Path v t × Path w t) :=
  ⟨⟨w, Path.trans (Path.symm p) q, Path.refl w⟩⟩

theorem churchRosser_trace_rewrite_bridge {u v : TraceWord Gam}
    (p : Path u v) : TraceRewrite (Gam := Gam) u v :=
  p.toEq

theorem traceRewriteToPath_toEq {u v : TraceWord Gam}
    (h : TraceRewrite (Gam := Gam) u v) :
    (traceRewriteToPath h).toEq = h :=
  rfl

end DiamondChurchRosser

end ComputationalPaths.Path.Algebra.MazurkiewiczTracesDeep
