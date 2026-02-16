/-
  ComputationalPaths/Path/Rewriting/AutomataPathDeep.lean

  Automata Theory and Language Recognition via Computational Paths

  We model DFA/NFA structures where computation runs are Paths,
  each transition step corresponds to a Step, acceptance is existence
  of a Path from initial to final state, and language operations
  (union, intersection, complement, concatenation) are reflected
  through Path combinators like congrArg, trans, symm.

  Since Path is a Type (structure with steps + proof), we use `def` for
  Path-producing declarations and `theorem` for propositional equalities
  between Paths.

  Author: armada-334 (AutomataPathDeep)
-/

import ComputationalPaths.Path.Basic

namespace AutomataPathDeep

open ComputationalPaths
open ComputationalPaths.Path

universe u v w

-- ============================================================================
-- SECTION 1: Core Automata Structures
-- ============================================================================

/-- A Deterministic Finite Automaton parameterized by state and alphabet types -/
structure DFA (Q : Type u) (Sym : Type v) where
  start : Q
  delta : Q → Sym → Q
  accept : Q → Bool

/-- A Nondeterministic Finite Automaton -/
structure NFA (Q : Type u) (Sym : Type v) where
  start : Q
  delta : Q → Sym → Q → Prop
  accept : Q → Bool

/-- Extended transition function: run a DFA on a list of symbols -/
def DFA.run {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q : Q) : List Sym → Q
  | [] => q
  | a :: ws => m.run (m.delta q a) ws

/-- A word is accepted by a DFA if running from start reaches an accepting state -/
def DFA.accepts {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (w : List Sym) : Bool :=
  m.accept (m.run m.start w)

/-- The language of a DFA -/
def DFA.language {Q : Type u} {Sym : Type v} (m : DFA Q Sym) : List Sym → Prop :=
  fun w => m.accepts w = true

-- ============================================================================
-- SECTION 2: Path-Based Computation Runs
-- ============================================================================

/-- Def 1: Running on empty word returns start state -/
def run_nil {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q : Q) :
    Path (m.run q []) q :=
  Path.refl q

/-- Def 2: Running on singleton is one delta step -/
def run_singleton {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q : Q) (a : Sym) :
    Path (m.run q [a]) (m.delta q a) :=
  Path.refl (m.delta q a)

/-- Def 3: Run decomposes into head step + tail run -/
def run_cons {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q : Q) (a : Sym) (w : List Sym) :
    Path (m.run q (a :: w)) (m.run (m.delta q a) w) :=
  Path.refl _

/-- Def 4: Run on append decomposes into two sequential runs -/
def run_append {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q : Q) :
    ∀ (w1 w2 : List Sym), Path (m.run q (w1 ++ w2)) (m.run (m.run q w1) w2)
  | [], _ => Path.refl _
  | _ :: w1, w2 => run_append m _ w1 w2

/-- Def 5: Reflexivity of run path -/
def run_path_refl {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q : Q) (w : List Sym) :
    Path (m.run q w) (m.run q w) :=
  Path.refl _

-- ============================================================================
-- SECTION 3: Congruence Paths for Automata
-- ============================================================================

/-- Def 6: Path between states induces path between acceptance values -/
def accept_path {Q : Type u} {Sym : Type v} (m : DFA Q Sym) {q1 q2 : Q}
    (p : Path q1 q2) : Path (m.accept q1) (m.accept q2) :=
  Path.congrArg m.accept p

/-- Def 7: Path between states induces path between run results -/
def run_congruence {Q : Type u} {Sym : Type v} (m : DFA Q Sym) {q1 q2 : Q}
    (p : Path q1 q2) (w : List Sym) : Path (m.run q1 w) (m.run q2 w) :=
  Path.congrArg (fun q => m.run q w) p

/-- Def 8: Acceptance is preserved along state paths and words -/
def accepts_congruence {Q : Type u} {Sym : Type v} (m : DFA Q Sym) {q1 q2 : Q}
    (p : Path q1 q2) (w : List Sym) :
    Path (m.accept (m.run q1 w)) (m.accept (m.run q2 w)) :=
  Path.congrArg m.accept (run_congruence m p w)

/-- Def 9: Language membership is path-invariant for start state -/
def language_path_invariant {Q : Type u} {Sym : Type v} (m : DFA Q Sym)
    {s1 s2 : Q} (hs : Path s1 s2) (w : List Sym) :
    Path (m.accept (m.run s1 w)) (m.accept (m.run s2 w)) :=
  accepts_congruence m hs w

/-- Def 10: Delta is congruent in the state argument -/
def delta_congruence {Q : Type u} {Sym : Type v} (m : DFA Q Sym)
    {q1 q2 : Q} (a : Sym) (p : Path q1 q2) :
    Path (m.delta q1 a) (m.delta q2 a) :=
  Path.congrArg (fun q => m.delta q a) p

-- ============================================================================
-- SECTION 4: DFA Minimization via Myhill-Nerode Equivalence
-- ============================================================================

/-- Two states are Myhill-Nerode equivalent if they yield same acceptance on all futures -/
def mnEquiv {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q1 q2 : Q) : Prop :=
  ∀ w : List Sym, m.accept (m.run q1 w) = m.accept (m.run q2 w)

/-- Theorem 11: MN equivalence is reflexive -/
theorem mnEquiv_refl {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q : Q) :
    mnEquiv m q q :=
  fun _ => rfl

/-- Theorem 12: MN equivalence is symmetric -/
theorem mnEquiv_symm {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q1 q2 : Q)
    (h : mnEquiv m q1 q2) : mnEquiv m q2 q1 :=
  fun w => (h w).symm

/-- Theorem 13: MN equivalence is transitive -/
theorem mnEquiv_trans {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q1 q2 q3 : Q)
    (h12 : mnEquiv m q1 q2) (h23 : mnEquiv m q2 q3) : mnEquiv m q1 q3 :=
  fun w => (h12 w).trans (h23 w)

/-- Theorem 14: MN equivalence is preserved by transitions -/
theorem mnEquiv_delta {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q1 q2 : Q)
    (a : Sym) (h : mnEquiv m q1 q2) : mnEquiv m (m.delta q1 a) (m.delta q2 a) :=
  fun w => h (a :: w)

/-- Theorem 15: MN equivalence preserved by full word run -/
theorem mnEquiv_run {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q1 q2 : Q)
    (h : mnEquiv m q1 q2) : ∀ w : List Sym, mnEquiv m (m.run q1 w) (m.run q2 w)
  | [] => h
  | a :: w => mnEquiv_run m _ _ (mnEquiv_delta m q1 q2 a h) w

/-- Def 16: MN equivalence lifts to Path on acceptance -/
def mnEquiv_to_path {Q : Type u} {Sym : Type v} (m : DFA Q Sym) {q1 q2 : Q}
    (h : mnEquiv m q1 q2) (w : List Sym) :
    Path (m.accept (m.run q1 w)) (m.accept (m.run q2 w)) :=
  Path.stepChain (h w)

-- ============================================================================
-- SECTION 5: Product Automata and Path Projections
-- ============================================================================

/-- Product DFA for intersection -/
def DFA.product {Q1 Q2 : Type u} {Sym : Type v}
    (m1 : DFA Q1 Sym) (m2 : DFA Q2 Sym) : DFA (Q1 × Q2) Sym where
  start := (m1.start, m2.start)
  delta := fun (q1, q2) a => (m1.delta q1 a, m2.delta q2 a)
  accept := fun (q1, q2) => m1.accept q1 && m2.accept q2

/-- Def 17: Product run projects to first component -/
def product_run_fst {Q1 Q2 : Type u} {Sym : Type v}
    (m1 : DFA Q1 Sym) (m2 : DFA Q2 Sym) (q1 : Q1) (q2 : Q2) :
    ∀ (w : List Sym),
      Path ((m1.product m2).run (q1, q2) w).1 (m1.run q1 w)
  | [] => Path.refl _
  | _ :: w => product_run_fst m1 m2 _ _ w

/-- Def 18: Product run projects to second component -/
def product_run_snd {Q1 Q2 : Type u} {Sym : Type v}
    (m1 : DFA Q1 Sym) (m2 : DFA Q2 Sym) (q1 : Q1) (q2 : Q2) :
    ∀ (w : List Sym),
      Path ((m1.product m2).run (q1, q2) w).2 (m2.run q2 w)
  | [] => Path.refl _
  | _ :: w => product_run_snd m1 m2 _ _ w

/-- Def 19: Path in product projects to first component via congrArg -/
def product_path_fst {Q1 Q2 : Type u}
    {p1 p2 : Q1 × Q2} (h : Path p1 p2) : Path p1.1 p2.1 :=
  Path.congrArg Prod.fst h

/-- Def 20: Path in product projects to second component via congrArg -/
def product_path_snd {Q1 Q2 : Type u}
    {p1 p2 : Q1 × Q2} (h : Path p1 p2) : Path p1.2 p2.2 :=
  Path.congrArg Prod.snd h

-- ============================================================================
-- SECTION 6: Union Automata
-- ============================================================================

/-- Union DFA: accepts if either component accepts -/
def DFA.union {Q1 Q2 : Type u} {Sym : Type v}
    (m1 : DFA Q1 Sym) (m2 : DFA Q2 Sym) : DFA (Q1 × Q2) Sym where
  start := (m1.start, m2.start)
  delta := fun (q1, q2) a => (m1.delta q1 a, m2.delta q2 a)
  accept := fun (q1, q2) => m1.accept q1 || m2.accept q2

/-- Def 21: Union run projects to first component -/
def union_run_fst {Q1 Q2 : Type u} {Sym : Type v}
    (m1 : DFA Q1 Sym) (m2 : DFA Q2 Sym) (q1 : Q1) (q2 : Q2) :
    ∀ (w : List Sym),
      Path ((m1.union m2).run (q1, q2) w).1 (m1.run q1 w)
  | [] => Path.refl _
  | _ :: w => union_run_fst m1 m2 _ _ w

/-- Def 22: Union run projects to second component -/
def union_run_snd {Q1 Q2 : Type u} {Sym : Type v}
    (m1 : DFA Q1 Sym) (m2 : DFA Q2 Sym) (q1 : Q1) (q2 : Q2) :
    ∀ (w : List Sym),
      Path ((m1.union m2).run (q1, q2) w).2 (m2.run q2 w)
  | [] => Path.refl _
  | _ :: w => union_run_snd m1 m2 _ _ w

-- ============================================================================
-- SECTION 7: Complement Automata
-- ============================================================================

/-- Complement DFA: flip accept/reject -/
def DFA.complement {Q : Type u} {Sym : Type v} (m : DFA Q Sym) : DFA Q Sym where
  start := m.start
  delta := m.delta
  accept := fun q => !m.accept q

/-- Theorem 23: Complement run equals original run -/
theorem complement_run_eq {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q : Q) (w : List Sym) :
    m.complement.run q w = m.run q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a ws ih => exact ih _

/-- Def 24: Complement run path to original run -/
def complement_run {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q : Q) (w : List Sym) :
    Path (m.complement.run q w) (m.run q w) :=
  Path.stepChain (complement_run_eq m q w)

/-- Def 25: Double complement acceptance returns to original -/
def complement_complement_accept {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q : Q) :
    Path (m.complement.complement.accept q) (m.accept q) := by
  show Path (!!m.accept q) (m.accept q)
  cases m.accept q <;> exact Path.refl _

/-- Def 26: Complement preserves transition structure -/
def complement_delta {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q : Q) (a : Sym) :
    Path (m.complement.delta q a) (m.delta q a) :=
  Path.refl _

-- ============================================================================
-- SECTION 8: Automata Homomorphisms and Functoriality
-- ============================================================================

/-- A homomorphism between DFAs -/
structure DFAHom {Q1 : Type u} {Q2 : Type v} {Sym : Type w}
    (m1 : DFA Q1 Sym) (m2 : DFA Q2 Sym) where
  mapState : Q1 → Q2
  map_start : Path (mapState m1.start) m2.start
  map_delta : ∀ q a, Path (mapState (m1.delta q a)) (m2.delta (mapState q) a)
  map_accept : ∀ q, m1.accept q = m2.accept (mapState q)

/-- Def 27: Homomorphism preserves run -/
def DFAHom.map_run {Q1 : Type u} {Q2 : Type v} {Sym : Type w}
    {m1 : DFA Q1 Sym} {m2 : DFA Q2 Sym} (f : DFAHom m1 m2) (q : Q1) :
    ∀ (ws : List Sym), Path (f.mapState (m1.run q ws)) (m2.run (f.mapState q) ws)
  | [] => Path.refl _
  | a :: ws =>
    Path.trans (f.map_run (m1.delta q a) ws)
      (run_congruence m2 (f.map_delta q a) ws)

/-- Def 28: Homomorphism preserves acceptance via Path -/
def DFAHom.preserves_accept_path {Q1 : Type u} {Q2 : Type v} {Sym : Type w}
    {m1 : DFA Q1 Sym} {m2 : DFA Q2 Sym} (f : DFAHom m1 m2) (q : Q1) :
    Path (m1.accept q) (m2.accept (f.mapState q)) :=
  Path.stepChain (f.map_accept q)

/-- Theorem 29: Homomorphism preserves acceptance propositionally -/
theorem DFAHom.preserves_language {Q1 : Type u} {Q2 : Type v} {Sym : Type w}
    {m1 : DFA Q1 Sym} {m2 : DFA Q2 Sym} (f : DFAHom m1 m2) (ws : List Sym) :
    m1.accept (m1.run m1.start ws) = m2.accept (m2.run (f.mapState m1.start) ws) :=
  (f.map_accept (m1.run m1.start ws)).trans
    (congrArg m2.accept (f.map_run m1.start ws).toEq)

/-- Identity homomorphism -/
def DFAHom.ident {Q : Type u} {Sym : Type v} (m : DFA Q Sym) : DFAHom m m where
  mapState := fun q => q
  map_start := Path.refl _
  map_delta := fun _ _ => Path.refl _
  map_accept := fun _ => rfl

/-- Def 30: Identity homomorphism preserves state -/
def DFAHom.ident_mapState {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q : Q) :
    Path ((DFAHom.ident m).mapState q) q :=
  Path.refl _

/-- Composition of homomorphisms -/
def DFAHom.compose {Q1 : Type u} {Q2 : Type v} {Q3 : Type w} {Sym : Type _}
    {m1 : DFA Q1 Sym} {m2 : DFA Q2 Sym} {m3 : DFA Q3 Sym}
    (g : DFAHom m2 m3) (f : DFAHom m1 m2) : DFAHom m1 m3 where
  mapState := fun q => g.mapState (f.mapState q)
  map_start := Path.trans (Path.congrArg g.mapState f.map_start) g.map_start
  map_delta := fun q a =>
    Path.trans (Path.congrArg g.mapState (f.map_delta q a)) (g.map_delta (f.mapState q) a)
  map_accept := fun q =>
    (f.map_accept q).trans (g.map_accept (f.mapState q))

/-- Def 31: Composition is correct on mapState -/
def DFAHom.compose_mapState {Q1 : Type u} {Q2 : Type v} {Q3 : Type w} {Sym : Type _}
    {m1 : DFA Q1 Sym} {m2 : DFA Q2 Sym} {m3 : DFA Q3 Sym}
    (g : DFAHom m2 m3) (f : DFAHom m1 m2) (q : Q1) :
    Path ((g.compose f).mapState q) (g.mapState (f.mapState q)) :=
  Path.refl _

-- ============================================================================
-- SECTION 9: Pumping Lemma Structure
-- ============================================================================

/-- A pumping decomposition of a word -/
structure PumpingDecomp (Sym : Type v) where
  x : List Sym
  y : List Sym
  z : List Sym
  y_nonempty : y ≠ []

/-- Reconstructed word from pumping decomposition -/
def PumpingDecomp.word {Sym : Type v} (d : PumpingDecomp Sym) : List Sym :=
  d.x ++ d.y ++ d.z

/-- Pumped word: repeat y part i times -/
def pumpWord {Sym : Type v} (x y z : List Sym) : Nat → List Sym
  | 0 => x ++ z
  | n + 1 => x ++ y ++ pumpWord [] y z n

/-- Def 32: Pumping with i=1 gives expected form -/
def pump_one {Sym : Type v} (x y z : List Sym) :
    Path (pumpWord x y z 1) (x ++ y ++ ([] ++ z)) :=
  Path.refl _

/-- Def 33: Pumping with i=0 removes y -/
def pump_zero {Sym : Type v} (x y z : List Sym) :
    Path (pumpWord x y z 0) (x ++ z) :=
  Path.refl _

/-- Def 34: Path relating pumped runs through a loop state -/
def pump_loop_state {Q : Type u} {Sym : Type v} (m : DFA Q Sym)
    (q_loop : Q) (y : List Sym) (h : Path (m.run q_loop y) q_loop) :
    ∀ (n : Nat), Path (m.run q_loop (List.flatten (List.replicate n y))) q_loop
  | 0 => Path.refl _
  | n + 1 =>
    Path.trans (run_append m q_loop y (List.flatten (List.replicate n y)))
      (Path.trans
        (run_congruence m h (List.flatten (List.replicate n y)))
        (pump_loop_state m q_loop y h n))

-- ============================================================================
-- SECTION 10: State Reachability
-- ============================================================================

/-- A state is reachable if there's a word leading to it from start -/
def Reachable {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q : Q) : Prop :=
  ∃ w : List Sym, m.run m.start w = q

/-- Theorem 35: Start state is always reachable -/
theorem start_reachable {Q : Type u} {Sym : Type v} (m : DFA Q Sym) :
    Reachable m m.start :=
  ⟨[], rfl⟩

/-- Theorem 36: Reachability is closed under transitions -/
theorem reachable_step {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q : Q) (a : Sym)
    (h : Reachable m q) : Reachable m (m.delta q a) :=
  match h with
  | ⟨w, p⟩ => ⟨w ++ [a], (run_append m m.start w [a]).toEq ▸ congrArg (fun q => m.delta q a) p⟩

/-- Theorem 37: Reachability extends along word runs -/
theorem reachable_run {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q : Q)
    (ws : List Sym) (h : Reachable m q) : Reachable m (m.run q ws) :=
  match h with
  | ⟨w0, p⟩ => ⟨w0 ++ ws, (run_append m m.start w0 ws).toEq ▸ congrArg (fun q => m.run q ws) p⟩

-- ============================================================================
-- SECTION 11: State Distinguishability and Indistinguishability
-- ============================================================================

/-- Two states are indistinguishable if no word separates them -/
def Indistinguishable {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q1 q2 : Q) : Prop :=
  ∀ w : List Sym, m.accept (m.run q1 w) = m.accept (m.run q2 w)

/-- Theorem 38: Indistinguishability refines MN equivalence -/
theorem indist_is_mnEquiv {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q1 q2 : Q)
    (h : Indistinguishable m q1 q2) : mnEquiv m q1 q2 :=
  h

/-- Theorem 39: Indistinguishability is reflexive -/
theorem indist_refl {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q : Q) :
    Indistinguishable m q q :=
  fun _ => rfl

/-- Theorem 40: Indistinguishability is symmetric -/
theorem indist_symm {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q1 q2 : Q)
    (h : Indistinguishable m q1 q2) : Indistinguishable m q2 q1 :=
  fun w => (h w).symm

/-- Theorem 41: Indistinguishability is transitive -/
theorem indist_trans' {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q1 q2 q3 : Q)
    (h12 : Indistinguishable m q1 q2) (h23 : Indistinguishable m q2 q3) :
    Indistinguishable m q1 q3 :=
  fun w => (h12 w).trans (h23 w)

/-- Theorem 42: Indistinguishable states have same acceptance on empty word -/
theorem indist_empty {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q1 q2 : Q)
    (h : Indistinguishable m q1 q2) : m.accept q1 = m.accept q2 :=
  h []

/-- Theorem 43: Indistinguishability preserved under delta -/
theorem indist_delta {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q1 q2 : Q)
    (a : Sym) (h : Indistinguishable m q1 q2) :
    Indistinguishable m (m.delta q1 a) (m.delta q2 a) :=
  fun w => h (a :: w)

/-- Def 44: Indistinguishability lifts to Path on acceptance -/
def indist_to_accept_path {Q : Type u} {Sym : Type v} (m : DFA Q Sym) {q1 q2 : Q}
    (h : Indistinguishable m q1 q2) (w : List Sym) :
    Path (m.accept (m.run q1 w)) (m.accept (m.run q2 w)) :=
  Path.stepChain (h w)

-- ============================================================================
-- SECTION 12: Subset Construction (NFA → DFA) Path Coherence
-- ============================================================================

/-- Powerset state type -/
def PowerState (Q : Type u) := Q → Prop

/-- State set equivalence -/
def stateSetEquiv {Q : Type u} (S1 S2 : PowerState Q) : Prop :=
  ∀ q : Q, S1 q ↔ S2 q

/-- Theorem 45: State set equivalence is reflexive -/
theorem stateSetEquiv_refl {Q : Type u} (S : PowerState Q) : stateSetEquiv S S :=
  fun _ => Iff.rfl

/-- Theorem 46: State set equivalence is symmetric -/
theorem stateSetEquiv_symm {Q : Type u} (S1 S2 : PowerState Q)
    (h : stateSetEquiv S1 S2) : stateSetEquiv S2 S1 :=
  fun q => (h q).symm

/-- Theorem 47: State set equivalence is transitive -/
theorem stateSetEquiv_trans' {Q : Type u} (S1 S2 S3 : PowerState Q)
    (h12 : stateSetEquiv S1 S2) (h23 : stateSetEquiv S2 S3) : stateSetEquiv S1 S3 :=
  fun q => (h12 q).trans (h23 q)

-- ============================================================================
-- SECTION 13: Regular Expression Structure
-- ============================================================================

/-- Regular expressions over an alphabet -/
inductive Regex (Sym : Type v) where
  | empty : Regex Sym
  | epsilon : Regex Sym
  | char : Sym → Regex Sym
  | union : Regex Sym → Regex Sym → Regex Sym
  | concat : Regex Sym → Regex Sym → Regex Sym
  | star : Regex Sym → Regex Sym

/-- Matching predicate for regex -/
inductive RegexMatch {Sym : Type v} : Regex Sym → List Sym → Prop where
  | epsilon : RegexMatch .epsilon []
  | char (a : Sym) : RegexMatch (.char a) [a]
  | unionL {r1 r2 w} : RegexMatch r1 w → RegexMatch (.union r1 r2) w
  | unionR {r1 r2 w} : RegexMatch r2 w → RegexMatch (.union r1 r2) w
  | concat {r1 r2 w1 w2} : RegexMatch r1 w1 → RegexMatch r2 w2 →
      RegexMatch (.concat r1 r2) (w1 ++ w2)
  | starNil {r} : RegexMatch (.star r) []
  | starCons {r w1 w2} : RegexMatch r w1 → RegexMatch (.star r) w2 →
      RegexMatch (.star r) (w1 ++ w2)

/-- Theorem 48: Empty regex matches nothing -/
theorem regex_empty_no_match {Sym : Type v} (w : List Sym) :
    ¬ RegexMatch (.empty : Regex Sym) w :=
  fun h => nomatch h

/-- Theorem 49: Epsilon regex matches empty word -/
theorem regex_epsilon_nil {Sym : Type v} : RegexMatch (.epsilon : Regex Sym) [] :=
  RegexMatch.epsilon

/-- Theorem 50: Char regex matches singleton -/
theorem regex_char_match {Sym : Type v} (a : Sym) : RegexMatch (.char a) [a] :=
  RegexMatch.char a

/-- Theorem 51: Star regex always matches empty word -/
theorem regex_star_nil {Sym : Type v} (r : Regex Sym) : RegexMatch (.star r) [] :=
  RegexMatch.starNil

/-- Theorem 52: Union of regex is commutative -/
theorem regex_union_comm {Sym : Type v} (r1 r2 : Regex Sym) (w : List Sym) :
    RegexMatch (.union r1 r2) w ↔ RegexMatch (.union r2 r1) w :=
  ⟨fun h => match h with
    | .unionL h1 => .unionR h1
    | .unionR h2 => .unionL h2,
   fun h => match h with
    | .unionL h2 => .unionR h2
    | .unionR h1 => .unionL h1⟩

/-- Theorem 53: Union of regex is associative -/
theorem regex_union_assoc {Sym : Type v} (r1 r2 r3 : Regex Sym) (w : List Sym) :
    RegexMatch (.union (.union r1 r2) r3) w ↔
    RegexMatch (.union r1 (.union r2 r3)) w :=
  ⟨fun h => match h with
    | .unionL (.unionL h1) => .unionL h1
    | .unionL (.unionR h2) => .unionR (.unionL h2)
    | .unionR h3 => .unionR (.unionR h3),
   fun h => match h with
    | .unionL h1 => .unionL (.unionL h1)
    | .unionR (.unionL h2) => .unionL (.unionR h2)
    | .unionR (.unionR h3) => .unionR h3⟩

-- ============================================================================
-- SECTION 14: DFA State Mapping
-- ============================================================================

/-- Map states of a DFA through a pair of functions -/
def DFA.mapStates {Q1 : Type u} {Q2 : Type v} {Sym : Type w}
    (m : DFA Q1 Sym) (f : Q1 → Q2) (g : Q2 → Q1) : DFA Q2 Sym where
  start := f m.start
  delta := fun q a => f (m.delta (g q) a)
  accept := fun q => m.accept (g q)

/-- Def 54: Mapped DFA has coherent start state -/
def mapStates_start {Q1 : Type u} {Q2 : Type v} {Sym : Type w}
    (m : DFA Q1 Sym) (f : Q1 → Q2) (g : Q2 → Q1) :
    Path (m.mapStates f g).start (f m.start) :=
  Path.refl _

/-- Def 55: Mapped DFA acceptance via path -/
def mapStates_accept {Q1 : Type u} {Q2 : Type v} {Sym : Type w}
    (m : DFA Q1 Sym) (f : Q1 → Q2) (g : Q2 → Q1) (q : Q2) :
    Path ((m.mapStates f g).accept q) (m.accept (g q)) :=
  Path.refl _

-- ============================================================================
-- SECTION 15: Path-Level Identities (congrArg coherence)
-- ============================================================================

/-- Theorem 56: congrArg distributes over trans for DFA runs -/
theorem congrArg_run_trans {Q : Type u} {Sym : Type v} (m : DFA Q Sym)
    {q1 q2 q3 : Q} (p12 : Path q1 q2) (p23 : Path q2 q3) (w : List Sym) :
    Path.congrArg (fun q => m.run q w) (Path.trans p12 p23) =
    Path.trans (Path.congrArg (fun q => m.run q w) p12)
               (Path.congrArg (fun q => m.run q w) p23) :=
  congrArg_trans (fun q => m.run q w) p12 p23

/-- Theorem 57: congrArg distributes over symm for DFA runs -/
theorem congrArg_run_symm {Q : Type u} {Sym : Type v} (m : DFA Q Sym)
    {q1 q2 : Q} (p : Path q1 q2) (w : List Sym) :
    Path.congrArg (fun q => m.run q w) (Path.symm p) =
    Path.symm (Path.congrArg (fun q => m.run q w) p) :=
  congrArg_symm (fun q => m.run q w) p

/-- Theorem 58: congrArg of accept over trans -/
theorem congrArg_accept_trans {Q : Type u} {Sym : Type v} (m : DFA Q Sym)
    {q1 q2 q3 : Q} (p : Path q1 q2) (r : Path q2 q3) :
    Path.congrArg m.accept (Path.trans p r) =
    Path.trans (Path.congrArg m.accept p) (Path.congrArg m.accept r) :=
  congrArg_trans m.accept p r

/-- Theorem 59: congrArg of accept over symm -/
theorem congrArg_accept_symm {Q : Type u} {Sym : Type v} (m : DFA Q Sym)
    {q1 q2 : Q} (p : Path q1 q2) :
    Path.congrArg m.accept (Path.symm p) =
    Path.symm (Path.congrArg m.accept p) :=
  congrArg_symm m.accept p

/-- Theorem 60: congrArg of delta over trans -/
theorem congrArg_delta_trans {Q : Type u} {Sym : Type v} (m : DFA Q Sym)
    {q1 q2 q3 : Q} (a : Sym) (p : Path q1 q2) (r : Path q2 q3) :
    Path.congrArg (fun q => m.delta q a) (Path.trans p r) =
    Path.trans (Path.congrArg (fun q => m.delta q a) p)
               (Path.congrArg (fun q => m.delta q a) r) :=
  congrArg_trans (fun q => m.delta q a) p r

/-- Theorem 61: congrArg of delta over symm -/
theorem congrArg_delta_symm {Q : Type u} {Sym : Type v} (m : DFA Q Sym)
    {q1 q2 : Q} (a : Sym) (p : Path q1 q2) :
    Path.congrArg (fun q => m.delta q a) (Path.symm p) =
    Path.symm (Path.congrArg (fun q => m.delta q a) p) :=
  congrArg_symm (fun q => m.delta q a) p

/-- Theorem 62: congrArg of Prod.fst over trans -/
theorem congrArg_fst_trans {Q1 Q2 : Type u}
    {p1 p2 p3 : Q1 × Q2} (h1 : Path p1 p2) (h2 : Path p2 p3) :
    Path.congrArg Prod.fst (Path.trans h1 h2) =
    Path.trans (Path.congrArg Prod.fst h1) (Path.congrArg Prod.fst h2) :=
  congrArg_trans Prod.fst h1 h2

/-- Theorem 63: congrArg of Prod.snd over trans -/
theorem congrArg_snd_trans {Q1 Q2 : Type u}
    {p1 p2 p3 : Q1 × Q2} (h1 : Path p1 p2) (h2 : Path p2 p3) :
    Path.congrArg Prod.snd (Path.trans h1 h2) =
    Path.trans (Path.congrArg Prod.snd h1) (Path.congrArg Prod.snd h2) :=
  congrArg_trans Prod.snd h1 h2

-- ============================================================================
-- SECTION 16: Groupoid Laws for State Paths
-- ============================================================================

/-- Theorem 64: trans_refl_left for state paths -/
theorem state_trans_refl_left {Q : Type u} {q1 q2 : Q} (p : Path q1 q2) :
    Path.trans (Path.refl q1) p = p :=
  trans_refl_left p

/-- Theorem 65: trans_refl_right for state paths -/
theorem state_trans_refl_right {Q : Type u} {q1 q2 : Q} (p : Path q1 q2) :
    Path.trans p (Path.refl q2) = p :=
  trans_refl_right p

/-- Theorem 66: symm_symm for state paths -/
theorem state_symm_symm {Q : Type u} {q1 q2 : Q} (p : Path q1 q2) :
    Path.symm (Path.symm p) = p :=
  symm_symm p

/-- Theorem 67: symm reverses trans -/
theorem state_symm_trans {Q : Type u} {q1 q2 q3 : Q} (p : Path q1 q2) (r : Path q2 q3) :
    Path.symm (Path.trans p r) = Path.trans (Path.symm r) (Path.symm p) :=
  symm_trans p r

/-- Theorem 68: trans_assoc for state paths -/
theorem state_trans_assoc {Q : Type u} {q1 q2 q3 q4 : Q}
    (p : Path q1 q2) (r : Path q2 q3) (s : Path q3 q4) :
    Path.trans (Path.trans p r) s = Path.trans p (Path.trans r s) :=
  trans_assoc p r s

-- ============================================================================
-- SECTION 17: Functoriality of Homomorphism Composition
-- ============================================================================

/-- Theorem 69: Composition is associative on mapState -/
theorem DFAHom_compose_assoc {Q1 : Type u} {Q2 : Type v} {Q3 : Type w}
    {Q4 : Type _} {Sym : Type _}
    {m1 : DFA Q1 Sym} {m2 : DFA Q2 Sym} {m3 : DFA Q3 Sym} {m4 : DFA Q4 Sym}
    (h' : DFAHom m3 m4) (g : DFAHom m2 m3) (f : DFAHom m1 m2) (q : Q1) :
    (h'.compose (g.compose f)).mapState q = ((h'.compose g).compose f).mapState q :=
  rfl

/-- Theorem 70: Identity homomorphism is left unit -/
theorem DFAHom_ident_compose {Q1 : Type u} {Q2 : Type v} {Sym : Type _}
    {m1 : DFA Q1 Sym} {m2 : DFA Q2 Sym} (f : DFAHom m1 m2) (q : Q1) :
    ((DFAHom.ident m2).compose f).mapState q = f.mapState q :=
  rfl

/-- Theorem 71: Identity homomorphism is right unit -/
theorem DFAHom_compose_ident {Q1 : Type u} {Q2 : Type v} {Sym : Type _}
    {m1 : DFA Q1 Sym} {m2 : DFA Q2 Sym} (f : DFAHom m1 m2) (q : Q1) :
    (f.compose (DFAHom.ident m1)).mapState q = f.mapState q :=
  rfl

-- ============================================================================
-- SECTION 18: Product/Union/Complement Coherence
-- ============================================================================

/-- Def 72: Product automaton acceptance factors -/
def product_accept_path {Q1 Q2 : Type u} {Sym : Type v}
    (m1 : DFA Q1 Sym) (m2 : DFA Q2 Sym) (q1 : Q1) (q2 : Q2) :
    Path ((m1.product m2).accept (q1, q2)) (m1.accept q1 && m2.accept q2) :=
  Path.refl _

/-- Def 73: Union automaton acceptance factors -/
def union_accept_path {Q1 Q2 : Type u} {Sym : Type v}
    (m1 : DFA Q1 Sym) (m2 : DFA Q2 Sym) (q1 : Q1) (q2 : Q2) :
    Path ((m1.union m2).accept (q1, q2)) (m1.accept q1 || m2.accept q2) :=
  Path.refl _

/-- Def 74: Complement negates acceptance -/
def complement_accept_path {Q : Type u} {Sym : Type v}
    (m : DFA Q Sym) (q : Q) :
    Path (m.complement.accept q) (!m.accept q) :=
  Path.refl _

/-- Theorem 75: MN equivalence classes are stable under complement -/
theorem mnEquiv_complement {Q : Type u} {Sym : Type v} (m : DFA Q Sym) (q1 q2 : Q)
    (h : mnEquiv m q1 q2) : mnEquiv m.complement q1 q2 := by
  intro w
  unfold DFA.complement mnEquiv at *
  simp only [] at *
  have h1 := complement_run_eq m q1 w
  have h2 := complement_run_eq m q2 w
  simp only [DFA.complement] at h1 h2
  rw [h1, h2]
  exact congrArg (fun b => !b) (h w)

/-- Theorem 76: Product of MN-equivalent states in first component -/
theorem mnEquiv_product_fst {Q1 Q2 : Type u} {Sym : Type v}
    (m1 : DFA Q1 Sym) (m2 : DFA Q2 Sym) (q1 q1' : Q1) (q2 : Q2)
    (h : mnEquiv m1 q1 q1') :
    mnEquiv (m1.product m2) (q1, q2) (q1', q2) := by
  intro w
  simp only [DFA.product]
  have p1 := (product_run_fst m1 m2 q1 q2 w).toEq
  have p2 := (product_run_snd m1 m2 q1 q2 w).toEq
  have p3 := (product_run_fst m1 m2 q1' q2 w).toEq
  have p4 := (product_run_snd m1 m2 q1' q2 w).toEq
  simp only [DFA.product] at p1 p2 p3 p4
  rw [p1, p2, p3, p4]
  exact congrArg (· && m2.accept (m2.run q2 w)) (h w)

/-- Theorem 77: Product of MN-equivalent states in second component -/
theorem mnEquiv_product_snd {Q1 Q2 : Type u} {Sym : Type v}
    (m1 : DFA Q1 Sym) (m2 : DFA Q2 Sym) (q1 : Q1) (q2 q2' : Q2)
    (h : mnEquiv m2 q2 q2') :
    mnEquiv (m1.product m2) (q1, q2) (q1, q2') := by
  intro w
  simp only [DFA.product]
  have p1 := (product_run_fst m1 m2 q1 q2 w).toEq
  have p2 := (product_run_snd m1 m2 q1 q2 w).toEq
  have p3 := (product_run_fst m1 m2 q1 q2' w).toEq
  have p4 := (product_run_snd m1 m2 q1 q2' w).toEq
  simp only [DFA.product] at p1 p2 p3 p4
  rw [p1, p2, p3, p4]
  exact congrArg (m1.accept (m1.run q1 w) && ·) (h w)

end AutomataPathDeep
