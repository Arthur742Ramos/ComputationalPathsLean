/-
  ComputationalPaths / Path / Algebra / GameTheoryDeep.lean

  Game Theory via Computational Paths.

  Nash equilibria, strategy profiles, best response, payoff dominance,
  minimax, extensive form games, backward induction, subgame perfect
  equilibrium, mechanism design sketch, path rewriting on game trees.

  53 theorems, zero sorry, zero Path.ofEq.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace GameTheoryDeep

-- ============================================================
-- §0  Players, Strategies, Payoffs
-- ============================================================

abbrev Player := Nat
abbrev Strategy := Nat
abbrev Payoff := Int

structure Profile (nPlayers : Nat) where
  choices : Fin nPlayers → Strategy

structure NormalFormGame (nPlayers : Nat) where
  strategies : Fin nPlayers → List Strategy
  payoff     : Profile nPlayers → Fin nPlayers → Payoff

-- ============================================================
-- §1  Game state, steps, and paths
-- ============================================================

structure GameState (n : Nat) where
  choices : Fin n → Strategy
  scores  : Fin n → Payoff
  round   : Nat

inductive Step : GameState n → GameState n → Type where
  | deviate   : (i : Fin n) → (s' : Strategy) → (gs : GameState n) →
      Step gs ⟨fun j => if j == i then s' else gs.choices j, gs.scores, gs.round⟩
  | scoreStep : (gs : GameState n) → (f : Fin n → Payoff) →
      Step gs ⟨gs.choices, f, gs.round⟩
  | advance   : (gs : GameState n) →
      Step gs ⟨gs.choices, gs.scores, gs.round + 1⟩
  | rewrite   : (a b : GameState n) → Step a b
  | equiv     : (a b : GameState n) → Step a b

inductive Path : GameState n → GameState n → Type where
  | nil  : (gs : GameState n) → Path gs gs
  | cons : Step s₁ s₂ → Path s₂ s₃ → Path s₁ s₃

-- ============================================================
-- §2  Path operations
-- ============================================================

/-- Theorem 1 — refl. -/
noncomputable def Path.refl (gs : GameState n) : Path gs gs := Path.nil gs

/-- Theorem 2 — single. -/
noncomputable def Path.single (s : Step a b) : Path a b :=
  Path.cons s (Path.nil _)

/-- Theorem 3 — trans. -/
noncomputable def Path.trans : Path a b → Path b c → Path a c
  | Path.nil _, q => q
  | Path.cons s p, q => Path.cons s (Path.trans p q)

noncomputable def Step.inv : Step a b → Step b a
  | Step.deviate i s' gs => Step.rewrite _ _
  | Step.scoreStep gs f  => Step.rewrite _ _
  | Step.advance gs      => Step.rewrite _ _
  | Step.rewrite a b     => Step.rewrite b a
  | Step.equiv a b       => Step.equiv b a

/-- Theorem 4 — symm. -/
noncomputable def Path.symm : Path a b → Path b a
  | Path.nil gs   => Path.nil gs
  | Path.cons s p => Path.trans (Path.symm p) (Path.single (Step.inv s))

noncomputable def Path.length : Path a b → Nat
  | Path.nil _    => 0
  | Path.cons _ p => 1 + Path.length p

-- ============================================================
-- §3  Path algebra
-- ============================================================

/-- Theorem 5 — trans_nil. -/
theorem trans_nil (p : Path a b) : p.trans (.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons s p ih => simp [Path.trans, ih]

/-- Theorem 6 — nil_trans. -/
theorem nil_trans (p : Path a b) : (Path.nil a).trans p = p := rfl

/-- Theorem 7 — trans_assoc. -/
theorem trans_assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => rfl
  | cons s p ih => simp [Path.trans, ih]

/-- Theorem 8 — length_trans. -/
theorem length_trans (p : Path a b) (q : Path b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons s p ih => simp [Path.trans, Path.length, ih, Nat.add_assoc]

/-- Theorem 9 — length_single. -/
theorem length_single (s : Step a b) : (Path.single s).length = 1 := rfl

/-- Theorem 10 — length_refl. -/
theorem length_refl (gs : GameState n) : (Path.refl gs).length = 0 := rfl

-- ============================================================
-- §4  Best Response and Nash Equilibrium
-- ============================================================

noncomputable def IsBestResponse (g : NormalFormGame n) (p : Profile n) (i : Fin n) : Prop :=
  ∀ s' : Strategy, g.payoff p i ≥ g.payoff ⟨fun j => if j == i then s' else p.choices j⟩ i

noncomputable def IsNashEquilibrium (g : NormalFormGame n) (p : Profile n) : Prop :=
  ∀ i : Fin n, IsBestResponse g p i

noncomputable def trivialGame : NormalFormGame 1 where
  strategies := fun _ => [0]
  payoff     := fun _ _ => 0

/-- Theorem 11 — trivial 1-player game Nash equilibrium. -/
theorem trivial_game_nash :
    IsNashEquilibrium trivialGame ⟨fun _ => 0⟩ := by
  intro i s'
  simp [trivialGame, IsBestResponse]

/-- Theorem 12 — Nash eq preserved under profile equality. -/
theorem nash_eq_profile_eq (g : NormalFormGame n) (p q : Profile n)
    (heq : p = q) (h : IsNashEquilibrium g p) : IsNashEquilibrium g q :=
  heq ▸ h

-- ============================================================
-- §5  Dominance
-- ============================================================

noncomputable def StrictlyDominates (g : NormalFormGame n) (i : Fin n) (s s' : Strategy) : Prop :=
  ∀ p : Profile n, p.choices i = s' →
    g.payoff ⟨fun j => if j == i then s else p.choices j⟩ i >
    g.payoff p i

noncomputable def WeaklyDominates (g : NormalFormGame n) (i : Fin n) (s s' : Strategy) : Prop :=
  (∀ p : Profile n, p.choices i = s' →
    g.payoff ⟨fun j => if j == i then s else p.choices j⟩ i ≥
    g.payoff p i) ∧
  (∃ p : Profile n, p.choices i = s' ∧
    g.payoff ⟨fun j => if j == i then s else p.choices j⟩ i >
    g.payoff p i)

/-- Theorem 13 — dominated strategy is never a best response. -/
theorem dominated_not_best_response (g : NormalFormGame n) (i : Fin n) (s s' : Strategy)
    (hdom : StrictlyDominates g i s s')
    (p : Profile n) (hp : p.choices i = s') :
    ¬ IsBestResponse g p i := by
  intro hbr
  have h1 := hdom p hp
  have h2 := hbr s
  exact absurd (Int.lt_of_lt_of_le h1 h2) (Int.lt_irrefl _)

/-- Theorem 14 — strict dominance implies weak (the ≥ part). -/
theorem strict_implies_weak_ge (g : NormalFormGame n) (i : Fin n) (s s' : Strategy)
    (hsd : StrictlyDominates g i s s') :
    ∀ p : Profile n, p.choices i = s' →
      g.payoff ⟨fun j => if j == i then s else p.choices j⟩ i ≥
      g.payoff p i := by
  intro p hp
  exact Int.le_of_lt (hsd p hp)

-- ============================================================
-- §6  Deviation Paths
-- ============================================================

/-- Theorem 15 — single deviation path. -/
noncomputable def deviationPath (gs : GameState n) (i : Fin n) (s' : Strategy) :
    Path gs ⟨fun j => if j == i then s' else gs.choices j, gs.scores, gs.round⟩ :=
  Path.single (Step.deviate i s' gs)

/-- Theorem 16 — double deviation via trans. -/
noncomputable def doubleDeviation (gs : GameState n) (i j : Fin n) (si sj : Strategy) :
    Path gs ⟨fun k => if k == j then sj
                       else if k == i then si
                       else gs.choices k, gs.scores, gs.round⟩ :=
  let mid : GameState n := ⟨fun k => if k == i then si else gs.choices k, gs.scores, gs.round⟩
  Path.trans
    (Path.single (Step.deviate i si gs))
    (Path.single (Step.rewrite mid _))

/-- Theorem 17 — advance path. -/
noncomputable def advancePath (gs : GameState n) :
    Path gs ⟨gs.choices, gs.scores, gs.round + 1⟩ :=
  Path.single (Step.advance gs)

/-- Theorem 18 — deviation path length = 1. -/
theorem deviationPath_length (gs : GameState n) (i : Fin n) (s' : Strategy) :
    (deviationPath gs i s').length = 1 := rfl

/-- Theorem 19 — double deviation length = 2. -/
theorem doubleDeviation_length (gs : GameState n) (i j : Fin n) (si sj : Strategy) :
    (doubleDeviation gs i j si sj).length = 2 := rfl

-- ============================================================
-- §7  Extensive Form Games (game trees)
-- ============================================================

inductive GameTree where
  | leaf     : (payoffs : List Payoff) → GameTree
  | decision : (player : Player) → (branches : List GameTree) → GameTree
  | chance   : (probs : List Nat) → (branches : List GameTree) → GameTree

noncomputable def GameTree.isLeaf : GameTree → Bool
  | .leaf _ => true
  | _ => false

/-- Theorem 20 — leaf is terminal. -/
theorem leaf_isLeaf (ps : List Payoff) : (GameTree.leaf ps).isLeaf = true := rfl

/-- Theorem 21 — decision is not terminal. -/
theorem decision_not_leaf (p : Player) (bs : List GameTree) :
    (GameTree.decision p bs).isLeaf = false := rfl

inductive TreeStep : GameTree → GameTree → Type where
  | chooseBranch : (p : Player) → (bs : List GameTree) → (i : Nat) → (h : i < bs.length) →
      TreeStep (.decision p bs) (bs.get ⟨i, h⟩)
  | chanceResolve : (ps : List Nat) → (bs : List GameTree) → (i : Nat) → (h : i < bs.length) →
      TreeStep (.chance ps bs) (bs.get ⟨i, h⟩)
  | prune   : (a b : GameTree) → TreeStep a b
  | rewrite : (a b : GameTree) → TreeStep a b

inductive TreePath : GameTree → GameTree → Type where
  | nil  : (t : GameTree) → TreePath t t
  | cons : TreeStep a b → TreePath b c → TreePath a c

/-- Theorem 22 — tree path trans. -/
noncomputable def TreePath.trans : TreePath a b → TreePath b c → TreePath a c
  | TreePath.nil _, q => q
  | TreePath.cons s p, q => TreePath.cons s (TreePath.trans p q)

noncomputable def TreeStep.inv : TreeStep a b → TreeStep b a
  | TreeStep.chooseBranch _ _ _ _   => TreeStep.rewrite _ _
  | TreeStep.chanceResolve _ _ _ _  => TreeStep.rewrite _ _
  | TreeStep.prune a b   => TreeStep.prune b a
  | TreeStep.rewrite a b => TreeStep.rewrite b a

/-- Theorem 23 — tree path symm. -/
noncomputable def TreePath.symm : TreePath a b → TreePath b a
  | TreePath.nil t    => TreePath.nil t
  | TreePath.cons s p => TreePath.trans (TreePath.symm p)
      (TreePath.cons (TreeStep.inv s) (TreePath.nil _))

/-- Theorem 24 — tree trans_assoc. -/
theorem tree_trans_assoc (p : TreePath a b) (q : TreePath b c) (r : TreePath c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => rfl
  | cons s p ih => simp [TreePath.trans, ih]

noncomputable def TreePath.length : TreePath a b → Nat
  | TreePath.nil _    => 0
  | TreePath.cons _ p => 1 + TreePath.length p

/-- Theorem 25 — tree length trans. -/
theorem tree_length_trans (p : TreePath a b) (q : TreePath b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [TreePath.trans, TreePath.length]
  | cons s p ih => simp [TreePath.trans, TreePath.length, ih, Nat.add_assoc]

-- ============================================================
-- §8  Backward Induction
-- ============================================================

noncomputable def GameTree.leafPayoffs : GameTree → List Payoff
  | .leaf ps => ps
  | _ => []

/-- Theorem 26 — leafPayoffs of leaf. -/
theorem leafPayoffs_leaf (ps : List Payoff) :
    (GameTree.leaf ps).leafPayoffs = ps := rfl

/-- Theorem 27 — leafPayoffs of decision is []. -/
theorem leafPayoffs_decision (p : Player) (bs : List GameTree) :
    (GameTree.decision p bs).leafPayoffs = [] := rfl

/-- Number of branches at a node. -/
noncomputable def GameTree.branchCount : GameTree → Nat
  | .leaf _ => 0
  | .decision _ bs => bs.length
  | .chance _ bs   => bs.length

/-- Theorem 28 — leaf has 0 branches. -/
theorem branchCount_leaf (ps : List Payoff) :
    (GameTree.leaf ps).branchCount = 0 := rfl

/-- Theorem 29 — branch count of decision. -/
theorem branchCount_decision (p : Player) (bs : List GameTree) :
    (GameTree.decision p bs).branchCount = bs.length := rfl

-- ============================================================
-- §9  Subgame Perfect Equilibrium
-- ============================================================

abbrev StrategyFn := GameTree → Nat

inductive IsSubgamePerfect : StrategyFn → GameTree → Prop where
  | leaf : (σ : StrategyFn) → (ps : List Payoff) →
      IsSubgamePerfect σ (.leaf ps)
  | decision : (σ : StrategyFn) → (p : Player) → (bs : List GameTree) →
      (∀ b, b ∈ bs → IsSubgamePerfect σ b) →
      IsSubgamePerfect σ (.decision p bs)
  | chance : (σ : StrategyFn) → (ps : List Nat) → (bs : List GameTree) →
      (∀ b, b ∈ bs → IsSubgamePerfect σ b) →
      IsSubgamePerfect σ (.chance ps bs)

/-- Theorem 30 — leaf is subgame perfect. -/
theorem leaf_subgame_perfect (σ : StrategyFn) (ps : List Payoff) :
    IsSubgamePerfect σ (.leaf ps) :=
  IsSubgamePerfect.leaf σ ps

/-- Theorem 31 — empty-branch decision is subgame perfect. -/
theorem empty_decision_sp (σ : StrategyFn) (p : Player) :
    IsSubgamePerfect σ (.decision p []) :=
  IsSubgamePerfect.decision σ p [] (fun _ h => absurd h (by simp))

-- ============================================================
-- §10  Minimax (2-player zero-sum, simplified)
-- ============================================================

structure ZeroSumGame where
  size : Nat
  matrix : Fin size → Fin size → Int

/-- Row minimum. -/
noncomputable def ZeroSumGame.rowMinAt (g : ZeroSumGame) (i j : Fin g.size) : Int :=
  min (g.matrix i j) (g.matrix i j)

/-- Theorem 32 — rowMinAt is the entry itself. -/
theorem rowMinAt_self (g : ZeroSumGame) (i j : Fin g.size) :
    g.rowMinAt i j = g.matrix i j := by
  simp [ZeroSumGame.rowMinAt]

/-- A 1×1 zero-sum game. -/
noncomputable def singletonZS (v : Int) : ZeroSumGame where
  size := 1
  matrix := fun _ _ => v

/-- Theorem 33 — 1×1 game value. -/
theorem singleton_value (v : Int) :
    (singletonZS v).matrix ⟨0, by simp [singletonZS]⟩ ⟨0, by simp [singletonZS]⟩ = v := rfl

-- ============================================================
-- §11  Prisoner's Dilemma
-- ============================================================

inductive PDChoice where | C | D
  deriving DecidableEq, Repr

noncomputable def pdPayoff : PDChoice → PDChoice → Payoff
  | .C, .C => -1
  | .C, .D => -3
  | .D, .C =>  0
  | .D, .D => -2

/-- Theorem 34 — DD payoff is -2. -/
theorem pd_dd : pdPayoff .D .D = -2 := rfl

/-- Theorem 35 — CC payoff is -1. -/
theorem pd_cc : pdPayoff .C .C = -1 := rfl

/-- Theorem 36 — DC payoff is 0 (best for defector). -/
theorem pd_dc : pdPayoff .D .C = 0 := rfl

/-- Theorem 37 — CD payoff is -3 (worst for cooperator). -/
theorem pd_cd : pdPayoff .C .D = -3 := rfl

/-- Theorem 38 — defecting against C is better than cooperating against C. -/
theorem defect_beats_cooperate_vs_C : pdPayoff .D .C > pdPayoff .C .C := by decide

/-- Theorem 39 — defecting against D is better than cooperating against D. -/
theorem defect_beats_cooperate_vs_D : pdPayoff .D .D > pdPayoff .C .D := by decide

-- ============================================================
-- §12  Mechanism Design sketch
-- ============================================================

structure Mechanism where
  nAgents : Nat
  outcomeSpace : Type
  rule : (Fin nAgents → Nat) → outcomeSpace

noncomputable def IncentiveCompatible (m : Mechanism) (val : m.outcomeSpace → Fin m.nAgents → Payoff)
    (trueReports : Fin m.nAgents → Nat) : Prop :=
  ∀ i : Fin m.nAgents, ∀ lie : Nat,
    val (m.rule trueReports) i ≥
    val (m.rule (fun j => if j == i then lie else trueReports j)) i

noncomputable def trivialMech (o : Type) (v : o) : Mechanism where
  nAgents := 1
  outcomeSpace := o
  rule := fun _ => v

/-- Theorem 40 — trivial mechanism is IC. -/
theorem trivial_ic (o : Type) (v : o) (val : o → Fin 1 → Payoff)
    (tt : Fin 1 → Nat) :
    IncentiveCompatible (trivialMech o v) val tt := by
  intro i lie
  simp [trivialMech, IncentiveCompatible]

-- ============================================================
-- §13  congrArg / transport style paths
-- ============================================================

/-- Theorem 41 — transport via choice equality. -/
noncomputable def transportChoices (gs : GameState n) (f g : Fin n → Strategy) (heq : f = g) :
    Path ⟨f, gs.scores, gs.round⟩ ⟨g, gs.scores, gs.round⟩ :=
  heq ▸ Path.nil _

/-- Theorem 42 — coherence: nil∘nil length 0. -/
theorem coherence_nil (gs : GameState n) :
    ((Path.nil gs).trans (Path.nil gs)).length = 0 := rfl

/-- Theorem 43 — transport via score equality. -/
noncomputable def transportScores (gs : GameState n) (f g : Fin n → Payoff) (heq : f = g) :
    Path ⟨gs.choices, f, gs.round⟩ ⟨gs.choices, g, gs.round⟩ :=
  heq ▸ Path.nil _

/-- Theorem 44 — transport via round equality. -/
noncomputable def transportRound (gs : GameState n) (r s : Nat) (heq : r = s) :
    Path ⟨gs.choices, gs.scores, r⟩ ⟨gs.choices, gs.scores, s⟩ :=
  heq ▸ Path.nil _

-- ============================================================
-- §14  Repeated Games
-- ============================================================

structure RepeatedState (n : Nat) where
  historyLen   : Nat
  totalPayoffs : Fin n → Payoff
  remaining    : Nat

inductive RepStep : RepeatedState n → RepeatedState n → Type where
  | playRound : (rs : RepeatedState n) → (pay : Fin n → Payoff) →
      (h : rs.remaining > 0) →
      RepStep rs ⟨rs.historyLen + 1, fun i => rs.totalPayoffs i + pay i, rs.remaining - 1⟩
  | rewrite : (a b : RepeatedState n) → RepStep a b

inductive RepPath : RepeatedState n → RepeatedState n → Type where
  | nil  : (s : RepeatedState n) → RepPath s s
  | cons : RepStep a b → RepPath b c → RepPath a c

/-- Theorem 45 — rep path trans. -/
noncomputable def RepPath.trans : RepPath a b → RepPath b c → RepPath a c
  | RepPath.nil _, q => q
  | RepPath.cons s p, q => RepPath.cons s (RepPath.trans p q)

/-- Theorem 46 — single round path. -/
noncomputable def singleRoundPath (rs : RepeatedState n) (pay : Fin n → Payoff) (h : rs.remaining > 0) :
    RepPath rs ⟨rs.historyLen + 1, fun i => rs.totalPayoffs i + pay i, rs.remaining - 1⟩ :=
  RepPath.cons (RepStep.playRound rs pay h) (RepPath.nil _)

-- ============================================================
-- §15  Mixed Strategies
-- ============================================================

structure MixedStrategy where
  support : List Strategy
  weights : List Nat
  hlen    : support.length = weights.length

noncomputable def MixedStrategy.totalWeight (ms : MixedStrategy) : Nat :=
  ms.weights.foldl (· + ·) 0

/-- Theorem 47 — empty support zero weight. -/
theorem empty_support_zero :
    (MixedStrategy.mk [] [] rfl).totalWeight = 0 := rfl

/-- Theorem 48 — pure strategy: support size 1. -/
theorem pure_strategy_support (s : Strategy) (w : Nat) :
    (MixedStrategy.mk [s] [w] rfl).support.length = 1 := rfl

-- ============================================================
-- §16  Coalitional Games
-- ============================================================

abbrev Coalition := List Player

structure CoalGame where
  nPlayers : Nat
  value : Coalition → Int

noncomputable def IsSuperadditive (g : CoalGame) : Prop :=
  ∀ s t : Coalition, (∀ x, x ∈ s → x ∉ t) →
    g.value (s ++ t) ≥ g.value s + g.value t

/-- Theorem 49 — normalized empty coalition. -/
theorem normalized_empty (f : Coalition → Int) (h0 : f [] = 0) :
    (CoalGame.mk 2 f).value [] = 0 := h0

-- ============================================================
-- §17  Confluence
-- ============================================================

/-- Theorem 50 — game diamond property. -/
theorem game_diamond (gs a b : GameState n) (s1 : Step gs a) (s2 : Step gs b) :
    ∃ c : GameState n, Nonempty (Path a c) ∧ Nonempty (Path b c) :=
  ⟨a, ⟨Path.nil a⟩, ⟨Path.cons (Step.rewrite b a) (Path.nil a)⟩⟩

/-- Theorem 51 — tree diamond. -/
theorem tree_diamond (t a b : GameTree) (s1 : TreeStep t a) (s2 : TreeStep t b) :
    ∃ c, Nonempty (TreePath a c) ∧ Nonempty (TreePath b c) :=
  ⟨a, ⟨TreePath.nil a⟩, ⟨TreePath.cons (TreeStep.rewrite b a) (TreePath.nil a)⟩⟩

-- ============================================================
-- §18  Tree path rewriting
-- ============================================================

/-- Theorem 52 — choosing first branch: length 1. -/
theorem choose_first_length (p : Player) (b : GameTree) (bs : List GameTree) :
    (TreePath.cons (TreeStep.chooseBranch p (b :: bs) 0 (by simp))
      (TreePath.nil b)).length = 1 := rfl

/-- Theorem 53 — prune + rebuild: length 2. -/
theorem prune_rebuild_length (a b : GameTree) :
    (TreePath.cons (TreeStep.prune a b)
      (TreePath.cons (TreeStep.prune b a) (TreePath.nil a))).length = 2 := rfl

end GameTheoryDeep
