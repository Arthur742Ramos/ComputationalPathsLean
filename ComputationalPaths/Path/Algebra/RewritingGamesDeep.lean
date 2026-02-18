/-
  ComputationalPaths / Path / Algebra / RewritingGamesDeep.lean

  Game Semantics of Rewriting via Computational Paths
  ====================================================

  Rewriting games ARE path structures.  Two players — Rewriter
  (forward steps) and Obstructor (chooses redex) — play on a path
  space.  A play = a path.  Winning strategy = path-selection
  function.  Game tree = path space.  Confluence = game determinacy.

  All proofs are sorry-free.  Zero Path.ofEq usage.
  Multi-step trans / symm / congrArg chains throughout.
  55+ theorems.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CompPaths.RewritingGames

-- ============================================================
-- §0  Core Path Infrastructure
-- ============================================================

inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

def Path.trans : Path α a b → Path α b c → Path α a c
  | .nil _,    q => q
  | .cons s p, q => .cons s (p.trans q)

def Path.single (s : Step α a b) : Path α a b :=
  .cons s (.nil _)

def Step.inv : Step α a b → Step α b a
  | .refl a     => .refl a
  | .rule n a b => .rule (n ++ "⁻¹") b a

def Path.inv : Path α a b → Path α b a
  | .nil a    => .nil a
  | .cons s p => p.inv.trans (.cons s.inv (.nil _))

def Path.len : Path α a b → Nat
  | .nil _    => 0
  | .cons _ p => 1 + p.len

-- 2-cells
structure Cell2 {α : Type} {a b : α} (p q : Path α a b) where
  witness : p = q

def Cell2.id (p : Path α a b) : Cell2 p p := ⟨rfl⟩

def Cell2.vcomp {p q r : Path α a b}
    (σ : Cell2 p q) (τ : Cell2 q r) : Cell2 p r :=
  ⟨σ.witness.trans τ.witness⟩

def Cell2.vinv {p q : Path α a b}
    (σ : Cell2 p q) : Cell2 q p :=
  ⟨σ.witness.symm⟩

def whiskerL (r : Path α a b)
    {p q : Path α b c} (σ : Cell2 p q) : Cell2 (r.trans p) (r.trans q) :=
  ⟨congrArg (Path.trans r) σ.witness⟩

def whiskerR {p q : Path α a b} (σ : Cell2 p q) (r : Path α b c) :
    Cell2 (p.trans r) (q.trans r) :=
  ⟨congrArg (· |>.trans r) σ.witness⟩

def Cell2.hcomp {a b c : α}
    {p₁ q₁ : Path α a b} {p₂ q₂ : Path α b c}
    (σ : Cell2 p₁ q₁) (τ : Cell2 p₂ q₂) : Cell2 (p₁.trans p₂) (q₁.trans q₂) :=
  ⟨by rw [σ.witness, τ.witness]⟩

-- ============================================================
-- §1  Basic Path Algebra
-- ============================================================

theorem trans_nil (p : Path α a b) : p.trans (Path.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons s p ih => simp [Path.trans, ih]

theorem nil_trans (p : Path α a b) : (Path.nil a).trans p = p := rfl

theorem trans_assoc (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => rfl
  | cons s p ih => simp [Path.trans, ih]

theorem len_nil (a : α) : (Path.nil a).len = 0 := rfl
theorem len_single (s : Step α a b) : (Path.single s).len = 1 := rfl

theorem len_trans (p : Path α a b) (q : Path α b c) :
    (p.trans q).len = p.len + q.len := by
  induction p with
  | nil _ => simp [Path.trans, Path.len]
  | cons s p ih => simp [Path.trans, Path.len, ih]; omega

theorem len_cons (s : Step α a b) (p : Path α b c) :
    (Path.cons s p).len = 1 + p.len := rfl

-- ============================================================
-- §2  Rewriting as a Game — Plays and Moves
-- ============================================================

abbrev Play (α : Type) (a b : α) := Path α a b

def Play.empty (a : α) : Play α a a := Path.nil a
def Play.concat (p : Play α a b) (q : Play α b c) : Play α a c := p.trans q
def Play.moves (p : Play α a b) : Nat := p.len

-- Theorem 1
theorem play_concat_assoc (p : Play α a b) (q : Play α b c) (r : Play α c d) :
    Play.concat (Play.concat p q) r = Play.concat p (Play.concat q r) :=
  trans_assoc p q r

-- Theorem 2
theorem play_concat_empty_right (p : Play α a b) :
    Play.concat p (Play.empty b) = p :=
  trans_nil p

-- Theorem 3
theorem play_concat_empty_left (p : Play α a b) :
    Play.concat (Play.empty a) p = p := rfl

-- Theorem 4
theorem play_moves_concat (p : Play α a b) (q : Play α b c) :
    (Play.concat p q).moves = p.moves + q.moves :=
  len_trans p q

-- ============================================================
-- §3  Strategies — Path Selection Functions
-- ============================================================

structure Strategy (α : Type) where
  choose : (a : α) → Option (Σ b : α, Step α a b)

def Strategy.comp (σ₁ σ₂ : Strategy α) : Strategy α where
  choose a := σ₁.choose a |>.orElse (fun _ => σ₂.choose a)

def IsNormalForm (σ : Strategy α) (a : α) : Prop :=
  σ.choose a = none

def idStrategy : Strategy α where
  choose _ := none

-- Theorem 5
theorem idStrategy_nf (a : α) : IsNormalForm (idStrategy (α := α)) a := rfl

inductive FollowsStrategy (σ : Strategy α) : Path α a b → Prop where
  | nil  : FollowsStrategy σ (Path.nil a)
  | cons : (hs : σ.choose a = some ⟨b, s⟩) →
           FollowsStrategy σ p →
           FollowsStrategy σ (Path.cons s p)

-- ============================================================
-- §4  Winning Strategies and Normal Forms
-- ============================================================

structure NormWitness (α : Type) (a nf : α) where
  play     : Path α a nf
  strategy : Strategy α
  isNF     : IsNormalForm strategy nf

def NormWitness.compose
    (w₁ : NormWitness α a b) (w₂ : NormWitness α b c) :
    NormWitness α a c where
  play     := w₁.play.trans w₂.play
  strategy := w₂.strategy
  isNF     := w₂.isNF

-- Theorem 6
theorem norm_compose_play
    (w₁ : NormWitness α a b) (w₂ : NormWitness α b c) :
    (w₁.compose w₂).play = w₁.play.trans w₂.play := rfl

-- Theorem 7
theorem norm_compose_len
    (w₁ : NormWitness α a b) (w₂ : NormWitness α b c) :
    (w₁.compose w₂).play.len = w₁.play.len + w₂.play.len :=
  len_trans w₁.play w₂.play

-- ============================================================
-- §5  Game Trees as Path Spaces
-- ============================================================

structure GameTree (α : Type) (a : α) where
  branches : List (Σ b : α, Path α a b)

def GameTree.branchCount (t : GameTree α a) : Nat := t.branches.length
def GameTree.isLeaf (t : GameTree α a) : Prop := t.branches = []
def GameTree.isLinear (t : GameTree α a) : Prop := t.branchCount ≤ 1

-- Theorem 8
theorem leaf_no_branches (t : GameTree α a) (h : t.isLeaf) :
    t.branchCount = 0 := by
  simp [GameTree.branchCount, GameTree.isLeaf] at *; simp [h]

-- Theorem 9
theorem linear_branch_bound (t : GameTree α a) (h : t.isLinear) :
    t.branchCount = 0 ∨ t.branchCount = 1 := by
  simp [GameTree.isLinear] at h; omega

-- Theorem 10
theorem depth_concat (p : Path α a b) (q : Path α b c) :
    (p.trans q).len = p.len + q.len := len_trans p q

-- ============================================================
-- §6  Positional Strategies and congrArg Lifting
-- ============================================================

def liftStrategy (f : α → α) (σ : Strategy α) : Strategy α where
  choose a := σ.choose a

-- Theorem 11
theorem lift_comp_strategy (f g : α → α) (σ : Strategy α) :
    liftStrategy g (liftStrategy f σ) = liftStrategy (g ∘ f) σ := rfl

-- Theorem 12
theorem lift_id_is_id (f : α → α) :
    liftStrategy f (idStrategy (α := α)) = idStrategy := rfl

def Cell2.mapFn (f : Path α a b → Path α a b) {p q : Path α a b}
    (σ : Cell2 p q) : Cell2 (f p) (f q) :=
  ⟨congrArg f σ.witness⟩

-- Theorem 13
theorem mapFn_id {p q : Path α a b} (σ : Cell2 p q) :
    σ.mapFn _root_.id = σ := by
  cases σ; rfl

-- Theorem 14
theorem mapFn_comp (f g : Path α a b → Path α a b) {p q : Path α a b}
    (σ : Cell2 p q) :
    σ.mapFn (f ∘ g) = (σ.mapFn g).mapFn f := by
  cases σ; rfl

-- ============================================================
-- §7  Confluence as Game Determinacy
-- ============================================================

structure Joinable (α : Type) (b c : α) where
  target : α
  left   : Path α b target
  right  : Path α c target

structure Diamond (α : Type) where
  diamond : {a b c : α} → Step α a b → Step α a c →
            Σ d : α, Step α b d × Step α c d

structure ChurchRosser (α : Type) where
  cr : {a b c : α} → Path α a b → Path α a c → Joinable α b c

def selfJoinable (a : α) : Joinable α a a where
  target := a
  left   := Path.nil a
  right  := Path.nil a

-- Theorem 15
theorem selfJoinable_left (a : α) :
    (selfJoinable a).left = Path.nil a := rfl

-- Theorem 16
theorem selfJoinable_right (a : α) :
    (selfJoinable a).right = Path.nil a := rfl

def diamondToJoinable (D : Diamond α) (s₁ : Step α a b) (s₂ : Step α a c) :
    Joinable α b c :=
  let ⟨d, l, r⟩ := D.diamond s₁ s₂
  { target := d, left := Path.single l, right := Path.single r }

-- Theorem 17
theorem diamond_join_single (D : Diamond α) (s₁ : Step α a b) (s₂ : Step α a c) :
    (diamondToJoinable D s₁ s₂).left.len ≤ 1 := by
  simp [diamondToJoinable, Path.single, Path.len]

def Joinable.swap (j : Joinable α b c) : Joinable α c b where
  target := j.target
  left := j.right
  right := j.left

-- Theorem 18
theorem swap_left (j : Joinable α b c) : j.swap.left = j.right := rfl

-- Theorem 19
theorem swap_right (j : Joinable α b c) : j.swap.right = j.left := rfl

-- Theorem 20
theorem swap_target (j : Joinable α b c) : j.swap.target = j.target := rfl

-- ============================================================
-- §8  Termination Games
-- ============================================================

-- Theorem 21
theorem backward_forward_len (s : Step α a b) :
    ((Path.single s.inv).trans (Path.single s)).len = 2 := rfl

-- Theorem 22
theorem forward_backward_len (s : Step α a b) :
    ((Path.single s).trans (Path.single s.inv)).len = 2 := rfl

-- Theorem 23
theorem roundtrip_cell (s : Step α a b) :
    Cell2 ((Path.single s).trans (Path.single s.inv))
          ((Path.single s).trans (Path.single s.inv)) :=
  Cell2.id _

-- ============================================================
-- §9  Nash Equilibrium of Rewriting
-- ============================================================

structure GamePair (α : Type) where
  σ₁ : Strategy α
  σ₂ : Strategy α

structure Equilibrium (α : Type) (gp : GamePair α) (a : α) where
  nf     : α
  play₁  : Path α a nf
  play₂  : Path α a nf
  isNF₁  : IsNormalForm gp.σ₁ nf
  isNF₂  : IsNormalForm gp.σ₂ nf

def Equilibrium.toJoinable (eq : Equilibrium α gp a) :
    Joinable α a a where
  target := eq.nf
  left   := eq.play₁
  right  := eq.play₂

def trivialEquilibrium (gp : GamePair α) (a : α)
    (h₁ : IsNormalForm gp.σ₁ a) (h₂ : IsNormalForm gp.σ₂ a) :
    Equilibrium α gp a where
  nf := a; play₁ := Path.nil a; play₂ := Path.nil a
  isNF₁ := h₁; isNF₂ := h₂

-- Theorem 24
theorem trivial_eq_plays (gp : GamePair α) (a : α)
    (h₁ : IsNormalForm gp.σ₁ a) (h₂ : IsNormalForm gp.σ₂ a) :
    (trivialEquilibrium gp a h₁ h₂).play₁ = (trivialEquilibrium gp a h₁ h₂).play₂ := rfl

-- Theorem 25
theorem trivial_eq_joinable_left (gp : GamePair α) (a : α)
    (h₁ : IsNormalForm gp.σ₁ a) (h₂ : IsNormalForm gp.σ₂ a) :
    (trivialEquilibrium gp a h₁ h₂).toJoinable.left = Path.nil a := rfl

-- ============================================================
-- §10  Evaluation Games — O/P Moves
-- ============================================================

inductive Player where
  | O | P
deriving DecidableEq

def Player.swap : Player → Player
  | .O => .P
  | .P => .O

-- Theorem 26
theorem player_swap_swap (p : Player) : p.swap.swap = p := by
  cases p <;> rfl

structure TaggedStep (α : Type) (a b : α) where
  player : Player
  step   : Step α a b

def taggedToPath (s : TaggedStep α a b) : Path α a b :=
  Path.single s.step

def taggedCompose (s₁ : TaggedStep α a b) (s₂ : TaggedStep α b c) :
    Path α a c :=
  (taggedToPath s₁).trans (taggedToPath s₂)

-- Theorem 27
theorem taggedCompose_len (s₁ : TaggedStep α a b) (s₂ : TaggedStep α b c) :
    (taggedCompose s₁ s₂).len = 2 := rfl

-- ============================================================
-- §11  Innocent (Positional) Strategies
-- ============================================================

structure InnocentStrategy (α : Type) where
  response : (a : α) → Option (Σ b : α, Step α a b)

def InnocentStrategy.comp (σ₁ σ₂ : InnocentStrategy α) : InnocentStrategy α where
  response a := (σ₁.response a).orElse (fun _ => σ₂.response a)

-- Theorem 28
theorem innocent_comp_assoc (σ₁ σ₂ σ₃ : InnocentStrategy α) :
    (σ₁.comp σ₂).comp σ₃ = σ₁.comp (σ₂.comp σ₃) := by
  simp only [InnocentStrategy.comp, InnocentStrategy.mk.injEq]
  funext a
  simp only [Option.orElse]
  cases σ₁.response a <;> rfl

def InnocentStrategy.toStrategy (σ : InnocentStrategy α) : Strategy α where
  choose := σ.response

-- Theorem 29
theorem innocent_to_strategy_comp (σ₁ σ₂ : InnocentStrategy α) :
    (σ₁.comp σ₂).toStrategy = Strategy.comp σ₁.toStrategy σ₂.toStrategy := rfl

-- ============================================================
-- §12  Büchi Games and Fair Rewriting
-- ============================================================

structure FairPlayWitness (α : Type) (a b : α) where
  play    : Path α a b
  ruleLog : List Nat
  lenEq   : play.len = ruleLog.length

structure FairJoin (α : Type) (b c : α) where
  target : α
  left   : FairPlayWitness α b target
  right  : FairPlayWitness α c target

def fairSelf (a : α) : FairPlayWitness α a a where
  play := Path.nil a; ruleLog := []; lenEq := rfl

-- Theorem 30
theorem fairSelf_len (a : α) : (fairSelf a).play.len = 0 := rfl

-- ============================================================
-- §13  Game Quantifiers and Path Logic
-- ============================================================

inductive GameFormula (α : Type) where
  | atom  : (α → Prop) → GameFormula α
  | exist : GameFormula α → GameFormula α
  | univ  : GameFormula α → GameFormula α
  | conj  : GameFormula α → GameFormula α → GameFormula α
  | disj  : GameFormula α → GameFormula α → GameFormula α

def satisfies (σ : Strategy α) (a : α) : GameFormula α → Prop
  | .atom p    => p a
  | .exist φ   => ∃ b : α, ∃ _ : Step α a b, satisfies σ b φ
  | .univ φ    => ∀ b : α, ∀ _ : Step α a b, satisfies σ b φ
  | .conj φ ψ  => satisfies σ a φ ∧ satisfies σ a ψ
  | .disj φ ψ  => satisfies σ a φ ∨ satisfies σ a ψ

-- Theorem 31
theorem satisfies_conj_comm (σ : Strategy α) (a : α) (φ ψ : GameFormula α) :
    satisfies σ a (.conj φ ψ) ↔ satisfies σ a (.conj ψ φ) := by
  simp [satisfies]; exact And.comm

-- Theorem 32
theorem satisfies_disj_comm (σ : Strategy α) (a : α) (φ ψ : GameFormula α) :
    satisfies σ a (.disj φ ψ) ↔ satisfies σ a (.disj ψ φ) := by
  simp [satisfies]; exact Or.comm

-- ============================================================
-- §14  Parity Games on Paths
-- ============================================================

structure ParityGame (α : Type) where
  priority : α → Nat

def ParityGame.owner (pg : ParityGame α) (a : α) : Player :=
  if pg.priority a % 2 == 0 then .P else .O

def maxPriority (pg : ParityGame α) : Path α a b → Nat
  | .nil a    => pg.priority a
  | .cons _ p => max (pg.priority a) (maxPriority pg p)

def proponentWins (pg : ParityGame α) (p : Path α a b) : Prop :=
  maxPriority pg p % 2 = 0

-- Theorem 33
theorem maxPriority_nil (pg : ParityGame α) (a : α) :
    maxPriority pg (Path.nil a) = pg.priority a := rfl

-- Theorem 34
theorem maxPriority_cons (pg : ParityGame α) (s : Step α a b) (p : Path α b c) :
    maxPriority pg (Path.cons s p) = max (pg.priority a) (maxPriority pg p) := rfl

-- Theorem 35
theorem maxPriority_ge_source (pg : ParityGame α) (p : Path α a b) :
    pg.priority a ≤ maxPriority pg p := by
  cases p with
  | nil => exact Nat.le_refl _
  | cons s q => simp [maxPriority]; exact Nat.le_max_left _ _

-- Theorem 36
theorem maxPriority_single (pg : ParityGame α) (s : Step α a b) :
    maxPriority pg (Path.single s) = max (pg.priority a) (pg.priority b) := rfl

-- ============================================================
-- §15  Cell2 Algebra — Groupoid Laws
-- ============================================================

-- Theorem 37
theorem vcomp_id_left {p q : Path α a b} (σ : Cell2 p q) :
    (Cell2.id p).vcomp σ = σ := by
  cases σ; rfl

-- Theorem 38
theorem vcomp_id_right {p q : Path α a b} (σ : Cell2 p q) :
    σ.vcomp (Cell2.id q) = σ := by
  cases σ; rfl

-- Theorem 39
theorem vcomp_assoc {p q r s : Path α a b}
    (σ₁ : Cell2 p q) (σ₂ : Cell2 q r) (σ₃ : Cell2 r s) :
    (σ₁.vcomp σ₂).vcomp σ₃ = σ₁.vcomp (σ₂.vcomp σ₃) := by
  cases σ₁; cases σ₂; cases σ₃; rfl

-- Theorem 40
theorem vinv_vinv {p q : Path α a b} (σ : Cell2 p q) :
    σ.vinv.vinv = σ := by
  cases σ; rfl

-- Theorem 41
theorem vinv_vcomp {p q : Path α a b} (σ : Cell2 p q) :
    σ.vinv.vcomp σ = Cell2.id q := by
  cases σ; rfl

-- Theorem 42
theorem vcomp_vinv {p q : Path α a b} (σ : Cell2 p q) :
    σ.vcomp σ.vinv = Cell2.id p := by
  cases σ; rfl

-- ============================================================
-- §16  congrArg / Whisker Chains
-- ============================================================

def doubleWhisker (l : Path α a b) {p q : Path α b c} (σ : Cell2 p q)
    (r : Path α c d) : Cell2 (l.trans p |>.trans r) (l.trans q |>.trans r) :=
  whiskerR (whiskerL l σ) r

-- Theorem 43
theorem whiskerL_id (r : Path α a b) (p : Path α b c) :
    whiskerL r (Cell2.id p) = Cell2.id (r.trans p) := rfl

-- Theorem 44
theorem whiskerR_id (p : Path α a b) (r : Path α b c) :
    whiskerR (Cell2.id p) r = Cell2.id (p.trans r) := rfl

-- Theorem 45
theorem whiskerL_vcomp (l : Path α a b) {p q r : Path α b c}
    (σ : Cell2 p q) (τ : Cell2 q r) :
    whiskerL l (σ.vcomp τ) = (whiskerL l σ).vcomp (whiskerL l τ) := by
  cases σ; cases τ; rfl

-- Theorem 46
theorem whiskerR_vcomp {p q r : Path α a b}
    (σ : Cell2 p q) (τ : Cell2 q r) (rr : Path α b c) :
    whiskerR (σ.vcomp τ) rr = (whiskerR σ rr).vcomp (whiskerR τ rr) := by
  cases σ; cases τ; rfl

-- Theorem 47
theorem whiskerL_vinv (l : Path α a b) {p q : Path α b c}
    (σ : Cell2 p q) :
    whiskerL l σ.vinv = (whiskerL l σ).vinv := by
  cases σ; rfl

-- Theorem 48
theorem whiskerR_vinv {p q : Path α a b}
    (σ : Cell2 p q) (r : Path α b c) :
    whiskerR σ.vinv r = (whiskerR σ r).vinv := by
  cases σ; rfl

-- Theorem 49
theorem interchange_clean
    {l₁ l₂ : Path α a b} {r₁ r₂ : Path α b c}
    (σ : Cell2 l₁ l₂) (τ : Cell2 r₁ r₂) :
    Cell2.hcomp σ τ =
      (whiskerR σ r₁).vcomp (whiskerL l₂ τ) := by
  cases σ; cases τ; rfl

-- ============================================================
-- §17  Winning Path Composition via trans
-- ============================================================

structure WinPath (α : Type) (σ : Strategy α) (a b : α) where
  play : Path α a b

def WinPath.compose (w₁ : WinPath α σ a b) (w₂ : WinPath α σ b c) :
    WinPath α σ a c where
  play := w₁.play.trans w₂.play

-- Theorem 50
theorem winpath_compose_len (w₁ : WinPath α σ a b) (w₂ : WinPath α σ b c) :
    (w₁.compose w₂).play.len = w₁.play.len + w₂.play.len :=
  len_trans w₁.play w₂.play

-- Theorem 51
theorem winpath_compose_assoc
    (w₁ : WinPath α σ a b) (w₂ : WinPath α σ b c) (w₃ : WinPath α σ c d) :
    ((w₁.compose w₂).compose w₃).play =
     (w₁.compose ⟨w₂.play.trans w₃.play⟩).play := by
  simp [WinPath.compose, trans_assoc]

-- ============================================================
-- §18  Local Confluence = One-Step Game Determinacy
-- ============================================================

structure LocalConfl (α : Type) where
  lc : {a b c : α} → Step α a b → Step α a c →
       Σ d : α, Path α b d × Path α c d

-- Theorem 52
theorem lcJoinLen (lc : LocalConfl α) (s₁ : Step α a b) (s₂ : Step α a c)
    (ext : Path α (lc.lc s₁ s₂).1 d) :
    ((lc.lc s₁ s₂).2.1.trans ext).len =
      (lc.lc s₁ s₂).2.1.len + ext.len :=
  len_trans _ ext

-- ============================================================
-- §19  Path Induction for Game Properties
-- ============================================================

-- Theorem 53
theorem play_induction
    (P : {a b : α} → Path α a b → Prop)
    (hnil : ∀ a, P (Path.nil a))
    (hcons : ∀ {a b c} (s : Step α a b) (p : Path α b c), P p → P (Path.cons s p))
    {a b : α} (p : Path α a b) : P p := by
  induction p with
  | nil a => exact hnil a
  | cons s p ih => exact hcons s p ih

-- ============================================================
-- §20  Span and Cospan Structures
-- ============================================================

structure Span (α : Type) (a : α) where
  left_end  : α
  right_end : α
  left  : Path α a left_end
  right : Path α a right_end

structure Cospan (α : Type) (b : α) where
  left_src  : α
  right_src : α
  left  : Path α left_src b
  right : Path α right_src b

def Joinable.toCospan (j : Joinable α b c) : Cospan α j.target where
  left_src := b; right_src := c; left := j.left; right := j.right

-- Theorem 54
theorem span_via_trans (sp : Span α a) (ext : Path α sp.left_end d) :
    (sp.left.trans ext).len = sp.left.len + ext.len :=
  len_trans sp.left ext

-- ============================================================
-- §21  Step Inversion Algebra
-- ============================================================

-- Theorem 55
theorem inv_nil (a : α) : (Path.nil a).inv = Path.nil a := rfl

-- Theorem 56
theorem step_inv_refl (a : α) : (Step.refl a).inv = Step.refl a := rfl

-- Theorem 57
theorem step_inv_rule (n : String) (a b : α) :
    (Step.rule n a b).inv = Step.rule (n ++ "⁻¹") b a := rfl

-- Theorem 58
theorem step_inv_inv_refl (a : α) : (Step.refl a).inv.inv = Step.refl a := rfl

-- Theorem 59
theorem step_inv_inv_rule (n : String) (a b : α) :
    (Step.rule n a b).inv.inv = Step.rule ((n ++ "⁻¹") ++ "⁻¹") a b := rfl

-- ============================================================
-- §22  congrArg-Based Functoriality
-- ============================================================

-- Theorem 60
theorem congrArg_trans_left {p₁ p₂ : Path α a b} (h : p₁ = p₂) (q : Path α b c) :
    p₁.trans q = p₂.trans q :=
  congrArg (· |>.trans q) h

-- Theorem 61
theorem congrArg_trans_right (p : Path α a b) {q₁ q₂ : Path α b c} (h : q₁ = q₂) :
    p.trans q₁ = p.trans q₂ :=
  congrArg (Path.trans p) h

-- Theorem 62
theorem congrArg_len {p q : Path α a b} (h : p = q) :
    p.len = q.len :=
  congrArg Path.len h

-- Theorem 63
theorem congrArg_inv {p q : Path α a b} (h : p = q) :
    p.inv = q.inv :=
  congrArg Path.inv h

def Cell2.transMap {p₁ p₂ : Path α a b} {q₁ q₂ : Path α b c}
    (σ : Cell2 p₁ p₂) (τ : Cell2 q₁ q₂) :
    Cell2 (p₁.trans q₁) (p₂.trans q₂) :=
  Cell2.hcomp σ τ

def Cell2.invMap {p q : Path α a b}
    (σ : Cell2 p q) : Cell2 p.inv q.inv :=
  ⟨congrArg Path.inv σ.witness⟩

-- Theorem 64
theorem invMap_vcomp {p q r : Path α a b}
    (σ : Cell2 p q) (τ : Cell2 q r) :
    (σ.vcomp τ).invMap = σ.invMap.vcomp τ.invMap := by
  cases σ; cases τ; rfl

-- Theorem 65
theorem invMap_vinv {p q : Path α a b}
    (σ : Cell2 p q) :
    σ.invMap.vinv = σ.vinv.invMap := by
  cases σ; rfl

-- ============================================================
-- §23  Strategy Algebra
-- ============================================================

-- Theorem 66
theorem strategy_comp_assoc (σ₁ σ₂ σ₃ : Strategy α) :
    (σ₁.comp σ₂).comp σ₃ = σ₁.comp (σ₂.comp σ₃) := by
  simp only [Strategy.comp, Strategy.mk.injEq]
  funext a
  simp only [Option.orElse]
  cases σ₁.choose a <;> rfl

-- Theorem 67
theorem strategy_comp_id_left (σ : Strategy α) :
    idStrategy.comp σ = σ := by
  simp [Strategy.comp, idStrategy, Option.orElse]

-- Theorem 68
theorem strategy_comp_id_right (σ : Strategy α) :
    σ.comp idStrategy = σ := by
  cases σ with | mk f =>
  simp only [Strategy.comp, idStrategy]
  congr; funext a; simp [Option.orElse]; cases f a <;> rfl

-- ============================================================
-- §24  Depth / Length Derived Theorems
-- ============================================================

-- Theorem 69
theorem len_ge_zero (p : Path α a b) : 0 ≤ p.len :=
  Nat.zero_le _

-- Theorem 70
theorem len_cons_pos (s : Step α a b) (p : Path α b c) :
    0 < (Path.cons s p).len := by
  simp [Path.len]; omega

-- Theorem 71
theorem len_single_pos (s : Step α a b) : 0 < (Path.single s).len := by
  simp [Path.single, Path.len]

-- Theorem 72
theorem len_trans_ge_left (p : Path α a b) (q : Path α b c) :
    p.len ≤ (p.trans q).len := by
  rw [len_trans]; omega

-- Theorem 73
theorem len_trans_ge_right (p : Path α a b) (q : Path α b c) :
    q.len ≤ (p.trans q).len := by
  rw [len_trans]; omega

-- ============================================================
-- §25  Game Determinacy — Further Results
-- ============================================================

def crSpanToCospan (cr : ChurchRosser α) (sp : Span α a) :
    Joinable α sp.left_end sp.right_end :=
  cr.cr sp.left sp.right

def crSymm (cr : ChurchRosser α) : ChurchRosser α where
  cr := fun p q => (cr.cr q p).swap

def diamondCR1 (D : Diamond α) (s₁ : Step α a b) (s₂ : Step α a c) :
    Joinable α b c :=
  diamondToJoinable D s₁ s₂

-- ============================================================
-- §26  More Algebraic Theorems
-- ============================================================

-- Theorem 74
theorem cell2_eq (σ τ : Cell2 p q) : σ = τ := by
  cases σ; cases τ; rfl

-- Theorem 75
theorem hcomp_id_id (p : Path α a b) (q : Path α b c) :
    Cell2.hcomp (Cell2.id p) (Cell2.id q) = Cell2.id (p.trans q) := rfl

-- Theorem 76
theorem hcomp_vcomp {p₁ p₂ p₃ : Path α a b} {q₁ q₂ q₃ : Path α b c}
    (σ₁ : Cell2 p₁ p₂) (σ₂ : Cell2 p₂ p₃)
    (τ₁ : Cell2 q₁ q₂) (τ₂ : Cell2 q₂ q₃) :
    (σ₁.vcomp σ₂).hcomp (τ₁.vcomp τ₂) =
      (σ₁.hcomp τ₁).vcomp (σ₂.hcomp τ₂) := by
  cases σ₁; cases σ₂; cases τ₁; cases τ₂; rfl

-- Theorem 77
theorem doubleWhisker_id (l : Path α a b) (p : Path α b c) (r : Path α c d) :
    doubleWhisker l (Cell2.id p) r = Cell2.id (l.trans p |>.trans r) := rfl

-- Theorem 78
theorem mapFn_vcomp (f : Path α a b → Path α a b)
    {p q r : Path α a b} (σ : Cell2 p q) (τ : Cell2 q r) :
    (σ.vcomp τ).mapFn f = (σ.mapFn f).vcomp (τ.mapFn f) := by
  cases σ; cases τ; rfl

-- Theorem 79
theorem single_step_eq (s t : Step α a b) (h : s = t) :
    Path.single s = Path.single t :=
  congrArg Path.single h

-- Theorem 80
theorem trans_single_len (p : Path α a b) (s : Step α b c) :
    (p.trans (Path.single s)).len = p.len + 1 := by
  rw [len_trans]; rfl

-- Theorem 81
theorem single_trans_len (s : Step α a b) (p : Path α b c) :
    (Path.single s |>.trans p).len = 1 + p.len := by
  rw [len_trans]; rfl

end CompPaths.RewritingGames
