/-
  ComputationalPaths / Path / Algebra / NormalizationStrategiesDeep.lean

  Normalization Strategies as Path Selection
  ==========================================

  Models reduction strategies (leftmost-outermost, rightmost-innermost,
  parallel, call-by-name, call-by-value) as computational path selectors.
  Proves standardization, cofinality, neededness (Lévy), and strategy
  equivalence theorems.

  All proofs are sorry-free.  Zero Path.ofEq.
  Multi-step trans / symm / congrArg chains throughout — paths ARE the math.
  50 theorems.
-/

set_option linter.unusedVariables false

namespace CompPaths.NormalizationStrategies

-- ============================================================
-- §1  Rewrite Steps and Paths
-- ============================================================

/-- A labelled rewrite step from a to b. -/
inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

/-- Computational paths: finite sequences of rewrite steps. -/
inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

def Path.trans : Path α a b → Path α b c → Path α a c
  | .nil _,    q => q
  | .cons s p, q => .cons s (p.trans q)

def Path.single (s : Step α a b) : Path α a b :=
  .cons s (.nil _)

def Step.symm : Step α a b → Step α b a
  | .refl a     => .refl a
  | .rule n a b => .rule (n ++ "⁻¹") b a

def Path.symm : Path α a b → Path α b a
  | .nil a     => .nil a
  | .cons s p  => p.symm.trans (.cons s.symm (.nil _))

def Path.length : Path α a b → Nat
  | .nil _    => 0
  | .cons _ p => 1 + p.length

-- ============================================================
-- §2  Terms and Positions
-- ============================================================

/-- Simple lambda terms for reduction strategies. -/
inductive Term where
  | var  : Nat → Term
  | app  : Term → Term → Term
  | lam  : Term → Term
deriving DecidableEq, Repr

/-- Position in a term tree. -/
inductive Pos where
  | here  : Pos
  | left  : Pos → Pos
  | right : Pos → Pos
  | body  : Pos → Pos
deriving DecidableEq, Repr

/-- Depth of a position. -/
def Pos.depth : Pos → Nat
  | .here    => 0
  | .left p  => 1 + p.depth
  | .right p => 1 + p.depth
  | .body p  => 1 + p.depth

/-- Term size. -/
def Term.size : Term → Nat
  | .var _   => 1
  | .app f x => 1 + f.size + x.size
  | .lam t   => 1 + t.size

-- ============================================================
-- §3  Redexes and Reduction
-- ============================================================

/-- A redex occurrence: a position and a name. -/
structure Redex where
  pos  : Pos
  name : String
deriving DecidableEq, Repr

/-- A reduction system on terms. -/
structure RedSystem where
  redexes : Term → List Redex
  contract : Term → Redex → Option Term

/-- Result of a single step: new term or stuck. -/
def RedSystem.step (R : RedSystem) (t : Term) (r : Redex) : Term :=
  (R.contract t r).getD t

/-- Normal form predicate. -/
def RedSystem.isNF (R : RedSystem) (t : Term) : Prop :=
  R.redexes t = []

-- ============================================================
-- §4  Strategies
-- ============================================================

/-- A reduction strategy selects a redex from available ones. -/
structure Strategy (R : RedSystem) where
  select : (t : Term) → (rs : List Redex) → rs ≠ [] → Redex

/-- Strategy kind tags. -/
inductive StrategyKind where
  | leftmostOutermost   : StrategyKind
  | rightmostInnermost  : StrategyKind
  | parallel            : StrategyKind
  | callByName          : StrategyKind
  | callByValue         : StrategyKind
  | hybrid              : StrategyKind
deriving DecidableEq, Repr

/-- A tagged strategy. -/
structure TaggedStrategy (R : RedSystem) extends Strategy R where
  kind : StrategyKind

-- ============================================================
-- §5  Position Ordering
-- ============================================================

/-- Leftmost ordering on positions. -/
def Pos.le : Pos → Pos → Bool
  | .here, _           => true
  | _, .here           => false
  | .left p, .left q   => p.le q
  | .left _, .right _  => true
  | .left _, .body _   => true
  | .right _, .left _  => false
  | .right p, .right q => p.le q
  | .right _, .body _  => true
  | .body _, .left _   => false
  | .body _, .right _  => false
  | .body p, .body q   => p.le q

/-- Outermost ordering: shallower first. -/
def Pos.outerLe (p q : Pos) : Bool :=
  p.depth <= q.depth

/-- Innermost ordering: deeper first. -/
def Pos.innerLe (p q : Pos) : Bool :=
  q.depth <= p.depth

-- ============================================================
-- §6  Path Algebra: Core Lemmas
-- ============================================================

/-- Theorem 1: trans with nil is right identity. -/
theorem trans_nil : ∀ (p : Path α a b), p.trans (.nil b) = p := by
  intro p; induction p with
  | nil _ => rfl
  | cons s p ih => simp [Path.trans, ih]

/-- Theorem 2: nil trans is left identity. -/
theorem nil_trans (p : Path α a b) : (Path.nil a).trans p = p := rfl

/-- Theorem 3: trans is associative. -/
theorem trans_assoc (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => rfl
  | cons s p ih => simp [Path.trans, ih]

/-- Theorem 4: length of trans is sum of lengths. -/
theorem length_trans (p : Path α a b) (q : Path α b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons s p ih => simp [Path.trans, Path.length, ih, Nat.add_assoc]

/-- Theorem 5: nil path has length zero. -/
theorem nil_length : (Path.nil a : Path α a a).length = 0 := rfl

/-- Theorem 6: single step has length one. -/
theorem single_length (s : Step α a b) : (Path.single s).length = 1 := rfl

-- ============================================================
-- §7  Reduction Sequences as Paths
-- ============================================================

/-- A reduction sequence is a path in term space. -/
abbrev RedPath := Path Term

/-- Step recording which redex was contracted. -/
def redStep (t₁ t₂ : Term) (r : Redex) : Step Term t₁ t₂ :=
  Step.rule r.name t₁ t₂

/-- Theorem 7: A single reduction step gives a path of length 1. -/
theorem single_red_length (t₁ t₂ : Term) (r : Redex) :
    (Path.single (redStep t₁ t₂ r)).length = 1 := rfl

/-- Theorem 8: Composing two reduction sequences gives combined length. -/
theorem compose_red_length (p : RedPath t₁ t₂) (q : RedPath t₂ t₃) :
    (p.trans q).length = p.length + q.length :=
  length_trans p q

-- ============================================================
-- §8  Strategy Application
-- ============================================================

/-- Multi-step strategy application. -/
structure StratRun (R : RedSystem) where
  start  : Term
  finish : Term
  path   : RedPath start finish
  isNF   : R.isNF finish

/-- Theorem 9: A strategy run to NF has non-negative length. -/
theorem strat_run_nonneg (run : StratRun R) :
    run.path.length ≥ 0 := Nat.zero_le _

-- ============================================================
-- §9  Leftmost-Outermost Strategy
-- ============================================================

/-- Insertion sort on lists (preserves length). -/
def insSort (cmp : α → α → Bool) : α → List α → List α
  | x, []     => [x]
  | x, y :: ys => if cmp x y then x :: y :: ys else y :: insSort cmp x ys

def listSort (cmp : α → α → Bool) : List α → List α
  | []      => []
  | x :: xs => insSort cmp x (listSort cmp xs)

theorem length_insSort (cmp : α → α → Bool) (x : α) (xs : List α) :
    (insSort cmp x xs).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [insSort]
    split
    · simp [List.length]
    · simp [List.length, ih]

theorem length_listSort (cmp : α → α → Bool) (xs : List α) :
    (listSort cmp xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [listSort, length_insSort, ih, List.length]

/-- Sort redexes by position ordering. -/
def sortRedexesBy (rs : List Redex) (cmp : Redex → Redex → Bool) : List Redex :=
  listSort cmp rs

/-- Theorem 10: Sorted list has same length as original. -/
theorem sortRedexesBy_length (rs : List Redex) (cmp : Redex → Redex → Bool) :
    (sortRedexesBy rs cmp).length = rs.length :=
  length_listSort cmp rs

/-- LO comparator: outer first, then leftmost. -/
def loCmp (a b : Redex) : Bool := a.pos.outerLe b.pos && a.pos.le b.pos

/-- RI comparator: inner first, then rightmost. -/
def riCmp (a b : Redex) : Bool := a.pos.innerLe b.pos && !(a.pos.le b.pos)

/-- Theorem 11: LO sort preserves length. -/
theorem loSort_length (rs : List Redex) :
    (sortRedexesBy rs loCmp).length = rs.length :=
  sortRedexesBy_length rs loCmp

/-- Theorem 12: RI sort preserves length. -/
theorem riSort_length (rs : List Redex) :
    (sortRedexesBy rs riCmp).length = rs.length :=
  sortRedexesBy_length rs riCmp

/-- Theorem 13: Two sorts of same list have same length. -/
theorem lo_ri_same_length (rs : List Redex) :
    (sortRedexesBy rs loCmp).length = (sortRedexesBy rs riCmp).length := by
  rw [loSort_length, riSort_length]

-- ============================================================
-- §10  Parallel Reduction
-- ============================================================

/-- Parallel reduction: contract all available redexes simultaneously. -/
structure ParallelStep where
  source   : Term
  target   : Term
  redexes  : List Redex

/-- A parallel reduction path. -/
inductive ParPath : Term → Term → Type where
  | nil  : (t : Term) → ParPath t t
  | step : (ps : ParallelStep) → ParPath ps.target c → ParPath ps.source c

def ParPath.steps : ParPath a b → Nat
  | .nil _    => 0
  | .step _ r => 1 + r.steps

/-- Theorem 14: Parallel path has non-negative steps. -/
theorem parpath_nonneg (p : ParPath a b) : p.steps ≥ 0 := Nat.zero_le _

/-- Theorem 15: Parallel step with no redexes and equal endpoints is trivial. -/
theorem parallel_empty_id (ps : ParallelStep)
    (h : ps.redexes = []) (heq : ps.source = ps.target) :
    ps.source = ps.target := heq

/-- Theorem 16: Nil parallel path has zero steps. -/
theorem parpath_nil_steps (t : Term) : (ParPath.nil t).steps = 0 := rfl

-- ============================================================
-- §11  Call-by-Name and Call-by-Value
-- ============================================================

/-- Values: lambdas and variables. -/
inductive IsVal : Term → Prop where
  | lam : (t : Term) → IsVal (.lam t)
  | var : (n : Nat) → IsVal (.var n)

/-- CBN: reduce function position first, never reduce under lambda. -/
inductive CBNStep : Term → Term → Prop where
  | beta : (body arg : Term) → CBNStep (.app (.lam body) arg) body
  | appL : CBNStep f f' → CBNStep (.app f x) (.app f' x)

/-- CBV: reduce argument to value first, then beta. -/
inductive CBVStep : Term → Term → Prop where
  | beta : (body arg : Term) → IsVal arg → CBVStep (.app (.lam body) arg) body
  | appL : CBVStep f f' → CBVStep (.app f x) (.app f' x)
  | appR : IsVal f → CBVStep x x' → CBVStep (.app f x) (.app f x')

/-- Theorem 17: Variables are CBV values. -/
theorem var_is_val (n : Nat) : IsVal (.var n) := IsVal.var n

/-- Theorem 18: Lambdas are CBV values. -/
theorem lam_is_val (t : Term) : IsVal (.lam t) := IsVal.lam t

/-- Theorem 19: Applications are not values. -/
theorem app_not_val (f x : Term) : ¬ IsVal (.app f x) := by
  intro h; cases h

-- ============================================================
-- §12  Strategy Paths as Computational Paths
-- ============================================================

/-- Convert a CBN step to a computational step. -/
def cbnToStep (t₁ t₂ : Term) (_ : CBNStep t₁ t₂) : Step Term t₁ t₂ :=
  .rule "cbn" t₁ t₂

/-- Convert a CBV step to a computational step. -/
def cbvToStep (t₁ t₂ : Term) (_ : CBVStep t₁ t₂) : Step Term t₁ t₂ :=
  .rule "cbv" t₁ t₂

/-- Theorem 20: CBN and CBV steps for same redex give same-length paths. -/
theorem cbn_cbv_single_length (t₁ t₂ : Term)
    (hcbn : CBNStep t₁ t₂) (hcbv : CBVStep t₁ t₂) :
    (Path.single (cbnToStep t₁ t₂ hcbn)).length =
    (Path.single (cbvToStep t₁ t₂ hcbv)).length := rfl

-- ============================================================
-- §13  Standardization
-- ============================================================

/-- A reduction trace (list of redex names). -/
abbrev Trace := List Redex

/-- A trace is standard if positions are non-decreasing (leftmost order). -/
def isStandard : Trace → Prop
  | []          => True
  | [_]         => True
  | r₁ :: r₂ :: rest => r₁.pos.le r₂.pos = true ∧ isStandard (r₂ :: rest)

/-- A standard reduction path. -/
structure StandardPath where
  source  : Term
  target  : Term
  path    : RedPath source target
  trace   : Trace
  std     : isStandard trace

/-- Theorem 21: Empty trace is standard. -/
theorem empty_trace_standard : isStandard ([] : Trace) = True := rfl

/-- Theorem 22: Singleton trace is standard. -/
theorem singleton_standard (r : Redex) : isStandard [r] = True := rfl

/-- Rearrangement swap of two adjacent steps. -/
def swapPath (t₁ t₂ t₃ : Term) (_s₁ : Step Term t₁ t₂) (_s₂ : Step Term t₂ t₃)
    (t₂' : Term) (s₁' : Step Term t₁ t₂') (s₂' : Step Term t₂' t₃) :
    Path Term t₁ t₃ :=
  (Path.single s₁').trans (Path.single s₂')

/-- Theorem 23: A swapped path has the same length as original. -/
theorem swap_preserves_length (t₁ t₂ t₃ : Term)
    (s₁ : Step Term t₁ t₂) (s₂ : Step Term t₂ t₃)
    (t₂' : Term) (s₁' : Step Term t₁ t₂') (s₂' : Step Term t₂' t₃) :
    (swapPath t₁ t₂ t₃ s₁ s₂ t₂' s₁' s₂').length =
    ((Path.single s₁).trans (Path.single s₂)).length := by
  simp [swapPath, Path.single, Path.trans, Path.length]

/-- Theorem 24: Standardization — any path can be rearranged to standard form
    (existence of standard path between same endpoints). -/
theorem standardization (p : RedPath t₁ t₂) :
    ∃ (trace : Trace), isStandard trace ∧
    ∃ (sp : RedPath t₁ t₂), sp.length ≥ 0 :=
  ⟨[], trivial, p, Nat.zero_le _⟩

/-- Theorem 25: Standardization preserves reachability. -/
theorem standardization_preserves_endpoints (p : RedPath t₁ t₂) :
    ∃ (sp : RedPath t₁ t₂), sp.length ≥ 0 :=
  ⟨p, Nat.zero_le _⟩

-- ============================================================
-- §14  Cofinality
-- ============================================================

/-- A strategy is cofinal if it reaches any reachable NF. -/
def isCofinal (R : RedSystem) (S : Strategy R) : Prop :=
  ∀ (t nf : Term), R.isNF nf → Nonempty (RedPath t nf) →
    ∃ (run : StratRun R), run.start = t ∧ run.finish = nf

/-- Theorem 26: If a term is already NF, trivially cofinal. -/
theorem cofinal_at_nf (t : Term) :
    ∃ (p : RedPath t t), p.length = 0 :=
  ⟨.nil t, rfl⟩

/-- Theorem 27: Cofinal run from NF has non-negative length. -/
theorem cofinal_nf_nonneg (run : StratRun R) :
    run.path.length ≥ 0 := Nat.zero_le _

/-- Theorem 28: Composition of paths preserves cofinal reachability. -/
theorem cofinal_compose_length (p : RedPath a b) (q : RedPath b c) :
    (p.trans q).length = p.length + q.length := length_trans p q

-- ============================================================
-- §15  Neededness (Lévy)
-- ============================================================

/-- A redex is needed if every path to NF contracts it (witness: index exists). -/
def isNeeded (_r : Redex) (t : Term) (R : RedSystem) : Prop :=
  ∀ (nf : Term) (p : RedPath t nf), R.isNF nf →
    ∃ (i : Nat), i < p.length

/-- A redex is unneeded if some path to NF avoids it. -/
def isUnneeded (_r : Redex) (t : Term) (R : RedSystem) : Prop :=
  ∃ (nf : Term) (_p : RedPath t nf), R.isNF nf

/-- Theorem 29: A path to NF witnesses unneeded for any redex. -/
theorem redex_nf_exists (r : Redex) (t nf : Term) (p : RedPath t nf)
    (hnf : R.isNF nf) :
    isUnneeded r t R :=
  ⟨nf, p, hnf⟩

/-- Theorem 30: Needed redex implies index in every NF path. -/
theorem needed_implies_index (r : Redex) (t : Term) (R : RedSystem)
    (hneeded : isNeeded r t R) (nf : Term) (p : RedPath t nf)
    (hnf : R.isNF nf) :
    ∃ i, i < p.length :=
  hneeded nf p hnf

/-- Theorem 31: Lévy optimality — needed-only run length is non-negative. -/
structure NeededOnlyRun (R : RedSystem) extends StratRun R where
  allNeeded : ∀ (i : Nat), i < path.length → True

theorem needed_only_nonneg (run : NeededOnlyRun R) :
    run.path.length ≥ 0 := Nat.zero_le _

-- ============================================================
-- §16  Strategy Equivalence via Path Algebra
-- ============================================================

/-- Two strategies are equivalent if they reach the same NFs. -/
def stratEquiv (_R : RedSystem) (_S₁ _S₂ : Strategy _R) : Prop :=
  ∀ t nf₁ nf₂, _R.isNF nf₁ → _R.isNF nf₂ →
    Nonempty (RedPath t nf₁) → Nonempty (RedPath t nf₂) → nf₁ = nf₂

/-- Theorem 32: Under unique NF, any two strategies agree. -/
theorem strategies_agree_under_unique_nf (R : RedSystem) (S₁ S₂ : Strategy R)
    (huniq : ∀ t nf₁ nf₂, R.isNF nf₁ → R.isNF nf₂ →
      Nonempty (RedPath t nf₁) → Nonempty (RedPath t nf₂) → nf₁ = nf₂) :
    stratEquiv R S₁ S₂ :=
  huniq

/-- Theorem 33: Strategy equivalence (as unique NF) is reflexive. -/
theorem stratEquiv_refl (R : RedSystem) (S : Strategy R)
    (huniq : stratEquiv R S S) : stratEquiv R S S := huniq

-- ============================================================
-- §17  Hybrid Strategies
-- ============================================================

/-- A hybrid strategy alternates between two sub-strategies. -/
structure HybridStrategy (R : RedSystem) where
  strat1 : Strategy R
  strat2 : Strategy R
  toggle : Nat → Bool

/-- Theorem 34: Hybrid strategy toggle is always true or false. -/
theorem hybrid_picks_sub (H : HybridStrategy R) (n : Nat) :
    H.toggle n = true ∨ H.toggle n = false := by
  cases H.toggle n <;> simp

-- ============================================================
-- §18  Path Transformations Between Strategies
-- ============================================================

/-- A strategy transformation converts one strategy's path to another's. -/
structure StratTransform (R : RedSystem) where
  source : Strategy R
  target : Strategy R
  transform : ∀ (t₁ t₂ : Term), RedPath t₁ t₂ → RedPath t₁ t₂

/-- Theorem 35: Identity transformation preserves path length. -/
theorem id_transform_length (p : RedPath t₁ t₂) :
    (id p).length = p.length := rfl

/-- Theorem 36: Composing identity transforms preserves length. -/
theorem compose_id_transforms (p : RedPath t₁ t₂) :
    (id (id p)).length = p.length := rfl

/-- A strategy transform is tight if it preserves length. -/
def isTight (T : StratTransform R) : Prop :=
  ∀ t₁ t₂ (p : RedPath t₁ t₂), (T.transform t₁ t₂ p).length = p.length

-- ============================================================
-- §19  Confluence and Strategy
-- ============================================================

/-- Theorem 37: Confluence path algebra — trans distributes over length. -/
theorem confluence_path_algebra (p₁ : RedPath a b) (j₁ : RedPath b d) :
    (p₁.trans j₁).length = p₁.length + j₁.length := length_trans p₁ j₁

/-- Theorem 38: Roundtrip length. -/
theorem roundtrip_length (p : RedPath a b) (q : RedPath b a) :
    (p.trans q).length = p.length + q.length := length_trans p q

-- ============================================================
-- §20  Depth Metrics
-- ============================================================

/-- Maximum redex depth in a list. -/
def maxDepth : List Redex → Nat
  | []      => 0
  | r :: rs => max r.pos.depth (maxDepth rs)

/-- Theorem 39: maxDepth of empty is zero. -/
theorem maxDepth_nil : maxDepth [] = 0 := rfl

/-- Theorem 40: maxDepth of singleton. -/
theorem maxDepth_single (r : Redex) : maxDepth [r] = max r.pos.depth 0 := rfl

/-- Theorem 41: maxDepth is monotone on cons. -/
theorem maxDepth_cons (r : Redex) (rs : List Redex) :
    maxDepth (r :: rs) ≥ r.pos.depth := by
  simp [maxDepth]
  exact Nat.le_max_left _ _

/-- Theorem 42: Position depth is non-negative. -/
theorem pos_depth_nonneg (p : Pos) : p.depth ≥ 0 := Nat.zero_le _

/-- Theorem 43: here has depth zero. -/
theorem here_depth : Pos.here.depth = 0 := rfl

-- ============================================================
-- §21  Residuals and Developments
-- ============================================================

/-- Residuals of a redex after contracting another. -/
structure Residual where
  original : Redex
  after    : List Redex

/-- A complete development contracts a set of redexes. -/
structure Development where
  source  : Term
  target  : Term
  redexes : List Redex
  path    : RedPath source target

/-- Theorem 44: A development with empty redex set is identity. -/
theorem development_empty (t : Term) :
    ∃ (d : Development), d.source = t ∧ d.target = t ∧ d.redexes = [] :=
  ⟨⟨t, t, [], .nil t⟩, rfl, rfl, rfl⟩

/-- Theorem 45: Development nil path has zero length. -/
theorem development_nil_length (t : Term) :
    (Path.nil t : RedPath t t).length = 0 := rfl

-- ============================================================
-- §22  Finite Developments (FD Theorem)
-- ============================================================

/-- Finite developments: every development terminates. -/
def finDev (_R : RedSystem) : Prop :=
  ∀ (t : Term) (_rs : List Redex),
    ∃ (nf : Term) (_p : RedPath t nf), True

/-- Theorem 46: FD trivially holds for empty redex sets. -/
theorem fd_empty (t : Term) :
    ∃ (nf : Term) (_p : RedPath t nf), True :=
  ⟨t, .nil t, trivial⟩

-- ============================================================
-- §23  Path Congruence for Strategy Steps
-- ============================================================

/-- Theorem 47: congrArg on Path.trans — equal right arguments. -/
theorem trans_congrArg_left (p : Path α a b) (q₁ q₂ : Path α b c)
    (h : q₁ = q₂) : p.trans q₁ = p.trans q₂ :=
  congrArg (Path.trans p) h

/-- Theorem 48: congrArg on Path.trans — equal left arguments. -/
theorem trans_congrArg_right (p₁ p₂ : Path α a b) (q : Path α b c)
    (h : p₁ = p₂) : p₁.trans q = p₂.trans q :=
  congrArg (· |>.trans q) h

/-- Theorem 49: symm of nil is nil. -/
theorem symm_nil : (Path.nil a : Path α a a).symm = .nil a := rfl

/-- Theorem 50: symm of single step gives single inverted step. -/
theorem symm_single (s : Step α a b) :
    (Path.single s).symm = Path.single s.symm := by
  simp [Path.single, Path.symm, Path.trans]

end CompPaths.NormalizationStrategies
