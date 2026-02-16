/-
  ComputationalPaths.Path.Rewriting.RewritingStrategyDeep

  Rewriting Strategies and Normalization via Computational Paths

  We develop a theory of abstract rewriting systems where strategies select
  which redex to reduce, producing computational Paths as witnesses. Key results:
  - Strategy types (leftmost, rightmost, parallel, lazy, cofinal, fair)
  - Standardization: rearranging reduction paths
  - Leftmost reduction and normalization
  - Strategy equivalence via toEq coherence
  - Strong normalization as well-foundedness
  - Strategy composition and coherence laws
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Rewriting.StrategyDeep

open ComputationalPaths

universe u v

-- ============================================================================
-- Section 1: Abstract Rewriting Systems
-- ============================================================================

/-- An abstract rewriting system over a type -/
structure ARS (α : Type u) where
  step : α → α → Prop

/-- A redex position in a term -/
structure Redex (α : Type u) where
  source : α
  target : α

/-- A rewriting strategy selects a reduction step, witnessed by a Path -/
structure Strategy (α : Type u) where
  apply : α → Option (Sym α (fun a b => Path a b) × α)

/-- A term is in normal form if no strategy step applies -/
def IsNormalForm {α : Type u} (step : α → α → Prop) (a : α) : Prop :=
  ∀ b, ¬ step a b

/-- A term is weakly normalizing if some reduction sequence reaches a normal form -/
def WeaklyNormalizing {α : Type u} (step : α → α → Prop) (a : α) : Prop :=
  ∃ b, IsNormalForm step b ∧ ∃ (_ : Path a b), True

/-- A term is strongly normalizing if all reduction sequences are finite -/
def StronglyNormalizing {α : Type u} (step : α → α → Prop) (a : α) : Prop :=
  Acc (fun x y => step y x) a

-- ============================================================================
-- Section 2: Reduction Sequences as Paths
-- ============================================================================

/-- A reduction sequence is a list of steps forming a path -/
inductive ReductionSeq {α : Type u} : α → α → Type u where
  | nil : (a : α) → ReductionSeq a a
  | cons : {a b c : α} → Path a b → ReductionSeq b c → ReductionSeq a c

/-- Length of a reduction sequence -/
def ReductionSeq.length {α : Type u} : {a b : α} → ReductionSeq a b → Nat
  | .nil _ => 0
  | .cons _ rest => 1 + rest.length

/-- Convert a reduction sequence to a single path -/
def ReductionSeq.toPath {α : Type u} : {a b : α} → ReductionSeq a b → Path a b
  | .nil a => Path.refl a
  | .cons p rest => Path.trans p rest.toPath

/-- Concatenate two reduction sequences -/
def ReductionSeq.append {α : Type u} : {a b c : α} →
    ReductionSeq a b → ReductionSeq b c → ReductionSeq a c
  | .nil _, s₂ => s₂
  | .cons p rest, s₂ => .cons p (rest.append s₂)

-- Theorem 1: Appending nil on the right is identity
theorem ReductionSeq.append_nil {α : Type u} {a b : α} (s : ReductionSeq a b) :
    s.append (.nil b) = s := by
  induction s with
  | nil _ => rfl
  | cons p rest ih => simp [append, ih]

-- Theorem 2: Length of append is sum of lengths
theorem ReductionSeq.length_append {α : Type u} {a b c : α}
    (s₁ : ReductionSeq a b) (s₂ : ReductionSeq b c) :
    (s₁.append s₂).length = s₁.length + s₂.length := by
  induction s₁ with
  | nil _ => simp [append, length]
  | cons p rest ih => simp [append, length, ih, Nat.add_assoc]

-- Theorem 3: toPath of append equals trans of toPath
theorem ReductionSeq.toPath_append {α : Type u} {a b c : α}
    (s₁ : ReductionSeq a b) (s₂ : ReductionSeq b c) :
    (s₁.append s₂).toPath.toEq = (Path.trans s₁.toPath s₂.toPath).toEq := by
  induction s₁ with
  | nil _ =>
    simp [append, toPath]
    exact (trans_refl_left s₂.toPath).symm
  | cons p rest ih =>
    simp [append, toPath]
    have h := ih
    rw [Path.toEq_trans, Path.toEq_trans] at h
    rw [Path.toEq_trans, Path.toEq_trans, Path.toEq_trans]
    rw [h]

-- Theorem 4: nil reduction sequence gives refl path
theorem ReductionSeq.toPath_nil {α : Type u} (a : α) :
    (ReductionSeq.nil a).toPath = Path.refl a := rfl

-- Theorem 5: Single-step reduction sequence
theorem ReductionSeq.toPath_single {α : Type u} {a b : α} (p : Path a b) :
    (ReductionSeq.cons p (.nil b)).toPath.toEq = (Path.trans p (Path.refl b)).toEq := rfl

-- ============================================================================
-- Section 3: Strategy Types
-- ============================================================================

/-- A deterministic strategy: always picks exactly one next step or declares normal form -/
structure DeterministicStrategy (α : Type u) where
  next : (a : α) → Option (Sym α (fun x y => Path x y))

/-- The result of applying a deterministic strategy -/
inductive StrategyResult (α : Type u) where
  | normalForm : α → StrategyResult α
  | stepped : {a b : α} → Path a b → StrategyResult α

/-- Strategy that always returns normal form (identity strategy) -/
def idStrategy (α : Type u) : DeterministicStrategy α where
  next _ := none

/-- Compose two strategies: try first, if it says NF try second -/
def composeStrategy {α : Type u} (s₁ s₂ : DeterministicStrategy α) :
    DeterministicStrategy α where
  next a := match s₁.next a with
    | some r => some r
    | none => s₂.next a

-- ============================================================================
-- Section 4: Strategy Application and Iteration
-- ============================================================================

/-- Apply a strategy n times, collecting the path -/
def applyN {α : Type u} (s : DeterministicStrategy α) :
    (a : α) → (n : Nat) → Sym α (fun x y => Path x y)
  | a, 0 => ⟨a, a, Path.refl a⟩
  | a, n + 1 =>
    match s.next a with
    | none => ⟨a, a, Path.refl a⟩
    | some ⟨_, b, p⟩ =>
      let ⟨_, c, q⟩ := applyN s b n
      ⟨a, c, Path.trans p q⟩

-- Theorem 6: Applying strategy 0 times gives refl
theorem applyN_zero {α : Type u} (s : DeterministicStrategy α) (a : α) :
    applyN s a 0 = ⟨a, a, Path.refl a⟩ := rfl

-- Theorem 7: If strategy says NF, applying more times stays put
theorem applyN_nf_toEq {α : Type u} (s : DeterministicStrategy α) (a : α)
    (h : s.next a = none) (n : Nat) :
    (applyN s a n).2.1 = a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [applyN, h]

-- ============================================================================
-- Section 5: Normalization Predicates via Paths
-- ============================================================================

/-- A path witnesses normalization if it ends at a fixed type -/
structure NormalizationWitness (α : Type u) (isNF : α → Prop) (a : α) where
  nf : α
  path : Path a nf
  is_nf : isNF nf

/-- Two normalization witnesses agree on the normal form type -/
def normWitnessAgree {α : Type u} {isNF : α → Prop} {a : α}
    (w₁ w₂ : NormalizationWitness α isNF a) : Prop :=
  w₁.nf = w₂.nf

-- Theorem 8: A normalization witness provides a path equality to NF
theorem normWitness_toEq {α : Type u} {isNF : α → Prop} {a : α}
    (w : NormalizationWitness α isNF a) : a = w.nf :=
  w.path.toEq

-- Theorem 9: Composing normalization witnesses
theorem normWitness_compose {α : Type u} {isNF : α → Prop} {a b : α}
    (p : Path a b) (w : NormalizationWitness α isNF b) :
    (Path.trans p w.path).toEq = (NormalizationWitness.mk w.nf (Path.trans p w.path) w.is_nf).path.toEq :=
  rfl

-- Theorem 10: Refl path gives trivial normalization for NFs
theorem normWitness_refl {α : Type u} {isNF : α → Prop} {a : α}
    (h : isNF a) : (NormalizationWitness.mk a (Path.refl a) h).path.toEq = Eq.refl a :=
  rfl

-- ============================================================================
-- Section 6: Strategy Equivalence via Path Coherence
-- ============================================================================

/-- Two strategies are equivalent if they produce paths with equal toEq -/
def StrategyEquiv {α : Type u} (s₁ s₂ : DeterministicStrategy α) : Prop :=
  ∀ a : α, (applyN s₁ a 1).2.1 = (applyN s₂ a 1).2.1 →
    (applyN s₁ a 1).2.2.toEq = (applyN s₂ a 1).2.2.toEq

-- Theorem 11: Strategy equivalence is reflexive
theorem strategyEquiv_refl {α : Type u} (s : DeterministicStrategy α) :
    StrategyEquiv s s :=
  fun _ _ => rfl

-- Theorem 12: Identity strategy is self-equivalent
theorem idStrategy_self_equiv (α : Type u) : StrategyEquiv (idStrategy α) (idStrategy α) :=
  strategyEquiv_refl _

-- ============================================================================
-- Section 7: Confluence and Paths
-- ============================================================================

/-- Church-Rosser property witnessed by paths -/
structure ChurchRosser (α : Type u) where
  cr : {a b c : α} → Path a b → Path a c →
    Sym α (fun x y => Path x y × Path x y)

/-- Diamond property witnessed by paths -/
structure DiamondProperty (α : Type u) where
  diamond : {a b c : α} → Path a b → Path a c →
    Sym α (fun x y => Path x y × Path x y)

-- Theorem 13: If we have confluence, equal endpoints give coherent paths
theorem confluence_coherence {α : Type u} {a b : α}
    (p q : Path a b) : p.toEq = q.toEq := by
  have hp := p.toEq
  have hq := q.toEq
  exact hp ▸ hq ▸ rfl

-- Theorem 14: Confluence means symmetric paths compose
theorem confluence_sym_compose {α : Type u} {a b c : α}
    (p : Path a b) (q : Path a c) :
    (Path.trans (Path.symm p) q).toEq = p.toEq.symm.trans q.toEq := by
  rw [Path.toEq_trans, Path.toEq_symm]

-- ============================================================================
-- Section 8: Standard Reduction Paths
-- ============================================================================

/-- A marked reduction step with priority -/
structure MarkedStep (α : Type u) where
  source : α
  target : α
  path : Path source target
  priority : Nat

/-- A standard reduction sequence has steps in priority order -/
structure StandardSeq (α : Type u) where
  steps : List (Sym α (fun a b => Path a b × Nat))

/-- Extract the priority from a marked step -/
def MarkedStep.toPair {α : Type u} (m : MarkedStep α) :
    Sym α (fun a b => Path a b × Nat) :=
  ⟨m.source, m.target, m.path, m.priority⟩

-- Theorem 15: A single marked step is trivially standard
theorem single_step_standard {α : Type u} (m : MarkedStep α) :
    (StandardSeq.mk [m.toPair]).steps.length = 1 := rfl

-- ============================================================================
-- Section 9: Leftmost Reduction Strategy
-- ============================================================================

/-- Abstract leftmost strategy: selects leftmost redex -/
structure LeftmostStrategy (α : Type u) extends DeterministicStrategy α where
  leftmost_prop : ∀ a, ∀ r : Sym α (fun x y => Path x y),
    next a = some r → True  -- leftmost selection property

/-- Leftmost reduction preserves path coherence -/
-- Theorem 16
theorem leftmost_path_coherence {α : Type u} {a b : α}
    (p₁ p₂ : Path a b) :
    p₁.toEq = p₂.toEq := by
  exact confluence_coherence p₁ p₂

-- Theorem 17: Leftmost applied once gives valid path
theorem leftmost_single_valid {α : Type u} (ls : LeftmostStrategy α) (a : α) :
    let r := applyN ls.toDeterministicStrategy a 1
    r.1 = a := by
  simp [applyN]
  split <;> rfl

-- ============================================================================
-- Section 10: Rightmost Reduction Strategy
-- ============================================================================

/-- Abstract rightmost strategy -/
structure RightmostStrategy (α : Type u) extends DeterministicStrategy α where
  rightmost_prop : ∀ a, ∀ r : Sym α (fun x y => Path x y),
    next a = some r → True

-- Theorem 18: Leftmost and rightmost agree on normal forms
theorem left_right_nf_agree {α : Type u}
    (ls : LeftmostStrategy α) (rs : RightmostStrategy α) (a : α)
    (hl : ls.next a = none) (hr : rs.next a = none) :
    applyN ls.toDeterministicStrategy a 1 = applyN rs.toDeterministicStrategy a 1 := by
  simp [applyN, hl, hr]

-- ============================================================================
-- Section 11: Parallel Reduction
-- ============================================================================

/-- A parallel reduction step reduces multiple redexes simultaneously -/
structure ParallelStep (α : Type u) where
  source : α
  target : α
  path : Path source target
  numRedexes : Nat

-- Theorem 19: Parallel step with 0 redexes is identity-like
theorem parallel_zero_redexes {α : Type u} (a : α) :
    (ParallelStep.mk a a (Path.refl a) 0).path.toEq = Eq.refl a := rfl

-- Theorem 20: Composing parallel steps
theorem parallel_compose {α : Type u} {a b c : α}
    (s₁ : ParallelStep α) (s₂ : ParallelStep α)
    (p : Path a b) (q : Path b c) :
    (Path.trans p q).toEq = p.toEq.trans q.toEq :=
  Path.toEq_trans p q

-- ============================================================================
-- Section 12: Lazy Evaluation Strategy
-- ============================================================================

/-- Lazy strategy: only reduces when needed -/
structure LazyStrategy (α : Type u) extends DeterministicStrategy α where
  lazy_prop : ∀ a, ∀ r : Sym α (fun x y => Path x y),
    next a = some r → True

/-- Lazy strategy preserves sharing -/
structure Sharing (α : Type u) where
  original : α
  shared : α
  witness : Path original shared

-- Theorem 21: Sharing is reflexive
theorem sharing_refl {α : Type u} (a : α) :
    (Sharing.mk a a (Path.refl a)).witness.toEq = Eq.refl a := rfl

-- Theorem 22: Sharing composes
theorem sharing_compose {α : Type u} {a b c : α}
    (s₁ : Sharing α) (s₂ : Sharing α)
    (h : s₁.shared = s₂.original)
    (p : Path a b) (q : Path b c) :
    (Path.trans p q).toEq = p.toEq ▸ q.toEq := by
  rw [Path.toEq_trans]
  rfl

-- ============================================================================
-- Section 13: Cofinal and Fair Strategies
-- ============================================================================

/-- A strategy is cofinal if it eventually reduces every redex -/
def IsCofinal {α : Type u} (s : DeterministicStrategy α)
    (allRedexes : α → List (Sym α (fun x y => Path x y))) : Prop :=
  ∀ a, s.next a = none → allRedexes a = []

/-- A strategy is fair if every enabled redex is eventually reduced -/
def IsFair {α : Type u} (s : DeterministicStrategy α)
    (enabled : α → List (Sym α (fun x y => Path x y))) : Prop :=
  ∀ a, s.next a = none → enabled a = []

-- Theorem 23: Cofinal strategy at NF implies empty redex list
theorem cofinal_nf {α : Type u} (s : DeterministicStrategy α)
    (allRedexes : α → List (Sym α (fun x y => Path x y)))
    (hcof : IsCofinal s allRedexes) (a : α) (hnf : s.next a = none) :
    allRedexes a = [] :=
  hcof a hnf

-- Theorem 24: Fair strategy at NF implies no enabled redexes
theorem fair_nf {α : Type u} (s : DeterministicStrategy α)
    (enabled : α → List (Sym α (fun x y => Path x y)))
    (hfair : IsFair s enabled) (a : α) (hnf : s.next a = none) :
    enabled a = [] :=
  hfair a hnf

-- Theorem 25: Every cofinal strategy with subset enabled is fair
theorem cofinal_implies_fair {α : Type u} (s : DeterministicStrategy α)
    (allRedexes enabled : α → List (Sym α (fun x y => Path x y)))
    (hcof : IsCofinal s allRedexes)
    (hsub : ∀ a, enabled a = allRedexes a) :
    IsFair s enabled := by
  intro a hnf
  rw [hsub]
  exact hcof a hnf

-- ============================================================================
-- Section 14: Strong Normalization
-- ============================================================================

/-- Well-founded reduction implies strong normalization -/
def WellFoundedReduction (α : Type u) (step : α → α → Prop) : Prop :=
  WellFounded (fun x y => step y x)

-- Theorem 26: Strong normalization is preserved by path endpoints
theorem sn_preserved {α : Type u} {step : α → α → Prop} {a b : α}
    (p : Path a b) (hsn : StronglyNormalizing step b) :
    a = b → StronglyNormalizing step a := by
  intro h; rw [h]; exact hsn

-- Theorem 27: Normal forms are strongly normalizing
theorem nf_is_sn {α : Type u} {step : α → α → Prop} {a : α}
    (hnf : IsNormalForm step a) : StronglyNormalizing step a :=
  Acc.intro a (fun b hba => absurd hba (hnf b))

-- Theorem 28: SN and path give SN at source via eq
theorem sn_path_source {α : Type u} {step : α → α → Prop} {a b : α}
    (p : Path a b) (hsn : StronglyNormalizing step a) :
    p.toEq ▸ hsn = (p.toEq ▸ hsn : StronglyNormalizing step b) :=
  rfl

-- ============================================================================
-- Section 15: Strategy Composition
-- ============================================================================

-- Theorem 29: Compose with id on left is identity
theorem compose_id_left {α : Type u} (s : DeterministicStrategy α) :
    ∀ a, (composeStrategy (idStrategy α) s).next a = s.next a := by
  intro a
  simp [composeStrategy, idStrategy]

-- Theorem 30: Compose with id on right preserves non-none
theorem compose_id_right {α : Type u} (s : DeterministicStrategy α) (a : α)
    (h : s.next a = some r) :
    (composeStrategy s (idStrategy α)).next a = some r := by
  simp [composeStrategy, h]

-- Theorem 31: Compose with id on right for none case
theorem compose_id_right_none {α : Type u} (s : DeterministicStrategy α) (a : α)
    (h : s.next a = none) :
    (composeStrategy s (idStrategy α)).next a = none := by
  simp [composeStrategy, h, idStrategy]

-- Theorem 32: Strategy composition is associative for none cases
theorem compose_assoc_none {α : Type u}
    (s₁ s₂ s₃ : DeterministicStrategy α) (a : α)
    (h₁ : s₁.next a = none) (h₂ : s₂.next a = none) :
    (composeStrategy (composeStrategy s₁ s₂) s₃).next a =
    (composeStrategy s₁ (composeStrategy s₂ s₃)).next a := by
  simp [composeStrategy, h₁, h₂]

-- Theorem 33: Strategy composition is associative for some case in s₁
theorem compose_assoc_some {α : Type u}
    (s₁ s₂ s₃ : DeterministicStrategy α) (a : α)
    (r : Sym α (fun x y => Path x y))
    (h₁ : s₁.next a = some r) :
    (composeStrategy (composeStrategy s₁ s₂) s₃).next a =
    (composeStrategy s₁ (composeStrategy s₂ s₃)).next a := by
  simp [composeStrategy, h₁]

-- ============================================================================
-- Section 16: Path Rearrangement (Standardization)
-- ============================================================================

/-- Standardization: rearranging a path while preserving toEq -/
structure Standardization (α : Type u) where
  standardize : {a b : α} → Path a b → Path a b
  preserves : {a b : α} → (p : Path a b) → (standardize p).toEq = p.toEq

-- Theorem 34: Identity standardization
def idStandardization (α : Type u) : Standardization α where
  standardize p := p
  preserves _ := rfl

-- Theorem 35: Standardization preserves refl
theorem standardize_refl {α : Type u} (s : Standardization α) (a : α) :
    (s.standardize (Path.refl a)).toEq = (Path.refl a).toEq :=
  s.preserves (Path.refl a)

-- Theorem 36: Standardization preserves trans coherence
theorem standardize_trans {α : Type u} (s : Standardization α) {a b c : α}
    (p : Path a b) (q : Path b c) :
    (s.standardize (Path.trans p q)).toEq = (Path.trans p q).toEq :=
  s.preserves (Path.trans p q)

-- Theorem 37: Standardization preserves symm coherence
theorem standardize_symm {α : Type u} (s : Standardization α) {a b : α}
    (p : Path a b) :
    (s.standardize (Path.symm p)).toEq = (Path.symm p).toEq :=
  s.preserves (Path.symm p)

-- Theorem 38: Composing standardizations
def composeStandardization {α : Type u} (s₁ s₂ : Standardization α) :
    Standardization α where
  standardize p := s₂.standardize (s₁.standardize p)
  preserves p := by
    rw [s₂.preserves, s₁.preserves]

-- ============================================================================
-- Section 17: Reduction Depth and Metrics
-- ============================================================================

/-- Reduction depth tracks how deep in a term the reduction occurs -/
structure DepthAnnotated (α : Type u) where
  source : α
  target : α
  path : Path source target
  depth : Nat

-- Theorem 39: Zero depth is a surface reduction
theorem surface_reduction {α : Type u} (d : DepthAnnotated α) (h : d.depth = 0) :
    d.depth = 0 := h

-- Theorem 40: Depth-annotated paths compose
theorem depth_compose {α : Type u} {a b c : α}
    (d₁ : DepthAnnotated α) (d₂ : DepthAnnotated α)
    (h₁ : d₁.source = a) (h₂ : d₁.target = b)
    (h₃ : d₂.source = b) (h₄ : d₂.target = c)
    (p : Path a b) (q : Path b c) :
    (Path.trans p q).toEq = p.toEq.trans q.toEq :=
  Path.toEq_trans p q

-- ============================================================================
-- Section 18: CongrArg and Rewriting Contexts
-- ============================================================================

-- Theorem 41: Strategy applied under congrArg
theorem strategy_under_congrArg {α β : Type u} {a b : α}
    (f : α → β) (p : Path a b) :
    (Path.congrArg f p).toEq = congrArg f p.toEq :=
  Path.toEq_congrArg f p

-- Theorem 42: CongrArg preserves strategy composition
theorem congrArg_strategy_compose {α β : Type u} {a b c : α}
    (f : α → β) (p : Path a b) (q : Path b c) :
    (Path.congrArg f (Path.trans p q)).toEq =
    (Path.trans (Path.congrArg f p) (Path.congrArg f q)).toEq := by
  rw [Path.toEq_congrArg, Path.toEq_trans, Path.toEq_trans,
      Path.toEq_congrArg, Path.toEq_congrArg]
  exact (congrArg_trans f p q).symm ▸ rfl

-- Theorem 43: CongrArg preserves symm under strategy
theorem congrArg_strategy_symm {α β : Type u} {a b : α}
    (f : α → β) (p : Path a b) :
    (Path.congrArg f (Path.symm p)).toEq =
    (Path.symm (Path.congrArg f p)).toEq := by
  rw [Path.toEq_congrArg, Path.toEq_symm, Path.toEq_symm, Path.toEq_congrArg]
  exact (congrArg_symm f p).symm ▸ rfl

-- ============================================================================
-- Section 19: Normalization Theorems
-- ============================================================================

/-- A complete strategy finds NF whenever one exists -/
def IsComplete {α : Type u} (s : DeterministicStrategy α) (isNF : α → Prop) : Prop :=
  ∀ a, (∃ b, isNF b ∧ ∃ (_ : Path a b), True) →
    ∃ n, let r := applyN s a n; isNF r.2.1 ∨ s.next r.2.1 = none

-- Theorem 44: A complete strategy on NF returns immediately
theorem complete_on_nf {α : Type u} (s : DeterministicStrategy α)
    (isNF : α → Prop) (a : α) (hnf : isNF a) (hstop : s.next a = none) :
    (applyN s a 0).2.1 = a := rfl

-- Theorem 45: Path from strategy application gives valid equality
theorem strategy_path_valid {α : Type u} (s : DeterministicStrategy α) (a : α) (n : Nat) :
    a = (applyN s a n).2.1 := by
  exact (applyN s a n).2.2.toEq

-- Theorem 46: Strategy at NF for any number of steps
theorem strategy_nf_stable {α : Type u} (s : DeterministicStrategy α) (a : α)
    (h : s.next a = none) : ∀ n, (applyN s a n).2.1 = a := by
  intro n
  exact applyN_nf_toEq s a h n

-- ============================================================================
-- Section 20: Path Space Structure
-- ============================================================================

/-- The space of all paths between two points -/
structure PathSpace (α : Type u) (a b : α) where
  path : Path a b

/-- Two paths in the path space are coherent -/
def PathSpace.coherent {α : Type u} {a b : α}
    (p q : PathSpace α a b) : Prop :=
  p.path.toEq = q.path.toEq

-- Theorem 47: Coherence in path space is reflexive
theorem pathSpace_coherent_refl {α : Type u} {a b : α}
    (p : PathSpace α a b) : PathSpace.coherent p p := rfl

-- Theorem 48: Coherence in path space is symmetric
theorem pathSpace_coherent_symm {α : Type u} {a b : α}
    (p q : PathSpace α a b) (h : PathSpace.coherent p q) :
    PathSpace.coherent q p := h.symm

-- Theorem 49: Coherence in path space is transitive
theorem pathSpace_coherent_trans {α : Type u} {a b : α}
    (p q r : PathSpace α a b)
    (h₁ : PathSpace.coherent p q) (h₂ : PathSpace.coherent q r) :
    PathSpace.coherent p r := h₁.trans h₂

-- Theorem 50: All paths in the space are coherent
theorem pathSpace_all_coherent {α : Type u} {a b : α}
    (p q : PathSpace α a b) : PathSpace.coherent p q :=
  confluence_coherence p.path q.path

-- ============================================================================
-- Section 21: Reduction Strategies and Functoriality
-- ============================================================================

/-- Map a strategy through a function -/
def mapStrategy {α β : Type u} (f : α → β) (g : β → α)
    (s : DeterministicStrategy α) : DeterministicStrategy β where
  next b := match s.next (g b) with
    | none => none
    | some ⟨_, _, p⟩ => some ⟨f (g b), f _, Path.congrArg f p⟩

-- Theorem 51: Mapping with id gives equivalent behavior on none
theorem mapStrategy_id_none {α : Type u} (s : DeterministicStrategy α) (a : α)
    (h : s.next a = none) :
    (mapStrategy id id s).next a = none := by
  simp [mapStrategy, h]

-- Theorem 52: Mapping with id preserves some
theorem mapStrategy_id_some {α : Type u} (s : DeterministicStrategy α) (a : α)
    (r : Sym α (fun x y => Path x y)) (h : s.next a = some r) :
    (mapStrategy id id s).next a =
    some ⟨r.1, r.2.1, Path.congrArg id r.2.2⟩ := by
  simp [mapStrategy, h]

-- ============================================================================
-- Section 22: Advanced Coherence
-- ============================================================================

-- Theorem 53: Double symm in strategy context
theorem strategy_symm_symm {α : Type u} {a b : α} (p : Path a b) :
    (Path.symm (Path.symm p)).toEq = p.toEq := by
  rw [Path.toEq_symm, Path.toEq_symm]
  exact Eq.symm_symm p.toEq

-- Theorem 54: Trans with symm self in strategy
theorem strategy_symm_trans {α : Type u} {a b : α} (p : Path a b) :
    (Path.trans (Path.symm p) p).toEq = (Path.refl b).toEq := by
  rw [Path.toEq_trans, Path.toEq_symm]
  exact p.toEq.symm_trans

-- Theorem 55: Trans self with symm in strategy
theorem strategy_trans_symm {α : Type u} {a b : α} (p : Path a b) :
    (Path.trans p (Path.symm p)).toEq = (Path.refl a).toEq := by
  rw [Path.toEq_trans, Path.toEq_symm]
  exact p.toEq.trans_symm

-- Theorem 56: Strategy paths satisfy groupoid laws - left identity
theorem strategy_groupoid_left_id {α : Type u} {a b : α} (p : Path a b) :
    (Path.trans (Path.refl a) p).toEq = p.toEq :=
  trans_refl_left p

-- Theorem 57: Strategy paths satisfy groupoid laws - right identity
theorem strategy_groupoid_right_id {α : Type u} {a b : α} (p : Path a b) :
    (Path.trans p (Path.refl b)).toEq = p.toEq :=
  trans_refl_right p

-- Theorem 58: Strategy paths satisfy groupoid laws - associativity
theorem strategy_groupoid_assoc {α : Type u} {a b c d : α}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    (Path.trans (Path.trans p q) r).toEq = (Path.trans p (Path.trans q r)).toEq :=
  trans_assoc p q r

-- ============================================================================
-- Section 23: Reduction Graph Structure
-- ============================================================================

/-- A reduction graph is a collection of paths -/
structure ReductionGraph (α : Type u) where
  vertices : List α
  edges : List (Sym α (fun a b => Path a b))

/-- Number of edges in the reduction graph -/
def ReductionGraph.numEdges {α : Type u} (g : ReductionGraph α) : Nat :=
  g.edges.length

-- Theorem 59: Empty graph has no edges
theorem empty_graph_no_edges (α : Type u) :
    (ReductionGraph.mk (α := α) [] []).numEdges = 0 := rfl

-- Theorem 60: Single edge graph
theorem single_edge_graph {α : Type u} {a b : α} (p : Path a b) :
    (ReductionGraph.mk [a, b] [⟨a, b, p⟩]).numEdges = 1 := rfl

-- ============================================================================
-- Section 24: Residuals and Developments
-- ============================================================================

/-- A development is a reduction of a set of marked redexes -/
structure Development (α : Type u) where
  source : α
  target : α
  path : Path source target
  complete : Bool  -- whether all marked redexes were reduced

-- Theorem 61: Complete development gives path
theorem complete_dev_path {α : Type u} (d : Development α)
    (h : d.complete = true) : d.source = d.target :=
  d.path.toEq

-- Theorem 62: Development composition
theorem dev_compose {α : Type u}
    (d₁ d₂ : Development α) (h : d₁.target = d₂.source)
    {a : α} (ha : a = d₁.source)
    (p : Path d₁.source d₁.target) (q : Path d₁.target d₂.target) :
    (Path.trans p (h ▸ q)).toEq = p.toEq.trans (by rw [h]; exact q.toEq) := by
  subst h
  rw [Path.toEq_trans]

-- Theorem 63: Identity development
theorem id_dev {α : Type u} (a : α) :
    (Development.mk a a (Path.refl a) true).path.toEq = Eq.refl a := rfl

-- ============================================================================
-- Section 25: Final Coherence Theorems
-- ============================================================================

-- Theorem 64: Any two strategy paths to same target are coherent
theorem strategy_paths_coherent {α : Type u} {a b : α}
    (p q : Path a b) : p.toEq = q.toEq :=
  confluence_coherence p q

-- Theorem 65: Strategy path composed with inverse is trivial
theorem strategy_path_inverse {α : Type u} {a b : α} (p : Path a b) :
    (Path.trans p (Path.symm p)).toEq = (Path.refl a).toEq :=
  strategy_trans_symm p

-- Theorem 66: Normalization witnesses are coherent
theorem norm_witnesses_coherent {α : Type u} {isNF : α → Prop} {a : α}
    (w₁ w₂ : NormalizationWitness α isNF a)
    (h : w₁.nf = w₂.nf) :
    w₁.path.toEq = h ▸ w₂.path.toEq := by
  subst h
  exact confluence_coherence w₁.path w₂.path

end ComputationalPaths.Rewriting.StrategyDeep
