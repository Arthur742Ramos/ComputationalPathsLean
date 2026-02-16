/-
  ComputationalPaths.Path.Rewriting.RewritingStrategyDeep

  Rewriting Strategies and Normalization via Computational Paths

  We develop a theory of abstract rewriting systems where strategies select
  which redex to reduce, producing computational Paths as witnesses.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Rewriting.StrategyDeep

open ComputationalPaths
open ComputationalPaths.Path

universe u v

-- ============================================================================
-- Section 1: Abstract Rewriting Systems
-- ============================================================================

/-- An abstract rewriting system over a type -/
structure ARS (α : Type u) where
  step : α → α → Prop

/-- A redex: source, target, and path witness -/
structure Redex (α : Type u) where
  source : α
  target : α
  path : Path source target

/-- A term is in normal form if no reduction applies -/
def IsNormalForm {α : Type u} (step : α → α → Prop) (a : α) : Prop :=
  ∀ b, ¬ step a b

/-- A term is strongly normalizing (well-founded) -/
def StronglyNormalizing {α : Type u} (step : α → α → Prop) (a : α) : Prop :=
  Acc (fun x y => step y x) a

-- ============================================================================
-- Section 2: Deterministic Strategy
-- ============================================================================

/-- A deterministic strategy: picks next step or declares normal form -/
structure DeterministicStrategy (α : Type u) where
  next : (a : α) → Option (Σ b : α, Path a b)

/-- Identity strategy: always returns normal form -/
def idStrategy (α : Type u) : DeterministicStrategy α where
  next _ := none

/-- Compose two strategies: try first, if NF try second -/
def composeStrategy {α : Type u} (s₁ s₂ : DeterministicStrategy α) :
    DeterministicStrategy α where
  next a := match s₁.next a with
    | some r => some r
    | none => s₂.next a

-- ============================================================================
-- Section 3: Strategy Application and Iteration
-- ============================================================================

/-- Apply a strategy n times, building a path -/
def applyN {α : Type u} (s : DeterministicStrategy α) :
    (a : α) → (n : Nat) → Σ b : α, Path a b
  | a, 0 => ⟨a, Path.refl a⟩
  | a, n + 1 =>
    match s.next a with
    | none => ⟨a, Path.refl a⟩
    | some ⟨b, p⟩ =>
      let ⟨c, q⟩ := applyN s b n
      ⟨c, Path.trans p q⟩

-- Theorem 1: Applying strategy 0 times gives refl
theorem applyN_zero {α : Type u} (s : DeterministicStrategy α) (a : α) :
    applyN s a 0 = ⟨a, Path.refl a⟩ := rfl

-- Theorem 2: If strategy says NF, one step stays put
theorem applyN_nf_one {α : Type u} (s : DeterministicStrategy α) (a : α)
    (h : s.next a = none) :
    applyN s a 1 = ⟨a, Path.refl a⟩ := by
  simp [applyN, h]

-- Theorem 3: Strategy produces valid equality
theorem strategy_valid_eq {α : Type u} (s : DeterministicStrategy α) (a : α) (n : Nat) :
    a = (applyN s a n).1 :=
  (applyN s a n).2.toEq

-- ============================================================================
-- Section 4: Normalization Witness
-- ============================================================================

/-- A path witnesses normalization if it ends at a normal form -/
structure NormalizationWitness (α : Type u) (isNF : α → Prop) (a : α) where
  nf : α
  path : Path a nf
  is_nf : isNF nf

-- Theorem 4: A normalization witness provides an equality
theorem normWitness_toEq {α : Type u} {isNF : α → Prop} {a : α}
    (w : NormalizationWitness α isNF a) : a = w.nf :=
  w.path.toEq

-- Theorem 5: Composing path with normalization witness
def normWitness_compose {α : Type u} {isNF : α → Prop} {a b : α}
    (p : Path a b) (w : NormalizationWitness α isNF b) :
    NormalizationWitness α isNF a :=
  ⟨w.nf, Path.trans p w.path, w.is_nf⟩

-- Theorem 6: Refl path gives trivial normalization for NFs
theorem normWitness_refl_toEq {α : Type u} {isNF : α → Prop} {a : α}
    (h : isNF a) : (NormalizationWitness.mk a (Path.refl a) h).path.toEq = rfl :=
  rfl

-- ============================================================================
-- Section 5: Path Coherence (UIP)
-- ============================================================================

-- Theorem 7: Any two paths between same endpoints have equal toEq
theorem path_toEq_unique {α : Type u} {a b : α}
    (p q : Path a b) : p.toEq = q.toEq :=
  Subsingleton.elim p.toEq q.toEq

-- Theorem 8: Trans of path and its symm gives rfl
theorem trans_symm_toEq {α : Type u} {a b : α} (p : Path a b) :
    (Path.trans p (Path.symm p)).toEq = rfl := by simp

-- Theorem 9: Trans of symm and path gives rfl
theorem symm_trans_toEq {α : Type u} {a b : α} (p : Path a b) :
    (Path.trans (Path.symm p) p).toEq = rfl := by simp

-- Theorem 10: Refl toEq is rfl
theorem refl_toEq {α : Type u} (a : α) :
    (Path.refl a).toEq = rfl := rfl

-- ============================================================================
-- Section 6: Strategy Equivalence
-- ============================================================================

/-- Two strategies are equivalent if they always reach the same target -/
def StrategyEquiv {α : Type u} (s₁ s₂ : DeterministicStrategy α) : Prop :=
  ∀ a : α, (applyN s₁ a 1).1 = (applyN s₂ a 1).1

-- Theorem 11: Strategy equivalence is reflexive
theorem strategyEquiv_refl {α : Type u} (s : DeterministicStrategy α) :
    StrategyEquiv s s :=
  fun _ => rfl

-- Theorem 12: Strategy equivalence is symmetric
theorem strategyEquiv_symm {α : Type u} {s₁ s₂ : DeterministicStrategy α}
    (h : StrategyEquiv s₁ s₂) : StrategyEquiv s₂ s₁ :=
  fun a => (h a).symm

-- Theorem 13: Strategy equivalence is transitive
theorem strategyEquiv_trans {α : Type u} {s₁ s₂ s₃ : DeterministicStrategy α}
    (h₁ : StrategyEquiv s₁ s₂) (h₂ : StrategyEquiv s₂ s₃) :
    StrategyEquiv s₁ s₃ :=
  fun a => (h₁ a).trans (h₂ a)

-- Theorem 14: Id strategy is self-equivalent
theorem idStrategy_self_equiv (α : Type u) :
    StrategyEquiv (idStrategy α) (idStrategy α) :=
  strategyEquiv_refl _

-- ============================================================================
-- Section 7: Strategy Composition Properties
-- ============================================================================

-- Theorem 15: Compose with id on left
theorem compose_id_left {α : Type u} (s : DeterministicStrategy α) :
    ∀ a, (composeStrategy (idStrategy α) s).next a = s.next a := by
  intro a; simp [composeStrategy, idStrategy]

-- Theorem 16: Compose with id on right, some case
theorem compose_id_right_some {α : Type u} (s : DeterministicStrategy α) (a : α)
    (r : Σ b : α, Path a b) (h : s.next a = some r) :
    (composeStrategy s (idStrategy α)).next a = some r := by
  simp [composeStrategy, h]

-- Theorem 17: Compose with id on right, none case
theorem compose_id_right_none {α : Type u} (s : DeterministicStrategy α) (a : α)
    (h : s.next a = none) :
    (composeStrategy s (idStrategy α)).next a = none := by
  simp [composeStrategy, h, idStrategy]

-- Theorem 18: Composition associativity when s₁ returns some
theorem compose_assoc_some {α : Type u}
    (s₁ s₂ s₃ : DeterministicStrategy α) (a : α)
    (r : Σ b : α, Path a b) (h₁ : s₁.next a = some r) :
    (composeStrategy (composeStrategy s₁ s₂) s₃).next a =
    (composeStrategy s₁ (composeStrategy s₂ s₃)).next a := by
  simp [composeStrategy, h₁]

-- Theorem 19: Composition associativity when s₁ none, s₂ some
theorem compose_assoc_none_some {α : Type u}
    (s₁ s₂ s₃ : DeterministicStrategy α) (a : α)
    (r : Σ b : α, Path a b) (h₁ : s₁.next a = none) (h₂ : s₂.next a = some r) :
    (composeStrategy (composeStrategy s₁ s₂) s₃).next a =
    (composeStrategy s₁ (composeStrategy s₂ s₃)).next a := by
  simp [composeStrategy, h₁, h₂]

-- Theorem 20: Composition associativity when s₁ none, s₂ none
theorem compose_assoc_none_none {α : Type u}
    (s₁ s₂ s₃ : DeterministicStrategy α) (a : α)
    (h₁ : s₁.next a = none) (h₂ : s₂.next a = none) :
    (composeStrategy (composeStrategy s₁ s₂) s₃).next a =
    (composeStrategy s₁ (composeStrategy s₂ s₃)).next a := by
  simp [composeStrategy, h₁, h₂]

-- ============================================================================
-- Section 8: Standardization
-- ============================================================================

/-- Standardization: rearranges a path while preserving the equality -/
structure Standardization (α : Type u) where
  standardize : {a b : α} → Path a b → Path a b

-- Theorem 21: Identity standardization
def idStandardization (α : Type u) : Standardization α where
  standardize p := p

-- Theorem 22: Standardization preserves toEq (by UIP, always true)
theorem standardize_preserves_toEq {α : Type u} (s : Standardization α) {a b : α}
    (p : Path a b) : (s.standardize p).toEq = p.toEq :=
  Subsingleton.elim _ _

-- Theorem 23: Composing standardizations
def composeStandardization {α : Type u} (s₁ s₂ : Standardization α) :
    Standardization α where
  standardize p := s₂.standardize (s₁.standardize p)

-- Theorem 24: Standardization of refl
theorem standardize_refl {α : Type u} (s : Standardization α) (a : α) :
    (s.standardize (Path.refl a)).toEq = rfl :=
  Subsingleton.elim _ _

-- Theorem 25: Standardization of trans
theorem standardize_trans_eq {α : Type u} (s : Standardization α) {a b c : α}
    (p : Path a b) (q : Path b c) :
    (s.standardize (Path.trans p q)).toEq = (Path.trans p q).toEq :=
  Subsingleton.elim _ _

-- ============================================================================
-- Section 9: Leftmost & Rightmost Strategies
-- ============================================================================

/-- Abstract leftmost strategy -/
structure LeftmostStrategy (α : Type u) extends DeterministicStrategy α where
  is_leftmost : ∀ a b, ∀ p : Path a b, next a = some ⟨b, p⟩ → True

/-- Abstract rightmost strategy -/
structure RightmostStrategy (α : Type u) extends DeterministicStrategy α where
  is_rightmost : ∀ a b, ∀ p : Path a b, next a = some ⟨b, p⟩ → True

-- Theorem 26: Leftmost and rightmost agree on NFs
theorem left_right_nf_agree {α : Type u}
    (ls : LeftmostStrategy α) (rs : RightmostStrategy α) (a : α)
    (hl : ls.next a = none) (hr : rs.next a = none) :
    applyN ls.toDeterministicStrategy a 1 = applyN rs.toDeterministicStrategy a 1 := by
  simp [applyN, hl, hr]

-- Theorem 27: Leftmost applied to NF stays put
theorem leftmost_nf_stable {α : Type u} (ls : LeftmostStrategy α) (a : α)
    (h : ls.next a = none) : (applyN ls.toDeterministicStrategy a 1).1 = a := by
  simp [applyN, h]

-- Theorem 28: Rightmost applied to NF stays put
theorem rightmost_nf_stable {α : Type u} (rs : RightmostStrategy α) (a : α)
    (h : rs.next a = none) : (applyN rs.toDeterministicStrategy a 1).1 = a := by
  simp [applyN, h]

-- ============================================================================
-- Section 10: Parallel Reduction
-- ============================================================================

/-- A parallel reduction step -/
structure ParallelStep (α : Type u) where
  source : α
  target : α
  path : Path source target
  numRedexes : Nat

-- Theorem 29: Parallel step with 0 redexes
theorem parallel_zero_refl {α : Type u} (a : α) :
    (ParallelStep.mk a a (Path.refl a) 0).path.toEq = rfl := rfl

-- Theorem 30: Composing parallel steps via trans
theorem parallel_compose_toEq {α : Type u} {a b c : α}
    (p : Path a b) (q : Path b c) :
    (Path.trans p q).toEq = p.toEq.trans q.toEq := by simp

-- ============================================================================
-- Section 11: Lazy Strategy and Sharing
-- ============================================================================

/-- Lazy strategy -/
structure LazyStrategy (α : Type u) extends DeterministicStrategy α where
  is_lazy : ∀ a, next a = none → True

/-- Sharing: two terms share structure via a path -/
structure Sharing (α : Type u) where
  original : α
  shared : α
  witness : Path original shared

-- Theorem 31: Sharing is reflexive
theorem sharing_refl {α : Type u} (a : α) :
    (Sharing.mk a a (Path.refl a)).witness.toEq = rfl := rfl

-- Theorem 32: Sharing composes via path trans
def sharing_trans {α : Type u} (s₁ s₂ : Sharing α)
    (h : s₁.shared = s₂.original) : Sharing α :=
  ⟨s₁.original, s₂.shared, Path.trans s₁.witness (h ▸ s₂.witness)⟩

-- ============================================================================
-- Section 12: Cofinal and Fair Strategies
-- ============================================================================

/-- A strategy is cofinal -/
def IsCofinal {α : Type u} (s : DeterministicStrategy α)
    (allRedexes : α → List (Redex α)) : Prop :=
  ∀ a, s.next a = none → allRedexes a = []

/-- A strategy is fair -/
def IsFair {α : Type u} (s : DeterministicStrategy α)
    (enabled : α → List (Redex α)) : Prop :=
  ∀ a, s.next a = none → enabled a = []

-- Theorem 33: Cofinal at NF
theorem cofinal_at_nf {α : Type u} (s : DeterministicStrategy α)
    (allRedexes : α → List (Redex α))
    (hcof : IsCofinal s allRedexes) (a : α) (hnf : s.next a = none) :
    allRedexes a = [] :=
  hcof a hnf

-- Theorem 34: Fair at NF
theorem fair_at_nf {α : Type u} (s : DeterministicStrategy α)
    (enabled : α → List (Redex α))
    (hfair : IsFair s enabled) (a : α) (hnf : s.next a = none) :
    enabled a = [] :=
  hfair a hnf

-- Theorem 35: Cofinal with equal sets implies fair
theorem cofinal_implies_fair {α : Type u} (s : DeterministicStrategy α)
    (allRedexes enabled : α → List (Redex α))
    (hcof : IsCofinal s allRedexes)
    (hsub : ∀ a, enabled a = allRedexes a) :
    IsFair s enabled := by
  intro a hnf; rw [hsub]; exact hcof a hnf

-- ============================================================================
-- Section 13: Strong Normalization
-- ============================================================================

-- Theorem 36: Normal forms are strongly normalizing
theorem nf_is_sn {α : Type u} {step : α → α → Prop} {a : α}
    (hnf : IsNormalForm step a) : StronglyNormalizing step a :=
  Acc.intro a (fun b hba => absurd hba (hnf b))

-- Theorem 37: SN is closed under equal terms
theorem sn_eq {α : Type u} {step : α → α → Prop} {a b : α}
    (h : a = b) (hsn : StronglyNormalizing step a) :
    StronglyNormalizing step b :=
  h ▸ hsn

-- Theorem 38: SN via path
theorem sn_via_path {α : Type u} {step : α → α → Prop} {a b : α}
    (p : Path a b) (hsn : StronglyNormalizing step a) :
    StronglyNormalizing step b :=
  sn_eq p.toEq hsn

-- ============================================================================
-- Section 14: CongrArg with Strategies
-- ============================================================================

-- Theorem 39: congrArg distributes over trans
theorem congrArg_trans_dist {α β : Type u} {a b c : α}
    (f : α → β) (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) := by simp

-- Theorem 40: congrArg distributes over symm
theorem congrArg_symm_dist {α β : Type u} {a b : α}
    (f : α → β) (p : Path a b) :
    Path.congrArg f (Path.symm p) =
    Path.symm (Path.congrArg f p) := by simp

-- Theorem 41: congrArg of refl is refl
theorem congrArg_refl_eq {α β : Type u} (f : α → β) (a : α) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp [Path.congrArg, Path.refl]

-- Theorem 42: congrArg composition
theorem congrArg_comp_eq {α β γ : Type u} {a b : α}
    (f : β → γ) (g : α → β) (p : Path a b) :
    Path.congrArg (fun x => f (g x)) p =
    Path.congrArg f (Path.congrArg g p) := by simp

-- Theorem 43: congrArg id is identity on paths
theorem congrArg_id_eq {α : Type u} {a b : α} (p : Path a b) :
    Path.congrArg (fun x : α => x) p = p := by simp

-- ============================================================================
-- Section 15: Reduction Depth
-- ============================================================================

/-- Reduction annotated with depth -/
structure DepthAnnotated (α : Type u) where
  source : α
  target : α
  path : Path source target
  depth : Nat

-- Theorem 44: Depth-annotated path gives valid equality
theorem depth_annotated_eq {α : Type u} (d : DepthAnnotated α) :
    d.source = d.target := d.path.toEq

-- ============================================================================
-- Section 16: Path Space
-- ============================================================================

/-- The space of paths between two points -/
structure PathSpace (α : Type u) (a b : α) where
  path : Path a b

-- Theorem 45: All paths in path space have same toEq
theorem pathSpace_toEq_unique {α : Type u} {a b : α}
    (p q : PathSpace α a b) : p.path.toEq = q.path.toEq :=
  Subsingleton.elim _ _

-- ============================================================================
-- Section 17: Developments
-- ============================================================================

/-- A development: reducing a set of marked redexes -/
structure Development (α : Type u) where
  source : α
  target : α
  path : Path source target
  complete : Bool

-- Theorem 46: Development gives equality
theorem dev_eq {α : Type u} (d : Development α) :
    d.source = d.target := d.path.toEq

-- Theorem 47: Identity development
theorem id_dev_refl {α : Type u} (a : α) :
    (Development.mk a a (Path.refl a) true).path.toEq = rfl := rfl

-- ============================================================================
-- Section 18: Groupoid Laws for Strategy Paths
-- ============================================================================

-- Theorem 48: Left identity
theorem strategy_left_id {α : Type u} {a b : α} (p : Path a b) :
    Path.trans (Path.refl a) p = p := by simp

-- Theorem 49: Right identity
theorem strategy_right_id {α : Type u} {a b : α} (p : Path a b) :
    Path.trans p (Path.refl b) = p := by simp

-- Theorem 50: Associativity
theorem strategy_assoc {α : Type u} {a b c d : α}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by simp

-- Theorem 51: Symm symm is identity
theorem strategy_symm_symm {α : Type u} {a b : α} (p : Path a b) :
    Path.symm (Path.symm p) = p := Path.symm_symm p

-- Theorem 52: Symm of trans
theorem strategy_symm_trans {α : Type u} {a b c : α}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) := by simp

-- Theorem 53: Symm of refl
theorem strategy_symm_refl {α : Type u} (a : α) :
    Path.symm (Path.refl a) = Path.refl a := by simp

-- ============================================================================
-- Section 19: Normalization Coherence
-- ============================================================================

-- Theorem 54: Two normalization witnesses toEq are equal by UIP
theorem norm_witnesses_toEq {α : Type u} {isNF : α → Prop} {a : α}
    (w₁ w₂ : NormalizationWitness α isNF a) (h : w₁.nf = w₂.nf) :
    w₁.path.toEq = h ▸ w₂.path.toEq :=
  Subsingleton.elim _ _

-- Theorem 55: Normalization witness from compose gives expected nf
theorem norm_compose_nf {α : Type u} {isNF : α → Prop} {a b : α}
    (p : Path a b) (w : NormalizationWitness α isNF b) :
    (normWitness_compose p w).nf = w.nf := rfl

-- ============================================================================
-- Section 20: Reduction Graph
-- ============================================================================

/-- A reduction graph -/
structure ReductionGraph (α : Type u) where
  vertices : List α
  edges : List (Redex α)

/-- Number of edges -/
def ReductionGraph.numEdges {α : Type u} (g : ReductionGraph α) : Nat :=
  g.edges.length

-- Theorem 56: Empty graph has no edges
theorem empty_graph_no_edges (α : Type u) :
    (ReductionGraph.mk (α := α) [] []).numEdges = 0 := rfl

-- ============================================================================
-- Section 21: Complete Strategy
-- ============================================================================

/-- A strategy is complete if it finds NF whenever one exists -/
def IsComplete {α : Type u} (s : DeterministicStrategy α) (isNF : α → Prop) : Prop :=
  ∀ a, (∃ b, isNF b ∧ ∃ (_ : Path a b), True) →
    ∃ n, isNF (applyN s a n).1

-- Theorem 57: A complete strategy on a NF returns immediately
theorem complete_on_nf {α : Type u} (s : DeterministicStrategy α)
    (isNF : α → Prop) (a : α) (hnf : isNF a) :
    isNF (applyN s a 0).1 := by
  simp [applyN]; exact hnf

-- ============================================================================
-- Section 22: Transport and Strategy
-- ============================================================================

-- Theorem 58: Transport along refl is identity
theorem strategy_transport_refl {α : Type u} {D : α → Sort v} {a : α} (x : D a) :
    Path.transport (Path.refl a) x = x := Path.transport_refl x

-- Theorem 59: Transport along trans is composition
theorem strategy_transport_trans {α : Type u} {D : α → Sort v} {a b c : α}
    (p : Path a b) (q : Path b c) (x : D a) :
    Path.transport (Path.trans p q) x = Path.transport q (Path.transport p x) :=
  Path.transport_trans p q x

-- Theorem 60: Transport along symm is inverse
theorem strategy_transport_symm {α : Type u} {D : α → Sort v} {a b : α}
    (p : Path a b) (x : D a) :
    Path.transport (Path.symm p) (Path.transport p x) = x :=
  Path.transport_symm_left p x

-- ============================================================================
-- Section 23: Whisker Operations
-- ============================================================================

-- Theorem 61: Whisker left with refl
theorem strategy_whiskerLeft_refl {α : Type u} {a b c : α}
    (p : Path a b) (q : Path b c) :
    Path.whiskerLeft (rfl : p = p) q = rfl := by simp

-- Theorem 62: Whisker right with refl
theorem strategy_whiskerRight_refl {α : Type u} {a b c : α}
    (p : Path a b) (q : Path b c) :
    Path.whiskerRight p (rfl : q = q) = rfl := by simp

-- ============================================================================
-- Section 24: Strategy-Specific Path Constructions
-- ============================================================================

/-- Build a redex from a path -/
def redexOfPath {α : Type u} {a b : α} (p : Path a b) : Redex α :=
  ⟨a, b, p⟩

-- Theorem 63: Redex of refl path
theorem redexOfPath_refl {α : Type u} (a : α) :
    (redexOfPath (Path.refl a)).source = (redexOfPath (Path.refl a)).target := rfl

-- Theorem 64: Redex path gives valid eq
theorem redexOfPath_eq {α : Type u} {a b : α} (p : Path a b) :
    (redexOfPath p).path.toEq = p.toEq := rfl

/-- A strategy step record -/
structure StrategyStep (α : Type u) where
  term : α
  result : α
  witness : Path term result
  strategyName : String

-- Theorem 65: Strategy step gives valid equality
theorem strategyStep_eq {α : Type u} (s : StrategyStep α) :
    s.term = s.result := s.witness.toEq

-- Theorem 66: Two strategy steps to same result have coherent witnesses
theorem strategyStep_coherent {α : Type u} {a b : α}
    (s₁ s₂ : StrategyStep α)
    (h₁ : s₁.term = a) (h₂ : s₁.result = b)
    (h₃ : s₂.term = a) (h₄ : s₂.result = b) :
    s₁.witness.toEq = h₁ ▸ h₂ ▸ h₃ ▸ h₄ ▸ s₂.witness.toEq :=
  Subsingleton.elim _ _

end ComputationalPaths.Rewriting.StrategyDeep
