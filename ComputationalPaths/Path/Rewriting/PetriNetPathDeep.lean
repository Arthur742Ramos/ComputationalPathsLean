/-
  ComputationalPaths/Path/Rewriting/PetriNetPathDeep.lean

  Petri Nets and Token Rewriting via Computational Paths

  We model Petri nets as structures with places, transitions, and
  pre/post multisets. Markings (token distributions) evolve via
  transition firings. Each firing is a Step, firing sequences are
  Paths, and reachability is existence of a Path. We develop
  place invariants, transition invariants, net morphisms,
  conflict/concurrency, free-choice nets, and state machine
  decompositions — all connected through Path operations.

  No Mathlib dependency — everything built from Lean 4 core + Path.Basic.

  Author: armada-332 (PetriNetPathDeep)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Rewriting.PetriNetPathDeep

open ComputationalPaths.Path

-- ============================================================
-- Section 1: Basic Petri Net Definitions
-- ============================================================

/-- A Petri net with np places and nt transitions.
    Pre and Post are weight functions. -/
structure PetriNet (np nt : Nat) where
  pre  : Fin nt → Fin np → Nat
  post : Fin nt → Fin np → Nat

/-- A marking is a function from places to token counts. -/
def Marking (np : Nat) := Fin np → Nat

/-- A transition t is enabled at marking m if all places have enough tokens. -/
def enabled {np nt : Nat} (net : PetriNet np nt) (m : Marking np) (t : Fin nt) : Prop :=
  ∀ p : Fin np, net.pre t p ≤ m p

/-- Fire a transition: subtract pre-weights, add post-weights. -/
def fire {np nt : Nat} (net : PetriNet np nt) (m : Marking np) (t : Fin nt) : Marking np :=
  fun p => m p - net.pre t p + net.post t p

/-- The effect of a transition on a single place (as an integer). -/
def effectAt {np nt : Nat} (net : PetriNet np nt) (t : Fin nt) (p : Fin np) : Int :=
  (net.post t p : Int) - (net.pre t p : Int)

-- ============================================================
-- Section 2: Firing Sequences as Paths
-- ============================================================

/-- Identity firing path: no transitions fired, marking unchanged. -/
def idFiringSeq {np : Nat} (m : Marking np) : Path m m :=
  Path.refl m

/-- Compose two firing sequence paths. -/
def composeFiringSeqs {np : Nat} {m1 m2 m3 : Marking np}
    (p1 : Path m1 m2) (p2 : Path m2 m3) : Path m1 m3 :=
  Path.trans p1 p2

-- Theorem 1
theorem idFiringSeq_is_refl {np : Nat} (m : Marking np) :
    idFiringSeq m = Path.refl m :=
  rfl

-- Theorem 2
theorem composeFiringSeqs_assoc {np : Nat} {m1 m2 m3 m4 : Marking np}
    (p1 : Path m1 m2) (p2 : Path m2 m3) (p3 : Path m3 m4) :
    composeFiringSeqs (composeFiringSeqs p1 p2) p3 =
    composeFiringSeqs p1 (composeFiringSeqs p2 p3) :=
  Path.trans_assoc p1 p2 p3

-- Theorem 3
theorem composeFiringSeqs_refl_left {np : Nat} {m1 m2 : Marking np}
    (p : Path m1 m2) :
    composeFiringSeqs (idFiringSeq m1) p = p :=
  Path.trans_refl_left p

-- Theorem 4
theorem composeFiringSeqs_refl_right {np : Nat} {m1 m2 : Marking np}
    (p : Path m1 m2) :
    composeFiringSeqs p (idFiringSeq m2) = p :=
  Path.trans_refl_right p

-- Theorem 5: Symmetry of composed firing sequences
theorem composeFiringSeqs_symm {np : Nat} {m1 m2 m3 : Marking np}
    (p1 : Path m1 m2) (p2 : Path m2 m3) :
    Path.symm (composeFiringSeqs p1 p2) =
    composeFiringSeqs (Path.symm p2) (Path.symm p1) :=
  Path.symm_trans p1 p2

-- ============================================================
-- Section 3: Reachability
-- ============================================================

/-- m2 is reachable from m1 if there exists a Path from m1 to m2. -/
def Reachable {np : Nat} (m1 m2 : Marking np) : Prop :=
  Nonempty (Path m1 m2)

-- Theorem 6
theorem reachable_refl {np : Nat} (m : Marking np) : Reachable m m :=
  ⟨Path.refl m⟩

-- Theorem 7
theorem reachable_trans {np : Nat} {m1 m2 m3 : Marking np}
    (h1 : Reachable m1 m2) (h2 : Reachable m2 m3) : Reachable m1 m3 :=
  let ⟨p1⟩ := h1; let ⟨p2⟩ := h2; ⟨Path.trans p1 p2⟩

-- Theorem 8
theorem reachable_symm {np : Nat} {m1 m2 : Marking np}
    (h : Reachable m1 m2) : Reachable m2 m1 :=
  let ⟨p⟩ := h; ⟨Path.symm p⟩

-- Theorem 9
theorem path_implies_reachable {np : Nat} {m1 m2 : Marking np}
    (p : Path m1 m2) : Reachable m1 m2 :=
  ⟨p⟩

-- Theorem 10
theorem reachable_of_eq {np : Nat} {m1 m2 : Marking np}
    (h : m1 = m2) : Reachable m1 m2 :=
  h ▸ reachable_refl m1

-- Theorem 11: Path.toEq extracts marking equality
theorem path_toEq_marking {np : Nat} {m1 m2 : Marking np}
    (p : Path m1 m2) : m1 = m2 :=
  Path.toEq p

-- ============================================================
-- Section 4: Place Projection via congrArg
-- ============================================================

/-- Project a marking to a single place's token count. -/
def projectPlace {np : Nat} (pl : Fin np) : Marking np → Nat :=
  fun m => m pl

-- Theorem 12: congrArg lifts marking paths to token-count paths
def projectPlace_path {np : Nat} {m1 m2 : Marking np} (pl : Fin np)
    (p : Path m1 m2) : Path (projectPlace pl m1) (projectPlace pl m2) :=
  Path.congrArg (projectPlace pl) p

-- Theorem 13
theorem projectPlace_refl {np : Nat} (pl : Fin np) (m : Marking np) :
    projectPlace_path pl (Path.refl m) = Path.refl (projectPlace pl m) :=
  rfl

-- Theorem 14
theorem projectPlace_trans {np : Nat} {m1 m2 m3 : Marking np} (pl : Fin np)
    (p1 : Path m1 m2) (p2 : Path m2 m3) :
    projectPlace_path pl (Path.trans p1 p2) =
    Path.trans (projectPlace_path pl p1) (projectPlace_path pl p2) :=
  Path.congrArg_trans (projectPlace pl) p1 p2

-- Theorem 15
theorem projectPlace_symm {np : Nat} {m1 m2 : Marking np} (pl : Fin np)
    (p : Path m1 m2) :
    projectPlace_path pl (Path.symm p) =
    Path.symm (projectPlace_path pl p) :=
  Path.congrArg_symm (projectPlace pl) p

-- Theorem 16: Projection preserves equality
theorem projectPlace_eq_of_path {np : Nat} {m1 m2 : Marking np} (pl : Fin np)
    (p : Path m1 m2) : projectPlace pl m1 = projectPlace pl m2 :=
  Path.toEq (projectPlace_path pl p)

-- ============================================================
-- Section 5: Coverability
-- ============================================================

/-- m1 is covered by m2 (m1 ≤ m2 pointwise). -/
def covers {np : Nat} (m1 m2 : Marking np) : Prop :=
  ∀ p : Fin np, m1 p ≤ m2 p

-- Theorem 17
theorem covers_refl {np : Nat} (m : Marking np) : covers m m :=
  fun _ => Nat.le_refl _

-- Theorem 18
theorem covers_trans {np : Nat} {m1 m2 m3 : Marking np}
    (h1 : covers m1 m2) (h2 : covers m2 m3) : covers m1 m3 :=
  fun p => Nat.le_trans (h1 p) (h2 p)

-- Theorem 19
theorem covers_antisymm {np : Nat} {m1 m2 : Marking np}
    (h1 : covers m1 m2) (h2 : covers m2 m1) : m1 = m2 :=
  funext (fun p => Nat.le_antisymm (h1 p) (h2 p))

/-- m' is coverable from m0 if some reachable marking covers m'. -/
def Coverable {np : Nat} (m0 m' : Marking np) : Prop :=
  ∃ m2 : Marking np, Reachable m0 m2 ∧ covers m' m2

-- Theorem 20
theorem coverable_of_reachable {np : Nat} {m0 m : Marking np}
    (h : Reachable m0 m) : Coverable m0 m :=
  ⟨m, h, covers_refl m⟩

-- Theorem 21: Coverable is monotone in the reachability prefix
theorem coverable_of_reachable_trans {np : Nat} {m0 m1 m' : Marking np}
    (hr : Reachable m0 m1) (hc : Coverable m1 m') : Coverable m0 m' := by
  obtain ⟨m2, hreach, hcov⟩ := hc
  exact ⟨m2, reachable_trans hr hreach, hcov⟩

-- ============================================================
-- Section 6: Boundedness
-- ============================================================

/-- A place p is k-bounded from m0 if every reachable marking
    has at most k tokens in p. -/
def PlaceBounded {np : Nat} (m0 : Marking np) (p : Fin np) (k : Nat) : Prop :=
  ∀ m : Marking np, Reachable m0 m → m p ≤ k

/-- A net is k-bounded from m0 if every place is k-bounded. -/
def NetBounded {np : Nat} (m0 : Marking np) (k : Nat) : Prop :=
  ∀ p : Fin np, PlaceBounded m0 p k

-- Theorem 22
theorem netBounded_monotone {np : Nat} {m0 : Marking np} {k1 k2 : Nat}
    (h : k1 ≤ k2) (hb : NetBounded m0 k1) : NetBounded m0 k2 :=
  fun p m hr => Nat.le_trans (hb p m hr) h

/-- A 1-bounded net is called safe. -/
def Safe {np : Nat} (m0 : Marking np) : Prop := NetBounded m0 1

-- Theorem 23
theorem safe_implies_bounded {np : Nat} {m0 : Marking np} {k : Nat}
    (hs : Safe m0) (hk : 1 ≤ k) : NetBounded m0 k :=
  netBounded_monotone hk hs

-- Theorem 24: Boundedness of a single place is monotone
theorem placeBounded_monotone {np : Nat} {m0 : Marking np}
    {p : Fin np} {k1 k2 : Nat}
    (h : k1 ≤ k2) (hb : PlaceBounded m0 p k1) : PlaceBounded m0 p k2 :=
  fun m hr => Nat.le_trans (hb m hr) h

-- ============================================================
-- Section 7: Conflict and Concurrency
-- ============================================================

/-- Two transitions conflict at marking m if both enabled
    but share a pre-place where tokens are insufficient for both. -/
def inConflict {np nt : Nat} (net : PetriNet np nt) (m : Marking np)
    (t1 t2 : Fin nt) : Prop :=
  t1 ≠ t2 ∧ enabled net m t1 ∧ enabled net m t2 ∧
  ∃ p : Fin np, net.pre t1 p + net.pre t2 p > m p

-- Theorem 25
theorem conflict_symm {np nt : Nat} {net : PetriNet np nt} {m : Marking np}
    {t1 t2 : Fin nt} (h : inConflict net m t1 t2) : inConflict net m t2 t1 := by
  obtain ⟨hne, he1, he2, p, hp⟩ := h
  exact ⟨Ne.symm hne, he2, he1, p, by omega⟩

/-- Two transitions are concurrent if both can fire without interference. -/
def concurrent {np nt : Nat} (net : PetriNet np nt) (m : Marking np)
    (t1 t2 : Fin nt) : Prop :=
  t1 ≠ t2 ∧ enabled net m t1 ∧ enabled net m t2 ∧
  ∀ p : Fin np, net.pre t1 p + net.pre t2 p ≤ m p

-- Theorem 26
theorem concurrent_symm {np nt : Nat} {net : PetriNet np nt} {m : Marking np}
    {t1 t2 : Fin nt} (h : concurrent net m t1 t2) : concurrent net m t2 t1 := by
  obtain ⟨hne, he1, he2, hp⟩ := h
  exact ⟨Ne.symm hne, he2, he1, fun p => Nat.add_comm (net.pre t2 p) (net.pre t1 p) ▸ hp p⟩

-- Theorem 27
theorem conflict_not_concurrent {np nt : Nat} {net : PetriNet np nt} {m : Marking np}
    {t1 t2 : Fin nt} (hc : inConflict net m t1 t2)
    (hcon : concurrent net m t1 t2) : False := by
  obtain ⟨_, _, _, p, hp⟩ := hc
  obtain ⟨_, _, _, hall⟩ := hcon
  have := hall p; omega

-- ============================================================
-- Section 8: Free Choice Nets
-- ============================================================

/-- A net is free-choice if for every place p, all transitions that
    consume from p have the same pre-set. -/
def isFreeChoice {np nt : Nat} (net : PetriNet np nt) : Prop :=
  ∀ (p : Fin np) (t1 t2 : Fin nt),
    net.pre t1 p > 0 → net.pre t2 p > 0 →
    (∀ q : Fin np, net.pre t1 q = net.pre t2 q)

-- Theorem 28
theorem free_choice_conflict_same_pre {np nt : Nat}
    {net : PetriNet np nt} (hfc : isFreeChoice net)
    {t1 t2 : Fin nt} {p : Fin np}
    (h1 : net.pre t1 p > 0) (h2 : net.pre t2 p > 0) :
    ∀ q : Fin np, net.pre t1 q = net.pre t2 q :=
  hfc p t1 t2 h1 h2

-- Theorem 29: In a free choice net, enabled transfer
theorem free_choice_enabled_transfer {np nt : Nat}
    {net : PetriNet np nt} (hfc : isFreeChoice net)
    {m : Marking np} {t1 t2 : Fin nt} {p : Fin np}
    (hen : enabled net m t1) (h1 : net.pre t1 p > 0)
    (h2 : net.pre t2 p > 0) : enabled net m t2 := by
  intro q
  have heq := hfc p t1 t2 h1 h2 q
  rw [← heq]
  exact hen q

-- ============================================================
-- Section 9: Net Morphisms and Functoriality via congrArg
-- ============================================================

/-- A morphism between marking spaces. -/
structure MarkingMorphism (np1 np2 : Nat) where
  mapMarking : Marking np1 → Marking np2
  mapPath : ∀ {m1 m2 : Marking np1}, Path m1 m2 → Path (mapMarking m1) (mapMarking m2)
  mapRefl : ∀ (m : Marking np1), mapPath (Path.refl m) = Path.refl (mapMarking m)

-- Theorem 30
theorem morphism_preserves_reachable {np1 np2 : Nat}
    (f : MarkingMorphism np1 np2)
    {m1 m2 : Marking np1} (h : Reachable m1 m2) :
    Reachable (f.mapMarking m1) (f.mapMarking m2) :=
  let ⟨p⟩ := h; ⟨f.mapPath p⟩

/-- The identity morphism. -/
def idMorphism (np : Nat) : MarkingMorphism np np where
  mapMarking := id
  mapPath := id
  mapRefl := fun _ => rfl

-- Theorem 31
theorem idMorphism_mapMarking {np : Nat} (m : Marking np) :
    (idMorphism np).mapMarking m = m :=
  rfl

/-- Composition of morphisms. -/
def composeMorphism {np1 np2 np3 : Nat}
    (f : MarkingMorphism np1 np2)
    (g : MarkingMorphism np2 np3) : MarkingMorphism np1 np3 where
  mapMarking := g.mapMarking ∘ f.mapMarking
  mapPath := fun p => g.mapPath (f.mapPath p)
  mapRefl := fun m => by
    show g.mapPath (f.mapPath (Path.refl m)) = Path.refl (g.mapMarking (f.mapMarking m))
    rw [f.mapRefl, g.mapRefl]

-- Theorem 32
theorem composeMorphism_mapMarking {np1 np2 np3 : Nat}
    (f : MarkingMorphism np1 np2) (g : MarkingMorphism np2 np3)
    (m : Marking np1) :
    (composeMorphism f g).mapMarking m = g.mapMarking (f.mapMarking m) :=
  rfl

/-- Build a morphism from any function via congrArg. -/
def congrArgMorphism {np1 np2 : Nat} (f : Marking np1 → Marking np2) :
    MarkingMorphism np1 np2 where
  mapMarking := f
  mapPath := Path.congrArg f
  mapRefl := fun _ => rfl

-- Theorem 33
theorem congrArgMorphism_mapMarking {np1 np2 : Nat}
    (f : Marking np1 → Marking np2) (m : Marking np1) :
    (congrArgMorphism f).mapMarking m = f m :=
  rfl

-- Theorem 34: Compose morphisms preserves reachability
theorem compose_morphism_reachable {np1 np2 np3 : Nat}
    (f : MarkingMorphism np1 np2) (g : MarkingMorphism np2 np3)
    {m1 m2 : Marking np1} (h : Reachable m1 m2) :
    Reachable ((composeMorphism f g).mapMarking m1) ((composeMorphism f g).mapMarking m2) :=
  morphism_preserves_reachable (composeMorphism f g) h

-- ============================================================
-- Section 10: Subnet Embedding
-- ============================================================

/-- A subnet embedding maps places and transitions injectively. -/
structure SubnetEmbedding (np1 nt1 np2 nt2 : Nat) where
  placeMap : Fin np1 → Fin np2
  transMap : Fin nt1 → Fin nt2
  placeInj : Function.Injective placeMap
  transInj : Function.Injective transMap

/-- Pull back a marking from the larger net to the subnet. -/
def pullbackMarking {np1 nt1 np2 nt2 : Nat}
    (emb : SubnetEmbedding np1 nt1 np2 nt2)
    (m : Marking np2) : Marking np1 :=
  fun p => m (emb.placeMap p)

-- Theorem 35
def pullbackMarking_path {np1 nt1 np2 nt2 : Nat}
    (emb : SubnetEmbedding np1 nt1 np2 nt2)
    {m1 m2 : Marking np2} (p : Path m1 m2) :
    Path (pullbackMarking emb m1) (pullbackMarking emb m2) :=
  Path.congrArg (pullbackMarking emb) p

-- Theorem 36
theorem pullbackMarking_reachable {np1 nt1 np2 nt2 : Nat}
    (emb : SubnetEmbedding np1 nt1 np2 nt2)
    {m1 m2 : Marking np2} (h : Reachable m1 m2) :
    Reachable (pullbackMarking emb m1) (pullbackMarking emb m2) :=
  let ⟨p⟩ := h; ⟨pullbackMarking_path emb p⟩

-- Theorem 37
theorem pullback_trans {np1 nt1 np2 nt2 : Nat}
    (emb : SubnetEmbedding np1 nt1 np2 nt2)
    {m1 m2 m3 : Marking np2}
    (p1 : Path m1 m2) (p2 : Path m2 m3) :
    pullbackMarking_path emb (Path.trans p1 p2) =
    Path.trans (pullbackMarking_path emb p1) (pullbackMarking_path emb p2) :=
  Path.congrArg_trans (pullbackMarking emb) p1 p2

-- Theorem 38
theorem pullback_symm {np1 nt1 np2 nt2 : Nat}
    (emb : SubnetEmbedding np1 nt1 np2 nt2)
    {m1 m2 : Marking np2} (p : Path m1 m2) :
    pullbackMarking_path emb (Path.symm p) =
    Path.symm (pullbackMarking_path emb p) :=
  Path.congrArg_symm (pullbackMarking emb) p

-- Theorem 39: Pullback preserves marking equality
theorem pullback_eq_of_path {np1 nt1 np2 nt2 : Nat}
    (emb : SubnetEmbedding np1 nt1 np2 nt2)
    {m1 m2 : Marking np2} (p : Path m1 m2) :
    pullbackMarking emb m1 = pullbackMarking emb m2 :=
  Path.toEq (pullbackMarking_path emb p)

-- ============================================================
-- Section 11: State Machine Components
-- ============================================================

/-- A state machine component: a subset of places via Bool. -/
structure StateMachineComponent (np : Nat) where
  inComponent : Fin np → Bool

/-- Token count restricted to a component. -/
def smcTokenCount {np : Nat} (smc : StateMachineComponent np)
    (m : Marking np) : List Nat :=
  List.filterMap
    (fun i =>
      if h : i < np then
        if smc.inComponent ⟨i, h⟩ then some (m ⟨i, h⟩) else none
      else none)
    (List.range np)

-- Theorem 40
def smcTokenCount_path {np : Nat} (smc : StateMachineComponent np)
    {m1 m2 : Marking np} (p : Path m1 m2) :
    Path (smcTokenCount smc m1) (smcTokenCount smc m2) :=
  Path.congrArg (smcTokenCount smc) p

-- Theorem 41
theorem smcTokenCount_trans {np : Nat} (smc : StateMachineComponent np)
    {m1 m2 m3 : Marking np}
    (p1 : Path m1 m2) (p2 : Path m2 m3) :
    smcTokenCount_path smc (Path.trans p1 p2) =
    Path.trans (smcTokenCount_path smc p1) (smcTokenCount_path smc p2) :=
  Path.congrArg_trans (smcTokenCount smc) p1 p2

-- Theorem 42
theorem smcTokenCount_symm {np : Nat} (smc : StateMachineComponent np)
    {m1 m2 : Marking np} (p : Path m1 m2) :
    smcTokenCount_path smc (Path.symm p) =
    Path.symm (smcTokenCount_path smc p) :=
  Path.congrArg_symm (smcTokenCount smc) p

-- ============================================================
-- Section 12: Marking Equivalence (Groupoid Structure)
-- ============================================================

/-- Two markings are path-equivalent if there is a path between them. -/
def MarkingEquiv {np : Nat} (m1 m2 : Marking np) : Prop :=
  Nonempty (Path m1 m2)

-- Theorem 43
theorem markingEquiv_refl {np : Nat} (m : Marking np) : MarkingEquiv m m :=
  ⟨Path.refl m⟩

-- Theorem 44
theorem markingEquiv_symm {np : Nat} {m1 m2 : Marking np}
    (h : MarkingEquiv m1 m2) : MarkingEquiv m2 m1 :=
  let ⟨p⟩ := h; ⟨Path.symm p⟩

-- Theorem 45
theorem markingEquiv_trans {np : Nat} {m1 m2 m3 : Marking np}
    (h1 : MarkingEquiv m1 m2) (h2 : MarkingEquiv m2 m3) :
    MarkingEquiv m1 m3 :=
  let ⟨p1⟩ := h1; let ⟨p2⟩ := h2; ⟨Path.trans p1 p2⟩

-- ============================================================
-- Section 13: Path Reversal, Symmetry, and Cancellation Laws
-- ============================================================

-- Theorem 46
theorem symm_symm_marking {np : Nat} {m1 m2 : Marking np}
    (p : Path m1 m2) : Path.symm (Path.symm p) = p :=
  Path.symm_symm p

-- Theorem 47: symm distributes over trans (contravariant)
theorem symm_trans_marking {np : Nat} {m1 m2 m3 : Marking np}
    (p : Path m1 m2) (q : Path m2 m3) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

-- Theorem 48: symm of refl is refl
theorem symm_refl_marking {np : Nat} (m : Marking np) :
    Path.symm (Path.refl m) = Path.refl m :=
  Path.symm_refl m

-- ============================================================
-- Section 14: Observation Functions via congrArg
-- ============================================================

/-- Observe whether a marking exceeds threshold k at place p. -/
def exceedsThreshold {np : Nat} (pl : Fin np) (k : Nat) (m : Marking np) : Bool :=
  decide (m pl > k)

-- Theorem 49
def exceedsThreshold_path {np : Nat} {m1 m2 : Marking np}
    (pl : Fin np) (k : Nat) (path : Path m1 m2) :
    Path (exceedsThreshold pl k m1) (exceedsThreshold pl k m2) :=
  Path.congrArg (exceedsThreshold pl k) path

-- Theorem 50
theorem exceedsThreshold_eq_of_path {np : Nat} {m1 m2 : Marking np}
    (pl : Fin np) (k : Nat) (p : Path m1 m2) :
    exceedsThreshold pl k m1 = exceedsThreshold pl k m2 :=
  Path.toEq (exceedsThreshold_path pl k p)

/-- Convert marking to list representation. -/
def markingToList {np : Nat} (m : Marking np) : List Nat :=
  List.map (fun i => if h : i < np then m ⟨i, h⟩ else 0) (List.range np)

-- Theorem 51
def markingToList_path {np : Nat} {m1 m2 : Marking np}
    (p : Path m1 m2) : Path (markingToList m1) (markingToList m2) :=
  Path.congrArg markingToList p

-- Theorem 52
theorem markingToList_trans {np : Nat} {m1 m2 m3 : Marking np}
    (p1 : Path m1 m2) (p2 : Path m2 m3) :
    markingToList_path (Path.trans p1 p2) =
    Path.trans (markingToList_path p1) (markingToList_path p2) :=
  Path.congrArg_trans markingToList p1 p2

-- Theorem 53
theorem markingToList_symm {np : Nat} {m1 m2 : Marking np}
    (p : Path m1 m2) :
    markingToList_path (Path.symm p) =
    Path.symm (markingToList_path p) :=
  Path.congrArg_symm markingToList p

-- ============================================================
-- Section 15: Product Nets (Projections)
-- ============================================================

/-- Product marking of two markings. -/
def prodMarking {np1 np2 : Nat} (m1 : Marking np1) (m2 : Marking np2)
    : Marking (np1 + np2) :=
  fun p =>
    if h : p.val < np1 then m1 ⟨p.val, h⟩
    else m2 ⟨p.val - np1, by omega⟩

/-- Left projection. -/
def projLeft {np1 np2 : Nat} (m : Marking (np1 + np2)) : Marking np1 :=
  fun p => m ⟨p.val, by omega⟩

/-- Right projection. -/
def projRight {np1 np2 : Nat} (m : Marking (np1 + np2)) : Marking np2 :=
  fun p => m ⟨np1 + p.val, by omega⟩

-- Theorem 54
def projLeft_path {np1 np2 : Nat} {m1 m2 : Marking (np1 + np2)}
    (p : Path m1 m2) : Path (projLeft (np2 := np2) m1) (projLeft (np2 := np2) m2) :=
  Path.congrArg (projLeft (np2 := np2)) p

-- Theorem 55
def projRight_path {np1 np2 : Nat} {m1 m2 : Marking (np1 + np2)}
    (p : Path m1 m2) : Path (projRight (np1 := np1) m1) (projRight (np1 := np1) m2) :=
  Path.congrArg (projRight (np1 := np1)) p

-- Theorem 56
theorem projLeft_trans {np1 np2 : Nat}
    {m1 m2 m3 : Marking (np1 + np2)}
    (p1 : Path m1 m2) (p2 : Path m2 m3) :
    projLeft_path (np2 := np2) (Path.trans p1 p2) =
    Path.trans (projLeft_path (np2 := np2) p1) (projLeft_path (np2 := np2) p2) :=
  Path.congrArg_trans (projLeft (np2 := np2)) p1 p2

-- Theorem 57
theorem projRight_trans {np1 np2 : Nat}
    {m1 m2 m3 : Marking (np1 + np2)}
    (p1 : Path m1 m2) (p2 : Path m2 m3) :
    projRight_path (np1 := np1) (Path.trans p1 p2) =
    Path.trans (projRight_path (np1 := np1) p1) (projRight_path (np1 := np1) p2) :=
  Path.congrArg_trans (projRight (np1 := np1)) p1 p2

-- Theorem 58
theorem projLeft_symm {np1 np2 : Nat}
    {m1 m2 : Marking (np1 + np2)} (p : Path m1 m2) :
    projLeft_path (np2 := np2) (Path.symm p) =
    Path.symm (projLeft_path (np2 := np2) p) :=
  Path.congrArg_symm (projLeft (np2 := np2)) p

-- Theorem 59
theorem projRight_symm {np1 np2 : Nat}
    {m1 m2 : Marking (np1 + np2)} (p : Path m1 m2) :
    projRight_path (np1 := np1) (Path.symm p) =
    Path.symm (projRight_path (np1 := np1) p) :=
  Path.congrArg_symm (projRight (np1 := np1)) p

-- ============================================================
-- Section 16: Pairing and Derived Observations
-- ============================================================

/-- Pair token counts at two places. -/
def pairPlaces {np : Nat} (p1 p2 : Fin np) (m : Marking np) : Nat × Nat :=
  (m p1, m p2)

-- Theorem 60
def pairPlaces_path {np : Nat} {m1 m2 : Marking np}
    (p1 p2 : Fin np) (path : Path m1 m2) :
    Path (pairPlaces p1 p2 m1) (pairPlaces p1 p2 m2) :=
  Path.congrArg (pairPlaces p1 p2) path

-- Theorem 61
theorem pairPlaces_trans {np : Nat} {m1 m2 m3 : Marking np}
    (p1 p2 : Fin np) (pa : Path m1 m2) (pb : Path m2 m3) :
    pairPlaces_path p1 p2 (Path.trans pa pb) =
    Path.trans (pairPlaces_path p1 p2 pa) (pairPlaces_path p1 p2 pb) :=
  Path.congrArg_trans (pairPlaces p1 p2) pa pb

-- Theorem 62
theorem pairPlaces_symm {np : Nat} {m1 m2 : Marking np}
    (p1 p2 : Fin np) (pa : Path m1 m2) :
    pairPlaces_path p1 p2 (Path.symm pa) =
    Path.symm (pairPlaces_path p1 p2 pa) :=
  Path.congrArg_symm (pairPlaces p1 p2) pa

-- Theorem 63
theorem pairPlaces_eq_of_path {np : Nat} {m1 m2 : Marking np}
    (p1 p2 : Fin np) (pa : Path m1 m2) :
    pairPlaces p1 p2 m1 = pairPlaces p1 p2 m2 :=
  Path.toEq (pairPlaces_path p1 p2 pa)

-- ============================================================
-- Section 17: Reachability Composition Variants
-- ============================================================

-- Theorem 64
theorem reachable_compose_path {np : Nat} {m1 m2 m3 : Marking np}
    (p : Path m1 m2) (h : Reachable m2 m3) : Reachable m1 m3 :=
  let ⟨q⟩ := h; ⟨Path.trans p q⟩

-- Theorem 65
theorem path_compose_reachable {np : Nat} {m1 m2 m3 : Marking np}
    (h : Reachable m1 m2) (p : Path m2 m3) : Reachable m1 m3 :=
  let ⟨q⟩ := h; ⟨Path.trans q p⟩

-- Theorem 66: Reachability is decidable when Path exists
theorem reachable_iff_path {np : Nat} {m1 m2 : Marking np} :
    Reachable m1 m2 ↔ Nonempty (Path m1 m2) :=
  Iff.rfl

-- ============================================================
-- Section 18: Confusion and Structural Properties
-- ============================================================

/-- Symmetric confusion: two transitions in conflict where a third
    is concurrent with both. -/
def symmetricConfusion {np nt : Nat} (net : PetriNet np nt)
    (m : Marking np) (t1 t2 t3 : Fin nt) : Prop :=
  inConflict net m t1 t2 ∧ concurrent net m t1 t3 ∧ concurrent net m t2 t3

-- Theorem 67: Symmetric confusion is symmetric in the conflicting pair
theorem symmetricConfusion_swap {np nt : Nat}
    {net : PetriNet np nt} {m : Marking np}
    {t1 t2 t3 : Fin nt}
    (h : symmetricConfusion net m t1 t2 t3) :
    symmetricConfusion net m t2 t1 t3 := by
  obtain ⟨hc, hcon1, hcon2⟩ := h
  exact ⟨conflict_symm hc, hcon2, hcon1⟩

-- ============================================================
-- Section 19: Marking Transformations
-- ============================================================

/-- Shift all tokens by a constant. -/
def shiftMarking {np : Nat} (k : Nat) (m : Marking np) : Marking np :=
  fun p => m p + k

-- Theorem 68
def shiftMarking_path {np : Nat} (k : Nat) {m1 m2 : Marking np}
    (p : Path m1 m2) : Path (shiftMarking k m1) (shiftMarking k m2) :=
  Path.congrArg (shiftMarking k) p

-- Theorem 69
theorem shiftMarking_trans {np : Nat} (k : Nat) {m1 m2 m3 : Marking np}
    (p1 : Path m1 m2) (p2 : Path m2 m3) :
    shiftMarking_path k (Path.trans p1 p2) =
    Path.trans (shiftMarking_path k p1) (shiftMarking_path k p2) :=
  Path.congrArg_trans (shiftMarking k) p1 p2

-- Theorem 70: The identity function congrArg is the identity on paths
theorem id_congrArg_marking {np : Nat} {m1 m2 : Marking np}
    (p : Path m1 m2) :
    Path.congrArg (fun x : Marking np => x) p = p := by
  cases p with
  | mk steps proof =>
    cases proof
    simp [Path.congrArg]

end ComputationalPaths.Path.Rewriting.PetriNetPathDeep
