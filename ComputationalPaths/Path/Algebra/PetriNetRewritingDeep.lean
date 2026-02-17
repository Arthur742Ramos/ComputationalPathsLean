/-
  ComputationalPaths / Path / Algebra / PetriNetRewritingDeep.lean

  Petri nets as rewriting systems formalised with computational paths.
  Markings as multisets (place → Nat), transitions as rewrite steps
  consuming/producing tokens, firing sequences as paths, reachability
  as path existence, coverability, liveness via infinite paths, Petri
  net unfolding, concurrent firing as parallel paths.

  All proofs are sorry‑free.  50 theorems.
-/

-- ============================================================
-- §1  Places, Markings, Transitions
-- ============================================================

structure Place where
  id : Nat
deriving DecidableEq, Repr

def Marking := Place → Nat

def Marking.zero : Marking := fun _ => 0
def Marking.add (m₁ m₂ : Marking) : Marking := fun p => m₁ p + m₂ p
def Marking.le (m₁ m₂ : Marking) : Prop := ∀ p : Place, m₁ p ≤ m₂ p
def Marking.sub (m₁ m₂ : Marking) : Marking := fun p => m₁ p - m₂ p

instance : LE Marking := ⟨Marking.le⟩

structure Transition where
  name : Nat
  pre  : Marking
  post : Marking

abbrev PetriNet := List Transition

-- ============================================================
-- §2  Enabledness and Firing (Step)
-- ============================================================

def Transition.enabled (t : Transition) (m : Marking) : Prop :=
  t.pre ≤ m

inductive Fire (N : PetriNet) : Marking → Marking → Prop where
  | fire (t : Transition) (m : Marking)
      (hmem : t ∈ N)
      (hen : t.enabled m) :
      Fire N m (Marking.add (Marking.sub m t.pre) t.post)

/-- Theorem 1: A fire step witnesses a specific transition. -/
theorem Fire.witness {N : PetriNet} {m m' : Marking} (f : Fire N m m') :
    ∃ t, t ∈ N ∧ t.enabled m ∧ m' = Marking.add (Marking.sub m t.pre) t.post := by
  cases f with
  | fire t m hmem hen => exact ⟨t, hmem, hen, rfl⟩

-- ============================================================
-- §3  Firing Sequences as Paths
-- ============================================================

inductive FPath (N : PetriNet) : Marking → Marking → Prop where
  | refl (m : Marking) : FPath N m m
  | step {a b c : Marking} : Fire N a b → FPath N b c → FPath N a c

/-- Theorem 2: Transitivity of firing paths. -/
theorem FPath.trans {N : PetriNet} {a b c : Marking}
    (p : FPath N a b) (q : FPath N b c) : FPath N a c := by
  induction p with
  | refl _ => exact q
  | step f _ ih => exact FPath.step f (ih q)

/-- Theorem 3: Single fire as a path. -/
theorem FPath.single {N : PetriNet} {a b : Marking}
    (f : Fire N a b) : FPath N a b :=
  FPath.step f (FPath.refl _)

/-- Theorem 4: Append a fire step. -/
theorem FPath.append {N : PetriNet} {a b c : Marking}
    (p : FPath N a b) (f : Fire N b c) : FPath N a c :=
  FPath.trans p (FPath.single f)

-- ============================================================
-- §4  Reachability
-- ============================================================

def Reachable (N : PetriNet) (m m' : Marking) : Prop := FPath N m m'

/-- Theorem 5: Reachability is reflexive. -/
theorem Reachable.refl (N : PetriNet) (m : Marking) : Reachable N m m :=
  FPath.refl m

/-- Theorem 6: Reachability is transitive. -/
theorem Reachable.trans {N : PetriNet} {a b c : Marking}
    (h1 : Reachable N a b) (h2 : Reachable N b c) : Reachable N a c :=
  FPath.trans h1 h2

/-- Theorem 7: A single fire implies reachability. -/
theorem Reachable.of_fire {N : PetriNet} {a b : Marking}
    (f : Fire N a b) : Reachable N a b :=
  FPath.single f

-- ============================================================
-- §5  Path Length (Step Counting)
-- ============================================================

inductive BoundedFPath (N : PetriNet) : Marking → Marking → Nat → Prop where
  | refl (m : Marking) : BoundedFPath N m m 0
  | step {a b c : Marking} {n : Nat} :
      Fire N a b → BoundedFPath N b c n → BoundedFPath N a c (n + 1)

/-- Theorem 8: A 0‑bounded path implies equality. -/
theorem BoundedFPath.zero_eq {N : PetriNet} {a b : Marking}
    (h : BoundedFPath N a b 0) : a = b := by
  cases h with
  | refl _ => rfl

/-- Theorem 9: Bounded path to unbounded path. -/
theorem BoundedFPath.toFPath {N : PetriNet} {a b : Marking} {n : Nat}
    (h : BoundedFPath N a b n) : FPath N a b := by
  induction h with
  | refl _ => exact FPath.refl _
  | step f _ ih => exact FPath.step f ih

/-- Theorem 10: Bounded path weakening. -/
theorem BoundedFPath.weaken {N : PetriNet} {a b : Marking} {n : Nat}
    (h : BoundedFPath N a b n) :
    ∃ _ : FPath N a b, True :=
  ⟨h.toFPath, trivial⟩

-- ============================================================
-- §6  Coverability
-- ============================================================

def Covers (m m' : Marking) : Prop := m ≤ m'

def Coverable (N : PetriNet) (m₀ target : Marking) : Prop :=
  ∃ m', Reachable N m₀ m' ∧ Covers target m'

/-- Theorem 11: Reachability implies coverability. -/
theorem Reachable.toCoverable {N : PetriNet} {m₀ target : Marking}
    (h : Reachable N m₀ target) : Coverable N m₀ target :=
  ⟨target, h, fun _ => Nat.le_refl _⟩

/-- Theorem 12: Covers is reflexive. -/
theorem Covers.refl (m : Marking) : Covers m m :=
  fun _ => Nat.le_refl _

/-- Theorem 13: Covers is transitive. -/
theorem Covers.trans {a b c : Marking}
    (h1 : Covers a b) (h2 : Covers b c) : Covers a c :=
  fun p => Nat.le_trans (h1 p) (h2 p)

/-- Theorem 14: Coverable via transitive reachability. -/
theorem Coverable.of_reach_trans {N : PetriNet} {m₀ m₁ target : Marking}
    (h1 : Reachable N m₀ m₁) (h2 : Coverable N m₁ target) :
    Coverable N m₀ target := by
  obtain ⟨m', hreach, hcov⟩ := h2
  exact ⟨m', Reachable.trans h1 hreach, hcov⟩

-- ============================================================
-- §7  Marking Algebra (congrArg‑style)
-- ============================================================

/-- Theorem 15: Marking add is commutative. -/
theorem Marking.add_comm (m₁ m₂ : Marking) :
    Marking.add m₁ m₂ = Marking.add m₂ m₁ := by
  funext p; simp [Marking.add, Nat.add_comm]

/-- Theorem 16: Marking add is associative. -/
theorem Marking.add_assoc' (m₁ m₂ m₃ : Marking) :
    Marking.add (Marking.add m₁ m₂) m₃ = Marking.add m₁ (Marking.add m₂ m₃) := by
  funext p; simp [Marking.add, Nat.add_assoc]

/-- Theorem 17: Adding zero marking is identity. -/
theorem Marking.add_zero (m : Marking) :
    Marking.add m Marking.zero = m := by
  funext p; simp [Marking.add, Marking.zero]

/-- Theorem 18: Zero is left identity. -/
theorem Marking.zero_add (m : Marking) :
    Marking.add Marking.zero m = m := by
  funext p; simp [Marking.add, Marking.zero]

-- ============================================================
-- §8  Monotonicity
-- ============================================================

theorem enabled_mono {t : Transition} {m₁ m₂ : Marking}
    (hen : t.enabled m₁) (hle : m₁ ≤ m₂) : t.enabled m₂ :=
  fun p => Nat.le_trans (hen p) (hle p)

/-- Theorem 19: Monotonicity of firing. -/
theorem fire_mono {N : PetriNet} {t : Transition} {m₁ m₂ : Marking}
    (hmem : t ∈ N) (hen1 : t.enabled m₁) (hle : m₁ ≤ m₂) :
    ∃ m₂', Fire N m₂ m₂' :=
  ⟨_, Fire.fire t m₂ hmem (enabled_mono hen1 hle)⟩

-- ============================================================
-- §9  Symmetric Paths (Reversible Petri Nets)
-- ============================================================

def Transition.rev (t : Transition) : Transition :=
  { name := t.name + 1000, pre := t.post, post := t.pre }

def PetriNet.revClose (N : PetriNet) : PetriNet :=
  N ++ N.map Transition.rev

inductive SymFPath (N : PetriNet) : Marking → Marking → Prop where
  | refl (m : Marking) : SymFPath N m m
  | fwd  {a b c : Marking} : Fire N a b → SymFPath N b c → SymFPath N a c
  | bwd  {a b c : Marking} : Fire N b a → SymFPath N b c → SymFPath N a c

/-- Theorem 20: Transitivity of symmetric paths. -/
theorem SymFPath.trans {N : PetriNet} {a b c : Marking}
    (p : SymFPath N a b) (q : SymFPath N b c) : SymFPath N a c := by
  induction p with
  | refl _ => exact q
  | fwd f _ ih => exact SymFPath.fwd f (ih q)
  | bwd f _ ih => exact SymFPath.bwd f (ih q)

/-- Theorem 21: Symmetry of symmetric paths. -/
theorem SymFPath.symm {N : PetriNet} {a b : Marking}
    (p : SymFPath N a b) : SymFPath N b a := by
  induction p with
  | refl _ => exact SymFPath.refl _
  | fwd f _ ih => exact SymFPath.trans ih (SymFPath.bwd f (SymFPath.refl _))
  | bwd f _ ih => exact SymFPath.trans ih (SymFPath.fwd f (SymFPath.refl _))

/-- Theorem 22: Forward path lifts to symmetric. -/
theorem FPath.toSym {N : PetriNet} {a b : Marking}
    (p : FPath N a b) : SymFPath N a b := by
  induction p with
  | refl _ => exact SymFPath.refl _
  | step f _ ih => exact SymFPath.fwd f ih

-- ============================================================
-- §10  Parallel Firing (Concurrent Steps)
-- ============================================================

def Concurrent (t₁ t₂ : Transition) : Prop :=
  ∀ p, t₁.pre p = 0 ∨ t₂.pre p = 0

inductive ParFire (N : PetriNet) : Marking → Marking → Prop where
  | par (t₁ t₂ : Transition) (m : Marking)
      (hm1 : t₁ ∈ N) (hm2 : t₂ ∈ N)
      (hen1 : t₁.enabled m) (hen2 : t₂.enabled m)
      (hconc : Concurrent t₁ t₂) :
      ParFire N m
        (Marking.add (Marking.sub (Marking.sub m t₁.pre) t₂.pre)
                     (Marking.add t₁.post t₂.post))

inductive ParPath (N : PetriNet) : Marking → Marking → Prop where
  | refl (m : Marking) : ParPath N m m
  | seqStep  {a b c : Marking} : Fire N a b → ParPath N b c → ParPath N a c
  | parStep  {a b c : Marking} : ParFire N a b → ParPath N b c → ParPath N a c

/-- Theorem 23: Transitivity of parallel paths. -/
theorem ParPath.trans {N : PetriNet} {a b c : Marking}
    (p : ParPath N a b) (q : ParPath N b c) : ParPath N a c := by
  induction p with
  | refl _ => exact q
  | seqStep f _ ih => exact ParPath.seqStep f (ih q)
  | parStep f _ ih => exact ParPath.parStep f (ih q)

/-- Theorem 24: Sequential path embeds in parallel path. -/
theorem FPath.toParPath {N : PetriNet} {a b : Marking}
    (p : FPath N a b) : ParPath N a b := by
  induction p with
  | refl _ => exact ParPath.refl _
  | step f _ ih => exact ParPath.seqStep f ih

-- ============================================================
-- §11  Diamond Property for Concurrent Transitions
-- ============================================================

/-- Theorem 25: Concurrent post-set addition is commutative. -/
theorem concurrent_post_comm (t₁ t₂ : Transition) :
    Marking.add t₁.post t₂.post = Marking.add t₂.post t₁.post :=
  Marking.add_comm t₁.post t₂.post

/-- Theorem 26: Concurrent pre-set subtraction commutes. -/
theorem concurrent_sub_comm {t₁ t₂ : Transition} {m : Marking}
    (hconc : Concurrent t₁ t₂) :
    Marking.sub (Marking.sub m t₁.pre) t₂.pre =
    Marking.sub (Marking.sub m t₂.pre) t₁.pre := by
  funext p
  simp [Marking.sub]
  cases hconc p with
  | inl h => simp [h]
  | inr h => simp [h]

/-- Theorem 27: Full diamond for concurrent transitions. -/
theorem concurrent_diamond {t₁ t₂ : Transition} {m : Marking}
    (hconc : Concurrent t₁ t₂) :
    Marking.add (Marking.sub (Marking.sub m t₁.pre) t₂.pre)
                (Marking.add t₁.post t₂.post) =
    Marking.add (Marking.sub (Marking.sub m t₂.pre) t₁.pre)
                (Marking.add t₂.post t₁.post) := by
  rw [concurrent_sub_comm hconc, concurrent_post_comm]

-- ============================================================
-- §12  Liveness
-- ============================================================

def Live (N : PetriNet) (m₀ : Marking) (t : Transition) : Prop :=
  ∀ m, Reachable N m₀ m → ∃ m', Reachable N m m' ∧ t.enabled m'

/-- Theorem 28: Liveness preserved through reachable markings. -/
theorem Live.of_reachable {N : PetriNet} {m₀ m₁ : Marking} {t : Transition}
    (hlive : Live N m₀ t) (hreach : Reachable N m₀ m₁) :
    Live N m₁ t :=
  fun m hm => hlive m (Reachable.trans hreach hm)

def DeadlockFree (N : PetriNet) (m₀ : Marking) : Prop :=
  ∀ m, Reachable N m₀ m → ∃ t, t ∈ N ∧ t.enabled m

/-- Theorem 29: Deadlock‑free implies extendability. -/
theorem deadlockFree_extend {N : PetriNet} {m₀ m : Marking}
    (hdf : DeadlockFree N m₀) (hreach : Reachable N m₀ m) :
    ∃ m', Fire N m m' := by
  obtain ⟨t, hmem, hen⟩ := hdf m hreach
  exact ⟨_, Fire.fire t m hmem hen⟩

/-- Theorem 30: Deadlock‑free preserved through reachability. -/
theorem DeadlockFree.of_reachable {N : PetriNet} {m₀ m₁ : Marking}
    (hdf : DeadlockFree N m₀) (hreach : Reachable N m₀ m₁) :
    DeadlockFree N m₁ :=
  fun m hm => hdf m (Reachable.trans hreach hm)

-- ============================================================
-- §13  Petri Net Unfolding (Occurrence Net)
-- ============================================================

structure Event where
  trans : Transition
  causal : List Nat

structure Condition where
  place : Place
  producer : Option Nat

structure OccurrenceNet where
  events     : List Event
  conditions : List Condition
  initial    : List Nat

def Causal (onet : OccurrenceNet) (i j : Nat) : Prop :=
  ∃ e, onet.events[j]? = some e ∧ i ∈ e.causal

inductive CausalPath (onet : OccurrenceNet) : Nat → Nat → Prop where
  | single {i j : Nat} : Causal onet i j → CausalPath onet i j
  | trans  {i j k : Nat} : CausalPath onet i j → CausalPath onet j k → CausalPath onet i k

/-- Theorem 31: Causal path transitivity. -/
theorem CausalPath.trans' {onet : OccurrenceNet} {a b c : Nat}
    (p : CausalPath onet a b) (q : CausalPath onet b c) :
    CausalPath onet a c :=
  CausalPath.trans p q

def ConcurrentEvents (onet : OccurrenceNet) (i j : Nat) : Prop :=
  ¬ CausalPath onet i j ∧ ¬ CausalPath onet j i ∧ i ≠ j

/-- Theorem 32: Concurrent events are symmetric. -/
theorem ConcurrentEvents.symm {onet : OccurrenceNet} {i j : Nat}
    (h : ConcurrentEvents onet i j) : ConcurrentEvents onet j i :=
  ⟨h.2.1, h.1, fun h' => h.2.2 h'.symm⟩

-- ============================================================
-- §14  Place Invariants
-- ============================================================

def WeightVec := Place → Int

def IsPlaceInvariant (N : PetriNet) (w : WeightVec) : Prop :=
  ∀ t ∈ N, ∀ p, w p * (t.post p : Int) = w p * (t.pre p : Int)

/-- Theorem 33: Zero weight vector is always an invariant. -/
theorem zero_invariant (N : PetriNet) :
    IsPlaceInvariant N (fun _ => 0) := by
  intro t _ p; simp

-- ============================================================
-- §15  Marking Order Properties
-- ============================================================

/-- Theorem 34: ≤ on markings is reflexive. -/
theorem Marking.le_refl' (m : Marking) : m ≤ m :=
  fun _ => Nat.le_refl _

/-- Theorem 35: ≤ on markings is transitive. -/
theorem Marking.le_trans' {a b c : Marking}
    (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  fun p => Nat.le_trans (h1 p) (h2 p)

/-- Theorem 36: ≤ on markings is antisymmetric. -/
theorem Marking.le_antisymm' {a b : Marking}
    (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  funext p; exact Nat.le_antisymm (h1 p) (h2 p)

/-- Theorem 37: Zero is the least marking. -/
theorem Marking.zero_le (m : Marking) : Marking.zero ≤ m :=
  fun _ => Nat.zero_le _

/-- Theorem 38: Add preserves ordering. -/
theorem Marking.add_le_add {a b c d : Marking}
    (h1 : a ≤ b) (h2 : c ≤ d) : Marking.add a c ≤ Marking.add b d :=
  fun p => Nat.add_le_add (h1 p) (h2 p)

-- ============================================================
-- §16  Structural Properties of Nets
-- ============================================================

def Transition.pure (t : Transition) : Prop :=
  ∀ p, t.pre p = 0 ∨ t.post p = 0

def PetriNet.pure (N : PetriNet) : Prop :=
  ∀ t ∈ N, Transition.pure t

def Transition.isSource (t : Transition) : Prop :=
  t.pre = Marking.zero

/-- Theorem 39: Source transitions are always enabled. -/
theorem source_always_enabled {t : Transition}
    (hsrc : t.isSource) (m : Marking) : t.enabled m := by
  intro p
  simp [Transition.isSource] at hsrc
  have : t.pre p = 0 := congrFun hsrc p
  omega

def Transition.isSink (t : Transition) : Prop :=
  t.post = Marking.zero

/-- Theorem 40: Firing a sink can only decrease tokens. -/
theorem sink_decreases {t : Transition} {m : Marking}
    (hsink : t.isSink) :
    Marking.add (Marking.sub m t.pre) t.post ≤ m := by
  intro p
  simp [Marking.add, Marking.sub, Transition.isSink] at *
  have : t.post p = 0 := congrFun hsink p
  omega

-- ============================================================
-- §17  Token Conservation
-- ============================================================

def totalTokens (places : List Place) (m : Marking) : Nat :=
  places.foldl (fun acc p => acc + m p) 0

/-- Theorem 41: Total tokens in zero marking is 0. -/
theorem totalTokens_zero (places : List Place) :
    totalTokens places Marking.zero = 0 := by
  simp [totalTokens, Marking.zero]
  induction places with
  | nil => rfl
  | cons _ _ ih =>
    simp [List.foldl]
    exact ih

-- ============================================================
-- §18  Path Equivalence (Confluence)
-- ============================================================

def Confluent (N : PetriNet) (m₀ : Marking) : Prop :=
  ∀ m₁ m₂, Reachable N m₀ m₁ → Reachable N m₀ m₂ →
    ∃ m₃, Reachable N m₁ m₃ ∧ Reachable N m₂ m₃

/-- Theorem 42: Confluence composes transitively. -/
theorem confluent_of_reachable {N : PetriNet} {m₀ m₁ : Marking}
    (hconf : Confluent N m₀) (hreach : Reachable N m₀ m₁) :
    Confluent N m₁ :=
  fun a b ha hb => hconf a b (Reachable.trans hreach ha) (Reachable.trans hreach hb)

-- ============================================================
-- §19  Subnet and Projection
-- ============================================================

def PetriNet.restrict (N : PetriNet) (sub : List Nat) : PetriNet :=
  N.filter (fun t => decide (t.name ∈ sub))

/-- Theorem 43: Firing in a subnet is firing in the parent. -/
theorem subnet_fire {N : PetriNet} {sub : List Nat} {m m' : Marking}
    (f : Fire (N.restrict sub) m m') : Fire N m m' := by
  cases f with
  | fire t m hmem hen =>
    have hmemN : t ∈ N := by
      simp [PetriNet.restrict] at hmem
      exact hmem.1
    exact Fire.fire t m hmemN hen

/-- Theorem 44: Paths in a subnet lift to paths in parent. -/
theorem subnet_path {N : PetriNet} {sub : List Nat} {m m' : Marking}
    (p : FPath (N.restrict sub) m m') : FPath N m m' := by
  induction p with
  | refl _ => exact FPath.refl _
  | step f _ ih => exact FPath.step (subnet_fire f) ih

-- ============================================================
-- §20  Firing with Trace (labelled paths)
-- ============================================================

inductive TracePath (N : PetriNet) : Marking → Marking → List Transition → Prop where
  | refl (m : Marking) : TracePath N m m []
  | step {a b c : Marking} {t : Transition} {ts : List Transition}
      (hmem : t ∈ N) (hen : t.enabled a)
      (hfired : b = Marking.add (Marking.sub a t.pre) t.post)
      (rest : TracePath N b c ts) :
      TracePath N a c (t :: ts)

/-- Theorem 45: Trace path to firing path (forget labels). -/
theorem TracePath.toFPath {N : PetriNet} {a b : Marking} {ts : List Transition}
    (h : TracePath N a b ts) : FPath N a b := by
  induction h with
  | refl _ => exact FPath.refl _
  | step hmem hen hfired _ ih =>
    subst hfired
    exact FPath.step (Fire.fire _ _ hmem hen) ih

/-- Theorem 46: Trace trans. -/
theorem TracePath.trans {N : PetriNet} {a b c : Marking} {ts₁ ts₂ : List Transition}
    (p : TracePath N a b ts₁) (q : TracePath N b c ts₂) :
    TracePath N a c (ts₁ ++ ts₂) := by
  induction p with
  | refl _ => exact q
  | step hmem hen hfired _ ih =>
    exact TracePath.step hmem hen hfired (ih q)

-- ============================================================
-- §21  Misc / Advanced
-- ============================================================

/-- Theorem 47: Empty net has only reflexive paths. -/
theorem empty_net_refl {m m' : Marking}
    (p : FPath [] m m') : m = m' := by
  induction p with
  | refl _ => rfl
  | step f _ _ =>
    cases f with
    | fire t _ hmem _ => simp at hmem

/-- Theorem 48: Marking sub self is zero. -/
theorem Marking.sub_self (m : Marking) :
    Marking.sub m m = Marking.zero := by
  funext p; simp [Marking.sub, Marking.zero, Nat.sub_self]

/-- Theorem 49: A transition with pre = post doesn't change marking. -/
theorem fire_identity {t : Transition} {m : Marking}
    (heq : t.pre = t.post) (hen : t.enabled m) :
    Marking.add (Marking.sub m t.pre) t.post = m := by
  funext p
  simp [Marking.add, Marking.sub]
  have hpre_le : t.pre p ≤ m p := hen p
  have hpost_eq : t.pre p = t.post p := congrFun heq p
  omega

/-- Theorem 50: Coverable is monotone in the initial marking. -/
theorem Coverable.mono_initial {N : PetriNet} {m₀ m₁ target : Marking}
    (hcov : Coverable N m₁ target) (hreach : Reachable N m₀ m₁) :
    Coverable N m₀ target :=
  Coverable.of_reach_trans hreach hcov
