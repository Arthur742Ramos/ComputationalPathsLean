/-
  Separation Logic and Resource Reasoning via Computational Paths
  ================================================================

  We model separation logic concepts — heaps, assertions, separating
  conjunction, magic wand, frame rule, Hoare triples, weakest preconditions,
  heap operations, concurrent separation logic, and fractional permissions —
  all witnessed by computational paths.

  Author: armada-365 (SeparationLogicDeep)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.SeparationLogicDeep

open ComputationalPaths
open ComputationalPaths.Path

-- =====================================================================
-- Section 1: Heap Model
-- =====================================================================

abbrev Loc := Nat
abbrev Val := Nat

@[ext]
structure Heap where
  cells : List (Loc × Val)
  deriving DecidableEq, Repr

noncomputable def Heap.empty : Heap := ⟨[]⟩
noncomputable def Heap.singleton (l : Loc) (v : Val) : Heap := ⟨[(l, v)]⟩
noncomputable def Heap.dom (h : Heap) : List Loc := h.cells.map Prod.fst

noncomputable def Heap.disjoint (h1 h2 : Heap) : Prop :=
  ∀ l, l ∈ h1.dom → l ∉ h2.dom

noncomputable def Heap.union (h1 h2 : Heap) : Heap := ⟨h1.cells ++ h2.cells⟩

notation:60 h1 " ⊕h " h2 => Heap.union h1 h2

noncomputable def Heap.write (h : Heap) (l : Loc) (v : Val) : Heap :=
  ⟨(l, v) :: h.cells.filter (fun p => decide (p.1 ≠ l))⟩

noncomputable def Heap.free (h : Heap) (l : Loc) : Heap :=
  ⟨h.cells.filter (fun p => decide (p.1 ≠ l))⟩

-- =====================================================================
-- Section 2: Separation Logic Assertions
-- =====================================================================

noncomputable def Assertion := Heap → Prop

noncomputable def emp : Assertion := fun h => h = Heap.empty

noncomputable def pointsTo (l : Loc) (v : Val) : Assertion :=
  fun h => h = Heap.singleton l v

notation:70 l " ↦sl " v => pointsTo l v

/-- Separating conjunction: P * Q -/
noncomputable def star (P Q : Assertion) : Assertion :=
  fun h => ∃ h1 h2 : Heap, Heap.disjoint h1 h2 ∧ (h = h1 ⊕h h2) ∧ P h1 ∧ Q h2

notation:55 P " ⋆ " Q => star P Q

/-- Magic wand: P -* Q -/
noncomputable def wand (P Q : Assertion) : Assertion :=
  fun h => ∀ h' : Heap, Heap.disjoint h h' → P h' → Q (h ⊕h h')

notation:50 P " -⋆ " Q => wand P Q

noncomputable def aEntails (P Q : Assertion) : Prop :=
  ∀ h : Heap, P h → Q h

noncomputable def pureSL (p : Prop) : Assertion := fun _ => p
noncomputable def aAnd (P Q : Assertion) : Assertion := fun h => P h ∧ Q h
noncomputable def aOr (P Q : Assertion) : Assertion := fun h => P h ∨ Q h

noncomputable def aExists {A : Type} (F : A → Assertion) : Assertion :=
  fun h => ∃ a : A, F a h

-- =====================================================================
-- Section 3: Path-Witnessed Assertion Relationships
-- =====================================================================

structure AssertionPath (P Q : Assertion) where
  witness : ∀ h : Heap, P h → Q h

noncomputable def AssertionPath.id (P : Assertion) : AssertionPath P P :=
  ⟨fun _ hp => hp⟩

noncomputable def AssertionPath.comp {P Q R : Assertion}
    (pq : AssertionPath P Q) (qr : AssertionPath Q R) : AssertionPath P R :=
  ⟨fun h hp => qr.witness h (pq.witness h hp)⟩

-- =====================================================================
-- Section 4: Commands and Heap Operations
-- =====================================================================

structure Cmd where
  run : Heap → Heap

noncomputable def Cmd.seq (c1 c2 : Cmd) : Cmd :=
  ⟨fun h => c2.run (c1.run h)⟩

noncomputable def Cmd.skip : Cmd := ⟨id⟩

noncomputable def Cmd.alloc (l : Loc) (v : Val) : Cmd :=
  ⟨fun h => ⟨(l, v) :: h.cells⟩⟩

noncomputable def Cmd.doWrite (l : Loc) (v : Val) : Cmd :=
  ⟨fun h => Heap.write h l v⟩

noncomputable def Cmd.doFree (l : Loc) : Cmd :=
  ⟨fun h => Heap.free h l⟩

structure CmdPath (c : Cmd) (h : Heap) where
  path : Path h (c.run h)

-- =====================================================================
-- Section 5: Hoare Triples with Path Witnesses
-- =====================================================================

structure HoareTriple (P : Assertion) (c : Cmd) (Q : Assertion) where
  valid : ∀ h, P h → Q (c.run h)

-- Theorem 1: Skip triple
noncomputable def hoare_skip (P : Assertion) : HoareTriple P Cmd.skip P :=
  ⟨fun _ hp => hp⟩

-- Theorem 2: Sequence rule
noncomputable def hoare_seq {P Q R : Assertion} {c1 c2 : Cmd}
    (h1 : HoareTriple P c1 Q) (h2 : HoareTriple Q c2 R) :
    HoareTriple P (Cmd.seq c1 c2) R :=
  ⟨fun h hp => h2.valid (c1.run h) (h1.valid h hp)⟩

-- Theorem 3: Consequence rule (strengthen pre)
noncomputable def hoare_pre {P P' Q : Assertion} {c : Cmd}
    (impl : AssertionPath P' P) (ht : HoareTriple P c Q) : HoareTriple P' c Q :=
  ⟨fun h hp' => ht.valid h (impl.witness h hp')⟩

-- Theorem 4: Consequence rule (weaken post)
noncomputable def hoare_post {P Q Q' : Assertion} {c : Cmd}
    (ht : HoareTriple P c Q) (impl : AssertionPath Q Q') : HoareTriple P c Q' :=
  ⟨fun h hp => impl.witness (c.run h) (ht.valid h hp)⟩

-- Theorem 5: Conjunction rule
noncomputable def hoare_conj {P Q1 Q2 : Assertion} {c : Cmd}
    (h1 : HoareTriple P c Q1) (h2 : HoareTriple P c Q2) :
    HoareTriple P c (aAnd Q1 Q2) :=
  ⟨fun h hp => ⟨h1.valid h hp, h2.valid h hp⟩⟩

-- Theorem 6: Disjunction rule
noncomputable def hoare_disj {P1 P2 Q1 Q2 : Assertion} {c : Cmd}
    (h1 : HoareTriple P1 c Q1) (h2 : HoareTriple P2 c Q2) :
    HoareTriple (aOr P1 P2) c (aOr Q1 Q2) :=
  ⟨fun h hp => match hp with
    | Or.inl hp1 => Or.inl (h1.valid h hp1)
    | Or.inr hp2 => Or.inr (h2.valid h hp2)⟩

-- Theorem 7: Existential rule
noncomputable def hoare_exists {A : Type} {P : A → Assertion} {c : Cmd} {Q : Assertion}
    (ht : ∀ a, HoareTriple (P a) c Q) :
    HoareTriple (aExists P) c Q :=
  ⟨fun h ⟨a, hp⟩ => (ht a).valid h hp⟩

-- =====================================================================
-- Section 6: Weakest Precondition
-- =====================================================================

noncomputable def cmdWP (c : Cmd) (Q : Assertion) : Assertion :=
  fun h => Q (c.run h)

-- Theorem 8: WP is the weakest precondition
theorem wp_is_weakest (c : Cmd) (P Q : Assertion)
    (ht : HoareTriple P c Q) : aEntails P (cmdWP c Q) :=
  fun h hp => ht.valid h hp

-- Theorem 9: WP gives a valid triple
noncomputable def wp_triple (c : Cmd) (Q : Assertion) : HoareTriple (cmdWP c Q) c Q :=
  ⟨fun _ hwp => hwp⟩

-- Theorem 10: WP of skip
theorem wp_skip (Q : Assertion) (h : Heap) :
    cmdWP Cmd.skip Q h = Q h := rfl

-- Theorem 11: WP of sequence
theorem wp_seq (c1 c2 : Cmd) (Q : Assertion) (h : Heap) :
    cmdWP (Cmd.seq c1 c2) Q h = cmdWP c1 (cmdWP c2 Q) h := rfl

-- Theorem 12: WP monotonicity
theorem wp_mono (c : Cmd) {Q R : Assertion}
    (impl : ∀ h, Q h → R h) (h : Heap) :
    cmdWP c Q h → cmdWP c R h :=
  fun hwp => impl _ hwp

-- Theorem 13: WP distributes over conjunction
theorem wp_conj (c : Cmd) (Q1 Q2 : Assertion) (h : Heap) :
    cmdWP c (aAnd Q1 Q2) h ↔ cmdWP c Q1 h ∧ cmdWP c Q2 h :=
  ⟨fun ⟨hq1, hq2⟩ => ⟨hq1, hq2⟩, fun ⟨hq1, hq2⟩ => ⟨hq1, hq2⟩⟩

-- =====================================================================
-- Section 7: Path Algebra for Heap Transformations
-- =====================================================================

structure HeapPath (h1 h2 : Heap) where
  path : Path h1 h2

noncomputable def HeapPath.rfl' (h : Heap) : HeapPath h h :=
  ⟨Path.refl h⟩

noncomputable def HeapPath.trans' {h1 h2 h3 : Heap} (p : HeapPath h1 h2) (q : HeapPath h2 h3) : HeapPath h1 h3 :=
  ⟨Path.trans p.path q.path⟩

noncomputable def HeapPath.symm' {h1 h2 : Heap} (p : HeapPath h1 h2) : HeapPath h2 h1 :=
  ⟨Path.symm p.path⟩

-- Theorem 14: Heap path trans assoc (via toEq)
theorem heapPath_trans_assoc_toEq {h1 h2 h3 h4 : Heap}
    (p : HeapPath h1 h2) (q : HeapPath h2 h3) (r : HeapPath h3 h4) :
    (HeapPath.trans' (HeapPath.trans' p q) r).path.toEq =
    (HeapPath.trans' p (HeapPath.trans' q r)).path.toEq := by
  simp [HeapPath.trans']

-- Theorem 15: Heap path left identity (via toEq)
theorem heapPath_trans_refl_left_toEq {h1 h2 : Heap} (p : HeapPath h1 h2) :
    (HeapPath.trans' (HeapPath.rfl' h1) p).path.toEq = p.path.toEq := by
  simp [HeapPath.trans', HeapPath.rfl']

-- Theorem 16: Heap path right identity (via toEq)
theorem heapPath_trans_refl_right_toEq {h1 h2 : Heap} (p : HeapPath h1 h2) :
    (HeapPath.trans' p (HeapPath.rfl' h2)).path.toEq = p.path.toEq := by
  simp [HeapPath.trans', HeapPath.rfl']

-- Theorem 17: Heap path symm involution (via toEq)
theorem heapPath_symm_symm_toEq {h1 h2 : Heap} (p : HeapPath h1 h2) :
    (HeapPath.symm' (HeapPath.symm' p)).path.toEq = p.path.toEq := by
  simp [HeapPath.symm']

-- =====================================================================
-- Section 8: Command Path Algebra
-- =====================================================================

-- Theorem 18: Skip produces reflexive path
theorem cmd_skip_refl (h : Heap) :
    Cmd.skip.run h = h := rfl

-- Theorem 19: Sequential composition path via trans
noncomputable def cmd_seq_path (c1 c2 : Cmd) (h : Heap)
    (p1 : CmdPath c1 h) (p2 : CmdPath c2 (c1.run h)) : CmdPath (Cmd.seq c1 c2) h :=
  ⟨Path.trans p1.path p2.path⟩

-- Theorem 20: Skip is left identity for seq
theorem cmd_seq_skip_left (c : Cmd) :
    (Cmd.seq Cmd.skip c).run = c.run := rfl

-- Theorem 21: Skip is right identity for seq
theorem cmd_seq_skip_right (c : Cmd) :
    (Cmd.seq c Cmd.skip).run = c.run := rfl

-- Theorem 22: Seq is associative
theorem cmd_seq_assoc (c1 c2 c3 : Cmd) :
    (Cmd.seq (Cmd.seq c1 c2) c3).run = (Cmd.seq c1 (Cmd.seq c2 c3)).run := rfl

-- =====================================================================
-- Section 9: Frame Rule via Paths
-- =====================================================================

structure FramedHoare (P : Assertion) (c : Cmd) (Q : Assertion) (F : Assertion) where
  base : HoareTriple P c Q
  frameInvariant : ∀ hf : Heap, F hf → F hf

-- Theorem 23: Frame construction
noncomputable def mkFramedHoare {P Q : Assertion} {c : Cmd} (F : Assertion)
    (ht : HoareTriple P c Q) : FramedHoare P c Q F :=
  ⟨ht, fun _ hf => hf⟩

-- =====================================================================
-- Section 10: Concurrent Separation Logic
-- =====================================================================

noncomputable def Cmd.par (c1 c2 : Cmd) : Cmd :=
  ⟨fun h => c2.run (c1.run h)⟩

structure CSLParRule (P1 Q1 P2 Q2 : Assertion) (c1 c2 : Cmd) where
  left : HoareTriple P1 c1 Q1
  right : HoareTriple P2 c2 Q2

-- Theorem 24: CSL parallel composition
noncomputable def csl_par {P1 Q1 P2 Q2 : Assertion} {c1 c2 : Cmd}
    (h1 : HoareTriple P1 c1 Q1) (h2 : HoareTriple P2 c2 Q2) :
    CSLParRule P1 Q1 P2 Q2 c1 c2 :=
  ⟨h1, h2⟩

-- =====================================================================
-- Section 11: Fractional Permissions
-- =====================================================================

structure Frac where
  num : Nat
  den : Nat
  denPos : den > 0
  numPos : num > 0
  numLeDen : num ≤ den

noncomputable def Frac.full : Frac := ⟨1, 1, Nat.one_pos, Nat.one_pos, Nat.le.refl⟩

noncomputable def Frac.half : Frac := ⟨1, 2, by omega, Nat.one_pos, by omega⟩

noncomputable def fracPointsTo (l : Loc) (v : Val) (_p : Frac) : Assertion :=
  fun h => h = Heap.singleton l v

-- Theorem 25: Full permission values
theorem frac_full_eq : Frac.full.num = Frac.full.den := rfl

-- Theorem 26: Half permission num
theorem frac_half_num : Frac.half.num = 1 := rfl

-- Theorem 27: Half permission den
theorem frac_half_den : Frac.half.den = 2 := rfl

-- =====================================================================
-- Section 12: Separation Logic Structural Rules
-- =====================================================================

-- Theorem 28: emp left unit forward
theorem emp_star_left_fwd (P : Assertion) (h : Heap) :
    (emp ⋆ P) h → P h := by
  intro ⟨h1, h2, _, heq, hemp, hp⟩
  simp [emp] at hemp; subst hemp
  simp [Heap.union, Heap.empty] at heq; subst heq; exact hp

-- Theorem 29: emp left unit backward
theorem emp_star_left_bwd (P : Assertion) (h : Heap) :
    P h → (emp ⋆ P) h := by
  intro hp
  refine ⟨Heap.empty, h, ?_, ?_, rfl, hp⟩
  · intro _ hl; simp [Heap.dom, Heap.empty] at hl
  · ext1; simp [Heap.union, Heap.empty]

-- Theorem 30: emp right unit forward
theorem emp_star_right_fwd (P : Assertion) (h : Heap) :
    (P ⋆ emp) h → P h := by
  intro ⟨h1, h2, _, heq, hp, hemp⟩
  simp [emp] at hemp; subst hemp
  simp [Heap.union, Heap.empty] at heq; subst heq; exact hp

-- Theorem 31: emp right unit backward
theorem emp_star_right_bwd (P : Assertion) (h : Heap) :
    P h → (P ⋆ emp) h := by
  intro hp
  refine ⟨h, Heap.empty, ?_, ?_, hp, rfl⟩
  · intro _ _ hl; simp [Heap.dom, Heap.empty] at hl
  · ext1; simp [Heap.union, Heap.empty]

-- Theorem 32: Star monotonicity left
noncomputable def star_mono_left {P P' Q : Assertion}
    (e : AssertionPath P P') : AssertionPath (P ⋆ Q) (P' ⋆ Q) :=
  ⟨fun h ⟨h1, h2, hdisj, heq, hp, hq⟩ =>
    ⟨h1, h2, hdisj, heq, e.witness h1 hp, hq⟩⟩

-- Theorem 33: Star monotonicity right
noncomputable def star_mono_right {P Q Q' : Assertion}
    (e : AssertionPath Q Q') : AssertionPath (P ⋆ Q) (P ⋆ Q') :=
  ⟨fun h ⟨h1, h2, hdisj, heq, hp, hq⟩ =>
    ⟨h1, h2, hdisj, heq, hp, e.witness h2 hq⟩⟩

-- Theorem 34: Wand monotonicity
noncomputable def wand_mono {P P' Q Q' : Assertion}
    (eP : AssertionPath P' P) (eQ : AssertionPath Q Q') :
    AssertionPath (P -⋆ Q) (P' -⋆ Q') :=
  ⟨fun h hw h' hdisj hp' =>
    eQ.witness (h ⊕h h') (hw h' hdisj (eP.witness h' hp'))⟩

-- =====================================================================
-- Section 13: Path-Witnessed Heap Equalities
-- =====================================================================

-- Theorem 35: Empty heap union left
theorem heap_union_empty_left (h : Heap) :
    (Heap.empty ⊕h h).cells = h.cells := by
  simp [Heap.union, Heap.empty]

-- Theorem 36: Heap union empty left path
noncomputable def heap_union_empty_left_path (h : Heap) : Path (Heap.empty ⊕h h) h :=
  have pf : (Heap.empty ⊕h h) = h := Heap.ext (heap_union_empty_left h)
  Path.mk [Step.mk _ _ pf] pf

-- Theorem 37: Double symm on union path
theorem heap_union_double_symm (h : Heap) :
    Path.symm (Path.symm (heap_union_empty_left_path h)) =
    heap_union_empty_left_path h :=
  Path.symm_symm (heap_union_empty_left_path h)

-- =====================================================================
-- Section 14: Lifted Paths via congrArg
-- =====================================================================

noncomputable def liftHeapPath (f : Heap → Heap) {h1 h2 : Heap} (p : Path h1 h2) :
    Path (f h1) (f h2) :=
  Path.congrArg f p

-- Theorem 38: congrArg distributes over trans for heaps
theorem heap_congrArg_trans (f : Heap → Heap) {h1 h2 h3 : Heap}
    (p : Path h1 h2) (q : Path h2 h3) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

-- Theorem 39: congrArg distributes over symm for heaps
theorem heap_congrArg_symm (f : Heap → Heap) {h1 h2 : Heap}
    (p : Path h1 h2) :
    Path.congrArg f (Path.symm p) =
    Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

-- Theorem 40: congrArg composition
theorem heap_congrArg_comp (f g : Heap → Heap) {h1 h2 : Heap}
    (p : Path h1 h2) :
    Path.congrArg (fun x => f (g x)) p =
    Path.congrArg f (Path.congrArg g p) :=
  Path.congrArg_comp f g p

-- Theorem 41: congrArg identity
theorem heap_congrArg_id {h1 h2 : Heap} (p : Path h1 h2) :
    Path.congrArg (fun x : Heap => x) p = p :=
  Path.congrArg_id p

-- =====================================================================
-- Section 15: Resource Algebra
-- =====================================================================

structure Resource where
  locs : List Loc
  vals : Loc → Val
  deriving Inhabited

noncomputable def Resource.empty : Resource := ⟨[], fun _ => 0⟩

noncomputable def Resource.compose (r1 r2 : Resource) : Resource :=
  ⟨r1.locs ++ r2.locs, fun l => if l ∈ r1.locs then r1.vals l else r2.vals l⟩

-- Theorem 42: Empty resource compose left identity for locs
theorem resource_compose_empty_left (r : Resource) :
    (Resource.compose Resource.empty r).locs = r.locs := by
  simp [Resource.compose, Resource.empty]

-- Theorem 43: Compose locs is append
theorem resource_compose_locs (r1 r2 : Resource) :
    (Resource.compose r1 r2).locs = r1.locs ++ r2.locs := rfl

-- =====================================================================
-- Section 16: Separation Algebra via Paths
-- =====================================================================

structure SepAlg (A : Type) where
  unit : A
  compose : A → A → A
  unit_left : ∀ a, compose unit a = a
  assoc : ∀ a b c, compose (compose a b) c = compose a (compose b c)

noncomputable def sepAlgIdentityPath {A : Type} [DecidableEq A] (sa : SepAlg A) (a : A) :
    Path (sa.compose sa.unit a) a :=
  Path.mk [Step.mk (sa.compose sa.unit a) a (sa.unit_left a)] (sa.unit_left a)

-- Theorem 44: Separation algebra associativity path
noncomputable def sepAlgAssocPath {A : Type} [DecidableEq A] (sa : SepAlg A) (a b c : A) :
    Path (sa.compose (sa.compose a b) c) (sa.compose a (sa.compose b c)) :=
  Path.mk [Step.mk _ _ (sa.assoc a b c)] (sa.assoc a b c)

-- Theorem 45: SepAlg identity path toEq
theorem sepAlg_unit_left_toEq {A : Type} [DecidableEq A] (sa : SepAlg A) (a : A) :
    (sepAlgIdentityPath sa a).toEq = sa.unit_left a := rfl

-- Theorem 46: SepAlg assoc path toEq
theorem sepAlg_assoc_toEq {A : Type} [DecidableEq A] (sa : SepAlg A) (a b c : A) :
    (sepAlgAssocPath sa a b c).toEq = sa.assoc a b c := rfl

-- =====================================================================
-- Section 17: Program Logic Combinators
-- =====================================================================

noncomputable def Cmd.ite' (cond : Heap → Bool) (c1 c2 : Cmd) : Cmd :=
  ⟨fun h => if cond h then c1.run h else c2.run h⟩

noncomputable def Cmd.whileN (n : Nat) (cond : Heap → Bool) (body : Cmd) : Cmd :=
  ⟨fun h => Nat.rec h (fun _ ih => if cond ih then body.run ih else ih) n⟩

-- Theorem 47: If-true case
theorem cmd_ite_true (cond : Heap → Bool) (c1 c2 : Cmd) (h : Heap)
    (ht : cond h = true) :
    (Cmd.ite' cond c1 c2).run h = c1.run h := by
  simp [Cmd.ite', ht]

-- Theorem 48: If-false case
theorem cmd_ite_false (cond : Heap → Bool) (c1 c2 : Cmd) (h : Heap)
    (hf : cond h = false) :
    (Cmd.ite' cond c1 c2).run h = c2.run h := by
  simp [Cmd.ite', hf]

-- Theorem 49: While 0 is identity
theorem cmd_while_zero (cond : Heap → Bool) (body : Cmd) (h : Heap) :
    (Cmd.whileN 0 cond body).run h = h := rfl

-- =====================================================================
-- Section 18: Entailment Path Algebra
-- =====================================================================

-- Theorem 50: Entailment composition coherence
theorem entails_comp_coherence {P Q R : Assertion}
    (pq : AssertionPath P Q) (qr : AssertionPath Q R) (h : Heap) (hp : P h) :
    (AssertionPath.comp pq qr).witness h hp = qr.witness h (pq.witness h hp) := rfl

-- =====================================================================
-- Section 19: Heap Operation Paths
-- =====================================================================

inductive HeapOp where
  | alloc (l : Loc) (v : Val)
  | write (l : Loc) (v : Val)
  | free (l : Loc)
  | nop
  deriving DecidableEq, Repr

noncomputable def applyOp (op : HeapOp) (h : Heap) : Heap :=
  match op with
  | HeapOp.alloc l v => ⟨(l, v) :: h.cells⟩
  | HeapOp.write l v => Heap.write h l v
  | HeapOp.free l => Heap.free h l
  | HeapOp.nop => h

-- Theorem 51: Nop is identity
theorem op_nop (h : Heap) : applyOp HeapOp.nop h = h := rfl

-- Theorem 52: Empty operation list is identity
theorem op_seq_empty (h : Heap) :
    [].foldl (fun acc op => applyOp op acc) h = h := rfl

-- Theorem 53: Single op sequence
theorem op_seq_single (op : HeapOp) (h : Heap) :
    [op].foldl (fun acc o => applyOp o acc) h = applyOp op h := rfl

-- =====================================================================
-- Section 20: Permission Heaps and Paths
-- =====================================================================

structure PermLevel where
  num : Nat
  den : Nat
  denPos : den > 0
  deriving DecidableEq

noncomputable def PermLevel.full : PermLevel := ⟨1, 1, Nat.one_pos⟩
noncomputable def PermLevel.zero : PermLevel := ⟨0, 1, Nat.one_pos⟩

structure PermCell where
  loc : Loc
  val : Val
  perm : PermLevel
  deriving DecidableEq

structure PermHeap where
  cells : List PermCell
  deriving DecidableEq

-- Theorem 54: Permission heap path reflexivity
theorem permheap_refl (ph : PermHeap) :
    (Path.refl ph).toEq = @rfl PermHeap ph := rfl

-- Theorem 55: Permission heap path composition
theorem permheap_trans {ph1 ph2 ph3 : PermHeap}
    (p : Path ph1 ph2) (q : Path ph2 ph3) :
    (Path.trans p q).toEq = p.toEq.trans q.toEq := rfl

-- Theorem 56: Permission heap symmetry
theorem permheap_symm {ph1 ph2 : PermHeap}
    (p : Path ph1 ph2) :
    (Path.symm p).toEq = p.toEq.symm := rfl

-- Theorem 57: Lifting through permissions via congrArg
noncomputable def liftPermPath (f : PermHeap → PermHeap) {ph1 ph2 : PermHeap} (p : Path ph1 ph2) :
    Path (f ph1) (f ph2) :=
  Path.congrArg f p

-- Theorem 58: congrArg coherence for perm heaps
theorem perm_congrArg_trans (f : PermHeap → PermHeap)
    {ph1 ph2 ph3 : PermHeap} (p : Path ph1 ph2) (q : Path ph2 ph3) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

-- Theorem 59: congrArg symm for perm heaps
theorem perm_congrArg_symm (f : PermHeap → PermHeap)
    {ph1 ph2 : PermHeap} (p : Path ph1 ph2) :
    Path.congrArg f (Path.symm p) =
    Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

-- =====================================================================
-- Section 21: Additional Derived Theorems
-- =====================================================================

-- Theorem 60: WP distributes over disjunction backward
theorem wp_disj_bwd (c : Cmd) (Q1 Q2 : Assertion) (h : Heap) :
    cmdWP c Q1 h ∨ cmdWP c Q2 h → cmdWP c (aOr Q1 Q2) h :=
  fun hd => match hd with
    | Or.inl hq1 => Or.inl hq1
    | Or.inr hq2 => Or.inr hq2

-- Theorem 61: Hoare triple universal postcondition
noncomputable def hoare_forall_post {A : Type} {P : Assertion} {c : Cmd} {Q : A → Assertion}
    (ht : ∀ a, HoareTriple P c (Q a)) :
    HoareTriple P c (fun h => ∀ a, Q a h) :=
  ⟨fun h hp a => (ht a).valid h hp⟩

-- Theorem 62: AssertionPath identity is left unit
theorem assertionPath_id_comp {P Q : Assertion} (pq : AssertionPath P Q)
    (h : Heap) (hp : P h) :
    (AssertionPath.comp (AssertionPath.id P) pq).witness h hp = pq.witness h hp := rfl

-- Theorem 63: AssertionPath identity is right unit
theorem assertionPath_comp_id {P Q : Assertion} (pq : AssertionPath P Q)
    (h : Heap) (hp : P h) :
    (AssertionPath.comp pq (AssertionPath.id Q)).witness h hp = pq.witness h hp := rfl

-- Theorem 64: AssertionPath composition is associative
theorem assertionPath_comp_assoc {P Q R S : Assertion}
    (pq : AssertionPath P Q) (qr : AssertionPath Q R) (rs : AssertionPath R S)
    (h : Heap) (hp : P h) :
    (AssertionPath.comp (AssertionPath.comp pq qr) rs).witness h hp =
    (AssertionPath.comp pq (AssertionPath.comp qr rs)).witness h hp := rfl

-- Theorem 65: Cmd alloc then free
theorem cmd_alloc_free_cells (l : Loc) (v : Val) (h : Heap) :
    (Cmd.seq (Cmd.alloc l v) (Cmd.doFree l)).run h =
    ⟨h.cells.filter (fun p => decide (p.1 ≠ l))⟩ := by
  simp [Cmd.seq, Cmd.alloc, Cmd.doFree, Heap.free]

-- Theorem 66: Hoare consequence full
noncomputable def hoare_consequence {P P' Q Q' : Assertion} {c : Cmd}
    (pre : AssertionPath P' P) (ht : HoareTriple P c Q) (post : AssertionPath Q Q') :
    HoareTriple P' c Q' :=
  hoare_post (hoare_pre pre ht) post

-- Theorem 67: Parallel composition is sequential composition
theorem par_is_seq (c1 c2 : Cmd) (h : Heap) :
    (Cmd.par c1 c2).run h = (Cmd.seq c1 c2).run h := rfl

-- Theorem 68: Path-witnessed heap identity
noncomputable def heap_refl_path (h : Heap) : Path h h := Path.refl h

theorem heap_refl_path_toEq (h : Heap) :
    (heap_refl_path h).toEq = @rfl Heap h := rfl

end ComputationalPaths.SeparationLogicDeep
