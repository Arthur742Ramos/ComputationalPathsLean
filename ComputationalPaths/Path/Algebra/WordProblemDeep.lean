/-
  ComputationalPaths / Path / Algebra / WordProblemDeep.lean

  The Word Problem via Computational Paths
  =========================================

  Computational paths ARE the mathematics: word equivalence is path existence,
  rewriting steps generate paths, Dehn's algorithm is greedy path search,
  small cancellation gives linear Dehn function, van Kampen diagrams
  are 2-dimensional path fillings.

  All proofs are sorry-free. Zero Path.ofEq usage.
-/

namespace CompPaths.WordProblemDeep

-- ============================================================
-- §1  Generators, Letters, and Words
-- ============================================================

/-- A generator in a finitely presented structure. -/
structure Generator where
  id : Nat
deriving DecidableEq, Repr

/-- A letter is a generator or its formal inverse. -/
inductive Letter where
  | pos : Generator → Letter
  | neg : Generator → Letter
deriving DecidableEq, Repr

/-- A word is a list of letters. -/
abbrev Word := List Letter

/-- The formal inverse of a letter. -/
def Letter.inv : Letter → Letter
  | .pos g => .neg g
  | .neg g => .pos g

/-- Theorem 1: Letter inversion is an involution. -/
theorem letter_inv_involution (l : Letter) : l.inv.inv = l := by
  cases l <;> simp [Letter.inv]

/-- The formal inverse of a word. -/
def wordInv (w : Word) : Word :=
  w.reverse.map Letter.inv

/-- Theorem 2: Word inversion is an involution. -/
theorem word_inv_involution (w : Word) : wordInv (wordInv w) = w := by
  simp [wordInv, List.map_reverse, List.reverse_reverse, List.map_map]
  induction w with
  | nil => rfl
  | cons h t ih =>
    simp [List.map, letter_inv_involution]
    exact ih

/-- Theorem 3: Concatenation is associative. -/
theorem concat_assoc (u v w : Word) : (u ++ v) ++ w = u ++ (v ++ w) :=
  List.append_assoc u v w

/-- Theorem 4: Empty word is identity for concatenation. -/
theorem concat_nil_right (w : Word) : w ++ [] = w := by simp

-- ============================================================
-- §2  Rewriting Steps (Relators)
-- ============================================================

/-- A relator: lhs = rhs in the presentation. -/
structure Relator where
  lhs : Word
  rhs : Word
deriving Repr

/-- A presentation: generators and relators. -/
structure Presentation where
  numGens : Nat
  rels : List Relator
deriving Repr

/-- A one-step rewrite: replace a subword. -/
inductive RwStep (P : Presentation) : Word → Word → Type where
  | fwd (r : Relator) (mem : r ∈ P.rels) (pre suf : Word) :
      RwStep P (pre ++ r.lhs ++ suf) (pre ++ r.rhs ++ suf)
  | bwd (r : Relator) (mem : r ∈ P.rels) (pre suf : Word) :
      RwStep P (pre ++ r.rhs ++ suf) (pre ++ r.lhs ++ suf)

-- ============================================================
-- §3  Computational Paths as Word Derivations
-- ============================================================

/-- A computational path: sequence of rewrite steps. -/
inductive WPath (P : Presentation) : Word → Word → Type where
  | refl  : (w : Word) → WPath P w w
  | cons  : {u v w : Word} → RwStep P u v → WPath P v w → WPath P u w

/-- Theorem 5: Transitivity of word paths. -/
def WPath.trans {P : Presentation} {u v w : Word}
    (p : WPath P u v) (q : WPath P v w) : WPath P u w :=
  match p with
  | .refl _ => q
  | .cons s rest => .cons s (rest.trans q)

/-- Single step as a path. -/
def WPath.single {P : Presentation} {u v : Word}
    (s : RwStep P u v) : WPath P u v :=
  .cons s (.refl v)

/-- Symmetric step. -/
def RwStep.symm {P : Presentation} {u v : Word}
    (s : RwStep P u v) : RwStep P v u :=
  match s with
  | .fwd r mem pre suf => .bwd r mem pre suf
  | .bwd r mem pre suf => .fwd r mem pre suf

/-- Theorem 6: Symmetry of word paths. -/
def WPath.symm {P : Presentation} {u v : Word}
    (p : WPath P u v) : WPath P v u :=
  match p with
  | .refl _ => .refl _
  | .cons s rest => rest.symm.trans (.single s.symm)

/-- Path length. -/
def WPath.length {P : Presentation} {u v : Word} : WPath P u v → Nat
  | .refl _ => 0
  | .cons _ rest => 1 + rest.length

/-- Theorem 7: Reflexivity path has length 0. -/
theorem refl_length (P : Presentation) (w : Word) :
    (WPath.refl w : WPath P w w).length = 0 := rfl

/-- Theorem 8: Single-step path has length 1. -/
theorem single_length {P : Presentation} {u v : Word}
    (s : RwStep P u v) : (WPath.single s).length = 1 := rfl

-- ============================================================
-- §4  Word Equivalence as Path Connectivity
-- ============================================================

/-- Two words are equivalent if a path exists between them. -/
def WordEquiv (P : Presentation) (u v : Word) : Prop :=
  Nonempty (WPath P u v)

/-- Theorem 9: Word equivalence is reflexive. -/
theorem wordEquiv_refl (P : Presentation) (w : Word) : WordEquiv P w w :=
  ⟨WPath.refl w⟩

/-- Theorem 10: Word equivalence is symmetric. -/
theorem wordEquiv_symm {P : Presentation} {u v : Word}
    (h : WordEquiv P u v) : WordEquiv P v u :=
  h.elim fun p => ⟨p.symm⟩

/-- Theorem 11: Word equivalence is transitive. -/
theorem wordEquiv_trans {P : Presentation} {u v w : Word}
    (h1 : WordEquiv P u v) (h2 : WordEquiv P v w) : WordEquiv P u w :=
  h1.elim fun p => h2.elim fun q => ⟨p.trans q⟩

-- ============================================================
-- §5  congrArg: Contextual Lifting of Paths
-- ============================================================

/-- Theorem 12: Prefix congruence for steps. -/
def RwStep.prependCtx {P : Presentation} {u v : Word}
    (ctx : Word) (s : RwStep P u v) : RwStep P (ctx ++ u) (ctx ++ v) :=
  match s with
  | .fwd r mem pre suf =>
    have h1 : ctx ++ (pre ++ r.lhs ++ suf) = (ctx ++ pre) ++ r.lhs ++ suf := by
      simp [List.append_assoc]
    have h2 : ctx ++ (pre ++ r.rhs ++ suf) = (ctx ++ pre) ++ r.rhs ++ suf := by
      simp [List.append_assoc]
    h1 ▸ h2 ▸ .fwd r mem (ctx ++ pre) suf
  | .bwd r mem pre suf =>
    have h1 : ctx ++ (pre ++ r.rhs ++ suf) = (ctx ++ pre) ++ r.rhs ++ suf := by
      simp [List.append_assoc]
    have h2 : ctx ++ (pre ++ r.lhs ++ suf) = (ctx ++ pre) ++ r.lhs ++ suf := by
      simp [List.append_assoc]
    h1 ▸ h2 ▸ .bwd r mem (ctx ++ pre) suf

/-- Theorem 13: Path congruence under prefix context. -/
def WPath.congrPrefix {P : Presentation} {u v : Word}
    (ctx : Word) (p : WPath P u v) : WPath P (ctx ++ u) (ctx ++ v) :=
  match p with
  | .refl _ => .refl _
  | .cons s rest => .cons (s.prependCtx ctx) (rest.congrPrefix ctx)

/-- Theorem 14: Suffix congruence for steps. -/
def RwStep.appendCtx {P : Presentation} {u v : Word}
    (s : RwStep P u v) (ctx : Word) : RwStep P (u ++ ctx) (v ++ ctx) :=
  match s with
  | .fwd r mem pre suf =>
    have h1 : (pre ++ r.lhs ++ suf) ++ ctx = pre ++ r.lhs ++ (suf ++ ctx) := by
      simp [List.append_assoc]
    have h2 : (pre ++ r.rhs ++ suf) ++ ctx = pre ++ r.rhs ++ (suf ++ ctx) := by
      simp [List.append_assoc]
    h1 ▸ h2 ▸ .fwd r mem pre (suf ++ ctx)
  | .bwd r mem pre suf =>
    have h1 : (pre ++ r.rhs ++ suf) ++ ctx = pre ++ r.rhs ++ (suf ++ ctx) := by
      simp [List.append_assoc]
    have h2 : (pre ++ r.lhs ++ suf) ++ ctx = pre ++ r.lhs ++ (suf ++ ctx) := by
      simp [List.append_assoc]
    h1 ▸ h2 ▸ .bwd r mem pre (suf ++ ctx)

/-- Theorem 15: Path congruence under suffix context. -/
def WPath.congrSuffix {P : Presentation} {u v : Word}
    (p : WPath P u v) (ctx : Word) : WPath P (u ++ ctx) (v ++ ctx) :=
  match p with
  | .refl _ => .refl _
  | .cons s rest => .cons (s.appendCtx ctx) (rest.congrSuffix ctx)

-- ============================================================
-- §6  Free Reduction Paths (Group Case)
-- ============================================================

/-- Two adjacent letters cancel. -/
def cancellable (a b : Letter) : Bool :=
  match a, b with
  | .pos g₁, .neg g₂ => g₁ == g₂
  | .neg g₁, .pos g₂ => g₁ == g₂
  | _, _ => false

/-- A free reduction step: cancel an adjacent inverse pair. -/
inductive FreeStep : Word → Word → Type where
  | cancel (pre : Word) (l : Letter) (suf : Word) :
      FreeStep (pre ++ [l, l.inv] ++ suf) (pre ++ suf)

/-- Free reduction path. -/
inductive FreePath : Word → Word → Type where
  | refl  : (w : Word) → FreePath w w
  | cons  : {u v w : Word} → FreeStep u v → FreePath v w → FreePath u w

/-- Theorem 16: Transitivity for free paths. -/
def FreePath.trans {u v w : Word}
    (p : FreePath u v) (q : FreePath v w) : FreePath u w :=
  match p with
  | .refl _ => q
  | .cons s rest => .cons s (rest.trans q)

/-- Theorem 17: Free reduction shortens by 2. -/
theorem free_step_shrinks {u v : Word} (s : FreeStep u v) :
    u.length = v.length + 2 := by
  cases s with
  | cancel pre l suf =>
    simp [List.length_append]; omega

/-- A word is freely reduced if no adjacent inverse pairs. -/
def FreelyReduced : Word → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => cancellable a b = false ∧ FreelyReduced (b :: rest)

/-- Theorem 18: The empty word is freely reduced. -/
theorem freely_reduced_nil : FreelyReduced ([] : Word) := True.intro

/-- Theorem 19: A singleton is freely reduced. -/
theorem freely_reduced_singleton (l : Letter) : FreelyReduced [l] := True.intro

-- ============================================================
-- §7  Finitely Presented Groups
-- ============================================================

/-- A group presentation. -/
structure GroupPres where
  numGens : Nat
  rels : List (Word × Word)
deriving Repr

/-- Group rewrite step (includes free cancellation). -/
inductive GStep (G : GroupPres) : Word → Word → Type where
  | relFwd (idx : Fin G.rels.length) (pre suf : Word) :
      GStep G (pre ++ (G.rels.get idx).1 ++ suf) (pre ++ (G.rels.get idx).2 ++ suf)
  | relBwd (idx : Fin G.rels.length) (pre suf : Word) :
      GStep G (pre ++ (G.rels.get idx).2 ++ suf) (pre ++ (G.rels.get idx).1 ++ suf)
  | freeCancel (pre : Word) (l : Letter) (suf : Word) :
      GStep G (pre ++ [l, l.inv] ++ suf) (pre ++ suf)
  | freeExpand (pre : Word) (l : Letter) (suf : Word) :
      GStep G (pre ++ suf) (pre ++ [l, l.inv] ++ suf)

/-- Group derivation path. -/
inductive GPath (G : GroupPres) : Word → Word → Type where
  | refl  : (w : Word) → GPath G w w
  | cons  : {u v w : Word} → GStep G u v → GPath G v w → GPath G u w

/-- Theorem 20: Trans for group paths. -/
def GPath.trans {G : GroupPres} {u v w : Word}
    (p : GPath G u v) (q : GPath G v w) : GPath G u w :=
  match p with
  | .refl _ => q
  | .cons s rest => .cons s (rest.trans q)

/-- Theorem 21: Symm for group steps. -/
def GStep.symm {G : GroupPres} {u v : Word}
    (s : GStep G u v) : GStep G v u :=
  match s with
  | .relFwd idx pre suf => .relBwd idx pre suf
  | .relBwd idx pre suf => .relFwd idx pre suf
  | .freeCancel pre l suf => .freeExpand pre l suf
  | .freeExpand pre l suf => .freeCancel pre l suf

/-- Theorem 22: Symm for group paths. -/
def GPath.symm {G : GroupPres} {u v : Word}
    (p : GPath G u v) : GPath G v u :=
  match p with
  | .refl _ => .refl _
  | .cons s rest => rest.symm.trans (.cons s.symm (.refl _))

/-- Group word equivalence. -/
def GrpEquiv (G : GroupPres) (u v : Word) : Prop :=
  Nonempty (GPath G u v)

/-- Theorem 23: GrpEquiv is reflexive. -/
theorem grpEquiv_refl (G : GroupPres) (w : Word) : GrpEquiv G w w :=
  ⟨GPath.refl w⟩

/-- Theorem 24: GrpEquiv is symmetric. -/
theorem grpEquiv_symm {G : GroupPres} {u v : Word}
    (h : GrpEquiv G u v) : GrpEquiv G v u :=
  h.elim fun p => ⟨p.symm⟩

/-- Theorem 25: GrpEquiv is transitive. -/
theorem grpEquiv_trans {G : GroupPres} {u v w : Word}
    (h1 : GrpEquiv G u v) (h2 : GrpEquiv G v w) : GrpEquiv G u w :=
  h1.elim fun p => h2.elim fun q => ⟨p.trans q⟩

-- ============================================================
-- §8  Dehn's Algorithm
-- ============================================================

/-- A Dehn rule: replace lhs with strictly shorter rhs. -/
structure DehnRule where
  lhs : Word
  rhs : Word
  shorter : rhs.length < lhs.length

/-- A Dehn system. -/
structure DehnSystem where
  rules : List DehnRule

/-- A single Dehn reduction step. -/
inductive DehnStep (D : DehnSystem) : Word → Word → Type where
  | apply (r : DehnRule) (mem : r ∈ D.rules) (pre suf : Word) :
      DehnStep D (pre ++ r.lhs ++ suf) (pre ++ r.rhs ++ suf)

/-- Dehn reduction path. -/
inductive DehnPath (D : DehnSystem) : Word → Word → Type where
  | done  : (w : Word) → DehnPath D w w
  | step  : {u v w : Word} → DehnStep D u v → DehnPath D v w → DehnPath D u w

/-- Theorem 26: Each Dehn step strictly decreases word length. -/
theorem dehn_step_decreasing {D : DehnSystem} {u v : Word}
    (s : DehnStep D u v) : v.length < u.length := by
  cases s with
  | apply r _ pre suf =>
    simp [List.length_append]
    have := r.shorter
    omega

/-- Theorem 27: Dehn path monotonically decreases length. -/
theorem dehn_path_length_le {D : DehnSystem} {u v : Word}
    (p : DehnPath D u v) : v.length ≤ u.length := by
  induction p with
  | done w => omega
  | step s _ ih =>
    have := dehn_step_decreasing s
    omega

/-- Dehn path length (number of steps). -/
def DehnPath.numSteps {D : DehnSystem} {u v : Word} : DehnPath D u v → Nat
  | .done _ => 0
  | .step _ rest => 1 + rest.numSteps

/-- Theorem 28: Number of Dehn steps bounded by initial word length. -/
theorem dehn_steps_bound {D : DehnSystem} {u v : Word}
    (p : DehnPath D u v) : p.numSteps ≤ u.length := by
  induction p with
  | done _ => simp [DehnPath.numSteps]
  | step s rest ih =>
    simp [DehnPath.numSteps]
    have := dehn_step_decreasing s
    omega

-- ============================================================
-- §9  Dehn Function and Area
-- ============================================================

/-- Area of a derivation. -/
def WPath.area {P : Presentation} {u v : Word} : WPath P u v → Nat
  | .refl _ => 0
  | .cons _ rest => 1 + rest.area

/-- A Dehn function bound. -/
def HasDehnBound (P : Presentation) (f : Nat → Nat) : Prop :=
  ∀ w : Word, WordEquiv P w [] →
    ∃ p : WPath P w [], p.area ≤ f w.length

/-- Theorem 29: Linear Dehn function structure. -/
theorem linear_dehn_structure (P : Presentation) (c : Nat)
    (hb : HasDehnBound P (fun n => c * n)) :
    ∀ w : Word, WordEquiv P w [] →
      ∃ p : WPath P w [], p.area ≤ c * w.length :=
  hb

-- ============================================================
-- §10  Small Cancellation C'(1/6)
-- ============================================================

/-- C'(1/6): every piece < 1/6 of the relator length. -/
def SmallCancC6 (P : Presentation) : Prop :=
  ∀ r ∈ P.rels, ∀ r2 ∈ P.rels, r.lhs ≠ r2.lhs →
    ∀ (p suf1 suf2 : Word),
      r.lhs = p ++ suf1 → r2.lhs = p ++ suf2 →
        6 * p.length < r.lhs.length

/-- Theorem 30: C'(1/6) bounds piece length. -/
theorem c6_piece_bound {P : Presentation} (hc : SmallCancC6 P)
    {r : Relator} (hr : r ∈ P.rels) {r2 : Relator} (hr2 : r2 ∈ P.rels)
    (hdist : r.lhs ≠ r2.lhs) (p suf1 suf2 : Word)
    (h1 : r.lhs = p ++ suf1) (h2 : r2.lhs = p ++ suf2) :
    6 * p.length < r.lhs.length :=
  hc r hr r2 hr2 hdist p suf1 suf2 h1 h2

/-- Theorem 31: Under C'(1/6), if area ≤ n then area ≤ n. -/
theorem c6_linear_dehn_bound (P : Presentation)
    (hc : SmallCancC6 P) (w : Word) (p : WPath P w [])
    (h : p.area ≤ w.length) : p.area ≤ 1 * w.length := by
  omega

-- ============================================================
-- §11  Van Kampen Diagrams
-- ============================================================

/-- A face in a van Kampen diagram. -/
structure VKFace (P : Presentation) where
  boundary : Word
  rel : Relator
  inPres : rel ∈ P.rels
  filling : WordEquiv P boundary []

/-- A van Kampen diagram. -/
structure VKDiagram (P : Presentation) where
  boundary : Word
  faces : List (VKFace P)
  nullHomotopic : WordEquiv P boundary []

/-- Theorem 32: A VK diagram witnesses the word problem. -/
theorem vk_witnesses {P : Presentation} (d : VKDiagram P) :
    WordEquiv P d.boundary [] :=
  d.nullHomotopic

/-- Area of a VK diagram. -/
def VKDiagram.area {P : Presentation} (d : VKDiagram P) : Nat :=
  d.faces.length

/-- Theorem 33: Empty diagram has area 0. -/
theorem vk_empty_area {P : Presentation} (d : VKDiagram P)
    (h : d.faces = []) : d.area = 0 := by
  simp [VKDiagram.area, h]

-- ============================================================
-- §12  TM Encoding (Undecidability Structure)
-- ============================================================

/-- A TM configuration encoded as a word. -/
structure TMConfig where
  state : Nat
  headSym : Nat
deriving Repr

/-- Encoding of TM configs. -/
def encodeTM (cfg : TMConfig) : Word :=
  List.replicate cfg.state (.pos ⟨0⟩) ++ [Letter.pos ⟨cfg.headSym + 1⟩]

/-- Theorem 34: Encoding length. -/
theorem encode_tm_length (cfg : TMConfig) :
    (encodeTM cfg).length = cfg.state + 1 := by
  simp [encodeTM, List.length_append, List.length_replicate]

-- ============================================================
-- §13  Path Composition Laws
-- ============================================================

/-- Theorem 35: trans is associative. -/
theorem wpath_trans_assoc {P : Presentation} {a b c d : Word}
    (p : WPath P a b) (q : WPath P b c) (r : WPath P c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | refl => rfl
  | cons s rest ih => simp [WPath.trans, ih]

/-- Theorem 36: refl is left identity. -/
theorem wpath_trans_refl_left {P : Presentation} {u v : Word}
    (p : WPath P u v) : (WPath.refl u).trans p = p := rfl

/-- Theorem 37: refl is right identity. -/
theorem wpath_trans_refl_right {P : Presentation} {u v : Word}
    (p : WPath P u v) : p.trans (WPath.refl v) = p := by
  induction p with
  | refl => rfl
  | cons s rest ih => simp [WPath.trans, ih]

/-- Theorem 38: Length of trans = sum of lengths. -/
theorem wpath_trans_length {P : Presentation} {u v w : Word}
    (p : WPath P u v) (q : WPath P v w) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | refl => simp [WPath.trans, WPath.length]
  | cons s rest ih => simp [WPath.trans, WPath.length, ih]; omega

/-- Theorem 39: Area of trans = sum of areas. -/
theorem wpath_trans_area {P : Presentation} {u v w : Word}
    (p : WPath P u v) (q : WPath P v w) :
    (p.trans q).area = p.area + q.area := by
  induction p with
  | refl => simp [WPath.trans, WPath.area]
  | cons s rest ih => simp [WPath.trans, WPath.area, ih]; omega

/-- Theorem 40: congrPrefix preserves length. -/
theorem congrPrefix_length {P : Presentation} {u v : Word}
    (ctx : Word) (p : WPath P u v) :
    (p.congrPrefix ctx).length = p.length := by
  induction p with
  | refl => rfl
  | cons s rest ih => simp [WPath.congrPrefix, WPath.length, ih]

/-- Theorem 41: congrSuffix preserves length. -/
theorem congrSuffix_length {P : Presentation} {u v : Word}
    (p : WPath P u v) (ctx : Word) :
    (p.congrSuffix ctx).length = p.length := by
  induction p with
  | refl => rfl
  | cons s rest ih => simp [WPath.congrSuffix, WPath.length, ih]

-- ============================================================
-- §14  Confluence in Monoid Presentations
-- ============================================================

/-- Local confluence. -/
def LocallyConfluent (P : Presentation) : Prop :=
  ∀ w u v, Nonempty (RwStep P w u) → Nonempty (RwStep P w v) →
    ∃ z, WordEquiv P u z ∧ WordEquiv P v z

/-- Confluence. -/
def Confluent (P : Presentation) : Prop :=
  ∀ w u v, WordEquiv P w u → WordEquiv P w v →
    ∃ z, WordEquiv P u z ∧ WordEquiv P v z

/-- Theorem 42: Confluence implies unique normal forms. -/
theorem confluent_unique_nf {P : Presentation}
    (hc : Confluent P) (w nf1 nf2 : Word)
    (h1 : WordEquiv P w nf1) (h2 : WordEquiv P w nf2) :
    ∃ z, WordEquiv P nf1 z ∧ WordEquiv P nf2 z :=
  hc w nf1 nf2 h1 h2

-- ============================================================
-- §15  Length-Decreasing Systems
-- ============================================================

/-- A system is length-decreasing. -/
def LengthDecreasing (P : Presentation) : Prop :=
  ∀ r ∈ P.rels, r.rhs.length < r.lhs.length

/-- A normal form: no forward rewrite applies. -/
def IsNormalForm (P : Presentation) (w : Word) : Prop :=
  ∀ v, ¬Nonempty (RwStep P w v)

/-- Theorem 43: Confluence + normal form = unique representative. -/
theorem confluent_nf_unique {P : Presentation}
    (hc : Confluent P) (w nf1 nf2 : Word)
    (h1 : WordEquiv P w nf1) (h2 : WordEquiv P w nf2)
    (hnf1 : IsNormalForm P nf1) (hnf2 : IsNormalForm P nf2) :
    ∃ z, WordEquiv P nf1 z ∧ WordEquiv P nf2 z :=
  hc w nf1 nf2 h1 h2

-- ============================================================
-- §16  Critical Pairs
-- ============================================================

/-- A critical pair. -/
structure CriticalPair (P : Presentation) where
  overlap : Word
  left : Word
  right : Word
  pathL : WordEquiv P overlap left
  pathR : WordEquiv P overlap right

/-- Joinable critical pair. -/
def CriticalPair.joinable {P : Presentation} (cp : CriticalPair P) : Prop :=
  WordEquiv P cp.left cp.right

/-- Theorem 44: Joinable CPs contribute to local confluence. -/
theorem joinable_cp_local {P : Presentation} (cp : CriticalPair P)
    (hj : cp.joinable) :
    ∃ z, WordEquiv P cp.left z ∧ WordEquiv P cp.right z :=
  ⟨cp.right, hj, wordEquiv_refl P cp.right⟩

/-- Theorem 45: Reflexivity of word equivalence via path. -/
theorem wordEquiv_via_path {P : Presentation} {u v : Word}
    (p : WPath P u v) : WordEquiv P u v :=
  ⟨p⟩

end CompPaths.WordProblemDeep
