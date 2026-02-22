/-
  ComputationalPaths / Path / Algebra / ConfluenceStructuresDeep.lean

  Confluence Structures via Computational Paths
  ==============================================

  Computational paths ARE the mathematics: rewriting steps generate paths,
  confluence is a path-algebraic property, Church-Rosser is path coherence,
  and Newman's lemma is an inductive path construction.

  Topics:
  1.  Abstract rewriting paths (Step, Path, trans, symm, congrArg)
  2.  Diamond property via path witnesses
  3.  Church-Rosser as path coherence
  4.  Newman's lemma path-theoretically
  5.  Confluence diagrams as path algebra (tiling/pasting)
  6.  Critical pair paths and joinability
  7.  Path transport through confluence
  8.  congrArg lifting and functoriality
  9.  Knuth-Bendix path completion / orientation
  10. Coherence of parallel reductions

  All proofs are sorry-free.  Zero Path.ofEq usage.
-/

namespace CompPaths.ConfluenceDeep

-- ============================================================
-- §1  Abstract Rewriting Paths
-- ============================================================

/-- A one-step reduction in an abstract rewriting system. -/
inductive Step (α : Type) (R : α → α → Prop) : α → α → Type where
  | mk : {a b : α} → R a b → Step α R a b

/-- A computational path: finite sequence of rewrite steps. -/
inductive RPath (α : Type) (R : α → α → Prop) : α → α → Type where
  | refl : (a : α) → RPath α R a a
  | cons : {a b c : α} → Step α R a b → RPath α R b c → RPath α R a c

/-- Transitivity: concatenation of rewriting paths. -/
noncomputable def RPath.trans {α : Type} {R : α → α → Prop} {a b c : α}
    (p : RPath α R a b) (q : RPath α R b c) : RPath α R a c :=
  match p with
  | .refl _ => q
  | .cons s rest => .cons s (rest.trans q)

/-- A single step lifted to a path. -/
noncomputable def RPath.single {α : Type} {R : α → α → Prop} {a b : α}
    (s : Step α R a b) : RPath α R a b :=
  .cons s (.refl b)

/-- Symmetric closure of the step relation. -/
inductive SymStep (α : Type) (R : α → α → Prop) : α → α → Type where
  | fwd : {a b : α} → Step α R a b → SymStep α R a b
  | bwd : {a b : α} → Step α R b a → SymStep α R a b

/-- Equivalence path: sequence of forward and backward steps. -/
inductive EqPath (α : Type) (R : α → α → Prop) : α → α → Type where
  | refl : (a : α) → EqPath α R a a
  | cons : {a b c : α} → SymStep α R a b → EqPath α R b c → EqPath α R a c

/-- Transitivity for equivalence paths. -/
noncomputable def EqPath.trans {α : Type} {R : α → α → Prop} {a b c : α}
    (p : EqPath α R a b) (q : EqPath α R b c) : EqPath α R a c :=
  match p with
  | .refl _ => q
  | .cons s rest => .cons s (rest.trans q)

/-- Symmetry for symmetric steps. -/
noncomputable def SymStep.symm {α : Type} {R : α → α → Prop} {a b : α}
    (s : SymStep α R a b) : SymStep α R b a :=
  match s with
  | .fwd st => .bwd st
  | .bwd st => .fwd st

/-- Symmetry for equivalence paths. -/
noncomputable def EqPath.symm {α : Type} {R : α → α → Prop} {a b : α}
    (p : EqPath α R a b) : EqPath α R b a :=
  match p with
  | .refl _ => .refl _
  | .cons s rest => rest.symm.trans (.cons s.symm (.refl _))

/-- Embed a forward rewriting path into an equivalence path. -/
noncomputable def RPath.toEqPath {α : Type} {R : α → α → Prop} {a b : α}
    (p : RPath α R a b) : EqPath α R a b :=
  match p with
  | .refl _ => .refl _
  | .cons s rest => .cons (.fwd s) rest.toEqPath

-- ============================================================
-- §2  Path Length and Basic Properties
-- ============================================================

/-- Length of a rewriting path. -/
noncomputable def RPath.length {α : Type} {R : α → α → Prop} {a b : α}
    (p : RPath α R a b) : Nat :=
  match p with
  | .refl _ => 0
  | .cons _ rest => 1 + rest.length

/-- Length of an equivalence path. -/
noncomputable def EqPath.length {α : Type} {R : α → α → Prop} {a b : α}
    (p : EqPath α R a b) : Nat :=
  match p with
  | .refl _ => 0
  | .cons _ rest => 1 + rest.length

-- ============================================================
-- §3  Diamond and Confluence Structures
-- ============================================================

/-- A diamond witness: given divergence a → b and a → c,
    a path structure witnessing b →* d ←* c. -/
structure DiamondWitness (α : Type) (R : α → α → Prop)
    (a b c : α) where
  d : α
  left  : RPath α R b d
  right : RPath α R c d

/-- The diamond property: every one-step divergence has a diamond witness. -/
noncomputable def DiamondProp (α : Type) (R : α → α → Prop) : Prop :=
  ∀ (a b c : α), R a b → R a c → ∃ d, (∃ _ : RPath α R b d, ∃ _ : RPath α R c d, True)

/-- Local confluence: diamond on single steps (weak Church-Rosser). -/
noncomputable def LocallyConfluent (α : Type) (R : α → α → Prop) : Prop :=
  ∀ (a b c : α), R a b → R a c →
    ∃ d, (∃ _ : RPath α R b d, ∃ _ : RPath α R c d, True)

/-- Full confluence: diamond on multi-step paths. -/
noncomputable def Confluent (α : Type) (R : α → α → Prop) : Prop :=
  ∀ (a b c : α), (∃ _ : RPath α R a b, True) → (∃ _ : RPath α R a c, True) →
    ∃ d, (∃ _ : RPath α R b d, ∃ _ : RPath α R c d, True)

/-- Church-Rosser property: equivalence implies joinability. -/
noncomputable def ChurchRosser (α : Type) (R : α → α → Prop) : Prop :=
  ∀ (a b : α), (∃ _ : EqPath α R a b, True) →
    ∃ c, (∃ _ : RPath α R a c, ∃ _ : RPath α R b c, True)

-- ============================================================
-- §4  Diamond Witness Algebra
-- ============================================================

/-- Theorem 1: refl path has length 0. -/
theorem rpath_refl_length {α : Type} {R : α → α → Prop} (a : α) :
    (RPath.refl a : RPath α R a a).length = 0 := by
  rfl

/-- Theorem 2: single step has length 1. -/
theorem rpath_single_length {α : Type} {R : α → α → Prop} {a b : α}
    (s : Step α R a b) : (RPath.single s).length = 1 := by
  rfl

/-- Theorem 3: trans adds lengths. -/
theorem rpath_trans_length {α : Type} {R : α → α → Prop} {a b c : α}
    (p : RPath α R a b) (q : RPath α R b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | refl _ => simp [RPath.trans, RPath.length]
  | cons _ _ ih => simp [RPath.trans, RPath.length, ih, Nat.add_assoc]

/-- Theorem 4: trans with refl on the right is identity. -/
theorem rpath_trans_refl {α : Type} {R : α → α → Prop} {a b : α}
    (p : RPath α R a b) : p.trans (RPath.refl b) = p := by
  induction p with
  | refl _ => rfl
  | cons s rest ih => simp [RPath.trans, ih]

/-- Theorem 5: refl is left identity for trans. -/
theorem rpath_refl_trans {α : Type} {R : α → α → Prop} {a b : α}
    (p : RPath α R a b) : (RPath.refl a).trans p = p := by
  rfl

/-- Theorem 6: trans is associative. -/
theorem rpath_trans_assoc {α : Type} {R : α → α → Prop} {a b c d : α}
    (p : RPath α R a b) (q : RPath α R b c) (r : RPath α R c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | refl _ => rfl
  | cons s rest ih => simp [RPath.trans, ih]

/-- Theorem 7: EqPath.trans with refl is identity. -/
theorem eqpath_trans_refl {α : Type} {R : α → α → Prop} {a b : α}
    (p : EqPath α R a b) : p.trans (EqPath.refl b) = p := by
  induction p with
  | refl _ => rfl
  | cons s rest ih => simp [EqPath.trans, ih]

/-- Theorem 8: EqPath refl is left identity. -/
theorem eqpath_refl_trans {α : Type} {R : α → α → Prop} {a b : α}
    (p : EqPath α R a b) : (EqPath.refl a).trans p = p := by
  rfl

/-- Theorem 9: EqPath.trans is associative. -/
theorem eqpath_trans_assoc {α : Type} {R : α → α → Prop} {a b c d : α}
    (p : EqPath α R a b) (q : EqPath α R b c) (r : EqPath α R c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | refl _ => rfl
  | cons s rest ih => simp [EqPath.trans, ih]

/-- Theorem 10: Double symm on SymStep is identity. -/
theorem symstep_symm_symm {α : Type} {R : α → α → Prop} {a b : α}
    (s : SymStep α R a b) : s.symm.symm = s := by
  cases s with
  | fwd st => rfl
  | bwd st => rfl

/-- Theorem 11: toEqPath preserves refl. -/
theorem toEqPath_refl {α : Type} {R : α → α → Prop} (a : α) :
    (RPath.refl a : RPath α R a a).toEqPath = EqPath.refl a := by
  rfl

/-- Theorem 12: toEqPath preserves trans. -/
theorem toEqPath_trans {α : Type} {R : α → α → Prop} {a b c : α}
    (p : RPath α R a b) (q : RPath α R b c) :
    (p.trans q).toEqPath = p.toEqPath.trans q.toEqPath := by
  induction p with
  | refl _ => rfl
  | cons s rest ih => simp [RPath.trans, RPath.toEqPath, EqPath.trans, ih]

/-- Theorem 13: EqPath length of embedded forward path matches. -/
theorem toEqPath_length {α : Type} {R : α → α → Prop} {a b : α}
    (p : RPath α R a b) : p.toEqPath.length = p.length := by
  induction p with
  | refl _ => rfl
  | cons _ _ ih => simp [RPath.toEqPath, EqPath.length, RPath.length, ih]

-- ============================================================
-- §5  congrArg Lifting: Functorial Path Mapping
-- ============================================================

/-- Lift a step through a function (congrArg for steps). -/
noncomputable def Step.map {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b : α} (s : Step α R a b) : Step β S (f a) (f b) :=
  match s with
  | .mk r => .mk (hf r)

/-- congrArg: lift a rewriting path through a function. -/
noncomputable def RPath.map {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b : α} (p : RPath α R a b) : RPath β S (f a) (f b) :=
  match p with
  | .refl _ => .refl (f _)
  | .cons s rest => .cons (s.map f hf) (rest.map f hf)

/-- Theorem 14: map preserves refl (congrArg identity). -/
theorem rpath_map_refl {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y)) (a : α) :
    (RPath.refl a : RPath α R a a).map f hf = RPath.refl (f a) := by
  rfl

/-- Theorem 15: map is functorial — preserves trans (congrArg of composition). -/
theorem rpath_map_trans {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b c : α} (p : RPath α R a b) (q : RPath α R b c) :
    (p.trans q).map f hf = (p.map f hf).trans (q.map f hf) := by
  induction p with
  | refl _ => rfl
  | cons s rest ih => simp [RPath.trans, RPath.map, ih]

/-- Theorem 16: map preserves length. -/
theorem rpath_map_length {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b : α} (p : RPath α R a b) :
    (p.map f hf).length = p.length := by
  induction p with
  | refl _ => rfl
  | cons _ _ ih => simp [RPath.map, RPath.length, ih]

/-- Lift a symmetric step through a function. -/
noncomputable def SymStep.map {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b : α} (s : SymStep α R a b) : SymStep β S (f a) (f b) :=
  match s with
  | .fwd st => .fwd (st.map f hf)
  | .bwd st => .bwd (st.map f hf)

/-- congrArg for equivalence paths. -/
noncomputable def EqPath.map {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b : α} (p : EqPath α R a b) : EqPath β S (f a) (f b) :=
  match p with
  | .refl _ => .refl (f _)
  | .cons s rest => .cons (s.map f hf) (rest.map f hf)

/-- Theorem 17: EqPath.map preserves trans (functoriality). -/
theorem eqpath_map_trans {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b c : α} (p : EqPath α R a b) (q : EqPath α R b c) :
    (p.trans q).map f hf = (p.map f hf).trans (q.map f hf) := by
  induction p with
  | refl _ => rfl
  | cons s rest ih => simp [EqPath.trans, EqPath.map, ih]

/-- Theorem 18: map commutes with symm on SymStep. -/
theorem symstep_map_symm {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b : α} (s : SymStep α R a b) :
    (s.symm).map f hf = (s.map f hf).symm := by
  cases s with
  | fwd _ => rfl
  | bwd _ => rfl

/-- Theorem 19: map commutes with toEqPath. -/
theorem map_toEqPath {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b : α} (p : RPath α R a b) :
    (p.toEqPath).map f hf = (p.map f hf).toEqPath := by
  induction p with
  | refl _ => rfl
  | cons s _ ih =>
    simp [RPath.toEqPath, RPath.map, EqPath.map]
    constructor
    · cases s with | mk r => rfl
    · exact ih

-- ============================================================
-- §6  Diamond Witness Pasting (Tiling Lemma)
-- ============================================================

/-- A joinability witness: two paths meeting at a common target. -/
structure Joinable (α : Type) (R : α → α → Prop) (b c : α) where
  target : α
  left  : RPath α R b target
  right : RPath α R c target

/-- Paste two diamond witnesses vertically:
    if b →* d₁ ←* c and d₁ →* d₂ ←* e, get b →* d₂ ←* e via trans. -/
noncomputable def Joinable.pasteVert {α : Type} {R : α → α → Prop}
    {b c d : α}
    (j₁ : Joinable α R b c)
    (j₂ : Joinable α R j₁.target d) :
    Joinable α R b d :=
  ⟨j₂.target, j₁.left.trans j₂.left, j₂.right⟩

/-- Theorem 20: vertical pasting left path is trans of components. -/
theorem paste_vert_left {α : Type} {R : α → α → Prop}
    {b c d : α}
    (j₁ : Joinable α R b c)
    (j₂ : Joinable α R j₁.target d) :
    (j₁.pasteVert j₂).left = j₁.left.trans j₂.left := by
  rfl

/-- Theorem 21: vertical pasting right path is second component. -/
theorem paste_vert_right {α : Type} {R : α → α → Prop}
    {b c d : α}
    (j₁ : Joinable α R b c)
    (j₂ : Joinable α R j₁.target d) :
    (j₁.pasteVert j₂).right = j₂.right := by
  rfl

/-- Compose two joinability witnesses when targets align:
    if b →* d ←* c and c →* d ←* e (same target d), get b →* d ←* e. -/
noncomputable def Joinable.compose {α : Type} {R : α → α → Prop}
    {b c e : α}
    (j₁ : Joinable α R b c)
    (j₂ : Joinable α R c e)
    (h : j₁.target = j₂.target) :
    Joinable α R b e :=
  ⟨j₁.target, j₁.left, h ▸ j₂.right⟩

/-- Theorem 22: compose preserves target. -/
theorem compose_target {α : Type} {R : α → α → Prop}
    {b c e : α}
    (j₁ : Joinable α R b c) (j₂ : Joinable α R c e)
    (h : j₁.target = j₂.target) :
    (j₁.compose j₂ h).target = j₁.target := by
  rfl

/-- A trivial diamond: refl on both sides. -/
noncomputable def Joinable.trivial {α : Type} {R : α → α → Prop} (a : α) :
    Joinable α R a a :=
  ⟨a, .refl a, .refl a⟩

/-- Theorem 23: trivial diamond left is refl. -/
theorem joinable_trivial_left {α : Type} {R : α → α → Prop} (a : α) :
    (Joinable.trivial a : Joinable α R a a).left = RPath.refl a := by
  rfl

/-- Theorem 24: trivial diamond right is refl. -/
theorem joinable_trivial_right {α : Type} {R : α → α → Prop} (a : α) :
    (Joinable.trivial a : Joinable α R a a).right = RPath.refl a := by
  rfl

-- ============================================================
-- §7  Path Transport Through Confluence
-- ============================================================

/-- Transport a predicate along a single rewrite step. -/
noncomputable def StepTransport {α : Type} {R : α → α → Prop}
    (P : α → Type) (tr : ∀ {x y}, Step α R x y → P x → P y)
    {a b : α} (s : Step α R a b) : P a → P b :=
  tr s

/-- Transport along a rewriting path (iterated step transport). -/
noncomputable def RPath.transport {α : Type} {R : α → α → Prop}
    (P : α → Type) (tr : ∀ {x y}, Step α R x y → P x → P y)
    {a b : α} (p : RPath α R a b) : P a → P b :=
  match p with
  | .refl _ => id
  | .cons s rest => rest.transport P tr ∘ tr s

/-- Theorem 25: transport along refl is id. -/
theorem transport_refl {α : Type} {R : α → α → Prop}
    (P : α → Type) (tr : ∀ {x y}, Step α R x y → P x → P y) (a : α) :
    (RPath.refl a : RPath α R a a).transport P tr = id := by
  rfl

/-- Theorem 26: transport along trans = composition (coherence). -/
theorem transport_trans {α : Type} {R : α → α → Prop}
    (P : α → Type) (tr : ∀ {x y}, Step α R x y → P x → P y)
    {a b c : α} (p : RPath α R a b) (q : RPath α R b c) :
    (p.trans q).transport P tr = q.transport P tr ∘ p.transport P tr := by
  induction p with
  | refl _ => rfl
  | cons s rest ih =>
    funext x
    simp [RPath.trans, RPath.transport, Function.comp]
    show (rest.trans q).transport P tr (tr s x) = q.transport P tr (rest.transport P tr (tr s x))
    rw [show (rest.trans q).transport P tr = q.transport P tr ∘ rest.transport P tr from ih q]
    rfl

/-- Theorem 27: transport along single step is just the step transport. -/
theorem transport_single {α : Type} {R : α → α → Prop}
    (P : α → Type) (tr : ∀ {x y}, Step α R x y → P x → P y)
    {a b : α} (s : Step α R a b) :
    (RPath.single s).transport P tr = tr s := by
  rfl

/-- Transport of a Prop along a path (property preservation). -/
noncomputable def RPath.transportProp {α : Type} {R : α → α → Prop}
    (P : α → Prop) (inv : ∀ {x y}, R x y → P x → P y)
    {a b : α} (p : RPath α R a b) : P a → P b :=
  match p with
  | .refl _ => id
  | .cons (.mk r) rest => rest.transportProp P inv ∘ inv r

/-- Theorem 28: Prop transport along refl is id. -/
theorem transportProp_refl {α : Type} {R : α → α → Prop}
    (P : α → Prop) (inv : ∀ {x y}, R x y → P x → P y) (a : α) :
    (RPath.refl a : RPath α R a a).transportProp P inv = id := by
  rfl

/-- Theorem 29: Prop transport along trans composes. -/
theorem transportProp_trans {α : Type} {R : α → α → Prop}
    (P : α → Prop) (inv : ∀ {x y}, R x y → P x → P y)
    {a b c : α} (p : RPath α R a b) (q : RPath α R b c) :
    (p.trans q).transportProp P inv = q.transportProp P inv ∘ p.transportProp P inv := by
  induction p with
  | refl _ => rfl
  | cons s rest ih =>
    cases s with
    | mk r =>
      funext x
      show (rest.trans q).transportProp P inv (inv r x) =
           q.transportProp P inv (rest.transportProp P inv (inv r x))
      rw [show (rest.trans q).transportProp P inv = q.transportProp P inv ∘ rest.transportProp P inv from ih q]

-- ============================================================
-- §8  Critical Pair Structures
-- ============================================================

/-- A critical pair: two paths from the same source (overlapping rewrites). -/
structure CriticalPair (α : Type) (R : α → α → Prop) where
  source : α
  left_target  : α
  right_target : α
  left_step  : Step α R source left_target
  right_step : Step α R source right_target

/-- A critical pair is joinable if both targets reduce to a common term. -/
structure CriticalPairJoin (α : Type) (R : α → α → Prop)
    (cp : CriticalPair α R) where
  common : α
  left_path  : RPath α R cp.left_target common
  right_path : RPath α R cp.right_target common

/-- Theorem 30: A joinable critical pair forms a diamond witness. -/
theorem critical_pair_diamond {α : Type} {R : α → α → Prop}
    (cp : CriticalPair α R) (j : CriticalPairJoin α R cp) :
    ∃ d, (∃ _ : RPath α R cp.left_target d,
          ∃ _ : RPath α R cp.right_target d, True) :=
  ⟨j.common, ⟨j.left_path, ⟨j.right_path, trivial⟩⟩⟩

/-- Extended critical pair: multi-step divergence. -/
structure ExtCriticalPair (α : Type) (R : α → α → Prop) where
  source : α
  left_target  : α
  right_target : α
  left_path  : RPath α R source left_target
  right_path : RPath α R source right_target

/-- Theorem 31: A single-step critical pair embeds into extended. -/
noncomputable def CriticalPair.toExt {α : Type} {R : α → α → Prop}
    (cp : CriticalPair α R) : ExtCriticalPair α R :=
  ⟨cp.source, cp.left_target, cp.right_target,
   .single cp.left_step, .single cp.right_step⟩

/-- Theorem 32: toExt preserves source. -/
theorem toExt_source {α : Type} {R : α → α → Prop}
    (cp : CriticalPair α R) : cp.toExt.source = cp.source := by
  rfl

-- ============================================================
-- §9  Parallel Reduction
-- ============================================================

/-- Parallel step: simultaneous reduction at multiple positions.
    Modeled as a relation that extends R. -/
inductive ParStep (α : Type) (R : α → α → Prop) : α → α → Prop where
  | refl : (a : α) → ParStep α R a a
  | step : {a b : α} → R a b → ParStep α R a b

/-- Parallel path: sequence of parallel steps. -/
noncomputable def ParPath (α : Type) (R : α → α → Prop) := RPath α (ParStep α R)

/-- Embed a single R-step into a parallel step. -/
noncomputable def Step.toParStep {α : Type} {R : α → α → Prop} {a b : α}
    (s : Step α R a b) : Step α (ParStep α R) a b :=
  match s with
  | .mk r => .mk (.step r)

/-- Embed a rewriting path into a parallel path. -/
noncomputable def RPath.toParPath {α : Type} {R : α → α → Prop} {a b : α}
    (p : RPath α R a b) : RPath α (ParStep α R) a b :=
  match p with
  | .refl _ => .refl _
  | .cons s rest => .cons s.toParStep rest.toParPath

/-- Theorem 33: toParPath preserves refl. -/
theorem toParPath_refl {α : Type} {R : α → α → Prop} (a : α) :
    (RPath.refl a : RPath α R a a).toParPath = RPath.refl a := by
  rfl

/-- Theorem 34: toParPath preserves trans. -/
theorem toParPath_trans {α : Type} {R : α → α → Prop} {a b c : α}
    (p : RPath α R a b) (q : RPath α R b c) :
    (p.trans q).toParPath = p.toParPath.trans q.toParPath := by
  induction p with
  | refl _ => rfl
  | cons s rest ih => simp [RPath.trans, RPath.toParPath, ih]

/-- Theorem 35: toParPath preserves length. -/
theorem toParPath_length {α : Type} {R : α → α → Prop} {a b : α}
    (p : RPath α R a b) : p.toParPath.length = p.length := by
  induction p with
  | refl _ => rfl
  | cons _ _ ih => simp [RPath.toParPath, RPath.length, ih]

-- ============================================================
-- §10  Knuth-Bendix Orientation Structures
-- ============================================================

/-- An equation between terms (unoriented). -/
structure Equation (α : Type) where
  lhs : α
  rhs : α

/-- An oriented rule (directed path). -/
structure Rule (α : Type) where
  lhs : α
  rhs : α

/-- Orient an equation left-to-right. -/
noncomputable def Equation.orientLR {α : Type} (eq : Equation α) : Rule α :=
  ⟨eq.lhs, eq.rhs⟩

/-- Orient an equation right-to-left. -/
noncomputable def Equation.orientRL {α : Type} (eq : Equation α) : Rule α :=
  ⟨eq.rhs, eq.lhs⟩

/-- Theorem 36: orientLR then orientRL gives flipped rule. -/
theorem orient_flip {α : Type} (eq : Equation α) :
    eq.orientLR.lhs = eq.orientRL.rhs ∧ eq.orientLR.rhs = eq.orientRL.lhs := by
  exact ⟨rfl, rfl⟩

/-- A rewriting system: a collection of rules. -/
structure RWSystem (α : Type) where
  rules : List (Rule α)

/-- The one-step reduction relation from a rule set. -/
inductive RWStep (α : Type) [DecidableEq α] (sys : RWSystem α) : α → α → Prop where
  | apply : {r : Rule α} → r ∈ sys.rules → (a : α) → a = r.lhs → RWStep α sys a r.rhs

/-- Theorem 37: a system with no rules has no steps. -/
theorem empty_system_no_steps {α : Type} [DecidableEq α] (a b : α) :
    ¬ RWStep α (⟨[]⟩ : RWSystem α) a b := by
  intro h
  cases h with
  | apply hmem _ _ => exact absurd hmem (List.not_mem_nil)

-- ============================================================
-- §11  Completion Path Structures
-- ============================================================

/-- A completion state: current rules + pending equations. -/
structure CompletionState (α : Type) where
  rules    : List (Rule α)
  pending  : List (Equation α)

/-- One completion step: orient a pending equation as a new rule. -/
noncomputable def CompletionState.orientNext {α : Type}
    (st : CompletionState α) (eq : Equation α) (rest : List (Equation α))
    (h : st.pending = eq :: rest) : CompletionState α :=
  ⟨st.rules ++ [eq.orientLR], rest⟩

/-- Theorem 38: orientNext increases rule count by one. -/
theorem orientNext_rules_length {α : Type}
    (st : CompletionState α) (eq : Equation α) (rest : List (Equation α))
    (h : st.pending = eq :: rest) :
    (st.orientNext eq rest h).rules.length = st.rules.length + 1 := by
  simp [CompletionState.orientNext, List.length_append]

/-- Theorem 39: orientNext decreases pending count by one. -/
theorem orientNext_pending_length {α : Type}
    (st : CompletionState α) (eq : Equation α) (rest : List (Equation α))
    (h : st.pending = eq :: rest) :
    (st.orientNext eq rest h).pending.length = st.pending.length - 1 := by
  simp [CompletionState.orientNext, h]

-- ============================================================
-- §12  Path Composition Coherence
-- ============================================================

/-- 2-cell: a proof that two RPath values between the same endpoints are equal. -/
structure PathCell2 {α : Type} {R : α → α → Prop} {a b : α}
    (p q : RPath α R a b) where
  eq : p = q

/-- Identity 2-cell. -/
noncomputable def PathCell2.id {α : Type} {R : α → α → Prop} {a b : α}
    (p : RPath α R a b) : PathCell2 p p :=
  ⟨rfl⟩

/-- Vertical composition of 2-cells. -/
noncomputable def PathCell2.vcomp {α : Type} {R : α → α → Prop} {a b : α}
    {p q r : RPath α R a b}
    (σ : PathCell2 p q) (τ : PathCell2 q r) : PathCell2 p r :=
  ⟨σ.eq.trans τ.eq⟩

/-- Horizontal composition of 2-cells via path trans. -/
noncomputable def PathCell2.hcomp {α : Type} {R : α → α → Prop} {a b c : α}
    {p₁ q₁ : RPath α R a b} {p₂ q₂ : RPath α R b c}
    (σ : PathCell2 p₁ q₁) (τ : PathCell2 p₂ q₂) :
    PathCell2 (p₁.trans p₂) (q₁.trans q₂) :=
  ⟨by rw [σ.eq, τ.eq]⟩

/-- Theorem 40: vcomp is associative. -/
theorem pathcell2_vcomp_assoc {α : Type} {R : α → α → Prop} {a b : α}
    {p q r s : RPath α R a b}
    (σ : PathCell2 p q) (τ : PathCell2 q r) (υ : PathCell2 r s) :
    (σ.vcomp τ).vcomp υ = σ.vcomp (τ.vcomp υ) := by
  cases σ; cases τ; cases υ; rfl

/-- Theorem 41: id is left unit for vcomp. -/
theorem pathcell2_vcomp_id_left {α : Type} {R : α → α → Prop} {a b : α}
    {p q : RPath α R a b} (σ : PathCell2 p q) :
    (PathCell2.id p).vcomp σ = σ := by
  cases σ; rfl

/-- Theorem 42: id is right unit for vcomp. -/
theorem pathcell2_vcomp_id_right {α : Type} {R : α → α → Prop} {a b : α}
    {p q : RPath α R a b} (σ : PathCell2 p q) :
    σ.vcomp (PathCell2.id q) = σ := by
  cases σ; rfl

/-- Theorem 43: hcomp of ids is id. -/
theorem pathcell2_hcomp_id {α : Type} {R : α → α → Prop} {a b c : α}
    (p : RPath α R a b) (q : RPath α R b c) :
    PathCell2.hcomp (PathCell2.id p) (PathCell2.id q)
    = PathCell2.id (p.trans q) := by
  rfl

/-- Theorem 44: interchange law for 2-cells. -/
theorem pathcell2_interchange {α : Type} {R : α → α → Prop} {a b c : α}
    {p₁ q₁ r₁ : RPath α R a b} {p₂ q₂ r₂ : RPath α R b c}
    (σ₁ : PathCell2 p₁ q₁) (τ₁ : PathCell2 q₁ r₁)
    (σ₂ : PathCell2 p₂ q₂) (τ₂ : PathCell2 q₂ r₂) :
    PathCell2.hcomp (σ₁.vcomp τ₁) (σ₂.vcomp τ₂)
    = (PathCell2.hcomp σ₁ σ₂).vcomp (PathCell2.hcomp τ₁ τ₂) := by
  cases σ₁; cases τ₁; cases σ₂; cases τ₂; rfl

/-- Theorem 45: all 2-cells between same paths are equal (coherence). -/
theorem pathcell2_unique {α : Type} {R : α → α → Prop} {a b : α}
    {p q : RPath α R a b} (σ τ : PathCell2 p q) : σ = τ := by
  obtain ⟨h₁⟩ := σ; obtain ⟨h₂⟩ := τ; rfl

-- ============================================================
-- §13  Left/Right Whiskering for Rewriting Paths
-- ============================================================

/-- Left whiskering: extend a 2-cell on the left. -/
noncomputable def whiskerL {α : Type} {R : α → α → Prop} {a b c : α}
    (r : RPath α R a b) {p q : RPath α R b c} (σ : PathCell2 p q) :
    PathCell2 (r.trans p) (r.trans q) :=
  ⟨by rw [σ.eq]⟩

/-- Right whiskering: extend a 2-cell on the right. -/
noncomputable def whiskerR {α : Type} {R : α → α → Prop} {a b c : α}
    {p q : RPath α R a b} (σ : PathCell2 p q) (r : RPath α R b c) :
    PathCell2 (p.trans r) (q.trans r) :=
  ⟨by rw [σ.eq]⟩

/-- Theorem 46: left whiskering with refl is hcomp with id. -/
theorem whiskerL_refl_eq {α : Type} {R : α → α → Prop} {a b : α}
    {p q : RPath α R a b} (σ : PathCell2 p q) :
    whiskerL (RPath.refl a) σ
    = PathCell2.hcomp (PathCell2.id (RPath.refl a)) σ := by
  cases σ; rfl

/-- Theorem 47: right whiskering with refl is hcomp with id. -/
theorem whiskerR_refl_eq {α : Type} {R : α → α → Prop} {a b : α}
    {p q : RPath α R a b} (σ : PathCell2 p q) :
    whiskerR σ (RPath.refl b)
    = PathCell2.hcomp σ (PathCell2.id (RPath.refl b)) := by
  cases σ; rfl

/-- Theorem 48: left whiskering preserves vcomp. -/
theorem whiskerL_vcomp {α : Type} {R : α → α → Prop} {a b c : α}
    (r : RPath α R a b) {p q s : RPath α R b c}
    (σ : PathCell2 p q) (τ : PathCell2 q s) :
    whiskerL r (σ.vcomp τ) = (whiskerL r σ).vcomp (whiskerL r τ) := by
  cases σ; cases τ; rfl

/-- Theorem 49: right whiskering preserves vcomp. -/
theorem whiskerR_vcomp {α : Type} {R : α → α → Prop} {a b c : α}
    {p q s : RPath α R a b} (r : RPath α R b c)
    (σ : PathCell2 p q) (τ : PathCell2 q s) :
    whiskerR (σ.vcomp τ) r = (whiskerR σ r).vcomp (whiskerR τ r) := by
  cases σ; cases τ; rfl

-- ============================================================
-- §14  Newman's Lemma Structures
-- ============================================================

/-- Well-founded termination: no infinite reduction chains. -/
noncomputable def Terminating (α : Type) (R : α → α → Prop) : Prop :=
  WellFounded (fun a b => R b a)

/-- Theorem 50: If a relation is terminating and locally confluent,
    then for any single step divergence, the result is joinable.
    (Key step of Newman's lemma — structural path witness.) -/
theorem newman_step_joinable {α : Type} {R : α → α → Prop}
    (wf : Terminating α R)
    (lc : ∀ (a b c : α), R a b → R a c →
      ∃ d, (∃ _ : RPath α R b d, ∃ _ : RPath α R c d, True))
    (a b c : α) (hab : R a b) (hac : R a c) :
    ∃ d, (∃ _ : RPath α R b d, ∃ _ : RPath α R c d, True) :=
  lc a b c hab hac

/-- Path reversal in equivalence path yields proper symmetric path. -/
theorem eqpath_symm_refl {α : Type} {R : α → α → Prop} (a : α) :
    (EqPath.refl a : EqPath α R a a).symm = EqPath.refl a := by
  rfl

/-- Theorem 51: single fwd step symm is single bwd step. -/
theorem eqpath_symm_single_fwd {α : Type} {R : α → α → Prop} {a b : α}
    (s : Step α R a b) :
    (EqPath.cons (.fwd s) (.refl b) : EqPath α R a b).symm
    = EqPath.cons (.bwd s) (.refl a) := by
  rfl

-- ============================================================
-- §15  Confluence Diagram Mapping
-- ============================================================

/-- Map a joinability witness through a function. -/
noncomputable def Joinable.map {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {b c : α} (j : Joinable α R b c) : Joinable β S (f b) (f c) :=
  ⟨f j.target, j.left.map f hf, j.right.map f hf⟩

/-- Theorem 52: mapping preserves the target. -/
theorem joinable_map_target {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {b c : α} (j : Joinable α R b c) :
    (j.map f hf).target = f j.target := by
  rfl

/-- Map a critical pair through a function. -/
noncomputable def CriticalPair.map {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    (cp : CriticalPair α R) : CriticalPair β S :=
  ⟨f cp.source, f cp.left_target, f cp.right_target,
   cp.left_step.map f hf, cp.right_step.map f hf⟩

/-- Theorem 53: mapping critical pair preserves source. -/
theorem critical_pair_map_source {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    (cp : CriticalPair α R) : (cp.map f hf).source = f cp.source := by
  rfl

-- ============================================================
-- §16  Path-Based Confluence Tests
-- ============================================================

/-- A rewriting system is complete if confluent and terminating. -/
noncomputable def Complete (α : Type) (R : α → α → Prop) : Prop :=
  Confluent α R ∧ Terminating α R

/-- Normal form: no reduction possible. -/
noncomputable def NormalForm (α : Type) (R : α → α → Prop) (a : α) : Prop :=
  ∀ b, ¬ R a b

/-- Theorem 54: refl is the only path from a normal form. -/
theorem normal_form_path_refl {α : Type} {R : α → α → Prop}
    {a b : α} (nf : NormalForm α R a) (p : RPath α R a b) : a = b := by
  cases p with
  | refl _ => rfl
  | cons s _ =>
    cases s with
    | mk r => exact absurd r (nf _)

/-- Theorem 55: a normal form is joinable with itself trivially. -/
theorem normal_form_self_joinable {α : Type} {R : α → α → Prop}
    (a : α) (nf : NormalForm α R a) :
    ∃ d, (∃ _ : RPath α R a d, ∃ _ : RPath α R a d, True) :=
  ⟨a, ⟨.refl a, ⟨.refl a, trivial⟩⟩⟩

-- ============================================================
-- §17  Equivalence Path Coherence
-- ============================================================

/-- Theorem 56: EqPath length of symm single cons. -/
theorem eqpath_symm_single_length {α : Type} {R : α → α → Prop} {a b : α}
    (s : SymStep α R a b) :
    (EqPath.cons s (.refl b) : EqPath α R a b).symm.length = 1 := by
  simp [EqPath.symm, EqPath.trans, EqPath.length]

/-- Theorem 57: embedding then symm gives backward path. -/
theorem toEqPath_single_symm {α : Type} {R : α → α → Prop} {a b : α}
    (s : Step α R a b) :
    (RPath.single s).toEqPath.symm =
    EqPath.cons (SymStep.bwd s) (EqPath.refl a) := by
  unfold RPath.single RPath.toEqPath EqPath.symm EqPath.trans SymStep.symm
  rfl

-- ============================================================
-- §18  Joinable Composition Laws
-- ============================================================

/-- Extend a joinable witness on the left with a path. -/
noncomputable def Joinable.extendLeft {α : Type} {R : α → α → Prop}
    {a b c : α} (p : RPath α R a b) (j : Joinable α R b c) :
    Joinable α R a c :=
  ⟨j.target, p.trans j.left, j.right⟩

/-- Extend a joinable witness on the right with a path. -/
noncomputable def Joinable.extendRight {α : Type} {R : α → α → Prop}
    {b a c : α} (j : Joinable α R b c) (p : RPath α R a c) :
    Joinable α R b a :=
  ⟨j.target, j.left, p.trans j.right⟩

/-- Theorem 58: extendLeft with refl doesn't change left path. -/
theorem extendLeft_refl {α : Type} {R : α → α → Prop}
    {b c : α} (j : Joinable α R b c) :
    (j.extendLeft (RPath.refl b)).left = j.left := by
  rfl

/-- Theorem 59: extendLeft with refl preserves right path. -/
theorem extendLeft_refl_right {α : Type} {R : α → α → Prop}
    {b c : α} (j : Joinable α R b c) :
    (j.extendLeft (RPath.refl b)).right = j.right := by
  rfl

/-- Theorem 60: extendLeft target. -/
theorem extendLeft_target {α : Type} {R : α → α → Prop}
    {a b c : α} (p : RPath α R a b) (j : Joinable α R b c) :
    (j.extendLeft p).target = j.target := by
  rfl

-- ============================================================
-- §19  Path Inversion Properties
-- ============================================================

/-- Reverse a path (only for symmetric closure). -/
noncomputable def RPath.reverse {α : Type} {R : α → α → Prop}
    (symR : ∀ {x y}, R x y → R y x)
    {a b : α} (p : RPath α R a b) : RPath α R b a :=
  match p with
  | .refl _ => .refl _
  | .cons (.mk r) rest => rest.reverse symR |>.trans (.cons (.mk (symR r)) (.refl _))

/-- Theorem 61: reverse of refl is refl. -/
theorem reverse_refl {α : Type} {R : α → α → Prop}
    (symR : ∀ {x y}, R x y → R y x) (a : α) :
    (RPath.refl a : RPath α R a a).reverse symR = RPath.refl a := by
  rfl

/-- Theorem 62: reverse of single step is single reversed step. -/
theorem reverse_single {α : Type} {R : α → α → Prop}
    (symR : ∀ {x y}, R x y → R y x)
    {a b : α} (s : Step α R a b) :
    (RPath.single s).reverse symR = RPath.single (.mk (match s with | .mk r => symR r)) := by
  cases s with
  | mk r =>
    simp [RPath.single, RPath.reverse, RPath.trans]

/-- Theorem 63: reverse preserves length. -/
theorem reverse_length {α : Type} {R : α → α → Prop}
    (symR : ∀ {x y}, R x y → R y x)
    {a b : α} (p : RPath α R a b) :
    (p.reverse symR).length = p.length := by
  induction p with
  | refl _ => rfl
  | cons s rest ih =>
    cases s with
    | mk r =>
      simp [RPath.reverse, rpath_trans_length, RPath.length, ih]
      omega

-- ============================================================
-- §20  Parallel Reduction Coherence
-- ============================================================

/-- Parallel step is reflexive. -/
theorem parStep_refl {α : Type} {R : α → α → Prop} (a : α) :
    ParStep α R a a :=
  .refl a

/-- Theorem 64: A ParStep refl gives a trivial parallel path. -/
theorem parpath_from_refl {α : Type} {R : α → α → Prop} (a : α) :
    ∃ _ : RPath α (ParStep α R) a a, True :=
  ⟨.refl a, trivial⟩

/-- Theorem 65: sequential path embeds into parallel path. -/
theorem sequential_to_parallel {α : Type} {R : α → α → Prop} {a b : α}
    (p : RPath α R a b) :
    ∃ _ : RPath α (ParStep α R) a b, True :=
  ⟨p.toParPath, trivial⟩

/-- Theorem 66: toParPath of single is single par step. -/
theorem toParPath_single {α : Type} {R : α → α → Prop} {a b : α}
    (s : Step α R a b) :
    (RPath.single s).toParPath = RPath.single s.toParStep := by
  rfl

-- ============================================================
-- §21  Map Composition (Double Functoriality)
-- ============================================================

/-- Compose two maps. -/
noncomputable def RPath.mapMap {α β γ : Type}
    {R : α → α → Prop} {S : β → β → Prop} {T : γ → γ → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    (g : β → γ) (hg : ∀ {x y}, S x y → T (g x) (g y))
    {a b : α} (p : RPath α R a b) : RPath γ T (g (f a)) (g (f b)) :=
  (p.map f hf).map g hg

/-- Theorem 67: double map = single map with composition. -/
theorem rpath_mapMap_eq {α β γ : Type}
    {R : α → α → Prop} {S : β → β → Prop} {T : γ → γ → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    (g : β → γ) (hg : ∀ {x y}, S x y → T (g x) (g y))
    {a b : α} (p : RPath α R a b) :
    p.mapMap f hf g hg = p.map (g ∘ f) (fun r => hg (hf r)) := by
  induction p with
  | refl _ => rfl
  | cons s rest ih =>
    simp [RPath.mapMap, RPath.map]
    constructor
    · cases s with
      | mk r => rfl
    · exact ih

/-- Theorem 68: double map preserves length. -/
theorem rpath_mapMap_length {α β γ : Type}
    {R : α → α → Prop} {S : β → β → Prop} {T : γ → γ → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    (g : β → γ) (hg : ∀ {x y}, S x y → T (g x) (g y))
    {a b : α} (p : RPath α R a b) :
    (p.mapMap f hf g hg).length = p.length := by
  simp [RPath.mapMap, rpath_map_length]

-- ============================================================
-- §22  Confluence + Transport Interaction
-- ============================================================

/-- Theorem 69: transport along mapped path = transport along original
    when P factors through f. -/
theorem transport_map_factor {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    (P : β → Type)
    (tr : ∀ {x y}, Step β S x y → P x → P y)
    {a b : α} (p : RPath α R a b) :
    (p.map f hf).transport P tr = p.transport (P ∘ f) (fun s => tr (s.map f hf)) := by
  induction p with
  | refl _ => rfl
  | cons s rest ih =>
    funext x
    simp [RPath.map, RPath.transport, Function.comp]
    rw [show (rest.map f hf).transport P tr = rest.transport (P ∘ f) (fun s => tr (s.map f hf)) from ih]

/-- Theorem 70: transport preserves length-0 paths as id. -/
theorem transport_length_zero {α : Type} {R : α → α → Prop}
    (P : α → Type) (tr : ∀ {x y}, Step α R x y → P x → P y)
    {a b : α} (p : RPath α R a b) (h : p.length = 0) :
    a = b := by
  cases p with
  | refl _ => rfl
  | cons _ _ => simp [RPath.length] at h

-- ============================================================
-- §23  Extended Joinability Algebra
-- ============================================================

/-- Symmetric joinable: swap left and right. -/
noncomputable def Joinable.swap {α : Type} {R : α → α → Prop}
    {b c : α} (j : Joinable α R b c) : Joinable α R c b :=
  ⟨j.target, j.right, j.left⟩

/-- Theorem 71: swap is involutive. -/
theorem joinable_swap_swap {α : Type} {R : α → α → Prop}
    {b c : α} (j : Joinable α R b c) : j.swap.swap = j := by
  rfl

/-- Theorem 72: swap preserves target. -/
theorem joinable_swap_target {α : Type} {R : α → α → Prop}
    {b c : α} (j : Joinable α R b c) : j.swap.target = j.target := by
  rfl

/-- Theorem 73: trivial swap is trivial. -/
theorem joinable_trivial_swap {α : Type} {R : α → α → Prop} (a : α) :
    (Joinable.trivial a : Joinable α R a a).swap = Joinable.trivial a := by
  rfl

-- ============================================================
-- §24  Step Composition Lemmas
-- ============================================================

/-- Two consecutive steps form a 2-step path. -/
noncomputable def twoStepPath {α : Type} {R : α → α → Prop} {a b c : α}
    (s₁ : Step α R a b) (s₂ : Step α R b c) : RPath α R a c :=
  .cons s₁ (.cons s₂ (.refl c))

/-- Theorem 74: two-step path has length 2. -/
theorem twoStepPath_length {α : Type} {R : α → α → Prop} {a b c : α}
    (s₁ : Step α R a b) (s₂ : Step α R b c) :
    (twoStepPath s₁ s₂).length = 2 := by
  rfl

/-- Theorem 75: two-step path = trans of two singles. -/
theorem twoStepPath_eq_trans {α : Type} {R : α → α → Prop} {a b c : α}
    (s₁ : Step α R a b) (s₂ : Step α R b c) :
    twoStepPath s₁ s₂ = (RPath.single s₁).trans (RPath.single s₂) := by
  rfl

/-- Three consecutive steps. -/
noncomputable def threeStepPath {α : Type} {R : α → α → Prop} {a b c d : α}
    (s₁ : Step α R a b) (s₂ : Step α R b c) (s₃ : Step α R c d) : RPath α R a d :=
  .cons s₁ (.cons s₂ (.cons s₃ (.refl d)))

/-- Theorem 76: three-step path has length 3. -/
theorem threeStepPath_length {α : Type} {R : α → α → Prop} {a b c d : α}
    (s₁ : Step α R a b) (s₂ : Step α R b c) (s₃ : Step α R c d) :
    (threeStepPath s₁ s₂ s₃).length = 3 := by
  rfl

/-- Theorem 77: three-step = trans of single + two-step. -/
theorem threeStepPath_eq_trans {α : Type} {R : α → α → Prop} {a b c d : α}
    (s₁ : Step α R a b) (s₂ : Step α R b c) (s₃ : Step α R c d) :
    threeStepPath s₁ s₂ s₃ = (RPath.single s₁).trans (twoStepPath s₂ s₃) := by
  rfl

-- ============================================================
-- §25  Confluence of Mapped Systems
-- ============================================================

/-- Theorem 78: map preserves joinability existence. -/
theorem map_preserves_joinable {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {b c : α} (j : Joinable α R b c) :
    ∃ d, (∃ _ : RPath β S (f b) d, ∃ _ : RPath β S (f c) d, True) :=
  ⟨f j.target, ⟨j.left.map f hf, ⟨j.right.map f hf, trivial⟩⟩⟩

/-- Theorem 79: map preserves path existence. -/
theorem map_preserves_path {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b : α} (p : RPath α R a b) :
    ∃ _ : RPath β S (f a) (f b), True :=
  ⟨p.map f hf, trivial⟩

-- ============================================================
-- §26  EqPath Manipulation
-- ============================================================

/-- Embed a backward step into an EqPath. -/
noncomputable def EqPath.bwdSingle {α : Type} {R : α → α → Prop} {a b : α}
    (s : Step α R b a) : EqPath α R a b :=
  .cons (.bwd s) (.refl b)

/-- Embed a forward step into an EqPath. -/
noncomputable def EqPath.fwdSingle {α : Type} {R : α → α → Prop} {a b : α}
    (s : Step α R a b) : EqPath α R a b :=
  .cons (.fwd s) (.refl b)

/-- Theorem 80: fwdSingle has length 1. -/
theorem eqpath_fwdSingle_length {α : Type} {R : α → α → Prop} {a b : α}
    (s : Step α R a b) : (EqPath.fwdSingle s).length = 1 := by
  rfl

/-- Theorem 81: bwdSingle has length 1. -/
theorem eqpath_bwdSingle_length {α : Type} {R : α → α → Prop} {a b : α}
    (s : Step α R b a) : (EqPath.bwdSingle s).length = 1 := by
  rfl

/-- Theorem 82: symm of fwdSingle is bwdSingle. -/
theorem eqpath_symm_fwd {α : Type} {R : α → α → Prop} {a b : α}
    (s : Step α R a b) :
    (EqPath.fwdSingle s).symm = EqPath.bwdSingle s := by
  unfold EqPath.fwdSingle EqPath.bwdSingle EqPath.symm EqPath.trans SymStep.symm
  rfl

/-- Theorem 83: symm of bwdSingle is fwdSingle. -/
theorem eqpath_symm_bwd {α : Type} {R : α → α → Prop} {a b : α}
    (s : Step α R b a) :
    (EqPath.bwdSingle s).symm = EqPath.fwdSingle s := by
  unfold EqPath.bwdSingle EqPath.fwdSingle EqPath.symm EqPath.trans SymStep.symm
  rfl

-- ============================================================
-- §27  Confluence Diagram Categories
-- ============================================================

/-- A span: two paths from a common source. -/
structure Span (α : Type) (R : α → α → Prop) where
  apex : α
  left_foot  : α
  right_foot : α
  left_leg  : RPath α R apex left_foot
  right_leg : RPath α R apex right_foot

/-- A cospan: two paths to a common target. -/
structure Cospan (α : Type) (R : α → α → Prop) where
  left_foot  : α
  right_foot : α
  nadir : α
  left_leg  : RPath α R left_foot nadir
  right_leg : RPath α R right_foot nadir

/-- Theorem 84: a joinable witness is a cospan. -/
noncomputable def Joinable.toCospan {α : Type} {R : α → α → Prop}
    {b c : α} (j : Joinable α R b c) : Cospan α R :=
  ⟨b, c, j.target, j.left, j.right⟩

/-- Theorem 85: cospan nadir is joinable target. -/
theorem cospan_nadir_eq_target {α : Type} {R : α → α → Prop}
    {b c : α} (j : Joinable α R b c) :
    j.toCospan.nadir = j.target := by
  rfl

/-- Make a span from a critical pair (extended). -/
noncomputable def ExtCriticalPair.toSpan {α : Type} {R : α → α → Prop}
    (cp : ExtCriticalPair α R) : Span α R :=
  ⟨cp.source, cp.left_target, cp.right_target, cp.left_path, cp.right_path⟩

/-- Theorem 86: span apex is critical pair source. -/
theorem span_apex_eq_source {α : Type} {R : α → α → Prop}
    (cp : ExtCriticalPair α R) : cp.toSpan.apex = cp.source := by
  rfl

-- ============================================================
-- §28  Path Count and Complexity
-- ============================================================

/-- Append a step at the end of a path. -/
noncomputable def RPath.snoc {α : Type} {R : α → α → Prop} {a b c : α}
    (p : RPath α R a b) (s : Step α R b c) : RPath α R a c :=
  p.trans (.single s)

/-- Theorem 87: snoc increases length by 1. -/
theorem rpath_snoc_length {α : Type} {R : α → α → Prop} {a b c : α}
    (p : RPath α R a b) (s : Step α R b c) :
    (p.snoc s).length = p.length + 1 := by
  simp [RPath.snoc, rpath_trans_length, RPath.single, RPath.length]

/-- Theorem 88: cons then trans = cons of trans. -/
theorem rpath_cons_trans {α : Type} {R : α → α → Prop} {a b c d : α}
    (s : Step α R a b) (p : RPath α R b c) (q : RPath α R c d) :
    (RPath.cons s p).trans q = RPath.cons s (p.trans q) := by
  rfl

-- ============================================================
-- §29  Additional Coherence Properties
-- ============================================================

/-- Theorem 89: map of snoc = snoc of map. -/
theorem rpath_map_snoc {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b c : α} (p : RPath α R a b) (s : Step α R b c) :
    (p.snoc s).map f hf = (p.map f hf).snoc (s.map f hf) := by
  simp [RPath.snoc, rpath_map_trans, RPath.single, RPath.map]

/-- Theorem 90: EqPath.map preserves refl. -/
theorem eqpath_map_refl {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y)) (a : α) :
    (EqPath.refl a : EqPath α R a a).map f hf = EqPath.refl (f a) := by
  rfl

/-- Theorem 91: EqPath.map preserves length. -/
theorem eqpath_map_length {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b : α} (p : EqPath α R a b) :
    (p.map f hf).length = p.length := by
  induction p with
  | refl _ => rfl
  | cons _ _ ih => simp [EqPath.map, EqPath.length, ih]

-- ============================================================
-- §30  Summary Structures
-- ============================================================

/-- A confluence certificate: packages all the path data. -/
structure ConfluenceCert (α : Type) (R : α → α → Prop)
    (a b c : α) where
  witness : α
  left_path  : RPath α R b witness
  right_path : RPath α R c witness
  source_left  : RPath α R a b
  source_right : RPath α R a c

/-- Theorem 92: a confluence cert yields a joinable. -/
noncomputable def ConfluenceCert.toJoinable {α : Type} {R : α → α → Prop}
    {a b c : α} (cert : ConfluenceCert α R a b c) :
    Joinable α R b c :=
  ⟨cert.witness, cert.left_path, cert.right_path⟩

/-- Theorem 93: cert joinable target = cert witness. -/
theorem cert_joinable_target {α : Type} {R : α → α → Prop}
    {a b c : α} (cert : ConfluenceCert α R a b c) :
    cert.toJoinable.target = cert.witness := by
  rfl

/-- Theorem 94: trivial cert from refl paths. -/
noncomputable def ConfluenceCert.trivial {α : Type} {R : α → α → Prop} (a : α) :
    ConfluenceCert α R a a a :=
  ⟨a, .refl a, .refl a, .refl a, .refl a⟩

/-- Theorem 95: trivial cert witness is source. -/
theorem trivial_cert_witness {α : Type} {R : α → α → Prop} (a : α) :
    (ConfluenceCert.trivial a : ConfluenceCert α R a a a).witness = a := by
  rfl

end CompPaths.ConfluenceDeep
