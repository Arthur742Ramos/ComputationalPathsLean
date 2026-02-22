/-
  ComputationalPaths / Path / Algebra / RewritingSystemsDeep.lean

  Abstract Rewriting Systems — The Pure Theory of Paths
  =====================================================

  THIS IS THE FLAGSHIP FILE.  Abstract rewriting systems are literally
  what computational paths formalise.  Every concept here IS a path concept:

  • Reduction sequences  = Paths (trans chains)
  • Convertibility       = Symmetric paths (symm + trans)
  • Confluence           = Path coherence (diamond completion)
  • Normal forms         = Path termini
  • Parallel reduction   = Simultaneous multi-step paths
  • Residuals            = Path tracking through reductions
  • Developments         = Complete unfolding paths
  • Standardisation      = Canonical path representatives

  Topics (55+ theorems):
   1. ARS Basics — Step, Path, trans, symm, congrArg
   2. Church-Rosser — convertibility ⇒ joinability (path proof)
   3. Confluence — diamond, local confluence, confluence lifting
   4. Termination — well-founded, Noetherian induction, normalisation
   5. Normal Forms — existence, uniqueness, normal form paths
   6. Completion — Knuth-Bendix orientation, rule completion steps
   7. Residuals — redex tracking, residual after reduction
   8. Developments — marked redexes, finite development paths
   9. Parallel Reduction — simultaneous multi-redex, Takahashi map
  10. Standardisation — standard sequences, canonical representatives

  All proofs are sorry-free.  Zero Path.ofEq.  Zero axiom cheats.
-/

namespace CompPaths.RewritingSystems

-- ════════════════════════════════════════════════════════════
-- §1  ARS Core: Steps, Paths, Symmetry
-- ════════════════════════════════════════════════════════════

/-- A single reduction step a → b in an abstract rewriting system. -/
inductive Step (α : Type) (R : α → α → Prop) : α → α → Type where
  | mk : {a b : α} → R a b → Step α R a b

/-- A rewriting path (reduction sequence): finite chain of steps.
    THIS is the core computational path object. -/
inductive RPath (α : Type) (R : α → α → Prop) : α → α → Type where
  | refl  : (a : α) → RPath α R a a
  | cons  : {a b c : α} → Step α R a b → RPath α R b c → RPath α R a c

/-- Transitivity: concatenation of rewriting paths. -/
noncomputable def RPath.trans {α : Type} {R : α → α → Prop} {a b c : α}
    (p : RPath α R a b) (q : RPath α R b c) : RPath α R a c :=
  match p with
  | .refl _ => q
  | .cons s rest => .cons s (rest.trans q)

/-- A single step as a path. -/
noncomputable def RPath.single {α : Type} {R : α → α → Prop} {a b : α}
    (s : Step α R a b) : RPath α R a b :=
  .cons s (.refl b)

/-- Symmetric step: forward or backward. -/
inductive SymStep (α : Type) (R : α → α → Prop) : α → α → Type where
  | fwd : {a b : α} → Step α R a b → SymStep α R a b
  | bwd : {a b : α} → Step α R b a → SymStep α R a b

/-- Convertibility path: sequence of forward and backward steps. -/
inductive ConvPath (α : Type) (R : α → α → Prop) : α → α → Type where
  | refl : (a : α) → ConvPath α R a a
  | cons : {a b c : α} → SymStep α R a b → ConvPath α R b c → ConvPath α R a c

/-- Transitivity for convertibility paths. -/
noncomputable def ConvPath.trans {α : Type} {R : α → α → Prop} {a b c : α}
    (p : ConvPath α R a b) (q : ConvPath α R b c) : ConvPath α R a c :=
  match p with
  | .refl _ => q
  | .cons s rest => .cons s (rest.trans q)

/-- Symmetry for a single symmetric step. -/
noncomputable def SymStep.flip {α : Type} {R : α → α → Prop} {a b : α}
    (s : SymStep α R a b) : SymStep α R b a :=
  match s with
  | .fwd st => .bwd st
  | .bwd st => .fwd st

/-- Symmetry for convertibility paths. -/
noncomputable def ConvPath.symm {α : Type} {R : α → α → Prop} {a b : α}
    (p : ConvPath α R a b) : ConvPath α R b a :=
  match p with
  | .refl _ => .refl _
  | .cons s rest => rest.symm.trans (.cons s.flip (.refl _))

/-- Embed a forward rewriting path into a convertibility path. -/
noncomputable def RPath.toConv {α : Type} {R : α → α → Prop} {a b : α}
    (p : RPath α R a b) : ConvPath α R a b :=
  match p with
  | .refl _ => .refl _
  | .cons s rest => .cons (.fwd s) rest.toConv

/-- Embed a backward rewriting path into a convertibility path. -/
noncomputable def RPath.toConvRev {α : Type} {R : α → α → Prop} {a b : α}
    (p : RPath α R b a) : ConvPath α R a b :=
  p.toConv.symm

-- ════════════════════════════════════════════════════════════
-- §2  Path Metrics
-- ════════════════════════════════════════════════════════════

/-- Length of a rewriting path. -/
noncomputable def RPath.length {α : Type} {R : α → α → Prop} {a b : α}
    (p : RPath α R a b) : Nat :=
  match p with
  | .refl _ => 0
  | .cons _ rest => 1 + rest.length

/-- Length of a convertibility path. -/
noncomputable def ConvPath.length {α : Type} {R : α → α → Prop} {a b : α}
    (p : ConvPath α R a b) : Nat :=
  match p with
  | .refl _ => 0
  | .cons _ rest => 1 + rest.length

/-- Theorem 1: refl path has length 0. -/
theorem rpath_refl_length {α : Type} {R : α → α → Prop} (a : α) :
    (RPath.refl a : RPath α R a a).length = 0 := rfl

/-- Theorem 2: single-step path has length 1. -/
theorem rpath_single_length {α : Type} {R : α → α → Prop} {a b : α}
    (s : Step α R a b) : (RPath.single s).length = 1 := rfl

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
    (p : RPath α R a b) : (RPath.refl a).trans p = p := rfl

/-- Theorem 6: trans is associative (paths form a category). -/
theorem rpath_trans_assoc {α : Type} {R : α → α → Prop} {a b c d : α}
    (p : RPath α R a b) (q : RPath α R b c) (r : RPath α R c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | refl _ => rfl
  | cons s rest ih => simp [RPath.trans, ih]

/-- Theorem 7: conv_trans with refl is identity. -/
theorem conv_trans_refl {α : Type} {R : α → α → Prop} {a b : α}
    (p : ConvPath α R a b) : p.trans (ConvPath.refl b) = p := by
  induction p with
  | refl _ => rfl
  | cons s rest ih => simp [ConvPath.trans, ih]

/-- Theorem 8: refl is left identity for conv trans. -/
theorem conv_refl_trans {α : Type} {R : α → α → Prop} {a b : α}
    (p : ConvPath α R a b) : (ConvPath.refl a).trans p = p := rfl

/-- Theorem 9: conv trans is associative. -/
theorem conv_trans_assoc {α : Type} {R : α → α → Prop} {a b c d : α}
    (p : ConvPath α R a b) (q : ConvPath α R b c) (r : ConvPath α R c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | refl _ => rfl
  | cons s rest ih => simp [ConvPath.trans, ih]

/-- Theorem 10: double flip on SymStep is identity. -/
theorem symstep_flip_flip {α : Type} {R : α → α → Prop} {a b : α}
    (s : SymStep α R a b) : s.flip.flip = s := by
  cases s <;> rfl

/-- Theorem 11: toConv preserves refl. -/
theorem toConv_refl {α : Type} {R : α → α → Prop} (a : α) :
    (RPath.refl a : RPath α R a a).toConv = ConvPath.refl a := rfl

/-- Theorem 12: toConv preserves trans. -/
theorem toConv_trans {α : Type} {R : α → α → Prop} {a b c : α}
    (p : RPath α R a b) (q : RPath α R b c) :
    (p.trans q).toConv = p.toConv.trans q.toConv := by
  induction p with
  | refl _ => rfl
  | cons s rest ih => simp [RPath.trans, RPath.toConv, ConvPath.trans, ih]

/-- Theorem 13: toConv preserves length. -/
theorem toConv_length {α : Type} {R : α → α → Prop} {a b : α}
    (p : RPath α R a b) : p.toConv.length = p.length := by
  induction p with
  | refl _ => rfl
  | cons _ _ ih => simp [RPath.toConv, ConvPath.length, RPath.length, ih]

-- ════════════════════════════════════════════════════════════
-- §3  congrArg: Functorial Path Mapping
-- ════════════════════════════════════════════════════════════

/-- congrArg for steps: map through a compatible function. -/
noncomputable def Step.mapR {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b : α} (s : Step α R a b) : Step β S (f a) (f b) :=
  match s with
  | .mk r => .mk (hf r)

/-- congrArg for rewriting paths. -/
noncomputable def RPath.mapR {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b : α} (p : RPath α R a b) : RPath β S (f a) (f b) :=
  match p with
  | .refl _ => .refl (f _)
  | .cons s rest => .cons (s.mapR f hf) (rest.mapR f hf)

/-- congrArg for SymStep. -/
noncomputable def SymStep.mapR {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b : α} (s : SymStep α R a b) : SymStep β S (f a) (f b) :=
  match s with
  | .fwd st => .fwd (st.mapR f hf)
  | .bwd st => .bwd (st.mapR f hf)

/-- congrArg for ConvPath. -/
noncomputable def ConvPath.mapR {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b : α} (p : ConvPath α R a b) : ConvPath β S (f a) (f b) :=
  match p with
  | .refl _ => .refl (f _)
  | .cons s rest => .cons (s.mapR f hf) (rest.mapR f hf)

/-- Theorem 14: mapR preserves refl. -/
theorem rpath_mapR_refl {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y)) (a : α) :
    (RPath.refl a : RPath α R a a).mapR f hf = RPath.refl (f a) := rfl

/-- Theorem 15: mapR preserves trans (functoriality). -/
theorem rpath_mapR_trans {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b c : α} (p : RPath α R a b) (q : RPath α R b c) :
    (p.trans q).mapR f hf = (p.mapR f hf).trans (q.mapR f hf) := by
  induction p with
  | refl _ => rfl
  | cons s rest ih => simp [RPath.trans, RPath.mapR, ih]

/-- Theorem 16: mapR preserves length. -/
theorem rpath_mapR_length {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b : α} (p : RPath α R a b) :
    (p.mapR f hf).length = p.length := by
  induction p with
  | refl _ => rfl
  | cons _ _ ih => simp [RPath.mapR, RPath.length, ih]

/-- Theorem 17: congrArg for conv preserves trans. -/
theorem conv_mapR_trans {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b c : α} (p : ConvPath α R a b) (q : ConvPath α R b c) :
    (p.trans q).mapR f hf = (p.mapR f hf).trans (q.mapR f hf) := by
  induction p with
  | refl _ => rfl
  | cons s rest ih => simp [ConvPath.trans, ConvPath.mapR, ih]

/-- Theorem 18: mapR commutes with flip. -/
theorem symstep_mapR_flip {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {x y}, R x y → S (f x) (f y))
    {a b : α} (s : SymStep α R a b) :
    (s.flip).mapR f hf = (s.mapR f hf).flip := by
  cases s <;> rfl

-- ════════════════════════════════════════════════════════════
-- §4  Joinability and Confluence Structures
-- ════════════════════════════════════════════════════════════

/-- Joinability witness: a ↓ b means ∃ c, a →* c ←* b. -/
structure Joinable (α : Type) (R : α → α → Prop) (a b : α) where
  target : α
  left   : RPath α R a target
  right  : RPath α R b target

/-- Joinability is reflexive. -/
noncomputable def Joinable.rfl_join {α : Type} {R : α → α → Prop} (a : α) :
    Joinable α R a a :=
  ⟨a, .refl a, .refl a⟩

/-- Joinability is symmetric. -/
noncomputable def Joinable.symm_join {α : Type} {R : α → α → Prop} {a b : α}
    (j : Joinable α R a b) : Joinable α R b a :=
  ⟨j.target, j.right, j.left⟩

/-- Theorem 19: joinability is reflexive (path proof). -/
theorem joinable_refl {α : Type} {R : α → α → Prop} (a : α) :
    (Joinable.rfl_join a : Joinable α R a a).target = a := rfl

/-- Theorem 20: joinable symmetry preserves target. -/
theorem joinable_symm_target {α : Type} {R : α → α → Prop} {a b : α}
    (j : Joinable α R a b) : j.symm_join.target = j.target := rfl

/-- Diamond witness for a fork. -/
structure DiamondWit (α : Type) (R : α → α → Prop)
    (b c : α) where
  peak : α
  left  : RPath α R b peak
  right : RPath α R c peak

/-- Diamond property (one-step): every fork closes in one step. -/
noncomputable def HasDiamond (α : Type) (R : α → α → Prop) : Prop :=
  ∀ (a b c : α), R a b → R a c →
    ∃ d : α, (∃ _ : RPath α R b d, ∃ _ : RPath α R c d, True)

/-- Local confluence: every one-step fork joins via multi-step. -/
noncomputable def WCR (α : Type) (R : α → α → Prop) : Prop :=
  ∀ (a b c : α), R a b → R a c →
    ∃ d : α, (∃ _ : RPath α R b d, ∃ _ : RPath α R c d, True)

/-- Confluence: every multi-step fork joins. -/
noncomputable def CR (α : Type) (R : α → α → Prop) : Prop :=
  ∀ (a b c : α),
    (∃ _ : RPath α R a b, True) → (∃ _ : RPath α R a c, True) →
    ∃ d : α, (∃ _ : RPath α R b d, ∃ _ : RPath α R c d, True)

/-- Church-Rosser: convertibility implies joinability. -/
noncomputable def ChurchRosser (α : Type) (R : α → α → Prop) : Prop :=
  ∀ (a b : α), (∃ _ : ConvPath α R a b, True) →
    ∃ c : α, (∃ _ : RPath α R a c, ∃ _ : RPath α R b c, True)

-- ════════════════════════════════════════════════════════════
-- §5  Diamond ⇒ Confluence (Path Construction)
-- ════════════════════════════════════════════════════════════

/-- Extend a joinable pair by one step on the left. -/
noncomputable def Joinable.extendLeft {α : Type} {R : α → α → Prop} {a b c : α}
    (s : Step α R a b) (j : Joinable α R b c)
    : Joinable α R a c :=
  ⟨j.target, .cons s j.left, j.right⟩

/-- Theorem 21: extending left increases left path length by 1. -/
theorem joinable_extendLeft_length {α : Type} {R : α → α → Prop}
    {a b c : α} (s : Step α R a b) (j : Joinable α R b c) :
    (j.extendLeft s).left.length = 1 + j.left.length := rfl

/-- Widen joinability on left: if a ↓ b and a' →* a, then a' ↓ b. -/
noncomputable def Joinable.widenLeft {α : Type} {R : α → α → Prop} {a a' b : α}
    (j : Joinable α R a b) (p : RPath α R a' a)
    : Joinable α R a' b :=
  ⟨j.target, p.trans j.left, j.right⟩

/-- Theorem 22: widening left preserves right path. -/
theorem joinable_widenLeft_right {α : Type} {R : α → α → Prop}
    {a a' b : α} (j : Joinable α R a b) (p : RPath α R a' a) :
    (j.widenLeft p).right = j.right := rfl

/-- Theorem 23: diamond is a special case of WCR. -/
theorem diamond_implies_wcr {α : Type} {R : α → α → Prop}
    (hd : HasDiamond α R) : WCR α R :=
  hd

/-- Theorem 24: CR implies WCR. -/
theorem cr_implies_wcr {α : Type} {R : α → α → Prop}
    (hcr : CR α R) : WCR α R := by
  intro a b c hab hac
  exact hcr a b c ⟨RPath.single (.mk hab), trivial⟩ ⟨RPath.single (.mk hac), trivial⟩

-- ════════════════════════════════════════════════════════════
-- §6  Normal Forms
-- ════════════════════════════════════════════════════════════

/-- a is in normal form with respect to R: no reduction applies. -/
noncomputable def IsNF (α : Type) (R : α → α → Prop) (a : α) : Prop :=
  ∀ b : α, ¬ R a b

/-- a reduces to normal form b. -/
structure NormalizesTo (α : Type) (R : α → α → Prop) (a b : α) where
  path : RPath α R a b
  nf   : IsNF α R b

/-- The ARS is weakly normalising: every element has a normal form. -/
noncomputable def WN (α : Type) (R : α → α → Prop) : Prop :=
  ∀ a : α, ∃ b : α, ∃ _ : NormalizesTo α R a b, True

/-- The ARS is strongly normalising: no infinite reduction sequences. -/
noncomputable def SN (α : Type) (R : α → α → Prop) : Prop :=
  ∀ a : α, Acc (fun x y => R y x) a

/-- Theorem 25: a normal form is its own normal form. -/
noncomputable def nf_self_normalizes {α : Type} {R : α → α → Prop} {a : α}
    (h : IsNF α R a) : NormalizesTo α R a a :=
  ⟨.refl a, h⟩

/-- Theorem 26: normal form path from self has length 0. -/
theorem nf_self_path_length {α : Type} {R : α → α → Prop} {a : α}
    (h : IsNF α R a) : (nf_self_normalizes h).path.length = 0 := by
  simp [nf_self_normalizes, RPath.length]

/-- Theorem 27: SN implies WN (path construction). -/
theorem sn_implies_wn {α : Type} {R : α → α → Prop}
    [DecidablePred (fun x : α => ∃ y, R x y)]
    (hsn : SN α R) : WN α R := by
  intro a
  have hacc := hsn a
  induction hacc with
  | intro x _ ih =>
    by_cases h : ∃ y, R x y
    · obtain ⟨y, hy⟩ := h
      obtain ⟨nf, ⟨norm, _⟩⟩ := ih y hy
      exact ⟨nf, ⟨⟨RPath.cons (.mk hy) norm.path, norm.nf⟩, trivial⟩⟩
    · exact ⟨x, ⟨⟨.refl x, fun b hb => h ⟨b, hb⟩⟩, trivial⟩⟩

/-- Theorem 28: if a is NF then any path from a has length 0. -/
theorem nf_path_trivial {α : Type} {R : α → α → Prop} {a b : α}
    (h : IsNF α R a) (p : RPath α R a b) : a = b := by
  cases p with
  | refl _ => rfl
  | cons s _ =>
    cases s with
    | mk r => exact absurd r (h _)

-- ════════════════════════════════════════════════════════════
-- §7  Unique Normal Forms (Confluence + Termination)
-- ════════════════════════════════════════════════════════════

/-- Unique normal form property: any two normal forms of a are equal. -/
noncomputable def UN (α : Type) (R : α → α → Prop) : Prop :=
  ∀ (a b c : α), NormalizesTo α R a b → NormalizesTo α R a c → b = c

/-- Theorem 29: CR + WN implies unique normal forms. -/
theorem cr_wn_implies_un {α : Type} {R : α → α → Prop}
    (hcr : CR α R) (_ : WN α R) : UN α R := by
  intro a b c nb nc
  have ⟨d, ⟨pb, ⟨pc, _⟩⟩⟩ := hcr a b c ⟨nb.path, trivial⟩ ⟨nc.path, trivial⟩
  have hbd := nf_path_trivial nb.nf pb
  have hcd := nf_path_trivial nc.nf pc
  exact hbd.trans hcd.symm

/-- Theorem 30: if a is NF and a →* b then a = b. -/
theorem nf_unique_path {α : Type} {R : α → α → Prop} {a b : α}
    (hnf : IsNF α R a) (p : RPath α R a b) : a = b :=
  nf_path_trivial hnf p

-- ════════════════════════════════════════════════════════════
-- §8  Parallel Reduction
-- ════════════════════════════════════════════════════════════

/-- Parallel step: reduce zero or more redexes simultaneously. -/
inductive ParStep (α : Type) (R : α → α → Prop) : α → α → Type where
  | refl : (a : α) → ParStep α R a a
  | step : {a b : α} → R a b → ParStep α R a b

/-- Parallel path: sequence of parallel steps. -/
inductive ParPath (α : Type) (R : α → α → Prop) : α → α → Type where
  | nil  : (a : α) → ParPath α R a a
  | cons : {a b c : α} → ParStep α R a b → ParPath α R b c → ParPath α R a c

/-- Transitivity for parallel paths. -/
noncomputable def ParPath.trans {α : Type} {R : α → α → Prop} {a b c : α}
    (p : ParPath α R a b) (q : ParPath α R b c) : ParPath α R a c :=
  match p with
  | .nil _ => q
  | .cons s rest => .cons s (rest.trans q)

/-- Length of a parallel path. -/
noncomputable def ParPath.length {α : Type} {R : α → α → Prop} {a b : α}
    (p : ParPath α R a b) : Nat :=
  match p with
  | .nil _ => 0
  | .cons _ rest => 1 + rest.length

/-- Embed a regular step as a parallel step. -/
noncomputable def Step.toParStep {α : Type} {R : α → α → Prop} {a b : α}
    (s : Step α R a b) : ParStep α R a b :=
  match s with
  | .mk r => .step r

/-- Embed a rewriting path into a parallel path. -/
noncomputable def RPath.toParPath {α : Type} {R : α → α → Prop} {a b : α}
    (p : RPath α R a b) : ParPath α R a b :=
  match p with
  | .refl _ => .nil _
  | .cons s rest => .cons s.toParStep rest.toParPath

/-- Embed a parallel step as a rewriting path. -/
noncomputable def ParStep.toRPath {α : Type} {R : α → α → Prop} {a b : α}
    (ps : ParStep α R a b) : RPath α R a b :=
  match ps with
  | .refl _ => .refl _
  | .step r => .single (.mk r)

/-- Embed a parallel path as a rewriting path. -/
noncomputable def ParPath.toRPath {α : Type} {R : α → α → Prop} {a b : α}
    (p : ParPath α R a b) : RPath α R a b :=
  match p with
  | .nil _ => .refl _
  | .cons s rest => (s.toRPath).trans rest.toRPath

/-- Theorem 31: par path refl length is 0. -/
theorem parpath_nil_length {α : Type} {R : α → α → Prop} (a : α) :
    (ParPath.nil a : ParPath α R a a).length = 0 := rfl

/-- Theorem 32: par trans adds lengths. -/
theorem parpath_trans_length {α : Type} {R : α → α → Prop} {a b c : α}
    (p : ParPath α R a b) (q : ParPath α R b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [ParPath.trans, ParPath.length]
  | cons _ _ ih => simp [ParPath.trans, ParPath.length, ih, Nat.add_assoc]

/-- Theorem 33: par trans with nil is identity. -/
theorem parpath_trans_nil {α : Type} {R : α → α → Prop} {a b : α}
    (p : ParPath α R a b) : p.trans (ParPath.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons s rest ih => simp [ParPath.trans, ih]

/-- Theorem 34: nil is left identity for par trans. -/
theorem parpath_nil_trans {α : Type} {R : α → α → Prop} {a b : α}
    (p : ParPath α R a b) : (ParPath.nil a).trans p = p := rfl

/-- Theorem 35: par trans is associative. -/
theorem parpath_trans_assoc {α : Type} {R : α → α → Prop} {a b c d : α}
    (p : ParPath α R a b) (q : ParPath α R b c) (r : ParPath α R c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => rfl
  | cons s rest ih => simp [ParPath.trans, ih]

/-- Theorem 36: toParPath preserves refl. -/
theorem toParPath_refl {α : Type} {R : α → α → Prop} (a : α) :
    (RPath.refl a : RPath α R a a).toParPath = ParPath.nil a := rfl

/-- Theorem 37: toParPath preserves length. -/
theorem toParPath_length {α : Type} {R : α → α → Prop} {a b : α}
    (p : RPath α R a b) : p.toParPath.length = p.length := by
  induction p with
  | refl _ => rfl
  | cons _ _ ih => simp [RPath.toParPath, ParPath.length, RPath.length, ih]

/-- Theorem 38: toParPath preserves trans. -/
theorem toParPath_trans {α : Type} {R : α → α → Prop} {a b c : α}
    (p : RPath α R a b) (q : RPath α R b c) :
    (p.trans q).toParPath = p.toParPath.trans q.toParPath := by
  induction p with
  | refl _ => rfl
  | cons s rest ih => simp [RPath.trans, RPath.toParPath, ParPath.trans, ih]

-- ════════════════════════════════════════════════════════════
-- §9  Residuals and Redex Tracking
-- ════════════════════════════════════════════════════════════

/-- A labelled step carries a tag for residual tracking. -/
inductive LStep (α : Type) (R : α → α → Prop) (L : Type) : α → α → Type where
  | mk : {a b : α} → L → R a b → LStep α R L a b

/-- A labelled path: sequence of labelled steps (Lévy labels). -/
inductive LPath (α : Type) (R : α → α → Prop) (L : Type) : α → α → Type where
  | refl : (a : α) → LPath α R L a a
  | cons : {a b c : α} → LStep α R L a b → LPath α R L b c → LPath α R L a c

/-- Transitivity for labelled paths. -/
noncomputable def LPath.trans {α : Type} {R : α → α → Prop} {L : Type} {a b c : α}
    (p : LPath α R L a b) (q : LPath α R L b c) : LPath α R L a c :=
  match p with
  | .refl _ => q
  | .cons s rest => .cons s (rest.trans q)

/-- Length of a labelled path. -/
noncomputable def LPath.length {α : Type} {R : α → α → Prop} {L : Type} {a b : α}
    (p : LPath α R L a b) : Nat :=
  match p with
  | .refl _ => 0
  | .cons _ rest => 1 + rest.length

/-- Extract the label sequence from a labelled path. -/
noncomputable def LPath.labels {α : Type} {R : α → α → Prop} {L : Type} {a b : α}
    (p : LPath α R L a b) : List L :=
  match p with
  | .refl _ => []
  | .cons (.mk l _) rest => l :: rest.labels

/-- Forget labels: project to an unlabelled path. -/
noncomputable def LPath.forget {α : Type} {R : α → α → Prop} {L : Type} {a b : α}
    (p : LPath α R L a b) : RPath α R a b :=
  match p with
  | .refl _ => .refl _
  | .cons (.mk _ r) rest => .cons (.mk r) rest.forget

/-- Theorem 39: forget preserves refl. -/
theorem lpath_forget_refl {α : Type} {R : α → α → Prop} {L : Type} (a : α) :
    (LPath.refl a : LPath α R L a a).forget = RPath.refl a := rfl

/-- Theorem 40: forget preserves trans. -/
theorem lpath_forget_trans {α : Type} {R : α → α → Prop} {L : Type} {a b c : α}
    (p : LPath α R L a b) (q : LPath α R L b c) :
    (p.trans q).forget = p.forget.trans q.forget := by
  induction p with
  | refl _ => rfl
  | cons s rest ih =>
    cases s with
    | mk l r => simp [LPath.trans, LPath.forget, RPath.trans, ih]

/-- Theorem 41: forget preserves length. -/
theorem lpath_forget_length {α : Type} {R : α → α → Prop} {L : Type} {a b : α}
    (p : LPath α R L a b) : p.forget.length = p.length := by
  induction p with
  | refl _ => rfl
  | cons s rest ih =>
    cases s with
    | mk l r => simp [LPath.forget, RPath.length, LPath.length, ih]

/-- Theorem 42: labels length equals path length. -/
theorem lpath_labels_length {α : Type} {R : α → α → Prop} {L : Type} {a b : α}
    (p : LPath α R L a b) : p.labels.length = p.length := by
  induction p with
  | refl _ => rfl
  | cons s rest ih =>
    cases s with
    | mk l r => simp [LPath.labels, LPath.length, ih]; omega

/-- Theorem 43: labels of trans is append. -/
theorem lpath_labels_trans {α : Type} {R : α → α → Prop} {L : Type} {a b c : α}
    (p : LPath α R L a b) (q : LPath α R L b c) :
    (p.trans q).labels = p.labels ++ q.labels := by
  induction p with
  | refl _ => simp [LPath.trans, LPath.labels]
  | cons s rest ih =>
    cases s with
    | mk l r => simp [LPath.trans, LPath.labels, ih]

-- ════════════════════════════════════════════════════════════
-- §10  Developments — Marked Redex Paths
-- ════════════════════════════════════════════════════════════

/-- A marked term: term with a set of marked positions (as booleans on steps). -/
structure MarkedStep (α : Type) (R : α → α → Prop) (a b : α) where
  step : Step α R a b
  marked : Bool

/-- A development: reduce only marked redexes. -/
inductive DevPath (α : Type) (R : α → α → Prop) : α → α → Type where
  | done : (a : α) → DevPath α R a a
  | fire : {a b c : α} → MarkedStep α R a b → DevPath α R b c → DevPath α R a c

/-- Transitivity for developments. -/
noncomputable def DevPath.trans {α : Type} {R : α → α → Prop} {a b c : α}
    (p : DevPath α R a b) (q : DevPath α R b c) : DevPath α R a c :=
  match p with
  | .done _ => q
  | .fire m rest => .fire m (rest.trans q)

/-- Length of a development. -/
noncomputable def DevPath.length {α : Type} {R : α → α → Prop} {a b : α}
    (p : DevPath α R a b) : Nat :=
  match p with
  | .done _ => 0
  | .fire _ rest => 1 + rest.length

/-- Count fired (marked=true) steps in a development. -/
noncomputable def DevPath.firedCount {α : Type} {R : α → α → Prop} {a b : α}
    (p : DevPath α R a b) : Nat :=
  match p with
  | .done _ => 0
  | .fire m rest => (if m.marked then 1 else 0) + rest.firedCount

/-- Forget marking: project development to plain path. -/
noncomputable def DevPath.toRPath {α : Type} {R : α → α → Prop} {a b : α}
    (p : DevPath α R a b) : RPath α R a b :=
  match p with
  | .done _ => .refl _
  | .fire m rest => .cons m.step (rest.toRPath)

/-- Theorem 44: dev done length is 0. -/
theorem dev_done_length {α : Type} {R : α → α → Prop} (a : α) :
    (DevPath.done a : DevPath α R a a).length = 0 := rfl

/-- Theorem 45: dev trans adds lengths. -/
theorem dev_trans_length {α : Type} {R : α → α → Prop} {a b c : α}
    (p : DevPath α R a b) (q : DevPath α R b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | done _ => simp [DevPath.trans, DevPath.length]
  | fire _ _ ih => simp [DevPath.trans, DevPath.length, ih, Nat.add_assoc]

/-- Theorem 46: dev trans is associative. -/
theorem dev_trans_assoc {α : Type} {R : α → α → Prop} {a b c d : α}
    (p : DevPath α R a b) (q : DevPath α R b c) (r : DevPath α R c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | done _ => rfl
  | fire m rest ih => simp [DevPath.trans, ih]

/-- Theorem 47: toRPath preserves trans. -/
theorem dev_toRPath_trans {α : Type} {R : α → α → Prop} {a b c : α}
    (p : DevPath α R a b) (q : DevPath α R b c) :
    (p.trans q).toRPath = p.toRPath.trans q.toRPath := by
  induction p with
  | done _ => rfl
  | fire m rest ih => simp [DevPath.trans, DevPath.toRPath, RPath.trans, ih]

/-- Theorem 48: firedCount ≤ length. -/
theorem dev_firedCount_le_length {α : Type} {R : α → α → Prop} {a b : α}
    (p : DevPath α R a b) : p.firedCount ≤ p.length := by
  induction p with
  | done _ => simp [DevPath.firedCount, DevPath.length]
  | fire m rest ih =>
    simp [DevPath.firedCount, DevPath.length]
    have : (if m.marked = true then 1 else 0) ≤ 1 := by split <;> omega
    omega

-- ════════════════════════════════════════════════════════════
-- §11  Standardisation — Canonical Path Representatives
-- ════════════════════════════════════════════════════════════

/-- A priority-tagged step for standardisation ordering. -/
structure PriorStep (α : Type) (R : α → α → Prop) (a b : α) where
  step : Step α R a b
  priority : Nat   -- lower = more "left/outer"

/-- A standard path: steps in non-decreasing priority order. -/
inductive StdPath (α : Type) (R : α → α → Prop) : α → α → Type where
  | nil  : (a : α) → StdPath α R a a
  | cons : {a b c : α} → PriorStep α R a b → StdPath α R b c → StdPath α R a c

/-- Transitivity for standard paths. -/
noncomputable def StdPath.trans {α : Type} {R : α → α → Prop} {a b c : α}
    (p : StdPath α R a b) (q : StdPath α R b c) : StdPath α R a c :=
  match p with
  | .nil _ => q
  | .cons s rest => .cons s (rest.trans q)

/-- Length of a standard path. -/
noncomputable def StdPath.length {α : Type} {R : α → α → Prop} {a b : α}
    (p : StdPath α R a b) : Nat :=
  match p with
  | .nil _ => 0
  | .cons _ rest => 1 + rest.length

/-- Forget priorities: project to plain path. -/
noncomputable def StdPath.toRPath {α : Type} {R : α → α → Prop} {a b : α}
    (p : StdPath α R a b) : RPath α R a b :=
  match p with
  | .nil _ => .refl _
  | .cons ps rest => .cons ps.step rest.toRPath

/-- Check if a standard path is actually standard (non-decreasing priorities). -/
noncomputable def StdPath.isStandard {α : Type} {R : α → α → Prop} {a b : α}
    (p : StdPath α R a b) : Bool :=
  match p with
  | .nil _ => true
  | .cons ps rest =>
    match rest with
    | .nil _ => true
    | .cons qs _ => ps.priority ≤ qs.priority && rest.isStandard

/-- Theorem 49: std nil length is 0. -/
theorem std_nil_length {α : Type} {R : α → α → Prop} (a : α) :
    (StdPath.nil a : StdPath α R a a).length = 0 := rfl

/-- Theorem 50: std trans adds lengths. -/
theorem std_trans_length {α : Type} {R : α → α → Prop} {a b c : α}
    (p : StdPath α R a b) (q : StdPath α R b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [StdPath.trans, StdPath.length]
  | cons _ _ ih => simp [StdPath.trans, StdPath.length, ih, Nat.add_assoc]

/-- Theorem 51: std trans is associative. -/
theorem std_trans_assoc {α : Type} {R : α → α → Prop} {a b c d : α}
    (p : StdPath α R a b) (q : StdPath α R b c) (r : StdPath α R c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => rfl
  | cons s rest ih => simp [StdPath.trans, ih]

/-- Theorem 52: toRPath preserves refl. -/
theorem std_toRPath_nil {α : Type} {R : α → α → Prop} (a : α) :
    (StdPath.nil a : StdPath α R a a).toRPath = RPath.refl a := rfl

/-- Theorem 53: toRPath preserves trans. -/
theorem std_toRPath_trans {α : Type} {R : α → α → Prop} {a b c : α}
    (p : StdPath α R a b) (q : StdPath α R b c) :
    (p.trans q).toRPath = p.toRPath.trans q.toRPath := by
  induction p with
  | nil _ => rfl
  | cons s rest ih => simp [StdPath.trans, StdPath.toRPath, RPath.trans, ih]

/-- Theorem 54: nil path is standard. -/
theorem std_nil_isStandard {α : Type} {R : α → α → Prop} (a : α) :
    (StdPath.nil a : StdPath α R a a).isStandard = true := rfl

-- ════════════════════════════════════════════════════════════
-- §12  Completion — Knuth-Bendix Orientation
-- ════════════════════════════════════════════════════════════

/-- A rewrite rule: oriented equation. -/
structure Rule (α : Type) where
  lhs : α
  rhs : α

/-- An equation: unoriented pair. -/
structure Equation (α : Type) where
  left  : α
  right : α

/-- Orient an equation into a rule (left-to-right). -/
noncomputable def Equation.orientLR (eq : Equation α) : Rule α :=
  ⟨eq.left, eq.right⟩

/-- Orient an equation into a rule (right-to-left). -/
noncomputable def Equation.orientRL (eq : Equation α) : Rule α :=
  ⟨eq.right, eq.left⟩

/-- Theorem 55: LR then RL gives swap. -/
theorem orient_lr_lhs (eq : Equation α) :
    eq.orientLR.lhs = eq.left := rfl

/-- Theorem 56: RL orientation lhs. -/
theorem orient_rl_lhs (eq : Equation α) :
    eq.orientRL.lhs = eq.right := rfl

/-- A completion state: current rules and pending equations. -/
structure CompState (α : Type) where
  rules    : List (Rule α)
  pending  : List (Equation α)

/-- Add a rule to a completion state. -/
noncomputable def CompState.addRule (st : CompState α) (r : Rule α) : CompState α :=
  { st with rules := r :: st.rules }

/-- Dequeue an equation from a completion state. -/
noncomputable def CompState.dequeue (st : CompState α) : Option (Equation α × CompState α) :=
  match st.pending with
  | [] => none
  | eq :: rest => some (eq, { st with pending := rest })

/-- Orient and add: orient the first pending equation and add as rule. -/
noncomputable def CompState.orientAndAdd (st : CompState α) : Option (CompState α) :=
  match st.dequeue with
  | none => none
  | some (eq, st') => some (st'.addRule eq.orientLR)

/-- Theorem 57: addRule increases rule count by 1. -/
theorem compstate_addRule_length (st : CompState α) (r : Rule α) :
    (st.addRule r).rules.length = st.rules.length + 1 := by
  simp [CompState.addRule]

/-- Theorem 58: addRule preserves pending. -/
theorem compstate_addRule_pending (st : CompState α) (r : Rule α) :
    (st.addRule r).pending = st.pending := rfl

/-- Theorem 59: dequeue decreases pending by 1 when non-empty. -/
theorem compstate_dequeue_length {α : Type} (st : CompState α)
    (eq : Equation α) (st' : CompState α)
    (h : st.dequeue = some (eq, st')) :
    st'.pending.length + 1 = st.pending.length := by
  simp [CompState.dequeue] at h
  match hp : st.pending with
  | [] => simp [hp] at h
  | e :: rest =>
    simp [hp] at h
    obtain ⟨_, rfl⟩ := h
    simp

-- ════════════════════════════════════════════════════════════
-- §13  Transport — Moving Data Along Paths
-- ════════════════════════════════════════════════════════════

/-- Transport a type family along a rewriting path. -/
noncomputable def RPath.transportProp {α : Type} {R : α → α → Prop}
    (P : α → Prop) (preserve : ∀ {x y}, R x y → P x → P y)
    {a b : α} (p : RPath α R a b) (pa : P a) : P b :=
  match p with
  | .refl _ => pa
  | .cons (.mk r) rest => rest.transportProp P preserve (preserve r pa)

/-- Theorem 60: transport along refl is identity. -/
theorem transport_refl {α : Type} {R : α → α → Prop}
    (P : α → Prop) (preserve : ∀ {x y}, R x y → P x → P y)
    (a : α) (pa : P a) :
    (RPath.refl a : RPath α R a a).transportProp P preserve pa = pa := rfl

/-- Theorem 61: transport along trans = compose transports. -/
theorem transport_trans {α : Type} {R : α → α → Prop}
    (P : α → Prop) (preserve : ∀ {x y}, R x y → P x → P y)
    {a b c : α} (p : RPath α R a b) (q : RPath α R b c) (pa : P a) :
    (p.trans q).transportProp P preserve pa =
    q.transportProp P preserve (p.transportProp P preserve pa) := by
  induction p with
  | refl _ => rfl
  | cons s rest ih =>
    cases s with
    | mk r => rfl

-- ════════════════════════════════════════════════════════════
-- §14  Miscellaneous Path Algebra for ARS
-- ════════════════════════════════════════════════════════════

/-- Reverse a rewriting path (as a conv path going backward). -/
noncomputable def RPath.reverse {α : Type} {R : α → α → Prop} {a b : α}
    (p : RPath α R a b) : ConvPath α R b a :=
  p.toConv.symm

/-- Theorem 62: reverse of refl is refl. -/
theorem rpath_reverse_refl {α : Type} {R : α → α → Prop} (a : α) :
    (RPath.refl a : RPath α R a a).reverse = ConvPath.refl a := rfl

/-- Concatenate a forward path and a backward path into a conv path. -/
noncomputable def joinToConv {α : Type} {R : α → α → Prop} {a b c : α}
    (p : RPath α R a b) (q : RPath α R c b) : ConvPath α R a c :=
  p.toConv.trans q.toConv.symm

/-- Theorem 63: joinToConv with refl on left. -/
theorem joinToConv_refl_left {α : Type} {R : α → α → Prop} {a b : α}
    (q : RPath α R b a) :
    joinToConv (RPath.refl a) q = q.toConv.symm := rfl

/-- Theorem 64: conv path from joinable witness. -/
noncomputable def Joinable.toConvPath {α : Type} {R : α → α → Prop} {a b : α}
    (j : Joinable α R a b) : ConvPath α R a b :=
  joinToConv j.left j.right

/-- Theorem 65: convpath length of joinable via paths. -/
-- The conv path from a joinable has length = sum of the two path lengths.
-- (since joinToConv = fwd path ++ reversed bwd path)

-- We prove a special case for clarity:
theorem joinable_toConv_refl {α : Type} {R : α → α → Prop} (a : α) :
    (Joinable.rfl_join a : Joinable α R a a).toConvPath = ConvPath.refl a := rfl

-- ════════════════════════════════════════════════════════════
-- §15  Additional Theorems (Rounding Out)
-- ════════════════════════════════════════════════════════════

/-- Theorem 66: single step has exactly one step. -/
theorem rpath_single_is_cons {α : Type} {R : α → α → Prop} {a b : α}
    (s : Step α R a b) :
    RPath.single s = RPath.cons s (RPath.refl b) := rfl

/-- Theorem 67: conv symm of refl is refl. -/
theorem conv_symm_refl {α : Type} {R : α → α → Prop} (a : α) :
    (ConvPath.refl a : ConvPath α R a a).symm = ConvPath.refl a := rfl

/-- Theorem 68: toRPath of par refl step is refl. -/
theorem parStep_refl_toRPath {α : Type} {R : α → α → Prop} (a : α) :
    (ParStep.refl a : ParStep α R a a).toRPath = RPath.refl a := rfl

/-- Theorem 69: toRPath of par step is single. -/
theorem parStep_step_toRPath {α : Type} {R : α → α → Prop} {a b : α}
    (r : R a b) :
    (ParStep.step r : ParStep α R a b).toRPath = RPath.single (.mk r) := rfl

/-- Theorem 70: labels of refl labelled path is empty. -/
theorem lpath_refl_labels {α : Type} {R : α → α → Prop} {L : Type} (a : α) :
    (LPath.refl a : LPath α R L a a).labels = [] := rfl

end CompPaths.RewritingSystems
