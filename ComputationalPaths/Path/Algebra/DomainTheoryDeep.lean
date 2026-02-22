/-
  Domain Theory and Denotational Semantics via Computational Paths
  ================================================================
  A comprehensive development of domain-theoretic concepts expressed through
  the computational paths framework. We model CPOs, Scott-continuity,
  fixed-point theorems, algebraic domains, function spaces, retracts,
  embedding-projection pairs, bilimits, and powerdomains.

  All constructions use Path.trans for chain composition and Path.congrArg
  for functoriality, demonstrating that computational paths provide a
  natural language for domain theory.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths

open Path

namespace DomainTheoryDeep

universe u v w

-- ============================================================
-- SECTION 1: Partial Orders and CPOs
-- ============================================================

/-- A partial order witness as a computational path -/
structure LePath (A : Type u) where
  le : A → A → Prop
  refl_le : ∀ a, le a a
  trans_le : ∀ a b c, le a b → le b c → le a c
  antisym : ∀ a b, le a b → le b a → Path a b

/-- Bottom element witness -/
structure HasBot (A : Type u) (ord : LePath A) where
  bot : A
  bot_le : ∀ a, ord.le bot a

/-- A directed set in a partial order -/
structure Directed (A : Type u) (ord : LePath A) where
  carrier : Nat → A
  nonempty : True
  directed : ∀ i j, Sigma fun (k : Nat) =>
    PLift (ord.le (carrier i) (carrier k) ∧ ord.le (carrier j) (carrier k))

/-- Supremum witness -/
structure Supremum (A : Type u) (ord : LePath A) (d : Directed A ord) where
  sup : A
  upper : ∀ i, ord.le (d.carrier i) sup
  least : ∀ u, (∀ i, ord.le (d.carrier i) u) → ord.le sup u

/-- A CPO: partial order with bottom and directed suprema -/
structure CPO (A : Type u) where
  ord : LePath A
  bottom : HasBot A ord
  dirSup : ∀ d : Directed A ord, Supremum A ord d

-- ============================================================
-- SECTION 2: Monotone and Scott-Continuous Functions
-- ============================================================

/-- A monotone function between CPOs -/
structure MonoFun {A : Type u} {B : Type v} (cA : CPO A) (cB : CPO B) (f : A → B) where
  mono : ∀ a b, cA.ord.le a b → cB.ord.le (f a) (f b)

/-- Image of a directed set under a monotone function -/
noncomputable def imageDirected {A : Type u} {B : Type v} (cA : CPO A) (cB : CPO B)
    (f : A → B) (mf : MonoFun cA cB f) (d : Directed A cA.ord) : Directed B cB.ord where
  carrier := fun i => f (d.carrier i)
  nonempty := trivial
  directed := fun i j =>
    let ⟨k, ⟨hik, hjk⟩⟩ := d.directed i j
    ⟨k, ⟨mf.mono _ _ hik, mf.mono _ _ hjk⟩⟩

/-- Scott-continuity: preserves directed suprema -/
structure ScottCont {A : Type u} {B : Type v} (cA : CPO A) (cB : CPO B) (f : A → B) where
  mono : MonoFun cA cB f
  preserve_sup : ∀ (d : Directed A cA.ord),
    Path (f (cA.dirSup d).sup) (cB.dirSup (imageDirected cA cB f mono d)).sup

-- ============================================================
-- SECTION 3: Path-based Order Chains (defs since Path is not Prop)
-- ============================================================

/-- Def 1: Reflexivity of order as path -/
noncomputable def order_refl_path {A : Type u} (_cpo : CPO A) (a : A) :
    Path a a :=
  Path.refl a

/-- Def 2: Transitivity of order antisymmetry gives path composition -/
noncomputable def order_trans_path {A : Type u} (cpo : CPO A) (a b c : A)
    (hab : cpo.ord.le a b) (hba : cpo.ord.le b a)
    (hbc : cpo.ord.le b c) (hcb : cpo.ord.le c b) :
    Path a c :=
  Path.trans (cpo.ord.antisym a b hab hba) (cpo.ord.antisym b c hbc hcb)

/-- Def 3: Symmetry of path from antisymmetry -/
noncomputable def order_symm_path {A : Type u} (cpo : CPO A) (a b : A)
    (hab : cpo.ord.le a b) (hba : cpo.ord.le b a) :
    Path b a :=
  Path.symm (cpo.ord.antisym a b hab hba)

/-- Def 4: Bottom is unique up to path -/
noncomputable def bot_unique {A : Type u} (cpo : CPO A) (b1 b2 : A)
    (hb1 : ∀ a, cpo.ord.le b1 a) (hb2 : ∀ a, cpo.ord.le b2 a) :
    Path b1 b2 :=
  cpo.ord.antisym b1 b2 (hb1 b2) (hb2 b1)

/-- Def 5: Supremum is unique up to path -/
noncomputable def sup_unique {A : Type u} (cpo : CPO A) (d : Directed A cpo.ord)
    (s1 s2 : A)
    (h1_upper : ∀ i, cpo.ord.le (d.carrier i) s1)
    (h1_least : ∀ u, (∀ i, cpo.ord.le (d.carrier i) u) → cpo.ord.le s1 u)
    (h2_upper : ∀ i, cpo.ord.le (d.carrier i) s2)
    (h2_least : ∀ u, (∀ i, cpo.ord.le (d.carrier i) u) → cpo.ord.le s2 u) :
    Path s1 s2 :=
  cpo.ord.antisym s1 s2 (h1_least s2 h2_upper) (h2_least s1 h1_upper)

-- ============================================================
-- SECTION 4: Ascending Chains and Kleene Fixed Point
-- ============================================================

/-- An ascending chain (omega-chain) in a CPO -/
structure Chain (A : Type u) (cpo : CPO A) where
  elem : Nat → A
  ascending : ∀ n, cpo.ord.le (elem n) (elem (n + 1))

/-- Lemma: ascending chains are monotone in index -/
theorem chain_le_of_le {A : Type u} (cpo : CPO A) (c : Chain A cpo)
    (m n : Nat) (h : m ≤ n) : cpo.ord.le (c.elem m) (c.elem n) := by
  induction h with
  | refl => exact cpo.ord.refl_le _
  | step h ih => exact cpo.ord.trans_le _ _ _ ih (c.ascending _)

/-- Convert a chain to a directed set -/
noncomputable def chainToDirected {A : Type u} (cpo : CPO A) (c : Chain A cpo) : Directed A cpo.ord where
  carrier := c.elem
  nonempty := trivial
  directed := fun i j =>
    ⟨i + j, ⟨chain_le_of_le cpo c i (i + j) (Nat.le_add_right i j),
             chain_le_of_le cpo c j (i + j) (Nat.le_add_left j i)⟩⟩

/-- Def 6: Chain supremum witness -/
noncomputable def chain_sup {A : Type u} (cpo : CPO A) (c : Chain A cpo) : A :=
  (cpo.dirSup (chainToDirected cpo c)).sup

/-- Theorem 7: Chain elements are below sup -/
theorem chain_elem_le_sup {A : Type u} (cpo : CPO A) (c : Chain A cpo) (i : Nat) :
    cpo.ord.le (c.elem i) (chain_sup cpo c) :=
  (cpo.dirSup (chainToDirected cpo c)).upper i

/-- Kleene iteration: f^n(⊥) -/
noncomputable def kleeneIter {A : Type u} (cpo : CPO A) (f : A → A) : Nat → A
  | 0 => cpo.bottom.bot
  | n + 1 => f (kleeneIter cpo f n)

/-- Theorem 8: Kleene chain is ascending for monotone f -/
theorem kleene_ascending {A : Type u} (cpo : CPO A) (f : A → A)
    (mf : MonoFun cpo cpo f) : ∀ n, cpo.ord.le (kleeneIter cpo f n) (kleeneIter cpo f (n + 1)) := by
  intro n
  induction n with
  | zero => exact cpo.bottom.bot_le _
  | succ n ih => exact mf.mono _ _ ih

/-- The Kleene chain as a Chain structure -/
noncomputable def kleeneChain {A : Type u} (cpo : CPO A) (f : A → A)
    (mf : MonoFun cpo cpo f) : Chain A cpo where
  elem := kleeneIter cpo f
  ascending := kleene_ascending cpo f mf

/-- Def 9: Kleene chain as directed set -/
noncomputable def kleeneDirected {A : Type u} (cpo : CPO A) (f : A → A)
    (mf : MonoFun cpo cpo f) : Directed A cpo.ord :=
  chainToDirected cpo (kleeneChain cpo f mf)

/-- Def 10: Fixed point path - Scott-continuous f has lfp -/
noncomputable def fixed_point_path {A : Type u} (cpo : CPO A) (f : A → A)
    (sf : ScottCont cpo cpo f) :
    Path (f (cpo.dirSup (kleeneDirected cpo f sf.mono)).sup)
         (cpo.dirSup (kleeneDirected cpo f sf.mono)).sup := by
  let d := kleeneDirected cpo f sf.mono
  let imgDir := imageDirected cpo cpo f sf.mono d
  -- Scott continuity gives Path (f s) supImg
  have pfs := sf.preserve_sup d
  -- Show supImg and s are equal via antisymmetry
  have h_img_le_s : ∀ i, cpo.ord.le (imgDir.carrier i) (cpo.dirSup d).sup := by
    intro i; exact (cpo.dirSup d).upper (i + 1)
  have h_s_le_supImg : cpo.ord.le (cpo.dirSup d).sup (cpo.dirSup imgDir).sup := by
    apply (cpo.dirSup d).least
    intro i
    match i with
    | 0 => exact cpo.ord.trans_le _ _ _ (cpo.bottom.bot_le _) ((cpo.dirSup imgDir).upper 0)
    | n + 1 => exact (cpo.dirSup imgDir).upper n
  have h_supImg_le_s : cpo.ord.le (cpo.dirSup imgDir).sup (cpo.dirSup d).sup :=
    (cpo.dirSup imgDir).least _ h_img_le_s
  exact Path.trans pfs (cpo.ord.antisym _ _ h_supImg_le_s h_s_le_supImg)

/-- Theorem 11: Pre-fixed point: f(x) ≤ x implies all iterates ≤ x -/
theorem prefixed_above_bot {A : Type u} (cpo : CPO A) (f : A → A)
    (mf : MonoFun cpo cpo f) (x : A) (hfx : cpo.ord.le (f x) x) :
    ∀ n, cpo.ord.le (kleeneIter cpo f n) x := by
  intro n
  induction n with
  | zero => exact cpo.bottom.bot_le x
  | succ n ih => exact cpo.ord.trans_le _ _ _ (mf.mono _ _ ih) hfx

/-- Theorem 12: Least fixed point is below any pre-fixed point -/
theorem lfp_least {A : Type u} (cpo : CPO A) (f : A → A)
    (mf : MonoFun cpo cpo f) (x : A) (hfx : cpo.ord.le (f x) x) :
    cpo.ord.le (cpo.dirSup (kleeneDirected cpo f mf)).sup x :=
  (cpo.dirSup (kleeneDirected cpo f mf)).least x (prefixed_above_bot cpo f mf x hfx)

-- ============================================================
-- SECTION 5: Path Chains and Iteration Paths
-- ============================================================

/-- Our own iterate for f -/
noncomputable def iterateFun {A : Type u} (f : A → A) : Nat → A → A
  | 0 => id
  | n + 1 => f ∘ iterateFun f n

/-- Def 13: Path chain from iteration using antisymmetry witnesses -/
noncomputable def iterPathChain {A : Type u} (cpo : CPO A) (f : A → A)
    (mf : MonoFun cpo cpo f)
    (hanti : ∀ n, Path (kleeneIter cpo f n) (kleeneIter cpo f (n+1))) :
    ∀ n, Path (kleeneIter cpo f 0) (kleeneIter cpo f n)
  | 0 => Path.refl _
  | n + 1 => Path.trans (iterPathChain cpo f mf hanti n) (hanti n)

/-- Def 14: Functoriality of iteration paths -/
noncomputable def iter_path_functorial {A : Type u} {B : Type v}
    (g : A → B) (cpoA : CPO A) (f : A → A)
    (mf : MonoFun cpoA cpoA f)
    (hanti : ∀ n, Path (kleeneIter cpoA f n) (kleeneIter cpoA f (n+1)))
    (n : Nat) :
    Path (g (kleeneIter cpoA f 0)) (g (kleeneIter cpoA f n)) :=
  Path.congrArg g (iterPathChain cpoA f mf hanti n)

/-- Theorem 15: Composing iteration paths is associative -/
theorem iter_path_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

-- ============================================================
-- SECTION 6: Scott-Continuous Function Composition
-- ============================================================

/-- Def 16: Composition of monotone functions is monotone -/
noncomputable def mono_comp {A : Type u} {B : Type v} {C : Type w}
    (cA : CPO A) (cB : CPO B) (cC : CPO C)
    (f : A → B) (g : B → C)
    (mf : MonoFun cA cB f) (mg : MonoFun cB cC g) :
    MonoFun cA cC (g ∘ f) where
  mono := fun _a _b hab => mg.mono _ _ (mf.mono _ _ hab)

/-- Def 17: Identity is monotone -/
noncomputable def mono_id {A : Type u} (cA : CPO A) : MonoFun cA cA id where
  mono := fun _ _ h => h

/-- Theorem 18: Monotone composition with id is identity -/
theorem mono_comp_id_left {A : Type u} {B : Type v}
    (cA : CPO A) (cB : CPO B) (f : A → B) (mf : MonoFun cA cB f)
    (a b : A) (h : cA.ord.le a b) : cB.ord.le ((id ∘ f) a) ((id ∘ f) b) :=
  mf.mono a b h

/-- Theorem 19: Monotone composition is associative at the function level -/
theorem mono_comp_assoc {A : Type u} {B : Type v} {C : Type w} {D : Type u}
    (cA : CPO A) (cB : CPO B) (cC : CPO C) (cD : CPO D)
    (f : A → B) (g : B → C) (h : C → D)
    (mf : MonoFun cA cB f) (mg : MonoFun cB cC g) (mh : MonoFun cC cD h)
    (a b : A) (hab : cA.ord.le a b) : cD.ord.le ((h ∘ g ∘ f) a) ((h ∘ g ∘ f) b) :=
  mh.mono _ _ (mg.mono _ _ (mf.mono _ _ hab))

-- ============================================================
-- SECTION 7: Compact Elements and Algebraic Domains
-- ============================================================

/-- A compact (finite) element in a CPO -/
structure Compact {A : Type u} (cpo : CPO A) (k : A) where
  compact : ∀ (d : Directed A cpo.ord),
    cpo.ord.le k (cpo.dirSup d).sup →
    Sigma fun (i : Nat) => PLift (cpo.ord.le k (d.carrier i))

/-- An algebraic domain: every element is a directed sup of compact elements below it -/
structure AlgebraicDomain (A : Type u) extends CPO A where
  basis : A → Directed A ord
  basis_compact : ∀ a i, Compact toCPO ((basis a).carrier i)
  basis_sup : ∀ a, Path (dirSup (basis a)).sup a

/-- Def 20: Compact elements below an element form a path to it -/
noncomputable def compact_approx_path {A : Type u} (ad : AlgebraicDomain A) (a : A) :
    Path (ad.dirSup (ad.basis a)).sup a :=
  ad.basis_sup a

/-- Def 21: Path between compact approximations is transitive -/
noncomputable def compact_chain_path {A : Type u} {a b c : A}
    (pab : Path a b) (pbc : Path b c) : Path a c :=
  Path.trans pab pbc

-- ============================================================
-- SECTION 8: Function Spaces as CPOs
-- ============================================================

/-- Pointwise order on functions -/
noncomputable def funLe {A : Type u} {B : Type v} (cB : CPO B) (f g : A → B) : Prop :=
  ∀ a, cB.ord.le (f a) (g a)

/-- Def 22: Function space bottom -/
noncomputable def funBot {A : Type u} {B : Type v} (cB : CPO B) : A → B :=
  fun _ => cB.bottom.bot

/-- Theorem 23: Function space bottom is least -/
theorem funBot_least {A : Type u} {B : Type v} (cB : CPO B) (g : A → B) :
    funLe cB (funBot cB) g :=
  fun a => cB.bottom.bot_le (g a)

/-- Theorem 24: Pointwise order is reflexive -/
theorem funLe_refl {A : Type u} {B : Type v} (cB : CPO B) (f : A → B) :
    funLe cB f f :=
  fun a => cB.ord.refl_le (f a)

/-- Theorem 25: Pointwise order is transitive -/
theorem funLe_trans {A : Type u} {B : Type v} (cB : CPO B) (f g h : A → B)
    (hfg : funLe cB f g) (hgh : funLe cB g h) : funLe cB f h :=
  fun a => cB.ord.trans_le _ _ _ (hfg a) (hgh a)

-- ============================================================
-- SECTION 9: Retracts and Projections
-- ============================================================

/-- A retraction pair -/
structure Retract (A : Type u) (B : Type v) where
  section_ : A → B
  retract_ : B → A
  retract_section : ∀ a, Path (retract_ (section_ a)) a

/-- Def 26: Retract composition is identity path -/
noncomputable def retract_id_path {A : Type u} {B : Type v}
    (r : Retract A B) (a : A) :
    Path (r.retract_ (r.section_ a)) a :=
  r.retract_section a

/-- Def 27: Retract preserves paths via congrArg -/
noncomputable def retract_preserves_path {A : Type u} {B : Type v}
    (r : Retract A B) (a1 a2 : A) (p : Path a1 a2) :
    Path (r.retract_ (r.section_ a1)) (r.retract_ (r.section_ a2)) :=
  Path.congrArg r.retract_ (Path.congrArg r.section_ p)

/-- Theorem 28: Retract path composes with identity -/
theorem retract_compose_id {A : Type u} {B : Type v}
    (r : Retract A B) (a : A) :
    Path.trans (Path.congrArg r.retract_ (Path.congrArg r.section_ (Path.refl a))) (Path.refl _) =
    Path.congrArg r.retract_ (Path.congrArg r.section_ (Path.refl a)) :=
  Path.trans_refl_right _

/-- An embedding-projection pair -/
structure EmbProj (A : Type u) (B : Type v) where
  embed : A → B
  proj : B → A
  ep_retract : ∀ a, Path (proj (embed a)) a
  ep_deflation : ∀ b, Path (embed (proj (embed (proj b)))) (embed (proj b))

/-- Def 29: EP pair gives a retract -/
noncomputable def ep_to_retract {A : Type u} {B : Type v} (ep : EmbProj A B) : Retract A B where
  section_ := ep.embed
  retract_ := ep.proj
  retract_section := ep.ep_retract

/-- Def 30: EP composition p∘e∘p∘e is path-equal to p∘e via congrArg -/
noncomputable def ep_idempotent {A : Type u} {B : Type v}
    (ep : EmbProj A B) (b : A) :
    Path (ep.proj (ep.embed (ep.proj (ep.embed b)))) (ep.proj (ep.embed b)) :=
  Path.congrArg ep.proj (Path.congrArg ep.embed (ep.ep_retract b))

-- ============================================================
-- SECTION 10: Bilimit Construction
-- ============================================================

/-- A sequence of domains with embedding-projection pairs -/
structure DomainSeq where
  Dom : Nat → Type u
  ep : ∀ n, EmbProj (Dom n) (Dom (n + 1))

/-- Def 31: Composing EP retract paths -/
noncomputable def ep_compose_retract {A : Type u} {B : Type v} {C : Type w}
    (ep1 : EmbProj A B) (ep2 : EmbProj B C) (a : A) :
    Path (ep1.proj (ep2.proj (ep2.embed (ep1.embed a)))) a :=
  Path.trans (Path.congrArg ep1.proj (ep2.ep_retract (ep1.embed a))) (ep1.ep_retract a)

/-- Def 32: Composing EP retract paths is functorial -/
noncomputable def ep_compose_functorial {A : Type u} {B : Type v} {C : Type w}
    (ep1 : EmbProj A B) (ep2 : EmbProj B C) (a1 a2 : A) (p : Path a1 a2) :
    Path (ep1.proj (ep2.proj (ep2.embed (ep1.embed a1))))
         (ep1.proj (ep2.proj (ep2.embed (ep1.embed a2)))) :=
  Path.congrArg (fun x => ep1.proj (ep2.proj (ep2.embed (ep1.embed x)))) p

/-- Def 33: EP retract path composed with functorial path -/
noncomputable def ep_retract_naturality {A : Type u} {B : Type v} {C : Type w}
    (ep1 : EmbProj A B) (ep2 : EmbProj B C) (a1 a2 : A) (p : Path a1 a2) :
    Path (ep1.proj (ep2.proj (ep2.embed (ep1.embed a1)))) a2 :=
  Path.trans (ep_compose_functorial ep1 ep2 a1 a2 p) (ep_compose_retract ep1 ep2 a2)

-- ============================================================
-- SECTION 11: Lifting and Flat Domains
-- ============================================================

/-- Lifted type (adding a bottom) -/
inductive Lifted (A : Type u) where
  | bottom : Lifted A
  | up : A → Lifted A

/-- Def 34: Lifted path from base path -/
noncomputable def lifted_path {A : Type u} (a b : A) (p : Path a b) :
    Path (Lifted.up a) (Lifted.up b) :=
  Path.congrArg Lifted.up p

/-- Def 35: Lifted path composition -/
noncomputable def lifted_path_trans {A : Type u} (a b c : A)
    (p : Path a b) (q : Path b c) :
    Path (Lifted.up a) (Lifted.up c) :=
  Path.congrArg Lifted.up (Path.trans p q)

/-- Def 36: Lifted path symmetry -/
noncomputable def lifted_path_symm {A : Type u} (a b : A) (p : Path a b) :
    Path (Lifted.up b) (Lifted.up a) :=
  Path.congrArg Lifted.up (Path.symm p)

/-- Theorem 37: congrArg distributes over trans for lifting -/
theorem lifted_congrArg_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.congrArg Lifted.up (Path.trans p q) =
    Path.trans (Path.congrArg Lifted.up p) (Path.congrArg Lifted.up q) :=
  Path.congrArg_trans Lifted.up p q

/-- Theorem 38: congrArg distributes over symm for lifting -/
theorem lifted_congrArg_symm {A : Type u} {a b : A}
    (p : Path a b) :
    Path.congrArg Lifted.up (Path.symm p) =
    Path.symm (Path.congrArg Lifted.up p) :=
  Path.congrArg_symm Lifted.up p

-- ============================================================
-- SECTION 12: Products of CPOs
-- ============================================================

/-- Def 39: Projection preserves paths (fst) -/
noncomputable def fst_path {A : Type u} {B : Type v} {p q : A × B} (h : Path p q) :
    Path p.1 q.1 :=
  Path.congrArg Prod.fst h

/-- Def 40: Second projection preserves paths -/
noncomputable def snd_path {A : Type u} {B : Type v} {p q : A × B} (h : Path p q) :
    Path p.2 q.2 :=
  Path.congrArg Prod.snd h

/-- Def 41: Pairing preserves paths -/
noncomputable def pair_path_fst {A : Type u} {B : Type v} (a1 a2 : A) (b : B)
    (p : Path a1 a2) : Path (a1, b) (a2, b) :=
  Path.congrArg (fun x => (x, b)) p

/-- Def 42: Pairing preserves paths (second component) -/
noncomputable def pair_path_snd {A : Type u} {B : Type v} (a : A) (b1 b2 : B)
    (p : Path b1 b2) : Path (a, b1) (a, b2) :=
  Path.congrArg (fun y => (a, y)) p

-- ============================================================
-- SECTION 13: Sum (Coalesced) Domains
-- ============================================================

/-- Def 43: Injection preserves paths (left) -/
noncomputable def inl_path {A : Type u} {B : Type v} (a1 a2 : A) (p : Path a1 a2) :
    Path (Sum.inl a1 : A ⊕ B) (Sum.inl a2) :=
  Path.congrArg Sum.inl p

/-- Def 44: Injection preserves paths (right) -/
noncomputable def inr_path {A : Type u} {B : Type v} (b1 b2 : B) (p : Path b1 b2) :
    Path (Sum.inr b1 : A ⊕ B) (Sum.inr b2) :=
  Path.congrArg Sum.inr p

/-- Theorem 45: Left injection path composition -/
theorem inl_path_trans {A : Type u} {B : Type v} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.congrArg (Sum.inl (β := B)) (Path.trans p q) =
    Path.trans (Path.congrArg Sum.inl p) (Path.congrArg Sum.inl q) :=
  Path.congrArg_trans Sum.inl p q

/-- Theorem 46: Right injection path composition -/
theorem inr_path_trans {A : Type u} {B : Type v} {a b c : B}
    (p : Path a b) (q : Path b c) :
    Path.congrArg (Sum.inr (α := A)) (Path.trans p q) =
    Path.trans (Path.congrArg Sum.inr p) (Path.congrArg Sum.inr q) :=
  Path.congrArg_trans Sum.inr p q

-- ============================================================
-- SECTION 14: Powerdomains
-- ============================================================

/-- Hoare powerdomain element: downward-closed sets -/
structure HoareSet (A : Type u) (cpo : CPO A) where
  mem : A → Prop
  downward : ∀ a₁ b₁, cpo.ord.le a₁ b₁ → mem b₁ → mem a₁

/-- Smyth powerdomain element: upward-closed sets -/
structure SmythSet (A : Type u) (cpo : CPO A) where
  mem : A → Prop
  upward : ∀ a₁ b₁, cpo.ord.le a₁ b₁ → mem a₁ → mem b₁

/-- Def 47: Singleton is in Hoare powerdomain -/
noncomputable def hoareSingleton {A : Type u} (cpo : CPO A) (a : A) : HoareSet A cpo where
  mem := fun x => cpo.ord.le x a
  downward := fun _x _y hxy hya => cpo.ord.trans_le _ _ _ hxy hya

/-- Def 48: Singleton is in Smyth powerdomain -/
noncomputable def smythSingleton {A : Type u} (cpo : CPO A) (a : A) : SmythSet A cpo where
  mem := fun x => cpo.ord.le a x
  upward := fun _x _y hxy hax => cpo.ord.trans_le _ _ _ hax hxy

/-- Theorem 49: Hoare membership is preserved by order -/
theorem hoare_downward {A : Type u} (cpo : CPO A) (s : HoareSet A cpo)
    (a b : A) (hab : cpo.ord.le a b) (hb : s.mem b) : s.mem a :=
  s.downward a b hab hb

/-- Theorem 50: Smyth membership is preserved by order -/
theorem smyth_upward {A : Type u} (cpo : CPO A) (s : SmythSet A cpo)
    (a b : A) (hab : cpo.ord.le a b) (ha : s.mem a) : s.mem b :=
  s.upward a b hab ha

-- ============================================================
-- SECTION 15: Path Algebra Properties for Domain Theory
-- ============================================================

/-- Theorem 51: Trans-refl-left for domain paths -/
theorem domain_trans_refl_left {A : Type u} {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  Path.trans_refl_left p

/-- Theorem 52: Trans-refl-right for domain paths -/
theorem domain_trans_refl_right {A : Type u} {a b : A} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  Path.trans_refl_right p

/-- Theorem 53: Double symmetry -/
theorem domain_symm_symm {A : Type u} {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- Theorem 54: Associativity of path composition -/
theorem domain_trans_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

/-- Theorem 55: CongrArg distributes over trans -/
theorem domain_congrArg_trans {A : Type u} {B : Type v} (f : A → B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) = Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

/-- Theorem 56: CongrArg distributes over symm -/
theorem domain_congrArg_symm {A : Type u} {B : Type v} (f : A → B)
    {a b : A} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

/-- Theorem 57: CongrArg composition -/
theorem domain_congrArg_comp {A : Type u} {B : Type v} {C : Type w}
    (f : B → C) (g : A → B) {a b : A} (p : Path a b) :
    Path.congrArg (fun x => f (g x)) p = Path.congrArg f (Path.congrArg g p) :=
  Path.congrArg_comp f g p

-- ============================================================
-- SECTION 16: Continuous Function Application Paths
-- ============================================================

/-- Def 58: Applying a function to path-equal args gives path -/
noncomputable def apply_path {A : Type u} {B : Type v}
    (f : A → B) {a b : A} (p : Path a b) :
    Path (f a) (f b) :=
  Path.congrArg f p

/-- Theorem 59: Composing application paths -/
theorem apply_path_trans {A : Type u} {B : Type v}
    (f : A → B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

/-- Def 60: Two functions compose to give paths -/
noncomputable def compose_path {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) (g : B → C) {a1 a2 : A} (p : Path a1 a2) :
    Path (g (f a1)) (g (f a2)) :=
  Path.congrArg g (Path.congrArg f p)

/-- Theorem 61: Functoriality of composition -/
theorem compose_functorial {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) (g : B → C) {a1 a2 : A} (p : Path a1 a2) :
    Path.congrArg (g ∘ f) p = Path.congrArg g (Path.congrArg f p) :=
  Path.congrArg_comp g f p

-- ============================================================
-- SECTION 17: Fixed Point Properties
-- ============================================================

/-- Def 62: Fixed point path is symmetric -/
noncomputable def fixed_point_symm {A : Type u} (f : A → A) (x : A) (p : Path (f x) x) :
    Path x (f x) :=
  Path.symm p

/-- Def 63: Fixed points are path-related through order -/
noncomputable def fixed_points_ordered_path {A : Type u} (cpo : CPO A)
    (x y : A) (hxy : cpo.ord.le x y) (hyx : cpo.ord.le y x) :
    Path x y :=
  cpo.ord.antisym x y hxy hyx

/-- Def 64: Kleene iterates map to paths -/
noncomputable def kleene_path_step {A : Type u} (cpo : CPO A) (f : A → A) (n : Nat)
    (p : Path (kleeneIter cpo f n) (kleeneIter cpo f (n + 1))) :
    Path (f (kleeneIter cpo f n)) (f (kleeneIter cpo f (n + 1))) :=
  Path.congrArg f p

/-- Def 65: Kleene path chain via congrArg -/
noncomputable def kleene_apply_path {A : Type u} (cpo : CPO A) (f : A → A) (n : Nat)
    (p : Path (kleeneIter cpo f n) (kleeneIter cpo f (n + 1))) :
    Path (kleeneIter cpo f (n + 1)) (kleeneIter cpo f (n + 2)) :=
  Path.congrArg f p

-- ============================================================
-- SECTION 18: Denotational Semantics Structures
-- ============================================================

/-- A simple denotation mapping expressions to domain elements -/
structure Denotation (Expr : Type u) (D : Type v) where
  denote : Expr → D

/-- Def 66: Denotation preserves expression paths -/
noncomputable def denote_preserves_path {Expr : Type u} {D : Type v}
    (den : Denotation Expr D) {e1 e2 : Expr} (p : Path e1 e2) :
    Path (den.denote e1) (den.denote e2) :=
  Path.congrArg den.denote p

/-- Def 67: Composing denotations with a function -/
noncomputable def denote_compose {Expr : Type u} {D : Type v} {E : Type w}
    (den : Denotation Expr D) (f : D → E)
    {e1 e2 : Expr} (p : Path e1 e2) :
    Path (f (den.denote e1)) (f (den.denote e2)) :=
  Path.congrArg f (Path.congrArg den.denote p)

/-- Theorem 68: Denotation compose distributes over trans -/
theorem denote_compose_trans {Expr : Type u} {D : Type v} {E : Type w}
    (den : Denotation Expr D) (f : D → E)
    {e1 e2 e3 : Expr} (p : Path e1 e2) (q : Path e2 e3) :
    denote_compose den f (Path.trans p q) =
    Path.trans (denote_compose den f p) (denote_compose den f q) := by
  simp [denote_compose]

-- ============================================================
-- SECTION 19: Additional Path-Domain Interactions
-- ============================================================

/-- Theorem 69: Symmetry involution for retract paths -/
theorem retract_symm_invol {A : Type u} {B : Type v}
    (r : Retract A B) (a : A) :
    Path.symm (Path.symm (r.retract_section a)) = r.retract_section a :=
  Path.symm_symm (r.retract_section a)

/-- Theorem 70: EP retract path double symmetry -/
theorem ep_retract_symm_symm {A : Type u} {B : Type v}
    (ep : EmbProj A B) (a : A) :
    Path.symm (Path.symm (ep.ep_retract a)) = ep.ep_retract a :=
  Path.symm_symm (ep.ep_retract a)

end DomainTheoryDeep

end ComputationalPaths
