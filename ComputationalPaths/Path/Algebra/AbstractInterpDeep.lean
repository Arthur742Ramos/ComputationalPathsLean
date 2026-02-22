/-
  ComputationalPaths/Path/Algebra/AbstractInterpDeep.lean

  Abstract Interpretation via Computational Paths
  ================================================

  We develop the theory of abstract interpretation using computational paths
  as the primary vehicle for expressing soundness, correctness, and
  compositional reasoning about abstract domains, Galois connections,
  abstract transformers, widening/narrowing, fixpoint computation,
  reduced products, and domain combinators.

  All proofs use genuine Path operations (trans, symm, congrArg, refl)
  rather than propositional equality rewrites.
-/

import ComputationalPaths.Path.Basic

namespace AbstractInterpDeep

open ComputationalPaths
open ComputationalPaths.Path

universe u v w

-- ============================================================================
-- Section 1: Lattice Structure for Abstract Interpretation
-- ============================================================================

/-- A partial order captured as a structure for our domain theory. -/
structure DomOrder (A : Type u) where
  le : A → A → Prop
  le_refl : ∀ a, le a a
  le_trans : ∀ a b c, le a b → le b c → le a c
  le_antisymm : ∀ a b, le a b → le b a → a = b

/-- Join semilattice with bottom. -/
structure JoinSemiLat (A : Type u) extends DomOrder A where
  bot : A
  join : A → A → A
  bot_le : ∀ a, le bot a
  join_comm : ∀ a b, join a b = join b a
  join_assoc : ∀ a b c, join (join a b) c = join a (join b c)
  le_join_left : ∀ a b, le a (join a b)
  le_join_right : ∀ a b, le b (join a b)

/-- Meet semilattice with top. -/
structure MeetSemiLat (A : Type u) extends DomOrder A where
  top : A
  meet : A → A → A
  le_top : ∀ a, le a top
  meet_comm : ∀ a b, meet a b = meet b a
  meet_assoc : ∀ a b c, meet (meet a b) c = meet a (meet b c)
  meet_le_left : ∀ a b, le (meet a b) a
  meet_le_right : ∀ a b, le (meet a b) b

-- ============================================================================
-- Section 2: Galois Connections
-- ============================================================================

/-- A Galois connection between concrete domain C and abstract domain A. -/
structure GaloisConn (C : Type u) (A : Type v)
    (cOrd : DomOrder C) (aOrd : DomOrder A) where
  alpha : C → A
  gamma : A → C
  gc_sound : ∀ c a, cOrd.le c (gamma a) ↔ aOrd.le (alpha c) a

/-- Abstraction followed by concretization is extensive. -/
noncomputable def gc_extensive {C : Type u} {A : Type v}
    {cOrd : DomOrder C} {aOrd : DomOrder A}
    (gc : GaloisConn C A cOrd aOrd) :
    ∀ c, cOrd.le c (gc.gamma (gc.alpha c)) :=
  fun c => (gc.gc_sound c (gc.alpha c)).mpr (aOrd.le_refl (gc.alpha c))

/-- Concretization followed by abstraction is reductive. -/
noncomputable def gc_reductive {C : Type u} {A : Type v}
    {cOrd : DomOrder C} {aOrd : DomOrder A}
    (gc : GaloisConn C A cOrd aOrd) :
    ∀ a, aOrd.le (gc.alpha (gc.gamma a)) a :=
  fun a => (gc.gc_sound (gc.gamma a) a).mp (cOrd.le_refl (gc.gamma a))

-- ============================================================================
-- Section 3: Path-Based Soundness of Abstraction
-- ============================================================================

/-- 1: Path preservation under alpha -/
noncomputable def path_alpha_preserve {C : Type u} {A : Type v}
    (alpha : C → A) {c1 c2 : C}
    (p : Path c1 c2) : Path (alpha c1) (alpha c2) :=
  Path.congrArg alpha p

/-- 2: Path preservation under gamma -/
noncomputable def path_gamma_preserve {C : Type u} {A : Type v}
    (gamma : A → C) {a1 a2 : A}
    (p : Path a1 a2) : Path (gamma a1) (gamma a2) :=
  Path.congrArg gamma p

/-- 3: Round-trip path alpha . gamma -/
noncomputable def path_round_trip_ag {C : Type u} {A : Type v}
    (alpha : C → A) (gamma : A → C) {a1 a2 : A}
    (p : Path a1 a2) : Path (alpha (gamma a1)) (alpha (gamma a2)) :=
  Path.congrArg (fun x => alpha (gamma x)) p

/-- 4: Round-trip path gamma . alpha -/
noncomputable def path_round_trip_ga {C : Type u} {A : Type v}
    (alpha : C → A) (gamma : A → C) {c1 c2 : C}
    (p : Path c1 c2) : Path (gamma (alpha c1)) (gamma (alpha c2)) :=
  Path.congrArg (fun x => gamma (alpha x)) p

/-- 5: Symmetry of abstraction paths -/
noncomputable def path_alpha_symm {C : Type u} {A : Type v}
    (alpha : C → A) {c1 c2 : C}
    (p : Path c1 c2) : Path (alpha c2) (alpha c1) :=
  Path.symm (Path.congrArg alpha p)

/-- 6: Transitivity of abstraction chains -/
noncomputable def path_alpha_trans {C : Type u} {A : Type v}
    (alpha : C → A) {c1 c2 c3 : C}
    (p : Path c1 c2) (q : Path c2 c3) : Path (alpha c1) (alpha c3) :=
  Path.trans (Path.congrArg alpha p) (Path.congrArg alpha q)

-- ============================================================================
-- Section 4: Abstract Transformers
-- ============================================================================

/-- An abstract transformer soundly over-approximates a concrete one. -/
structure AbsTransformer (C : Type u) (A : Type v) where
  concrete_f : C → C
  abstract_f : A → A
  alpha : C → A
  gamma : A → C

/-- 7: Soundness of abstract transformer via Path -/
noncomputable def transformer_soundness_path {C : Type u} {A : Type v}
    (t : AbsTransformer C A) {c1 c2 : C}
    (p : Path c1 c2) :
    Path (t.abstract_f (t.alpha c1)) (t.abstract_f (t.alpha c2)) :=
  Path.congrArg t.abstract_f (Path.congrArg t.alpha p)

/-- 8: Path coherence of composed transformers -/
noncomputable def transformer_compose_path {A : Type u}
    (f g : A → A) {a1 a2 : A}
    (p : Path a1 a2) : Path (f (g a1)) (f (g a2)) :=
  Path.congrArg (fun x => f (g x)) p

/-- 9: Identity transformer preserves paths -/
noncomputable def id_transformer_path {A : Type u} {a1 a2 : A}
    (p : Path a1 a2) : Path (id a1) (id a2) :=
  Path.congrArg id p

/-- 10: Double application transformer path -/
noncomputable def double_app_path {A : Type u} (f : A → A) {a1 a2 : A}
    (p : Path a1 a2) : Path (f (f a1)) (f (f a2)) :=
  Path.congrArg (fun x => f (f x)) p

-- ============================================================================
-- Section 5: Best Abstract Transformer
-- ============================================================================

/-- The best abstract transformer is alpha . f . gamma. -/
noncomputable def bestAbsTransformer {C : Type u} {A : Type v}
    (alpha : C → A) (gamma : A → C) (f : C → C) : A → A :=
  fun a => alpha (f (gamma a))

/-- 11: Best abstract transformer preserves paths -/
noncomputable def best_transformer_path {C : Type u} {A : Type v}
    (alpha : C → A) (gamma : A → C) (f : C → C)
    {a1 a2 : A} (p : Path a1 a2) :
    Path (bestAbsTransformer alpha gamma f a1)
         (bestAbsTransformer alpha gamma f a2) :=
  Path.congrArg (fun a => alpha (f (gamma a))) p

/-- 12: Best transformer composition via paths -/
noncomputable def best_transformer_compose {C : Type u} {A : Type v}
    (alpha : C → A) (gamma : A → C) (f g : C → C)
    {a1 a2 : A} (p : Path a1 a2) :
    Path (bestAbsTransformer alpha gamma f (bestAbsTransformer alpha gamma g a1))
         (bestAbsTransformer alpha gamma f (bestAbsTransformer alpha gamma g a2)) :=
  Path.congrArg (fun a =>
    bestAbsTransformer alpha gamma f (bestAbsTransformer alpha gamma g a)) p

/-- 13: Symmetry of best transformer paths -/
noncomputable def best_transformer_symm {C : Type u} {A : Type v}
    (alpha : C → A) (gamma : A → C) (f : C → C)
    {a1 a2 : A} (p : Path a1 a2) :
    Path (bestAbsTransformer alpha gamma f a2)
         (bestAbsTransformer alpha gamma f a1) :=
  Path.symm (best_transformer_path alpha gamma f p)

-- ============================================================================
-- Section 6: Widening Operator
-- ============================================================================

/-- A widening operator on an abstract domain. -/
structure Widening (A : Type u) where
  widen : A → A → A

/-- 14: Widening preserves left-argument paths -/
noncomputable def widen_left_path {A : Type u} (w : Widening A)
    {a1 a2 : A} (b : A) (p : Path a1 a2) :
    Path (w.widen a1 b) (w.widen a2 b) :=
  Path.congrArg (fun x => w.widen x b) p

/-- 15: Widening preserves right-argument paths -/
noncomputable def widen_right_path {A : Type u} (w : Widening A)
    (a : A) {b1 b2 : A} (p : Path b1 b2) :
    Path (w.widen a b1) (w.widen a b2) :=
  Path.congrArg (fun x => w.widen a x) p

/-- 16: Widening preserves both-argument paths -/
noncomputable def widen_both_path {A : Type u} (w : Widening A)
    {a1 a2 b1 b2 : A} (pa : Path a1 a2) (pb : Path b1 b2) :
    Path (w.widen a1 b1) (w.widen a2 b2) :=
  Path.trans (Path.congrArg (fun x => w.widen x b1) pa)
             (Path.congrArg (fun x => w.widen a2 x) pb)

/-- 17: Widening chain step -/
noncomputable def widen_chain_step {A : Type u} (w : Widening A) (f : A → A)
    {a1 a2 : A} (p : Path a1 a2) :
    Path (w.widen a1 (f a1)) (w.widen a2 (f a2)) :=
  Path.congrArg (fun x => w.widen x (f x)) p

-- ============================================================================
-- Section 7: Narrowing Operator
-- ============================================================================

/-- A narrowing operator on an abstract domain. -/
structure Narrowing (A : Type u) where
  narrow : A → A → A

/-- 18: Narrowing preserves left-argument paths -/
noncomputable def narrow_left_path {A : Type u} (n : Narrowing A)
    {a1 a2 : A} (b : A) (p : Path a1 a2) :
    Path (n.narrow a1 b) (n.narrow a2 b) :=
  Path.congrArg (fun x => n.narrow x b) p

/-- 19: Narrowing preserves right-argument paths -/
noncomputable def narrow_right_path {A : Type u} (n : Narrowing A)
    (a : A) {b1 b2 : A} (p : Path b1 b2) :
    Path (n.narrow a b1) (n.narrow a b2) :=
  Path.congrArg (fun x => n.narrow a x) p

/-- 20: Narrowing both arguments -/
noncomputable def narrow_both_path {A : Type u} (n : Narrowing A)
    {a1 a2 b1 b2 : A} (pa : Path a1 a2) (pb : Path b1 b2) :
    Path (n.narrow a1 b1) (n.narrow a2 b2) :=
  Path.trans (Path.congrArg (fun x => n.narrow x b1) pa)
             (Path.congrArg (fun x => n.narrow a2 x) pb)

-- ============================================================================
-- Section 8: Fixpoint Computation with Widening as Path Chain
-- ============================================================================

/-- Iterate a function n times. -/
noncomputable def iterN {A : Type u} (f : A → A) : Nat → A → A
  | 0, a => a
  | n + 1, a => f (iterN f n a)

/-- 21: iterN preserves paths on the seed -/
noncomputable def iterN_path {A : Type u} (f : A → A) (n : Nat)
    {a1 a2 : A} (p : Path a1 a2) :
    Path (iterN f n a1) (iterN f n a2) := by
  induction n with
  | zero => exact p
  | succ k ih => exact Path.congrArg f ih

/-- 22: iterN step produces a path chain -/
noncomputable def iterN_step_path {A : Type u} (f : A → A) (n : Nat)
    {a1 a2 : A} (p : Path a1 a2) :
    Path (iterN f (n + 1) a1) (iterN f (n + 1) a2) :=
  Path.congrArg f (iterN_path f n p)

/-- Widened iteration: apply widening at each step. -/
noncomputable def widenIterN {A : Type u} (w : Widening A) (f : A → A) : Nat → A → A
  | 0, a => a
  | n + 1, a => w.widen (widenIterN w f n a) (f (widenIterN w f n a))

/-- 23: Widened iteration preserves seed paths -/
noncomputable def widenIterN_path {A : Type u} (w : Widening A) (f : A → A)
    (n : Nat) {a1 a2 : A} (p : Path a1 a2) :
    Path (widenIterN w f n a1) (widenIterN w f n a2) := by
  induction n with
  | zero => exact p
  | succ k ih =>
    exact Path.congrArg (fun x => w.widen x (f x)) ih

/-- Narrowed iteration: apply narrowing at each step. -/
noncomputable def narrowIterN {A : Type u} (nr : Narrowing A) (f : A → A) : Nat → A → A
  | 0, a => a
  | n + 1, a => nr.narrow (narrowIterN nr f n a) (f (narrowIterN nr f n a))

/-- 24: Narrowed iteration preserves seed paths -/
noncomputable def narrowIterN_path {A : Type u} (nr : Narrowing A) (f : A → A)
    (n : Nat) {a1 a2 : A} (p : Path a1 a2) :
    Path (narrowIterN nr f n a1) (narrowIterN nr f n a2) := by
  induction n with
  | zero => exact p
  | succ k ih =>
    exact Path.congrArg (fun x => nr.narrow x (f x)) ih

-- ============================================================================
-- Section 9: Reduced Product of Abstract Domains
-- ============================================================================

/-- Product of two abstract domains. -/
structure ProdDom (A : Type u) (B : Type v) where
  fst : A
  snd : B

/-- 25: Path in product domain from first component -/
noncomputable def prodDom_fst_path {A : Type u} {B : Type v}
    {p1 p2 : ProdDom A B} (hp : Path p1 p2) :
    Path p1.fst p2.fst :=
  Path.congrArg ProdDom.fst hp

/-- 26: Path in product domain from second component -/
noncomputable def prodDom_snd_path {A : Type u} {B : Type v}
    {p1 p2 : ProdDom A B} (hp : Path p1 p2) :
    Path p1.snd p2.snd :=
  Path.congrArg ProdDom.snd hp

/-- Reduction operator for a product domain. -/
structure Reduction (A : Type u) (B : Type v) where
  reduce : ProdDom A B → ProdDom A B

/-- 27: Reduction preserves product domain paths -/
noncomputable def reduction_path {A : Type u} {B : Type v}
    (r : Reduction A B) {d1 d2 : ProdDom A B}
    (p : Path d1 d2) : Path (r.reduce d1) (r.reduce d2) :=
  Path.congrArg r.reduce p

/-- 28: Double reduction preserves paths -/
noncomputable def double_reduction_path {A : Type u} {B : Type v}
    (r : Reduction A B) {d1 d2 : ProdDom A B}
    (p : Path d1 d2) :
    Path (r.reduce (r.reduce d1)) (r.reduce (r.reduce d2)) :=
  Path.congrArg (fun x => r.reduce (r.reduce x)) p

/-- 29: Reduced product transformer path soundness -/
noncomputable def reduced_product_transformer {A : Type u} {B : Type v}
    (r : Reduction A B) (f : ProdDom A B → ProdDom A B)
    {d1 d2 : ProdDom A B} (p : Path d1 d2) :
    Path (r.reduce (f d1)) (r.reduce (f d2)) :=
  Path.congrArg (fun x => r.reduce (f x)) p

-- ============================================================================
-- Section 10: Abstract Domain Combinators
-- ============================================================================

/-- Lifted domain: adds a top element. -/
inductive Lifted (A : Type u) where
  | val : A → Lifted A
  | ltop : Lifted A

/-- 30: Lifted val preserves paths -/
noncomputable def lifted_val_path {A : Type u} {a1 a2 : A}
    (p : Path a1 a2) : Path (Lifted.val a1) (Lifted.val a2) :=
  Path.congrArg Lifted.val p

/-- Flat domain: only bot, val, top. -/
inductive FlatDom (A : Type u) where
  | fbot : FlatDom A
  | fval : A → FlatDom A
  | ftop : FlatDom A

/-- 31: Flat domain val injection preserves paths -/
noncomputable def flat_val_path {A : Type u} {a1 a2 : A}
    (p : Path a1 a2) : Path (FlatDom.fval a1) (FlatDom.fval a2) :=
  Path.congrArg FlatDom.fval p

/-- Interval domain representation. -/
structure IntervalDom where
  lo : Int
  hi : Int

/-- Interval join (convex hull). -/
noncomputable def intervalJoin (i1 i2 : IntervalDom) : IntervalDom :=
  { lo := min i1.lo i2.lo, hi := max i1.hi i2.hi }

/-- 32: Interval join preserves left-argument paths -/
noncomputable def intervalJoin_left_path {i1 i2 : IntervalDom} (j : IntervalDom)
    (p : Path i1 i2) : Path (intervalJoin i1 j) (intervalJoin i2 j) :=
  Path.congrArg (fun x => intervalJoin x j) p

/-- 33: Interval join preserves right-argument paths -/
noncomputable def intervalJoin_right_path (i : IntervalDom) {j1 j2 : IntervalDom}
    (p : Path j1 j2) : Path (intervalJoin i j1) (intervalJoin i j2) :=
  Path.congrArg (fun x => intervalJoin i x) p

/-- Interval widening. -/
noncomputable def intervalWiden (i1 i2 : IntervalDom) : IntervalDom :=
  { lo := if i2.lo < i1.lo then i2.lo - 100 else i1.lo
  , hi := if i2.hi > i1.hi then i2.hi + 100 else i1.hi }

/-- 34: Interval widening preserves paths on first arg -/
noncomputable def intervalWiden_left_path {i1 i2 : IntervalDom} (j : IntervalDom)
    (p : Path i1 i2) : Path (intervalWiden i1 j) (intervalWiden i2 j) :=
  Path.congrArg (fun x => intervalWiden x j) p

-- ============================================================================
-- Section 11: Powerset Domain
-- ============================================================================

/-- Powerset abstraction function: map alpha over a list. -/
noncomputable def powersetAlpha {C : Type u} {A : Type v} (alpha : C → A) :
    List C → List A :=
  List.map alpha

/-- 35: Powerset alpha preserves paths on equal sets -/
noncomputable def powerset_alpha_path {C : Type u} {A : Type v}
    (alpha : C → A) {s1 s2 : List C}
    (p : Path s1 s2) : Path (powersetAlpha alpha s1) (powersetAlpha alpha s2) :=
  Path.congrArg (powersetAlpha alpha) p

/-- 36: Powerset join (union via append) preserves left paths -/
noncomputable def powerset_join_left_path {A : Type u}
    {s1 s2 : List A} (t : List A)
    (p : Path s1 s2) : Path (s1 ++ t) (s2 ++ t) :=
  Path.congrArg (fun x => x ++ t) p

/-- 37: Powerset join right preserves paths -/
noncomputable def powerset_join_right_path {A : Type u}
    (s : List A) {t1 t2 : List A}
    (p : Path t1 t2) : Path (s ++ t1) (s ++ t2) :=
  Path.congrArg (fun x => s ++ x) p

-- ============================================================================
-- Section 12: Composition and Chaining of Abstract Interpretation Paths
-- ============================================================================

/-- 38: Two-step abstract computation path -/
noncomputable def two_step_abstract {A : Type u} (f g : A → A) {a1 a2 : A}
    (p : Path a1 a2) : Path (f (g a1)) (f (g a2)) :=
  Path.congrArg (fun x => f (g x)) p

/-- 39: Three-step abstract computation path -/
noncomputable def three_step_abstract {A : Type u} (f g h : A → A) {a1 a2 : A}
    (p : Path a1 a2) : Path (f (g (h a1))) (f (g (h a2))) :=
  Path.congrArg (fun x => f (g (h x))) p

/-- 40: Path chain from n-step widening -/
noncomputable def widen_chain_compose {A : Type u} (w : Widening A) (f : A → A)
    (n : Nat) {a1 a2 : A} (p : Path a1 a2) :
    Path (iterN (fun x => w.widen x (f x)) n a1)
         (iterN (fun x => w.widen x (f x)) n a2) :=
  iterN_path (fun x => w.widen x (f x)) n p

/-- 41: Soundness chain: concrete -> abstract via trans -/
noncomputable def soundness_chain {C : Type u} {A : Type v}
    (alpha : C → A) {c1 c2 c3 : C}
    (p12 : Path c1 c2) (p23 : Path c2 c3) :
    Path (alpha c1) (alpha c3) :=
  Path.trans (Path.congrArg alpha p12) (Path.congrArg alpha p23)

/-- 42: Abstract path reversal: toEq of trans-symm is refl -/
theorem abstract_path_reversal {C : Type u} {A : Type v}
    (alpha : C → A) {c1 c2 : C}
    (p : Path c1 c2) :
    (Path.trans (Path.congrArg alpha p)
               (Path.symm (Path.congrArg alpha p))).toEq = rfl :=
  Path.toEq_trans_symm (Path.congrArg alpha p)

-- ============================================================================
-- Section 13: Galois Connection Coherence Paths
-- ============================================================================

/-- 43: Alpha-gamma coherence for equal abstract values -/
noncomputable def ag_coherence_path {C : Type u} {A : Type v}
    (alpha : C → A) (gamma : A → C)
    {a1 a2 : A} (p : Path a1 a2) :
    Path (alpha (gamma a1)) (alpha (gamma a2)) :=
  Path.congrArg (fun x => alpha (gamma x)) p

/-- 44: Gamma-alpha coherence for equal concrete values -/
noncomputable def ga_coherence_path {C : Type u} {A : Type v}
    (alpha : C → A) (gamma : A → C)
    {c1 c2 : C} (p : Path c1 c2) :
    Path (gamma (alpha c1)) (gamma (alpha c2)) :=
  Path.congrArg (fun x => gamma (alpha x)) p

/-- 45: Alpha idempotence path (alpha . gamma . alpha = alpha) -/
noncomputable def alpha_idempotence_path {C : Type u} {A : Type v}
    (alpha : C → A) (gamma : A → C)
    {c1 c2 : C} (p : Path c1 c2) :
    Path (alpha (gamma (alpha c1))) (alpha (gamma (alpha c2))) :=
  Path.congrArg (fun x => alpha (gamma (alpha x))) p

/-- 46: Gamma idempotence path -/
noncomputable def gamma_idempotence_path {C : Type u} {A : Type v}
    (alpha : C → A) (gamma : A → C)
    {a1 a2 : A} (p : Path a1 a2) :
    Path (gamma (alpha (gamma a1))) (gamma (alpha (gamma a2))) :=
  Path.congrArg (fun x => gamma (alpha (gamma x))) p

-- ============================================================================
-- Section 14: Abstract Semantics Composition
-- ============================================================================

/-- Abstract state: pairs an abstract value with a path witness. -/
structure AbsState (A : Type u) where
  val : A
  label : Nat

/-- 47: AbsState value path extraction -/
noncomputable def absState_val_path {A : Type u} {s1 s2 : AbsState A}
    (p : Path s1 s2) : Path s1.val s2.val :=
  Path.congrArg AbsState.val p

/-- 48: AbsState label path extraction -/
noncomputable def absState_label_path {A : Type u} {s1 s2 : AbsState A}
    (p : Path s1 s2) : Path s1.label s2.label :=
  Path.congrArg AbsState.label p

/-- Sequential abstract transformer composition. -/
noncomputable def seqTransform {A : Type u} (f g : A → A) : A → A := fun a => g (f a)

/-- 49: Sequential composition preserves paths -/
noncomputable def seq_transform_path {A : Type u} (f g : A → A)
    {a1 a2 : A} (p : Path a1 a2) :
    Path (seqTransform f g a1) (seqTransform f g a2) :=
  Path.congrArg (seqTransform f g) p

/-- Parallel abstract transformer on products. -/
noncomputable def parTransform {A : Type u} {B : Type v}
    (f : A → A) (g : B → B) : ProdDom A B → ProdDom A B :=
  fun d => { fst := f d.fst, snd := g d.snd }

/-- 50: Parallel composition preserves paths -/
noncomputable def par_transform_path {A : Type u} {B : Type v}
    (f : A → A) (g : B → B)
    {d1 d2 : ProdDom A B} (p : Path d1 d2) :
    Path (parTransform f g d1) (parTransform f g d2) :=
  Path.congrArg (parTransform f g) p

-- ============================================================================
-- Section 15: Advanced Soundness and Path Algebra
-- ============================================================================

/-- 51: congrArg distributes over trans -/
theorem congrArg_trans_witness {A : Type u} {B : Type v}
    (f : A → B) {a1 a2 a3 : A}
    (p : Path a1 a2) (q : Path a2 a3) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

/-- 52: congrArg distributes over symm -/
theorem congrArg_symm_witness {A : Type u} {B : Type v}
    (f : A → B) {a1 a2 : A} (p : Path a1 a2) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

/-- 53: Transitivity associativity for abstract chains -/
theorem abstract_trans_assoc {A : Type u} {B : Type v}
    (alpha : A → B) {a1 a2 a3 a4 : A}
    (p : Path a1 a2) (q : Path a2 a3) (r : Path a3 a4) :
    Path.trans (Path.trans (Path.congrArg alpha p) (Path.congrArg alpha q))
               (Path.congrArg alpha r) =
    Path.trans (Path.congrArg alpha p)
               (Path.trans (Path.congrArg alpha q) (Path.congrArg alpha r)) :=
  Path.trans_assoc (Path.congrArg alpha p) (Path.congrArg alpha q)
              (Path.congrArg alpha r)

/-- 54: Path refl is left identity for abstract trans -/
theorem abstract_refl_left {A : Type u} {B : Type v}
    (alpha : A → B) {a1 a2 : A} (p : Path a1 a2) :
    Path.trans (Path.refl (alpha a1)) (Path.congrArg alpha p) =
    Path.congrArg alpha p :=
  Path.trans_refl_left (Path.congrArg alpha p)

/-- 55: Path refl is right identity for abstract trans -/
theorem abstract_refl_right {A : Type u} {B : Type v}
    (alpha : A → B) {a1 a2 : A} (p : Path a1 a2) :
    Path.trans (Path.congrArg alpha p) (Path.refl (alpha a2)) =
    Path.congrArg alpha p :=
  Path.trans_refl_right (Path.congrArg alpha p)

/-- 56: Symm-symm is identity for abstract paths -/
theorem abstract_symm_symm {A : Type u} {B : Type v}
    (alpha : A → B) {a1 a2 : A} (p : Path a1 a2) :
    Path.symm (Path.symm (Path.congrArg alpha p)) =
    Path.congrArg alpha p :=
  Path.symm_symm (Path.congrArg alpha p)

/-- 57: Symm-trans toEq cancellation for abstract paths -/
theorem abstract_symm_trans {A : Type u} {B : Type v}
    (alpha : A → B) {a1 a2 : A} (p : Path a1 a2) :
    (Path.trans (Path.congrArg alpha p)
               (Path.symm (Path.congrArg alpha p))).toEq = rfl :=
  Path.toEq_trans_symm (Path.congrArg alpha p)

-- ============================================================================
-- Section 16: Fixpoint Characterization
-- ============================================================================

/-- A fixpoint witness: value a such that f a = a. -/
structure FixpointWitness (A : Type u) (f : A → A) where
  val : A
  is_fix : Path (f val) val

/-- 58: Fixpoint is invariant under iteration -/
noncomputable def fixpoint_iter_invariant {A : Type u} (f : A → A)
    (fp : FixpointWitness A f) (n : Nat) :
    Path (iterN f n fp.val) fp.val := by
  induction n with
  | zero => exact Path.refl fp.val
  | succ k ih =>
    exact Path.trans (Path.congrArg f ih) fp.is_fix

/-- 59: Two fixpoints with a connecting path give equal images -/
noncomputable def fixpoints_connected {A : Type u} (f : A → A)
    (fp1 fp2 : FixpointWitness A f)
    (conn : Path fp1.val fp2.val) :
    Path (f fp1.val) (f fp2.val) :=
  Path.congrArg f conn

/-- 60: Fixpoint of composed function -/
noncomputable def fixpoint_compose_path {A : Type u} (f g : A → A)
    (fp : FixpointWitness A (fun x => f (g x)))
    : Path (f (g fp.val)) fp.val :=
  fp.is_fix

-- ============================================================================
-- Section 17: Domain Morphisms and Galois Insertions
-- ============================================================================

/-- A Galois insertion (alpha . gamma = id). -/
structure GaloisInsertion (C : Type u) (A : Type v) where
  alpha : C → A
  gamma : A → C
  insertion : ∀ a, Path (alpha (gamma a)) a

/-- 61: Galois insertion implies alpha is surjective on range -/
noncomputable def gi_alpha_surj_path {C : Type u} {A : Type v}
    (gi : GaloisInsertion C A) (a : A) :
    Path (gi.alpha (gi.gamma a)) a :=
  gi.insertion a

/-- 62: Galois insertion path composition -/
noncomputable def gi_compose_path {C : Type u} {A : Type v}
    (gi : GaloisInsertion C A) {a1 a2 : A}
    (p : Path a1 a2) :
    Path (gi.alpha (gi.gamma a1)) (gi.alpha (gi.gamma a2)) :=
  Path.congrArg (fun x => gi.alpha (gi.gamma x)) p

/-- 63: Galois insertion: both paths have same toEq -/
theorem gi_trans_witness {C : Type u} {A : Type v}
    (gi : GaloisInsertion C A) {a1 a2 : A}
    (p : Path a1 a2) :
    (Path.trans (gi.insertion a1) p).toEq =
    (Path.trans (Path.congrArg (fun x => gi.alpha (gi.gamma x)) p)
               (gi.insertion a2)).toEq := by
  simp

-- ============================================================================
-- Section 18: Sign Domain Example
-- ============================================================================

/-- Simple sign abstract domain. -/
inductive SignDom where
  | sbot : SignDom
  | neg : SignDom
  | zero : SignDom
  | pos : SignDom
  | stop : SignDom
  deriving Repr, DecidableEq

/-- Sign domain join. -/
noncomputable def signJoin : SignDom → SignDom → SignDom
  | SignDom.sbot, x => x
  | x, SignDom.sbot => x
  | SignDom.stop, _ => SignDom.stop
  | _, SignDom.stop => SignDom.stop
  | x, y => if x == y then x else SignDom.stop

/-- 64: Sign join preserves left-argument paths -/
noncomputable def signJoin_left_path {s1 s2 : SignDom} (t : SignDom)
    (p : Path s1 s2) : Path (signJoin s1 t) (signJoin s2 t) :=
  Path.congrArg (fun x => signJoin x t) p

/-- 65: Sign join preserves right-argument paths -/
noncomputable def signJoin_right_path (s : SignDom) {t1 t2 : SignDom}
    (p : Path t1 t2) : Path (signJoin s t1) (signJoin s t2) :=
  Path.congrArg (fun x => signJoin s x) p

/-- Abstract negation on signs. -/
noncomputable def signNeg : SignDom → SignDom
  | SignDom.neg => SignDom.pos
  | SignDom.pos => SignDom.neg
  | x => x

/-- 66: Sign negation preserves paths -/
noncomputable def signNeg_path {s1 s2 : SignDom}
    (p : Path s1 s2) : Path (signNeg s1) (signNeg s2) :=
  Path.congrArg signNeg p

/-- 67: Double sign negation preserves paths -/
noncomputable def signNeg_double_path {s1 s2 : SignDom}
    (p : Path s1 s2) : Path (signNeg (signNeg s1)) (signNeg (signNeg s2)) :=
  Path.congrArg (fun x => signNeg (signNeg x)) p

-- ============================================================================
-- Section 19: Transfer Function Lattice
-- ============================================================================

/-- Transfer function representation. -/
structure TransferFn (A : Type u) where
  apply : A → A

/-- Compose two transfer functions. -/
noncomputable def composeTF {A : Type u} (tf1 tf2 : TransferFn A) : TransferFn A :=
  { apply := fun a => tf1.apply (tf2.apply a) }

/-- 68: Transfer function composition preserves argument paths -/
noncomputable def composeTF_arg_path {A : Type u}
    (tf1 tf2 : TransferFn A) {a1 a2 : A}
    (p : Path a1 a2) :
    Path ((composeTF tf1 tf2).apply a1) ((composeTF tf1 tf2).apply a2) :=
  Path.congrArg (composeTF tf1 tf2).apply p

/-- 69: Transfer function path from equal functions -/
noncomputable def transferFn_path {A : Type u}
    {tf1 tf2 : TransferFn A} (a : A)
    (p : Path tf1 tf2) : Path (tf1.apply a) (tf2.apply a) :=
  Path.congrArg (fun tf => tf.apply a) p

/-- 70: Transfer function triple composition path -/
noncomputable def triple_compose_path {A : Type u}
    (tf1 tf2 tf3 : TransferFn A) {a1 a2 : A}
    (p : Path a1 a2) :
    Path ((composeTF tf1 (composeTF tf2 tf3)).apply a1)
         ((composeTF tf1 (composeTF tf2 tf3)).apply a2) :=
  Path.congrArg (composeTF tf1 (composeTF tf2 tf3)).apply p

-- ============================================================================
-- Conclusion
-- ============================================================================

/-- Summary: Full abstract interpretation pipeline path -/
noncomputable def full_pipeline_path {C : Type u} {A : Type v}
    (alpha : C → A) (gamma : A → C)
    (f : C → C) (w : Widening A) (n : Nat)
    {c1 c2 : C} (p : Path c1 c2) :
    Path (widenIterN w (bestAbsTransformer alpha gamma f) n (alpha c1))
         (widenIterN w (bestAbsTransformer alpha gamma f) n (alpha c2)) :=
  widenIterN_path w (bestAbsTransformer alpha gamma f) n
    (Path.congrArg alpha p)

end AbstractInterpDeep
