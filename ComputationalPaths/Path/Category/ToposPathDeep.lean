/-
  ComputationalPaths/Path/Category/ToposPathDeep.lean

  Elementary Topos Structure via Computational Paths

  Develops the categorical structure of an elementary topos using Path equalities:
  - Subobject classifier and characteristic morphisms
  - Pullback squares with Path coherence
  - Exponential objects, evaluation, currying
  - Power objects and singleton morphisms
  - Internal logic: conjunction, disjunction, implication as morphisms
  - Lawvere-Tierney topologies
  - Sheafification structure
  - Natural number object with recursion/induction
  - All coherence via Path.trans, Path.symm, Path.congrArg

  Author: armada-335 (ToposPathDeep)
-/

import ComputationalPaths.Path.Basic

open ComputationalPaths

namespace ToposPathDeep

-- ===================================================================
-- Section 1: Basic Categorical Infrastructure
-- ===================================================================

/-- Morphisms in our topos -/
structure Mor (A B : Type) where
  fn : A → B

/-- Identity morphism -/
def Mor.id (A : Type) : Mor A A := ⟨fun a => a⟩

/-- Composition of morphisms -/
def Mor.comp {A B C : Type} (g : Mor B C) (f : Mor A B) : Mor A C :=
  ⟨fun a => g.fn (f.fn a)⟩

/-- Terminal object -/
inductive Ter : Type where
  | pt : Ter

/-- Unique morphism to terminal -/
def Mor.terminal (A : Type) : Mor A Ter := ⟨fun _ => Ter.pt⟩

-- ===================================================================
-- Section 2: Subobject Classifier
-- ===================================================================

/-- The subobject classifier Om -/
inductive Om : Type where
  | top : Om
  | bot : Om
  deriving DecidableEq

/-- The truth morphism true : Ter → Om -/
def truthMor : Mor Ter Om := ⟨fun _ => Om.top⟩

/-- Characteristic morphism for a subobject -/
def charMor {A : Type} (P : A → Prop) [DecidablePred P] : Mor A Om :=
  ⟨fun a => if P a then Om.top else Om.bot⟩

/-- Def 1: Truth morphism sends terminal point to top -/
def truth_sends_to_top :
    Path (truthMor.fn Ter.pt) Om.top :=
  Path.refl Om.top

/-- Def 2: Characteristic morphism reflects membership -/
def char_reflects_mem {A : Type} (P : A → Prop) [DecidablePred P]
    (a : A) (h : P a) :
    Path ((charMor P).fn a) Om.top := by
  unfold charMor
  simp [h]
  exact Path.refl Om.top

/-- Def 3: Characteristic morphism reflects non-membership -/
def char_reflects_nonmem {A : Type} (P : A → Prop) [DecidablePred P]
    (a : A) (h : ¬P a) :
    Path ((charMor P).fn a) Om.bot := by
  unfold charMor
  simp [h]
  exact Path.refl Om.bot

-- ===================================================================
-- Section 3: Pullback Squares
-- ===================================================================

/-- Pullback of two morphisms -/
structure Pullback {A B C : Type} (f : Mor A C) (g : Mor B C) where
  fst : A
  snd : B
  commutes : Path (f.fn fst) (g.fn snd)

/-- Def 4: Pullback commutativity via Path -/
def pullback_commutes {A B C : Type} {f : Mor A C} {g : Mor B C}
    (pb : Pullback f g) :
    Path (f.fn pb.fst) (g.fn pb.snd) :=
  pb.commutes

/-- Def 5: Pullback symmetry gives reversed Path -/
def pullback_symm {A B C : Type} {f : Mor A C} {g : Mor B C}
    (pb : Pullback f g) :
    Path (g.fn pb.snd) (f.fn pb.fst) :=
  Path.symm pb.commutes

/-- Def 6: Pullback along identity is identity -/
def pullback_along_id {A B : Type} (f : Mor A B)
    (a : A) :
    Path ((Mor.comp (Mor.id B) f).fn a) (f.fn a) :=
  Path.refl (f.fn a)

/-- Def 7: Pullback composition coherence -/
def pullback_comp_coherence {A B C D : Type}
    (f : Mor A B) (g : Mor B C) (h : Mor C D)
    (a : A) :
    Path ((Mor.comp (Mor.comp h g) f).fn a)
         ((Mor.comp h (Mor.comp g f)).fn a) :=
  Path.refl (h.fn (g.fn (f.fn a)))

-- ===================================================================
-- Section 4: Exponential Objects
-- ===================================================================

/-- Exponential object (internal hom) -/
structure Exp (A B : Type) where
  app : A → B

/-- Evaluation morphism: B^A × A → B -/
def evalMor (A B : Type) : Mor (Exp A B × A) B :=
  ⟨fun p => p.1.app p.2⟩

/-- Currying: (C × A → B) → (C → B^A) -/
def curryMor {A B C : Type} (f : Mor (C × A) B) : Mor C (Exp A B) :=
  ⟨fun c => ⟨fun a => f.fn (c, a)⟩⟩

/-- Uncurrying: (C → B^A) → (C × A → B) -/
def uncurryMor {A B C : Type} (g : Mor C (Exp A B)) : Mor (C × A) B :=
  ⟨fun p => (g.fn p.1).app p.2⟩

/-- Def 8: Evaluation after currying is the original morphism -/
def eval_after_curry {A B C : Type} (f : Mor (C × A) B)
    (c : C) (a : A) :
    Path ((evalMor A B).fn ((curryMor f).fn c, a)) (f.fn (c, a)) :=
  Path.refl (f.fn (c, a))

/-- Def 9: Currying after uncurrying recovers original -/
def curry_uncurry {A B C : Type} (g : Mor C (Exp A B))
    (c : C) (a : A) :
    Path (((curryMor (uncurryMor g)).fn c).app a) ((g.fn c).app a) :=
  Path.refl ((g.fn c).app a)

/-- Def 10: Uncurrying after currying recovers original -/
def uncurry_curry {A B C : Type} (f : Mor (C × A) B)
    (p : C × A) :
    Path ((uncurryMor (curryMor f)).fn p) (f.fn (p.1, p.2)) :=
  Path.refl (f.fn (p.1, p.2))

/-- Def 11: Evaluation naturality -/
def eval_naturality {A B C : Type}
    (g : Mor B C) (e : Exp A B) (a : A) :
    Path (g.fn ((evalMor A B).fn (e, a)))
         ((evalMor A C).fn (⟨fun x => g.fn (e.app x)⟩, a)) :=
  Path.refl (g.fn (e.app a))

/-- Def 12: Curry preserves composition -/
def curry_comp {A B C D : Type}
    (f : Mor (C × A) B) (g : Mor D C) (d : D) (a : A) :
    Path (((curryMor f).fn (g.fn d)).app a)
         (((curryMor ⟨fun p => f.fn (g.fn p.1, p.2)⟩).fn d).app a) :=
  Path.refl (f.fn (g.fn d, a))

-- ===================================================================
-- Section 5: Power Objects
-- ===================================================================

/-- Power object P(A) as A → Om -/
def PowerObj (A : Type) := Mor A Om

/-- Singleton morphism: A → P(A) -/
def singletonMor (A : Type) [DecidableEq A] : Mor A (PowerObj A) :=
  ⟨fun a => ⟨fun x => if a = x then Om.top else Om.bot⟩⟩

/-- Membership relation -/
def membership (A : Type) : Mor (A × PowerObj A) Om :=
  ⟨fun p => p.2.fn p.1⟩

/-- Def 13: Singleton contains the element -/
def singleton_contains {A : Type} [DecidableEq A]
    (a : A) :
    Path ((membership A).fn (a, (singletonMor A).fn a)) Om.top := by
  unfold membership singletonMor
  simp
  exact Path.refl Om.top

/-- Def 14: Singleton excludes other elements -/
def singleton_excludes {A : Type} [DecidableEq A]
    (a b : A) (h : a ≠ b) :
    Path ((membership A).fn (b, (singletonMor A).fn a)) Om.bot := by
  unfold membership singletonMor
  simp [h]
  exact Path.refl Om.bot

/-- Def 15: Membership factors through truth -/
def mem_through_truth {A : Type} [DecidableEq A]
    (a : A) :
    Path ((membership A).fn (a, (singletonMor A).fn a))
         (truthMor.fn Ter.pt) := by
  unfold membership singletonMor truthMor
  simp
  exact Path.refl Om.top

-- ===================================================================
-- Section 6: Internal Logic - Conjunction, Disjunction, Implication
-- ===================================================================

/-- Conjunction: Om × Om → Om -/
def conjMor : Mor (Om × Om) Om :=
  ⟨fun p => match p.1, p.2 with
    | Om.top, Om.top => Om.top
    | _, _ => Om.bot⟩

/-- Disjunction: Om × Om → Om -/
def disjMor : Mor (Om × Om) Om :=
  ⟨fun p => match p.1, p.2 with
    | Om.bot, Om.bot => Om.bot
    | _, _ => Om.top⟩

/-- Implication: Om × Om → Om -/
def implMor : Mor (Om × Om) Om :=
  ⟨fun p => match p.1, p.2 with
    | Om.top, Om.bot => Om.bot
    | _, _ => Om.top⟩

/-- Negation: Om → Om -/
def negMor : Mor Om Om :=
  ⟨fun p => match p with
    | Om.top => Om.bot
    | Om.bot => Om.top⟩

/-- Def 16: Conjunction is commutative -/
def conj_comm (a b : Om) :
    Path (conjMor.fn (a, b)) (conjMor.fn (b, a)) := by
  cases a <;> cases b <;> exact Path.refl _

/-- Def 17: Disjunction is commutative -/
def disj_comm (a b : Om) :
    Path (disjMor.fn (a, b)) (disjMor.fn (b, a)) := by
  cases a <;> cases b <;> exact Path.refl _

/-- Def 18: Conjunction with top is identity -/
def conj_top_id (a : Om) :
    Path (conjMor.fn (Om.top, a)) a := by
  cases a <;> exact Path.refl _

/-- Def 19: Disjunction with bot is identity -/
def disj_bot_id (a : Om) :
    Path (disjMor.fn (Om.bot, a)) a := by
  cases a <;> exact Path.refl _

/-- Def 20: Conjunction with bot is bot -/
def conj_bot_absorb (a : Om) :
    Path (conjMor.fn (Om.bot, a)) Om.bot := by
  cases a <;> exact Path.refl _

/-- Def 21: Disjunction with top is top -/
def disj_top_absorb (a : Om) :
    Path (disjMor.fn (Om.top, a)) Om.top := by
  cases a <;> exact Path.refl _

/-- Def 22: Double negation -/
def double_negation (a : Om) :
    Path (negMor.fn (negMor.fn a)) a := by
  cases a <;> exact Path.refl _

/-- Def 23: Conjunction associativity -/
def conj_assoc (a b c : Om) :
    Path (conjMor.fn (conjMor.fn (a, b), c))
         (conjMor.fn (a, conjMor.fn (b, c))) := by
  cases a <;> cases b <;> cases c <;> exact Path.refl _

/-- Def 24: Disjunction associativity -/
def disj_assoc (a b c : Om) :
    Path (disjMor.fn (disjMor.fn (a, b), c))
         (disjMor.fn (a, disjMor.fn (b, c))) := by
  cases a <;> cases b <;> cases c <;> exact Path.refl _

/-- Def 25: Implication modus ponens -/
def modus_ponens :
    Path (conjMor.fn (Om.top, implMor.fn (Om.top, Om.top))) Om.top :=
  Path.refl Om.top

/-- Def 26: Implication with false antecedent -/
def ex_falso (b : Om) :
    Path (implMor.fn (Om.bot, b)) Om.top := by
  cases b <;> exact Path.refl _

/-- Def 27: De Morgan's law (conjunction) -/
def de_morgan_conj (a b : Om) :
    Path (negMor.fn (conjMor.fn (a, b)))
         (disjMor.fn (negMor.fn a, negMor.fn b)) := by
  cases a <;> cases b <;> exact Path.refl _

/-- Def 28: De Morgan's law (disjunction) -/
def de_morgan_disj (a b : Om) :
    Path (negMor.fn (disjMor.fn (a, b)))
         (conjMor.fn (negMor.fn a, negMor.fn b)) := by
  cases a <;> cases b <;> exact Path.refl _

/-- Def 29: Distributivity of conjunction over disjunction -/
def conj_disj_distrib (a b c : Om) :
    Path (conjMor.fn (a, disjMor.fn (b, c)))
         (disjMor.fn (conjMor.fn (a, b), conjMor.fn (a, c))) := by
  cases a <;> cases b <;> cases c <;> exact Path.refl _

/-- Def 30: Implication contrapositive -/
def contrapositive (a b : Om) :
    Path (implMor.fn (a, b))
         (implMor.fn (negMor.fn b, negMor.fn a)) := by
  cases a <;> cases b <;> exact Path.refl _

/-- Def 31: Conjunction idempotence -/
def conj_idempotent (a : Om) :
    Path (conjMor.fn (a, a)) a := by
  cases a <;> exact Path.refl _

/-- Def 32: Disjunction idempotence -/
def disj_idempotent (a : Om) :
    Path (disjMor.fn (a, a)) a := by
  cases a <;> exact Path.refl _

/-- Def 33: Absorption law conj-disj -/
def absorption_conj_disj (a b : Om) :
    Path (conjMor.fn (a, disjMor.fn (a, b))) a := by
  cases a <;> cases b <;> exact Path.refl _

/-- Def 34: Absorption law disj-conj -/
def absorption_disj_conj (a b : Om) :
    Path (disjMor.fn (a, conjMor.fn (a, b))) a := by
  cases a <;> cases b <;> exact Path.refl _

/-- Def 35: Negation of top is bot -/
def neg_top :
    Path (negMor.fn Om.top) Om.bot :=
  Path.refl Om.bot

/-- Def 36: Negation of bot is top -/
def neg_bot :
    Path (negMor.fn Om.bot) Om.top :=
  Path.refl Om.top

-- ===================================================================
-- Section 7: Lawvere-Tierney Topologies
-- ===================================================================

/-- A Lawvere-Tierney topology j : Om → Om -/
structure LTTopology where
  j : Mor Om Om
  preserves_top : Path (j.fn Om.top) Om.top
  idempotent : (a : Om) → Path (j.fn (j.fn a)) (j.fn a)
  preserves_conj : (a b : Om) →
    Path (j.fn (conjMor.fn (a, b)))
         (conjMor.fn (j.fn a, j.fn b))

/-- The identity topology -/
def idTopology : LTTopology where
  j := Mor.id Om
  preserves_top := Path.refl Om.top
  idempotent := fun a => Path.refl a
  preserves_conj := fun _ _ => Path.refl _

/-- The double-negation topology -/
def dblNegTopology : LTTopology where
  j := ⟨fun a => negMor.fn (negMor.fn a)⟩
  preserves_top := Path.refl Om.top
  idempotent := fun a => by cases a <;> exact Path.refl _
  preserves_conj := fun a b => by cases a <;> cases b <;> exact Path.refl _

/-- Def 37: Identity topology is idempotent -/
def id_topology_idempotent (a : Om) :
    Path (idTopology.j.fn (idTopology.j.fn a)) (idTopology.j.fn a) :=
  idTopology.idempotent a

/-- Def 38: Double negation topology preserves top -/
def dblNeg_preserves_top :
    Path (dblNegTopology.j.fn Om.top) Om.top :=
  dblNegTopology.preserves_top

/-- Def 39: Double negation topology is idempotent -/
def dblNeg_idempotent (a : Om) :
    Path (dblNegTopology.j.fn (dblNegTopology.j.fn a))
         (dblNegTopology.j.fn a) :=
  dblNegTopology.idempotent a

/-- Def 40: Topology triple application coherence via Path.trans -/
def topology_triple_coherence (t : LTTopology) (a : Om) :
    Path (t.j.fn (t.j.fn (t.j.fn a))) (t.j.fn a) :=
  Path.trans (t.idempotent (t.j.fn a)) (t.idempotent a)

/-- Def 41: Topology preserves conjunction symmetry via congrArg -/
def topology_conj_symm (t : LTTopology) (a b : Om) :
    Path (t.j.fn (conjMor.fn (a, b))) (t.j.fn (conjMor.fn (b, a))) :=
  Path.congrArg t.j.fn (conj_comm a b)

-- ===================================================================
-- Section 8: Sheafification / Closure
-- ===================================================================

/-- Closure operator induced by a topology -/
def closureOp (t : LTTopology) {A : Type}
    (chi : Mor A Om) : Mor A Om :=
  ⟨fun a => t.j.fn (chi.fn a)⟩

/-- A subobject is closed if j ∘ chi = chi -/
structure ClosedSubobj (t : LTTopology) {A : Type} (chi : Mor A Om) where
  closed : (a : A) → Path (t.j.fn (chi.fn a)) (chi.fn a)

/-- A subobject is dense if j ∘ chi = top -/
structure DenseSubobj (t : LTTopology) {A : Type} (chi : Mor A Om) where
  dense : (a : A) → Path (t.j.fn (chi.fn a)) Om.top

/-- Def 42: Closure is idempotent -/
def closure_idempotent (t : LTTopology) {A : Type}
    (chi : Mor A Om) (a : A) :
    Path (t.j.fn (t.j.fn (chi.fn a))) (t.j.fn (chi.fn a)) :=
  t.idempotent (chi.fn a)

/-- Def 43: Closure of closed is itself -/
def closure_of_closed (t : LTTopology) {A : Type}
    (chi : Mor A Om) (cl : ClosedSubobj t chi) (a : A) :
    Path ((closureOp t chi).fn a) (chi.fn a) :=
  cl.closed a

/-- Def 44: Closure preserves top -/
def closure_preserves_top (t : LTTopology) {A : Type}
    (chi : Mor A Om) (a : A) (h : Path (chi.fn a) Om.top) :
    Path ((closureOp t chi).fn a) Om.top :=
  Path.trans (Path.congrArg t.j.fn h) t.preserves_top

/-- Def 45: Dense subobject closure gives top -/
def dense_closure_top (t : LTTopology) {A : Type}
    (chi : Mor A Om) (d : DenseSubobj t chi) (a : A) :
    Path ((closureOp t chi).fn a) Om.top :=
  d.dense a

/-- Def 46: Double closure equals single closure via trans -/
def double_closure_eq (t : LTTopology) {A : Type}
    (chi : Mor A Om) (a : A) :
    Path ((closureOp t (closureOp t chi)).fn a) ((closureOp t chi).fn a) :=
  t.idempotent (chi.fn a)

-- ===================================================================
-- Section 9: Natural Number Object
-- ===================================================================

/-- Natural number object specification -/
structure NNO (N : Type) where
  zero : Ter → N
  succ : N → N

/-- The standard NNO -/
def stdNNO : NNO Nat where
  zero := fun _ => 0
  succ := Nat.succ

/-- Recursion from NNO -/
def nnoRec {A : Type} (a : A) (f : A → A) : Nat → A
  | 0 => a
  | n + 1 => f (nnoRec a f n)

/-- Iteration via NNO -/
def nnoIter {A : Type} (f : A → A) (n : Nat) (a : A) : A :=
  nnoRec a f n

/-- Def 47: NNO recursion base case -/
def nno_rec_zero {A : Type} (a : A) (f : A → A) :
    Path (nnoRec a f 0) a :=
  Path.refl a

/-- Def 48: NNO recursion step case -/
def nno_rec_succ {A : Type} (a : A) (f : A → A) (n : Nat) :
    Path (nnoRec a f (n + 1)) (f (nnoRec a f n)) :=
  Path.refl (f (nnoRec a f n))

/-- Def 49: NNO recursion commutes with successor -/
def nno_rec_succ_comm {A : Type} (a : A) (f : A → A) (n : Nat) :
    Path (nnoRec a f (stdNNO.succ n)) (f (nnoRec a f n)) :=
  Path.refl (f (nnoRec a f n))

/-- Def 50: Zero iterations is identity -/
def nno_iter_zero {A : Type} (f : A → A) (a : A) :
    Path (nnoIter f 0 a) a :=
  Path.refl a

/-- Def 51: One iteration is f -/
def nno_iter_one {A : Type} (f : A → A) (a : A) :
    Path (nnoIter f 1 a) (f a) :=
  Path.refl (f a)

/-- Def 52: Iteration step -/
def nno_iter_step {A : Type} (f : A → A) (n : Nat) (a : A) :
    Path (nnoIter f (n + 1) a) (f (nnoIter f n a)) :=
  Path.refl (f (nnoIter f n a))

/-- Def 53: NNO with function application -/
def nno_func_coherence {A B : Type}
    (g : A → B) (f : B → B) (a : A) (n : Nat) :
    Path (nnoRec (g a) f n) (nnoIter f n (g a)) :=
  Path.refl (nnoRec (g a) f n)

-- ===================================================================
-- Section 10: Path Coherence Diagrams
-- ===================================================================

/-- Theorem 54: Symm is involutive -/
theorem symm_involutive {X : Type} {a b : X} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- Theorem 55: congrArg distributes over trans -/
theorem congrArg_trans_distrib {X Y : Type} (f : X → Y)
    {a b c : X} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

/-- Theorem 56: congrArg distributes over symm -/
theorem congrArg_symm_distrib {X Y : Type} (f : X → Y)
    {a b : X} (p : Path a b) :
    Path.congrArg f (Path.symm p) =
    Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

/-- Theorem 57: Trans with refl on left -/
theorem trans_left_unit {X : Type} {a b : X} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  Path.trans_refl_left p

/-- Theorem 58: Trans with refl on right -/
theorem trans_right_unit {X : Type} {a b : X} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  Path.trans_refl_right p

/-- Theorem 59: Trans associativity -/
theorem trans_assoc_paths {X : Type} {a b c d : X}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

/-- Theorem 60: Symm-trans identity -/
theorem symm_trans_id {X : Type} {a b c : X} (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

-- ===================================================================
-- Section 11: Topos Coherence Combining Everything
-- ===================================================================

/-- Def 61: Morphism composition associativity -/
def mor_comp_assoc {A B C D : Type}
    (f : Mor A B) (g : Mor B C) (h : Mor C D) (a : A) :
    Path ((Mor.comp h (Mor.comp g f)).fn a)
         ((Mor.comp (Mor.comp h g) f).fn a) :=
  Path.refl (h.fn (g.fn (f.fn a)))

/-- Def 62: Terminal morphism uniqueness -/
def terminal_unique {A : Type} (f g : Mor A Ter) (a : A) :
    Path (f.fn a) (g.fn a) := by
  have hf : f.fn a = Ter.pt := by cases (f.fn a); rfl
  have hg : g.fn a = Ter.pt := by cases (g.fn a); rfl
  exact Path.trans (Path.mk [] hf) (Path.mk [] hg.symm)

/-- Def 63: Subobject classifier for total predicate -/
def subobj_total {A : Type} [DecidablePred (fun (_ : A) => True)]
    (a : A) :
    Path ((charMor (fun _ : A => True)).fn a) Om.top := by
  unfold charMor
  simp
  exact Path.refl Om.top

/-- Def 64: Topology and conjunction coherence -/
def topology_conj_coherence (t : LTTopology) (a b : Om) :
    Path (t.j.fn (conjMor.fn (a, b)))
         (conjMor.fn (t.j.fn a, t.j.fn b)) :=
  t.preserves_conj a b

/-- Def 65: Comprehensive topos coherence via Path.trans chain -/
def comprehensive_topos_coherence (t : LTTopology) :
    Path (t.j.fn (conjMor.fn (Om.top, Om.top))) Om.top :=
  Path.trans
    (t.preserves_conj Om.top Om.top)
    (Path.trans
      (Path.congrArg (fun x => conjMor.fn (x, t.j.fn Om.top)) t.preserves_top)
      (Path.congrArg (fun x => conjMor.fn (Om.top, x)) t.preserves_top))

/-- Def 66: Exponential and eval in topos -/
def exp_eval_topos {A B : Type}
    (f : Exp A B) (a : A) :
    Path ((evalMor A B).fn (f, a)) (f.app a) :=
  Path.refl (f.app a)

end ToposPathDeep
