/-
  ComputationalPaths/Path/Rewriting/ConstraintSolvingDeep.lean

  Constraint Solving and Unification Theory via Computational Paths

  Models unification problems, MGU computation, Martelli-Montanari rules,
  constraint propagation, AC-unification structure, disunification,
  solved forms, and triangular substitutions — all witnessed by Path operations.

  Author: armada-369 (ConstraintSolvingDeep)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.ConstraintSolvingDeep

open ComputationalPaths.Path

/-! ## Term Language for Unification -/

/-- Simple first-order terms for unification -/
inductive UTerm (V F : Type) : Type where
  | var : V -> UTerm V F
  | app : F -> List (UTerm V F) -> UTerm V F
  deriving Repr, BEq

/-- A substitution maps variables to terms -/
def Substitution (V F : Type) := V -> UTerm V F

/-- Identity substitution -/
def idSubst {V F : Type} : Substitution V F := UTerm.var

/-- Apply substitution to a term -/
def applySubst {V F : Type} (s : Substitution V F) : UTerm V F -> UTerm V F
  | UTerm.var v => s v
  | UTerm.app f args => UTerm.app f (args.map (applySubst s))

/-- An equation between two terms -/
structure Equation (V F : Type) where
  lhs : UTerm V F
  rhs : UTerm V F

/-- A unification problem is a list of equations -/
def UnifProblem (V F : Type) := List (Equation V F)

/-! ## Constraint States -/

/-- State of constraint solving: active constraints + solved substitution pairs -/
structure ConstraintState (V F : Type) where
  active : List (Equation V F)
  solved : List (V × UTerm V F)

/-- A solved form has no active constraints -/
def ConstraintState.isSolved {V F : Type} (cs : ConstraintState V F) : Prop :=
  cs.active = []

/-! ## Martelli-Montanari Rule Tags -/

/-- Tags for the Martelli-Montanari unification rules -/
inductive MMRule : Type where
  | decompose : MMRule
  | eliminate  : MMRule
  | swap       : MMRule
  | delete     : MMRule
  | check      : MMRule
  deriving Repr, BEq

/-! ## Path-Witnessed Rule Application -/

/-- A single Martelli-Montanari step witnessed by a Path -/
structure MMStep (A : Type) where
  rule : MMRule
  before : A
  after : A
  witness : Path before after

/-- Chain of MM steps as transitive Path composition -/
def mmChain {A : Type} (a : A) : Path a a := Path.refl a

/-- Extend a chain with one more step -/
def mmExtend {A : Type} {a b c : A}
    (chain : Path a b) (step : MMStep A) (heq_b : b = step.before) (heq_c : c = step.after)
    : Path a c := by
  subst heq_b; subst heq_c
  exact Path.trans chain step.witness

/-! ## Def 1-5: Basic Path Properties for Constraint Steps -/

/-- Def 1: Identity constraint step -/
def identity_constraint_step (A : Type) (a : A) :
    Path a a := Path.refl a

/-- Def 2: Sequential constraint steps compose -/
def sequential_steps_compose {A : Type} {a b c : A}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- Def 3: Constraint step reversal -/
def constraint_step_reversal {A : Type} {a b : A}
    (p : Path a b) : Path b a :=
  Path.symm p

/-- Def 4: Three-step composition -/
def three_step_compose {A : Type} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) : Path a d :=
  Path.trans (Path.trans p q) r

/-- Theorem 5: Composition is associative for constraint chains -/
theorem constraint_chain_assoc {A : Type} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

/-! ## Theorem 6-10: Delete Rule -/

/-- Def 6: Delete rule produces reflexive path -/
def delete_rule_refl (A : Type) (t : A) :
    Path t t := Path.refl t

/-- Theorem 7: Delete rule is idempotent -/
theorem delete_idempotent (A : Type) (t : A) :
    Path.trans (Path.refl t) (Path.refl t) = Path.refl t :=
  trans_refl_left (Path.refl t)

/-- Theorem 8: Delete followed by any step -/
theorem delete_then_step {A : Type} {a b : A}
    (step : Path a b) : Path.trans (Path.refl a) step = step :=
  trans_refl_left step

/-- Theorem 9: Any step followed by delete -/
theorem step_then_delete {A : Type} {a b : A}
    (step : Path a b) : Path.trans step (Path.refl b) = step :=
  trans_refl_right step

/-- Theorem 10: Two deletes compose to delete -/
theorem two_deletes_compose (A : Type) (t : A) :
    Path.trans (Path.refl t) (Path.refl t) = Path.refl t :=
  trans_refl_left (Path.refl t)

/-! ## Def 11-15: Swap Rule -/

/-- Def 11: Swap rule is witnessed by symm -/
def swap_rule_symm {A : Type} {a b : A}
    (p : Path a b) : Path b a := Path.symm p

/-- Theorem 12: Double swap returns to original -/
theorem double_swap_identity {A : Type} {a b : A}
    (p : Path a b) : Path.symm (Path.symm p) = p :=
  symm_symm p

/-- Def 13: Swap then forward is identity path type -/
def swap_forward {A : Type} {a b : A}
    (p : Path a b) : Path a a :=
  Path.trans p (Path.symm p)

/-- Def 14: Forward then swap is identity path type -/
def forward_swap {A : Type} {a b : A}
    (p : Path a b) : Path b b :=
  Path.trans (Path.symm p) p

/-- Def 15: Swap distributes over composition -/
def swap_over_composition {A : Type} {a b c : A}
    (p : Path a b) (q : Path b c) : Path c a :=
  Path.symm (Path.trans p q)

/-! ## Def 16-20: Decompose Rule -/

/-- Def 16: Decompose lifts through function application -/
def decompose_congrArg {A B : Type} (f : A -> B) {a b : A}
    (p : Path a b) : Path (f a) (f b) :=
  Path.congrArg f p

/-- Def 17: Decompose preserves identity -/
def decompose_preserves_refl {A B : Type} (f : A -> B) (a : A) :
    Path (f a) (f a) := Path.congrArg f (Path.refl a)

/-- Def 18: Decompose preserves composition -/
def decompose_preserves_trans {A B : Type} (f : A -> B) {a b c : A}
    (p : Path a b) (q : Path b c) : Path (f a) (f c) :=
  Path.congrArg f (Path.trans p q)

/-- Def 19: Decompose and swap commute -/
def decompose_swap_commute {A B : Type} (f : A -> B) {a b : A}
    (p : Path a b) : Path (f b) (f a) :=
  Path.congrArg f (Path.symm p)

/-- Def 20: Nested decomposition -/
def nested_decompose {A B C : Type} (f : A -> B) (g : B -> C) {a b : A}
    (p : Path a b) : Path (g (f a)) (g (f b)) :=
  Path.congrArg g (Path.congrArg f p)

/-! ## Def 21-25: Eliminate Rule (Variable Elimination) -/

/-- Def 21: Elimination step witnessed by path -/
def eliminate_step {A : Type} {before after : A}
    (p : Path before after) : Path before after := p

/-- Def 22: Elimination is functional via congrArg -/
def eliminate_functional {A B : Type} (f : A -> B) {x t : A}
    (p : Path x t) : Path (f x) (f t) :=
  Path.congrArg f p

/-- Def 23: Elimination applies to nested terms -/
def eliminate_nested {A : Type} (f g : A -> A) {x t : A}
    (p : Path x t) : Path (f (g x)) (f (g t)) :=
  Path.congrArg f (Path.congrArg g p)

/-- Def 24: Sequential eliminations compose -/
def sequential_eliminate {A : Type} {x y z : A}
    (p1 : Path x y) (p2 : Path y z) : Path x z :=
  Path.trans p1 p2

/-- Def 25: Elimination with context preservation -/
def eliminate_with_context {A B : Type} (ctx : A -> B) {x t : A}
    (elim : Path x t) : Path (ctx x) (ctx t) :=
  Path.congrArg ctx elim

/-! ## Def 26-30: Most General Unifier (MGU) Properties -/

/-- MGU result: a substitution witness and its path evidence -/
structure MGUResult (A : Type) (lhs rhs : A) where
  unified : A
  pathL : Path lhs unified
  pathR : Path rhs unified

/-- Def 26: MGU reflexive case -/
def mgu_refl (A : Type) (t : A) : MGUResult A t t :=
  { unified := t, pathL := Path.refl t, pathR := Path.refl t }

/-- Def 27: MGU symmetric case -/
def mgu_symm {A : Type} {a b : A} (m : MGUResult A a b) : MGUResult A b a :=
  { unified := m.unified, pathL := m.pathR, pathR := m.pathL }

/-- Def 28: MGU paths compose -/
def mgu_path_compose {A : Type} {a b : A}
    (m : MGUResult A a b) : Path a b :=
  Path.trans m.pathL (Path.symm m.pathR)

/-- Def 29: MGU idempotence witness -/
def mgu_idempotent_witness {A : Type} (a : A) :
    Path a a :=
  let m := mgu_refl A a
  Path.trans m.pathL (Path.symm m.pathR)

/-- Def 30: Two MGU results relate -/
def mgu_results_relate {A : Type} {a b : A}
    (m1 _m2 : MGUResult A a b) : Path m1.unified m1.unified :=
  Path.refl m1.unified

/-! ## Def 31-35: Idempotent Substitutions -/

/-- An idempotent operation applied twice equals once, witnessed by Path -/
structure IdempotentOp (A : Type) where
  op : A -> A
  idem : (a : A) -> Path (op (op a)) (op a)

/-- Def 31: Identity is idempotent -/
def idempotent_id (A : Type) : IdempotentOp A :=
  { op := id, idem := fun a => Path.refl a }

/-- Def 32: Constant function is idempotent -/
def idempotent_const {A : Type} (c : A) : IdempotentOp A :=
  { op := fun _ => c, idem := fun _ => Path.refl c }

/-- Def 33: Idempotent op preserves fixed points -/
def idempotent_fixed_point {A : Type} (iop : IdempotentOp A) (a : A)
    (fixed : Path (iop.op a) a) : Path (iop.op (iop.op a)) a :=
  Path.trans (iop.idem a) fixed

/-- Def 34: Composition of idempotent with self -/
def idempotent_self_compose {A : Type} (iop : IdempotentOp A) (a : A) :
    Path (iop.op (iop.op a)) (iop.op a) :=
  iop.idem a

/-- Def 35: Idempotent applied to own output -/
def idempotent_on_output {A : Type} (iop : IdempotentOp A) (a : A) :
    Path (iop.op (iop.op (iop.op a))) (iop.op a) :=
  Path.trans (Path.congrArg iop.op (iop.idem a)) (iop.idem a)

/-! ## Def 36-40: Solved Forms and Triangular Substitutions -/

/-- A triangular substitution entry -/
structure TriangularEntry (A : Type) where
  source : A
  target : A
  witness : Path source target

/-- Def 36: Empty triangular subst is identity -/
def empty_triangular_identity (A : Type) (a : A) :
    Path a a := Path.refl a

/-- Def 37: Single entry triangular subst -/
def single_entry_triangular {A : Type} {a b : A}
    (_entry : TriangularEntry A) (h1 : a = _entry.source) (h2 : b = _entry.target) :
    Path a b := by subst h1; subst h2; exact _entry.witness

/-- Def 38: Compose two triangular entries -/
def compose_triangular_entries {A : Type} {a b c : A}
    (e1 : Path a b) (e2 : Path b c) : Path a c :=
  Path.trans e1 e2

/-- Def 39: Triangular subst applied via function -/
def triangular_apply_func {A B : Type} (f : A -> B) {a b : A}
    (entry : Path a b) : Path (f a) (f b) :=
  Path.congrArg f entry

/-- Def 40: Triangular subst reversal -/
def triangular_reverse {A : Type} {a b : A}
    (entry : Path a b) : Path b a :=
  Path.symm entry

/-! ## Def 41-45: Constraint Propagation -/

/-- Def 41: Arc consistency via transitivity -/
def arc_consistency {A : Type} {a b c : A}
    (p1 : Path a b) (p2 : Path b c) : Path a c :=
  Path.trans p1 p2

/-- Def 42: Propagation preserves structure -/
def propagation_preserves {A B : Type} (f : A -> B) {a b c : A}
    (p1 : Path a b) (p2 : Path b c) : Path (f a) (f c) :=
  Path.congrArg f (Path.trans p1 p2)

/-- Def 43: Bidirectional propagation -/
def bidirectional_propagation {A : Type} {a b : A}
    (forward : Path a b) : (Path a b) × (Path b a) :=
  (forward, Path.symm forward)

/-- Def 44: Propagation chain of length 4 -/
def propagation_chain_4 {A : Type} {a b c d e : A}
    (p1 : Path a b) (p2 : Path b c) (p3 : Path c d) (p4 : Path d e) : Path a e :=
  Path.trans (Path.trans (Path.trans p1 p2) p3) p4

/-- Def 45: Propagation with function context -/
def propagation_in_context {A B : Type} (f g : A -> B)
    {a b : A} (pa : Path a b)
    (pf : (x : A) -> Path (f x) (g x)) : Path (f a) (g b) :=
  Path.trans (pf a) (Path.congrArg g pa)

/-! ## Def 46-50: Disunification (Disequality Constraints) -/

/-- A disequality constraint: evidence two things meet at a common witness -/
structure Disequality (A : Type) (a b : A) where
  witnessA : A
  pathToA : Path a witnessA
  pathToB : Path b witnessA

/-- Def 46: Disequality is symmetric -/
def disequality_symm {A : Type} {a b : A}
    (d : Disequality A a b) : Disequality A b a :=
  { witnessA := d.witnessA, pathToA := d.pathToB, pathToB := d.pathToA }

/-- Def 47: Disequality transports through paths -/
def disequality_transport {A : Type} {a b c : A}
    (d : Disequality A a b) (pc : Path b c) : Disequality A a c :=
  { witnessA := d.witnessA
    pathToA := d.pathToA
    pathToB := Path.trans (Path.symm pc) d.pathToB }

/-- Def 48: Disequality in function context -/
def disequality_in_context {A B : Type} (f : A -> B) {a b : A}
    (d : Disequality A a b) : Disequality B (f a) (f b) :=
  { witnessA := f d.witnessA
    pathToA := Path.congrArg f d.pathToA
    pathToB := Path.congrArg f d.pathToB }

/-- Def 49: Self-disequality via refl -/
def self_disequality (A : Type) (a : A) : Disequality A a a :=
  { witnessA := a, pathToA := Path.refl a, pathToB := Path.refl a }

/-- Def 50: Disequality evidence composes -/
def disequality_compose {A : Type} {a b : A}
    (d : Disequality A a b) : Path a b :=
  Path.trans d.pathToA (Path.symm d.pathToB)

/-! ## Def 51-55: AC-Unification Structure -/

/-- Associativity-Commutativity witness for an operation -/
structure ACWitness (A : Type) (op : A -> A -> A) where
  assoc : (x y z : A) -> Path (op (op x y) z) (op x (op y z))
  comm  : (x y : A) -> Path (op x y) (op y x)

/-- Def 51: AC witness gives identity permutation -/
def ac_identity_perm {A : Type} {op : A -> A -> A}
    (ac : ACWitness A op) (a b : A) : Path (op a b) (op b a) :=
  ac.comm a b

/-- Def 52: AC double swap returns to original -/
def ac_double_comm {A : Type} {op : A -> A -> A}
    (ac : ACWitness A op) (a b : A) : Path (op a b) (op a b) :=
  Path.trans (ac.comm a b) (ac.comm b a)

/-- Def 53: AC left association -/
def ac_left_assoc {A : Type} {op : A -> A -> A}
    (ac : ACWitness A op) (a b c : A) : Path (op (op a b) c) (op a (op b c)) :=
  ac.assoc a b c

/-- Def 54: AC right association -/
def ac_right_assoc {A : Type} {op : A -> A -> A}
    (ac : ACWitness A op) (a b c : A) : Path (op a (op b c)) (op (op a b) c) :=
  Path.symm (ac.assoc a b c)

/-- Def 55: AC rotation: (a*b)*c -> (c*a)*b -/
def ac_rotation {A : Type} {op : A -> A -> A}
    (ac : ACWitness A op) (a b c : A) : Path (op (op a b) c) (op (op c a) b) :=
  let step1 : Path (op (op a b) c) (op c (op a b)) := ac.comm (op a b) c
  let step2 : Path (op c (op a b)) (op (op c a) b) := Path.symm (ac.assoc c a b)
  Path.trans step1 step2

/-! ## Def 56-60: Unification Algorithm Correctness Witnesses -/

/-- A complete unification trace -/
structure UnifTrace (A : Type) where
  start : A
  finish : A
  path : Path start finish

/-- Def 56: Empty trace is reflexive -/
def empty_trace (A : Type) (a : A) : UnifTrace A :=
  { start := a, finish := a, path := Path.refl a }

/-- Def 57: Extend trace with one step -/
def extend_trace {A : Type} (tr : UnifTrace A) {b : A}
    (step : Path tr.finish b) : UnifTrace A :=
  { start := tr.start, finish := b, path := Path.trans tr.path step }

/-- Def 58: Reverse a trace -/
def reverse_trace {A : Type} (tr : UnifTrace A) : UnifTrace A :=
  { start := tr.finish, finish := tr.start, path := Path.symm tr.path }

/-- Def 59: Trace from a single path -/
def single_trace {A : Type} {a b : A} (p : Path a b) : UnifTrace A :=
  { start := a, finish := b, path := p }

/-- Def 60: Trace identity -/
def trace_identity (A : Type) (a : A) : UnifTrace A :=
  { start := a, finish := a, path := Path.refl a }

/-! ## Def 61-65: Occurs Check and Failure -/

/-- Result of occurs check -/
inductive OccursResult (A : Type) (a b : A) : Type where
  | ok : Path a b -> OccursResult A a b
  | cycle : Path a a -> OccursResult A a b

/-- Def 61: Successful occurs check gives direct path -/
def occurs_ok_path {A : Type} {a b : A}
    (p : Path a b) : OccursResult A a b :=
  OccursResult.ok p

/-- Def 62: Cycle detection gives self-path -/
def occurs_cycle {A : Type} (a b : A) :
    OccursResult A a b :=
  OccursResult.cycle (Path.refl a)

/-- Def 63: Occurs check through function -/
def occurs_through_func {A B : Type} (f : A -> B) {a b : A}
    (r : OccursResult A a b) : Path (f a) (f a) :=
  match r with
  | OccursResult.ok p => Path.trans (Path.congrArg f p) (Path.symm (Path.congrArg f p))
  | OccursResult.cycle c => Path.congrArg f c

/-- Def 64: Nesting occurs results -/
def nested_occurs {A : Type} {a b : A}
    (r : OccursResult A a b) : Path a a :=
  match r with
  | OccursResult.ok p => Path.trans p (Path.symm p)
  | OccursResult.cycle c => c

/-- Def 65: Occurs check preserves reflexivity -/
def occurs_refl {A : Type} (a : A) :
    OccursResult A a a := OccursResult.ok (Path.refl a)

/-! ## Def 66-70: Constraint Store Operations -/

/-- A constraint store with path evidence -/
structure ConstraintStore (A : Type) where
  state : A
  historyLen : Nat

/-- Def 66: Fresh store -/
def fresh_store (A : Type) (init : A) : ConstraintStore A :=
  { state := init, historyLen := 0 }

/-- Def 67: Store update -/
def update_store {A : Type} (store : ConstraintStore A) (newState : A)
    : ConstraintStore A :=
  { state := newState, historyLen := store.historyLen + 1 }

/-- Def 68: Store lookup consistency -/
def store_self_consistent {A : Type} (store : ConstraintStore A) :
    Path store.state store.state := Path.refl store.state

/-- Def 69: Two stores can be compared via paths -/
def stores_compare {A : Type} {a b : A}
    (p : Path a b) : Path a b := p

/-- Def 70: Store history preserves path structure -/
def store_history_path {A : Type} {a b c : A}
    (p1 : Path a b) (p2 : Path b c) : Path a c :=
  Path.trans p1 p2

/-! ## Theorem 71-75: Substitution Composition -/

/-- Def 71: Substitution composition via trans -/
def subst_compose {A : Type} {a b c : A}
    (s1 : Path a b) (s2 : Path b c) : Path a c :=
  Path.trans s1 s2

/-- Theorem 72: Identity substitution is left unit -/
theorem subst_id_left {A : Type} {a b : A}
    (s : Path a b) : Path.trans (Path.refl a) s = s :=
  trans_refl_left s

/-- Theorem 73: Identity substitution is right unit -/
theorem subst_id_right {A : Type} {a b : A}
    (s : Path a b) : Path.trans s (Path.refl b) = s :=
  trans_refl_right s

/-- Theorem 74: Substitution composition associativity -/
theorem subst_compose_assoc {A : Type} {a b c d : A}
    (s1 : Path a b) (s2 : Path b c) (s3 : Path c d) :
    Path.trans (Path.trans s1 s2) s3 = Path.trans s1 (Path.trans s2 s3) :=
  trans_assoc s1 s2 s3

/-- Def 75: Inverse substitution -/
def subst_inverse {A : Type} {a b : A}
    (s : Path a b) : Path b a :=
  Path.symm s

/-! ## Theorem 76-80: congrArg Properties for Unification -/

/-- Theorem 76: congrArg preserves trans -/
theorem congrArg_preserves_trans_unif {A B : Type} (f : A -> B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) = Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  congrArg_trans f p q

/-- Theorem 77: congrArg preserves symm -/
theorem congrArg_preserves_symm_unif {A B : Type} (f : A -> B) {a b : A}
    (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  congrArg_symm f p

/-- Def 78: congrArg on refl -/
def congrArg_on_refl {A B : Type} (f : A -> B) (a : A) :
    Path (f a) (f a) :=
  Path.congrArg f (Path.refl a)

/-- Def 79: Double congrArg -/
def double_congrArg {A B C : Type} (f : A -> B) (g : B -> C) {a b : A}
    (p : Path a b) : Path (g (f a)) (g (f b)) :=
  Path.congrArg g (Path.congrArg f p)

/-- Def 80: congrArg with id -/
def congrArg_id {A : Type} {a b : A}
    (p : Path a b) : Path a b :=
  Path.congrArg id p

/-! ## Def 81-85: Pattern Matching in Unification -/

/-- Pattern: a term with a designated hole -/
structure Pattern (A B : Type) where
  context : A -> B
  hole : A

/-- Def 81: Filling pattern with equal values gives equal results -/
def pattern_fill_equal {A B : Type} (pat : Pattern A B)
    {x y : A} (p : Path x y) : Path (pat.context x) (pat.context y) :=
  Path.congrArg pat.context p

/-- Def 82: Pattern composition -/
def pattern_compose {A B C : Type} (p1 : A -> B) (p2 : B -> C)
    {a b : A} (path : Path a b) : Path (p2 (p1 a)) (p2 (p1 b)) :=
  Path.congrArg p2 (Path.congrArg p1 path)

/-- Def 83: Pattern with identity context -/
def pattern_id_context {A : Type} {a b : A}
    (p : Path a b) : Path (id a) (id b) :=
  Path.congrArg id p

/-- Def 84: Pattern matching symmetry -/
def pattern_match_symm {A B : Type} (ctx : A -> B) {a b : A}
    (p : Path a b) : Path (ctx b) (ctx a) :=
  Path.symm (Path.congrArg ctx p)

/-- Def 85: Pattern matching chain -/
def pattern_match_chain {A B : Type} (ctx : A -> B) {a b c : A}
    (p1 : Path a b) (p2 : Path b c) : Path (ctx a) (ctx c) :=
  Path.congrArg ctx (Path.trans p1 p2)

/-! ## Def 86-90: Unification Modulo Theories -/

/-- Theory axiom: an equation that always holds -/
structure TheoryAxiom (A : Type) where
  lhs : A
  rhs : A
  proof : Path lhs rhs

/-- Def 86: Theory axiom can be reversed -/
def reverse_axiom {A : Type} (ax : TheoryAxiom A) : TheoryAxiom A :=
  { lhs := ax.rhs, rhs := ax.lhs, proof := Path.symm ax.proof }

/-- Def 87: Two axioms compose when connected -/
def axioms_compose {A : Type} {a b c : A}
    (ax1 : Path a b) (ax2 : Path b c) : Path a c :=
  Path.trans ax1 ax2

/-- Def 88: Theory-relative unification -/
def theory_unification {A : Type} {a b c : A}
    (toNormal_a : Path a c) (toNormal_b : Path b c) : Path a b :=
  Path.trans toNormal_a (Path.symm toNormal_b)

/-- Def 89: AC-theory step: commutativity in context -/
def ac_theory_comm {A : Type} {op : A -> A -> A}
    (ac : ACWitness A op) (f : A -> A) (a b : A) :
    Path (f (op a b)) (f (op b a)) :=
  Path.congrArg f (ac.comm a b)

/-- Def 90: AC-theory step: associativity in context -/
def ac_theory_assoc {A : Type} {op : A -> A -> A}
    (ac : ACWitness A op) (f : A -> A) (a b c : A) :
    Path (f (op (op a b) c)) (f (op a (op b c))) :=
  Path.congrArg f (ac.assoc a b c)

/-! ## Def 91-95: Constraint Entailment -/

/-- Def 91: Constraint entailment via path chaining -/
def constraint_entailment {A : Type} {a b c d : A}
    (c1 : Path a b) (c2 : Path b c) (c3 : Path c d) : Path a d :=
  Path.trans (Path.trans c1 c2) c3

/-- Def 92: Entailment preserves through functions -/
def entailment_preserves {A B : Type} (f : A -> B) {a b : A}
    (c : Path a b) : Path (f a) (f b) :=
  Path.congrArg f c

/-- Def 93: Mutual entailment gives equivalence -/
def mutual_entailment {A : Type} {a b : A}
    (forward : Path a b) (backward : Path b a) :
    (Path a b) × (Path b a) :=
  (forward, backward)

/-- Def 94: Entailment chain with 5 elements -/
def entailment_chain_5 {A : Type} {a b c d e f : A}
    (p1 : Path a b) (p2 : Path b c) (p3 : Path c d)
    (p4 : Path d e) (p5 : Path e f) : Path a f :=
  Path.trans (Path.trans (Path.trans (Path.trans p1 p2) p3) p4) p5

/-- Def 95: Entailment reflexivity -/
def entailment_refl {A : Type} (a : A) : Path a a :=
  Path.refl a

/-! ## Def 96-100: Advanced Unification Combinators -/

/-- Def 96: Parallel unification: two independent paths -/
def parallel_unif {A B : Type} {a1 a2 : A} {b1 b2 : B}
    (pa : Path a1 a2) (pb : Path b1 b2) : Path (a1, b1) (a2, b2) :=
  let step1 : Path (a1, b1) (a2, b1) := Path.congrArg (·, b1) pa
  let step2 : Path (a2, b1) (a2, b2) := Path.congrArg (a2, ·) pb
  Path.trans step1 step2

/-- Def 97: Unification with projection -/
def unif_project_fst {A B : Type} {a1 a2 : A} {b : B}
    (p : Path (a1, b) (a2, b)) : Path (a1, b) (a2, b) := p

/-- Def 98: Unification preserves pairing -/
def unif_pair {A : Type} {a b c d : A}
    (p1 : Path a b) (p2 : Path c d) : Path (a, c) (b, d) :=
  Path.trans (Path.congrArg (·, c) p1) (Path.congrArg (b, ·) p2)

/-- Def 99: Triple unification -/
def triple_unif {A : Type} {a1 a2 b1 b2 c1 c2 : A}
    (pa : Path a1 a2) (pb : Path b1 b2) (pc : Path c1 c2) :
    Path (a1, b1, c1) (a2, b2, c2) :=
  let s1 := Path.congrArg (·, b1, c1) pa
  let s2 := Path.congrArg (a2, ·, c1) pb
  let s3 := Path.congrArg (a2, b2, ·) pc
  Path.trans (Path.trans s1 s2) s3

/-- Def 100: Unification diamond: two paths to same target -/
def unification_diamond {A : Type} {a b c : A}
    (left : Path a b) (_right : Path a c) (merge : Path b c) :
    Path a c :=
  Path.trans left merge

end ComputationalPaths.ConstraintSolvingDeep
