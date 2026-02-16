/-
  ComputationalPaths/Path/Rewriting/TerminationOrderDeep.lean

  Termination Orders and Well-Founded Rewriting via Computational Paths

  Topics: well-founded orders, LPO, RPO, KBO, multiset ordering,
  polynomial interpretations, embedding orders, reduction orderings,
  all expressed through Path equalities and operations.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.TerminationOrderDeep

open ComputationalPaths
open ComputationalPaths.Path

-- ============================================================================
-- Section 1: Basic Order Structures
-- ============================================================================

/-- A strict order relation -/
structure StrictOrder (A : Type) where
  rel : A → A → Prop
  irrefl : ∀ a, ¬ rel a a
  transitive : ∀ a b c, rel a b → rel b c → rel a c

/-- A preorder -/
structure PreOrder' (A : Type) where
  le : A → A → Prop
  refl_le : ∀ a, le a a
  trans_le : ∀ a b c, le a b → le b c → le a c

/-- Well-founded accessibility predicate -/
inductive Acc' {A : Type} (r : A → A → Prop) : A → Prop where
  | intro : ∀ x, (∀ y, r y x → Acc' r y) → Acc' r x

/-- A relation is well-founded if every element is accessible -/
def WellFounded' {A : Type} (r : A → A → Prop) : Prop :=
  ∀ a, Acc' r a

/-- Reduction ordering: well-founded, closed under contexts -/
structure ReductionOrdering (A : Type) extends StrictOrder A where
  wf : WellFounded' rel
  closed_context : ∀ (f : A → A) (a b : A), rel a b → rel (f a) (f b)

-- ============================================================================
-- Section 2: Path-Witnessed Order Properties
-- ============================================================================

/-- Theorem 1: Associativity of path composition -/
theorem path_trans_assoc_order {A : Type} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

/-- Theorem 2: Left identity for path composition -/
theorem path_order_left_unit {A : Type} {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  trans_refl_left p

/-- Theorem 3: Right identity for path composition -/
theorem path_order_right_unit {A : Type} {a b : A} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  trans_refl_right p

/-- Theorem 4: Symmetry involution -/
theorem path_order_symm_involution {A : Type} {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  symm_symm p

/-- Theorem 5: Symmetry distributes over trans -/
theorem path_order_symm_trans {A : Type} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

-- ============================================================================
-- Section 3: LPO Structures
-- ============================================================================

/-- Function symbol with arity and precedence -/
structure FunSym where
  name : Nat
  arity : Nat
  precedence : Nat

def precGt (f g : FunSym) : Prop := f.precedence > g.precedence
def precEq (f g : FunSym) : Prop := f.precedence = g.precedence

/-- Theorem 6: Precedence ordering is transitive -/
theorem prec_trans (f g h : FunSym)
    (pfg : f.precedence > g.precedence)
    (pgh : g.precedence > h.precedence) :
    f.precedence > h.precedence :=
  Nat.lt_trans pgh pfg

/-- Theorem 7: Precedence equality is reflexive -/
theorem precEq_refl (f : FunSym) : precEq f f := rfl

/-- Theorem 8: Precedence equality is symmetric -/
theorem precEq_symm' {f g : FunSym} (h : precEq f g) : precEq g f := h.symm

/-- Theorem 9: Precedence equality is transitive -/
theorem precEq_trans' {f g h : FunSym} (p : precEq f g) (q : precEq g h) : precEq f h :=
  p.trans q

-- ============================================================================
-- Section 4: Well-Founded Induction
-- ============================================================================

/-- Theorem 10: Accessibility implies induction -/
theorem acc_ind {A : Type} {r : A → A → Prop} {P : A → Prop}
    (step : ∀ x, (∀ y, r y x → P y) → P x)
    (a : A) (ha : Acc' r a) : P a := by
  induction ha with
  | intro x _ ih => exact step x (fun y hy => ih y hy)

/-- Theorem 11: Accessibility is downward closed -/
theorem acc_downward {A : Type} {r : A → A → Prop} {a b : A}
    (ha : Acc' r a) (rab : r b a) : Acc' r b := by
  cases ha with
  | intro x hx => exact hx b rab

/-- No infinite descending chain: ¬∃f, ∀n, r(f(n+1))(f n) -/
def NoInfiniteChain {A : Type} (r : A → A → Prop) : Prop :=
  ¬ ∃ (f : Nat → A), ∀ n, r (f (n + 1)) (f n)

/-- Theorem 12: Well-foundedness implies no infinite chains -/
theorem wf_no_infinite_chain {A : Type} {r : A → A → Prop}
    (hwf : WellFounded' r) : NoInfiniteChain r := by
  intro ⟨f, hf⟩
  have go : ∀ a, Acc' r a → ∀ n, f n = a → False := by
    intro a hacc
    induction hacc with
    | intro x _ ih =>
      intro n heq
      exact ih (f (n + 1)) (heq ▸ hf n) (n + 1) rfl
  exact go (f 0) (hwf (f 0)) 0 rfl

-- ============================================================================
-- Section 5: Knuth-Bendix Ordering (KBO)
-- ============================================================================

/-- Weight function for KBO -/
structure WeightFun where
  w0 : Nat
  varWeight : Nat
  funWeight : FunSym → Nat
  w0_pos : w0 > 0
  var_ge_w0 : varWeight ≥ w0

/-- KBO comparison: weight then precedence -/
def kboGtSimple (w1 w2 : Nat) (prec1 prec2 : Nat) : Prop :=
  w1 > w2 ∨ (w1 = w2 ∧ prec1 > prec2)

/-- Theorem 13: KBO is irreflexive -/
theorem kbo_irrefl (w p : Nat) : ¬ kboGtSimple w w p p := by
  intro h; unfold kboGtSimple at h; omega

/-- Theorem 14: KBO is transitive -/
theorem kbo_trans {w1 w2 w3 p1 p2 p3 : Nat}
    (h12 : kboGtSimple w1 w2 p1 p2)
    (h23 : kboGtSimple w2 w3 p2 p3) :
    kboGtSimple w1 w3 p1 p3 := by
  unfold kboGtSimple at *; omega

/-- Theorem 15: Larger weight always wins in KBO -/
theorem kbo_weight_wins (w1 w2 p1 p2 : Nat)
    (hw : w1 > w2) : kboGtSimple w1 w2 p1 p2 := by
  left; exact hw

-- ============================================================================
-- Section 6: Multiset Ordering
-- ============================================================================

/-- Multiset ordering step: replace one element with smaller ones -/
inductive MultisetGt : List Nat → List Nat → Prop where
  | step : ∀ (pre suf : List Nat) (a : Nat) (repls : List Nat),
      (∀ x, x ∈ repls → x < a) →
      MultisetGt (pre ++ [a] ++ suf) (pre ++ repls ++ suf)

/-- Theorem 16: Source of multiset ordering step is nonempty -/
theorem multiset_gt_nonempty (m n : List Nat) (h : MultisetGt m n) : m ≠ [] := by
  cases h with
  | step pre suf a _ _ => simp

-- ============================================================================
-- Section 7: Polynomial Interpretations
-- ============================================================================

/-- A simple polynomial interpretation -/
structure SimplePolyInterp where
  interp : Nat → Nat
  mono : ∀ x y, x > y → interp x > interp y

/-- Theorem 17: Composition of monotone interpretations is monotone -/
theorem poly_compose_monotone (p1 p2 : SimplePolyInterp)
    (x y : Nat) (hxy : x > y) :
    p1.interp (p2.interp x) > p1.interp (p2.interp y) :=
  p1.mono _ _ (p2.mono x y hxy)

-- ============================================================================
-- Section 8: Tree-Based Subterm Relations
-- ============================================================================

/-- Simple binary tree -/
inductive Tree where
  | leaf : Nat → Tree
  | node : Nat → Tree → Tree → Tree

/-- Subterm relation for trees -/
inductive TreeSubterm : Tree → Tree → Prop where
  | left : ∀ n l r, TreeSubterm l (Tree.node n l r)
  | right : ∀ n l r, TreeSubterm r (Tree.node n l r)
  | trans_left : ∀ s n l r, TreeSubterm s l → TreeSubterm s (Tree.node n l r)
  | trans_right : ∀ s n l r, TreeSubterm s r → TreeSubterm s (Tree.node n l r)

/-- Theorem 18: Leaf is never a superterm -/
theorem leaf_no_superterm (n : Nat) (t : Tree) : ¬ TreeSubterm t (Tree.leaf n) := by
  intro h; cases h

/-- Theorem 19: Subterm is transitive -/
theorem tree_subterm_trans (s t u : Tree)
    (h1 : TreeSubterm s t) (h2 : TreeSubterm t u) : TreeSubterm s u := by
  induction h2 with
  | left n l r => exact TreeSubterm.trans_left s n l r h1
  | right n l r => exact TreeSubterm.trans_right s n l r h1
  | trans_left _ n l r _ ih => exact TreeSubterm.trans_left s n l r (ih h1)
  | trans_right _ n l r _ ih => exact TreeSubterm.trans_right s n l r (ih h1)

-- ============================================================================
-- Section 9: Homeomorphic Embedding
-- ============================================================================

/-- Homeomorphic embedding on trees -/
inductive TreeEmbed : Tree → Tree → Prop where
  | leaf : ∀ n, TreeEmbed (Tree.leaf n) (Tree.leaf n)
  | dive_left : ∀ s n l r, TreeEmbed s l → TreeEmbed s (Tree.node n l r)
  | dive_right : ∀ s n l r, TreeEmbed s r → TreeEmbed s (Tree.node n l r)
  | couple : ∀ n l1 r1 l2 r2, TreeEmbed l1 l2 → TreeEmbed r1 r2 →
      TreeEmbed (Tree.node n l1 r1) (Tree.node n l2 r2)

/-- Theorem 20: Embedding is reflexive -/
theorem tree_embed_refl : ∀ t, TreeEmbed t t := by
  intro t
  induction t with
  | leaf n => exact TreeEmbed.leaf n
  | node n l r ihl ihr => exact TreeEmbed.couple n l r l r ihl ihr

/-- Theorem 21: Subterm implies embedding -/
theorem subterm_implies_embed (s t : Tree) (h : TreeSubterm s t) :
    TreeEmbed s t := by
  induction h with
  | left n l r => exact TreeEmbed.dive_left l n l r (tree_embed_refl l)
  | right n l r => exact TreeEmbed.dive_right r n l r (tree_embed_refl r)
  | trans_left _ n l r _ ih => exact TreeEmbed.dive_left _ n l r ih
  | trans_right _ n l r _ ih => exact TreeEmbed.dive_right _ n l r ih

-- ============================================================================
-- Section 10: Rewrite Sequences as Paths
-- ============================================================================

/-- A rewrite step witnessed by a path -/
structure RewriteStep (A : Type) where
  lhs : A
  rhs : A
  witness : Path lhs rhs

/-- A finite rewrite sequence -/
structure RewriteSeq (A : Type) where
  start : A
  finish : A
  witness : Path start finish

/-- Compose two rewrite sequences -/
def RewriteSeq.compose {A : Type} (s1 : RewriteSeq A) (s2 : RewriteSeq A)
    (h : s1.finish = s2.start) : RewriteSeq A :=
  { start := s1.start, finish := s2.finish,
    witness := Path.trans s1.witness (h ▸ s2.witness) }

/-- Identity rewrite sequence -/
def RewriteSeq.identity {A : Type} (a : A) : RewriteSeq A :=
  { start := a, finish := a, witness := Path.refl a }

/-- Theorem 22: Left identity -/
theorem rewrite_id_left {A : Type} {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  trans_refl_left p

/-- Theorem 23: Right identity -/
theorem rewrite_id_right {A : Type} {a b : A} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  trans_refl_right p

/-- Theorem 24: Associativity for rewrite chains -/
theorem rewrite_chain_assoc {A : Type} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

-- ============================================================================
-- Section 11: Context Closure Properties
-- ============================================================================

/-- Theorem 25: Context closure via congrArg -/
def context_closure_path {A B : Type} (f : A → B)
    {a b : A} (p : Path a b) : Path (f a) (f b) :=
  Path.congrArg f p

/-- Theorem 26: Context closure preserves composition -/
theorem context_closure_trans {A B : Type} (f : A → B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  congrArg_trans f p q

/-- Theorem 27: Context closure preserves inversion -/
theorem context_closure_symm {A B : Type} (f : A → B)
    {a b : A} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  congrArg_symm f p

/-- Theorem 28: Context applied to refl is refl -/
theorem context_refl {A B : Type} (f : A → B) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp [Path.congrArg, Path.refl]

-- ============================================================================
-- Section 12: Measure Functions
-- ============================================================================

/-- A measure function -/
structure MeasureFun (A : Type) where
  measure : A → Nat

/-- Measure-based termination: r a b (a below b) implies measure b > measure a -/
def MeasureTerminating {A : Type} (mf : MeasureFun A) (r : A → A → Prop) : Prop :=
  ∀ a b, r a b → mf.measure b > mf.measure a

/-- Theorem 29: Measure termination implies no infinite chains -/
theorem measure_no_chain {A : Type} (mf : MeasureFun A) (r : A → A → Prop)
    (hmt : MeasureTerminating mf r) : NoInfiniteChain r := by
  intro ⟨f, hf⟩
  -- hf n : r (f (n+1)) (f n), so measure (f n) > measure (f (n+1))
  have hmono : ∀ n, mf.measure (f n) > mf.measure (f (n + 1)) :=
    fun n => hmt _ _ (hf n)
  have descent : ∀ n, mf.measure (f 0) ≥ n + mf.measure (f n) := by
    intro n
    induction n with
    | zero => omega
    | succ k ih => have := hmono k; omega
  have := descent (mf.measure (f 0) + 1)
  omega

-- ============================================================================
-- Section 13: Lexicographic Ordering
-- ============================================================================

/-- Lexicographic ordering on pairs -/
inductive LexOrder {A B : Type} (ra : A → A → Prop) (rb : B → B → Prop)
    : A × B → A × B → Prop where
  | fst : ∀ a1 a2 b1 b2, ra a1 a2 → LexOrder ra rb (a1, b1) (a2, b2)
  | snd : ∀ a b1 b2, rb b1 b2 → LexOrder ra rb (a, b1) (a, b2)

/-- Theorem 30: Lex ordering is transitive -/
theorem lex_trans {A B : Type} {ra : A → A → Prop} {rb : B → B → Prop}
    (tra : ∀ x y z, ra x y → ra y z → ra x z)
    (trb : ∀ x y z, rb x y → rb y z → rb x z)
    {p q s : A × B}
    (hpq : LexOrder ra rb p q) (hqs : LexOrder ra rb q s) :
    LexOrder ra rb p s := by
  cases hpq with
  | fst a1 a2 b1 b2 ha =>
    cases hqs with
    | fst _ a4 _ b4 ha2 => exact LexOrder.fst a1 a4 b1 b4 (tra _ _ _ ha ha2)
    | snd _ b3 b4 _ => exact LexOrder.fst a1 _ b1 b4 ha
  | snd a b1 b2 hb =>
    cases hqs with
    | fst _ a4 _ b4 ha2 => exact LexOrder.fst a a4 b1 b4 ha2
    | snd _ b3 b4 hb2 => exact LexOrder.snd a b1 b4 (trb _ _ _ hb hb2)

/-- Theorem 31: Lex ordering is irreflexive -/
theorem lex_irrefl {A B : Type} {ra : A → A → Prop} {rb : B → B → Prop}
    (ira : ∀ x, ¬ ra x x) (irb : ∀ x, ¬ rb x x)
    (p : A × B) : ¬ LexOrder ra rb p p := by
  intro h
  cases h with
  | fst a1 a2 b1 b2 ha => exact ira a1 ha
  | snd a b1 b2 hb => exact irb b1 hb

-- ============================================================================
-- Section 14: Matrix Interpretations
-- ============================================================================

/-- A 2x2 matrix for matrix interpretations -/
structure Mat2 where
  a11 : Nat
  a12 : Nat
  a21 : Nat
  a22 : Nat

/-- Matrix multiplication -/
def Mat2.mul (m n : Mat2) : Mat2 :=
  { a11 := m.a11 * n.a11 + m.a12 * n.a21
    a12 := m.a11 * n.a12 + m.a12 * n.a22
    a21 := m.a21 * n.a11 + m.a22 * n.a21
    a22 := m.a21 * n.a12 + m.a22 * n.a22 }

def Mat2.ident : Mat2 :=
  { a11 := 1, a12 := 0, a21 := 0, a22 := 1 }

/-- Theorem 32: Right multiplication by identity -/
theorem mat2_mul_id (m : Mat2) : m.mul Mat2.ident = m := by
  simp [Mat2.mul, Mat2.ident]

/-- Theorem 33: Left multiplication by identity -/
theorem mat2_id_mul (m : Mat2) : Mat2.ident.mul m = m := by
  simp [Mat2.mul, Mat2.ident]

-- ============================================================================
-- Section 15: Arctic Semiring
-- ============================================================================

/-- Arctic semiring element -/
inductive Arctic where
  | negInf : Arctic
  | fin : Nat → Arctic

def Arctic.add : Arctic → Arctic → Arctic
  | Arctic.negInf, b => b
  | a, Arctic.negInf => a
  | Arctic.fin a, Arctic.fin b => Arctic.fin (max a b)

def Arctic.mul : Arctic → Arctic → Arctic
  | Arctic.negInf, _ => Arctic.negInf
  | _, Arctic.negInf => Arctic.negInf
  | Arctic.fin a, Arctic.fin b => Arctic.fin (a + b)

/-- Theorem 34: Arctic addition is commutative -/
theorem arctic_add_comm (a b : Arctic) : Arctic.add a b = Arctic.add b a := by
  cases a <;> cases b <;> simp [Arctic.add, Nat.max_comm]

/-- Theorem 35: negInf is left absorber for mul -/
theorem arctic_mul_negInf_left (a : Arctic) : Arctic.mul Arctic.negInf a = Arctic.negInf := by
  cases a <;> simp [Arctic.mul]

/-- Theorem 36: negInf is right absorber for mul -/
theorem arctic_mul_negInf_right (a : Arctic) : Arctic.mul a Arctic.negInf = Arctic.negInf := by
  cases a <;> simp [Arctic.mul]

/-- Theorem 37: fin 0 is left identity for mul on fin -/
theorem arctic_mul_fin_zero_left (n : Nat) :
    Arctic.mul (Arctic.fin 0) (Arctic.fin n) = Arctic.fin n := by
  simp [Arctic.mul]

/-- Theorem 38: fin 0 is right identity for mul on fin -/
theorem arctic_mul_fin_zero_right (n : Nat) :
    Arctic.mul (Arctic.fin n) (Arctic.fin 0) = Arctic.fin n := by
  simp [Arctic.mul]

-- ============================================================================
-- Section 16: Reflexive-Transitive Closure
-- ============================================================================

/-- Reflexive-transitive closure -/
inductive RTClosure {A : Type} (r : A → A → Prop) : A → A → Prop where
  | refl : ∀ a, RTClosure r a a
  | step : ∀ a b c, r a b → RTClosure r b c → RTClosure r a c

/-- Theorem 39: RTClosure is transitive -/
theorem rtc_trans {A : Type} {r : A → A → Prop} {a b c : A}
    (h1 : RTClosure r a b) (h2 : RTClosure r b c) : RTClosure r a c := by
  induction h1 with
  | refl _ => exact h2
  | step x y _ hxy _ ih => exact RTClosure.step x y c hxy (ih h2)

/-- Theorem 40: Single step embeds into RTClosure -/
theorem rtc_single {A : Type} {r : A → A → Prop} {a b : A}
    (h : r a b) : RTClosure r a b :=
  RTClosure.step a b b h (RTClosure.refl b)

/-- Rewrite system -/
structure RewriteSystem (A : Type) where
  step : A → A → Prop

/-- Local confluence -/
def LocallyConfluent {A : Type} (rs : RewriteSystem A) : Prop :=
  ∀ a b c, rs.step a b → rs.step a c →
    ∃ d, RTClosure rs.step b d ∧ RTClosure rs.step c d

/-- Confluence -/
def Confluent {A : Type} (rs : RewriteSystem A) : Prop :=
  ∀ a b c, RTClosure rs.step a b → RTClosure rs.step a c →
    ∃ d, RTClosure rs.step b d ∧ RTClosure rs.step c d

/-- Terminating system -/
def SystemTerminating {A : Type} (rs : RewriteSystem A) : Prop :=
  WellFounded' (fun a b => rs.step b a)

-- ============================================================================
-- Section 17: Dependency Pairs
-- ============================================================================

structure DepPair (A : Type) where
  caller : A
  callee : A

inductive DPChain {A : Type} (dp : A → A → Prop) : List A → Prop where
  | nil : DPChain dp []
  | single : ∀ a, DPChain dp [a]
  | cons : ∀ a b rest, dp a b → DPChain dp (b :: rest) → DPChain dp (a :: b :: rest)

def DPTerminating {A : Type} (dp : A → A → Prop) : Prop :=
  ¬ ∃ (f : Nat → A), ∀ n, dp (f n) (f (n + 1))

-- ============================================================================
-- Section 18: Path Coherence for Context Closure
-- ============================================================================

/-- Theorem 41: Double context = composition -/
theorem double_context_path {A B C : Type} (f : B → C) (g : A → B)
    {a b : A} (p : Path a b) :
    Path.congrArg f (Path.congrArg g p) = Path.congrArg (fun x => f (g x)) p := by
  cases p with
  | mk steps proof =>
    cases proof
    simp [Path.congrArg]

/-- Theorem 42: Left unit for congruence paths -/
theorem congruence_left_unit {A B : Type} (f : A → B)
    {a b : A} (p : Path a b) :
    Path.trans (Path.congrArg f (Path.refl a)) (Path.congrArg f p) =
    Path.congrArg f p := by
  rw [context_refl]; exact trans_refl_left (Path.congrArg f p)

/-- Theorem 43: Right unit for congruence paths -/
theorem congruence_right_unit {A B : Type} (f : A → B)
    {a b : A} (p : Path a b) :
    Path.trans (Path.congrArg f p) (Path.congrArg f (Path.refl b)) =
    Path.congrArg f p := by
  rw [context_refl]; exact trans_refl_right (Path.congrArg f p)

/-- Theorem 44: Double symm elimination in context -/
theorem context_double_symm {A B : Type} (f : A → B)
    {a b : A} (p : Path a b) :
    Path.symm (Path.symm (Path.congrArg f p)) = Path.congrArg f p :=
  symm_symm (Path.congrArg f p)

-- ============================================================================
-- Section 19: Fourfold Path Coherence
-- ============================================================================

/-- Theorem 45: Fourfold associativity -/
theorem fourfold_assoc {A : Type} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans (Path.trans p q) r) s =
    Path.trans p (Path.trans q (Path.trans r s)) := by
  rw [trans_assoc, trans_assoc]

/-- Theorem 46: Symm distributes over triple composition -/
theorem symm_triple_distrib {A : Type} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.symm (Path.trans (Path.trans p q) r) =
    Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)) := by
  rw [symm_trans, symm_trans]

-- ============================================================================
-- Section 20: Additional Termination Theorems
-- ============================================================================

/-- Theorem 47: Termination preserved by subrelation -/
theorem termination_subrelation {A : Type} (r1 r2 : A → A → Prop)
    (hsub : ∀ a b, r1 a b → r2 a b)
    (hwf : NoInfiniteChain r2) : NoInfiniteChain r1 := by
  intro ⟨f, hf⟩
  exact hwf ⟨f, fun n => hsub _ _ (hf n)⟩

/-- Theorem 48: Nat.lt is well-founded -/
theorem nat_lt_acc : ∀ n, Acc' (fun (a : Nat) (b : Nat) => a < b) n := by
  intro n
  induction n with
  | zero => exact Acc'.intro 0 (fun y (hy : y < 0) => absurd hy (Nat.not_lt_zero y))
  | succ k ih =>
    exact Acc'.intro (k + 1) (fun y (hy : y < k + 1) => by
      by_cases h : y = k
      · exact h ▸ ih
      · have : y < k := by omega
        exact acc_downward ih this)

/-- Theorem 49: Nat.lt is well-founded -/
theorem nat_lt_wf : WellFounded' (fun (a : Nat) (b : Nat) => a < b) :=
  nat_lt_acc

-- ============================================================================
-- Section 21: Semantic Model Termination
-- ============================================================================

structure SemanticModel (A : Type) where
  carrier : Type
  interp : A → carrier
  gt : carrier → carrier → Prop
  gt_wf : WellFounded' gt

def SemanticTerminating {A : Type} (sm : SemanticModel A) (r : A → A → Prop) : Prop :=
  ∀ a b, r a b → sm.gt (sm.interp a) (sm.interp b)

/-- Theorem 50: Semantic termination implies no infinite chains -/
theorem semantic_termination_sound {A : Type} (sm : SemanticModel A) (r : A → A → Prop)
    (hst : SemanticTerminating sm r) : NoInfiniteChain r := by
  intro ⟨f, hf⟩
  exact wf_no_infinite_chain sm.gt_wf ⟨fun n => sm.interp (f n), fun n => hst _ _ (hf n)⟩

-- ============================================================================
-- Section 22: Path Transport Properties
-- ============================================================================

/-- Theorem 51: Compose transports -/
theorem path_compose_transport {A B C : Type}
    (f : A → B) (g : B → C) {a b : A}
    (p : Path a b) :
    Path.congrArg g (Path.congrArg f p) = Path.congrArg (fun x => g (f x)) p := by
  cases p with
  | mk steps proof => cases proof; simp [Path.congrArg]

/-- Theorem 52: Refl transports trivially -/
theorem refl_transport {A B : Type} (f : A → B) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp [Path.congrArg, Path.refl]

/-- Theorem 53: Symm reverses transport -/
theorem symm_transport {A B : Type} (f : A → B) {a b : A} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  congrArg_symm f p

/-- Theorem 54: Trans composes transport -/
theorem trans_transport {A B : Type} (f : A → B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  congrArg_trans f p q

-- ============================================================================
-- Section 23: Simplification Ordering Properties
-- ============================================================================

/-- A simplification ordering has the subterm property -/
structure SimplificationOrdering extends StrictOrder Tree where
  subterm_prop : ∀ s t, TreeSubterm s t → rel s t

/-- Theorem 55: Simplification orderings are irreflexive -/
theorem simpl_order_irrefl (so : SimplificationOrdering) (t : Tree) :
    ¬ so.rel t t :=
  so.irrefl t

-- ============================================================================
-- Section 24: Tree Size Properties
-- ============================================================================

/-- Tree size -/
def Tree.size : Tree → Nat
  | Tree.leaf _ => 1
  | Tree.node _ l r => 1 + l.size + r.size

/-- Theorem 56: Left subtree is smaller -/
theorem left_subtree_smaller (n : Nat) (l r : Tree) :
    l.size < (Tree.node n l r).size := by
  simp [Tree.size]; omega

/-- Theorem 57: Right subtree is smaller -/
theorem right_subtree_smaller (n : Nat) (l r : Tree) :
    r.size < (Tree.node n l r).size := by
  simp [Tree.size]; omega

/-- Theorem 58: Tree size is always positive -/
theorem tree_size_pos (t : Tree) : t.size > 0 := by
  cases t <;> simp [Tree.size] <;> omega

-- ============================================================================
-- Section 25: Final Path Groupoid Properties
-- ============================================================================

/-- Theorem 59: Symm of refl is refl -/
theorem symm_refl_eq {A : Type} (a : A) :
    Path.symm (Path.refl a) = Path.refl a := by
  simp [Path.symm, Path.refl]

/-- Theorem 60: Congruence distributes over compound composition -/
theorem congrArg_fourfold {A B : Type} (f : A → B)
    {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.congrArg f (Path.trans (Path.trans p q) r) =
    Path.trans (Path.trans (Path.congrArg f p) (Path.congrArg f q)) (Path.congrArg f r) := by
  rw [congrArg_trans, congrArg_trans]

end ComputationalPaths.TerminationOrderDeep
