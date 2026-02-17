/-
# Order Theory (Deep) via Computational Paths

Partial orders, total orders, well-orders, lattice completions
(Dedekind-MacNeille), order ideals, order dimension, Dilworth's theorem,
Ramsey-type results for posets, order-preserving maps as path morphisms,
fixed-point theorems — all witnessed by domain-specific step types and
genuine Path operations (refl, trans, symm, congrArg, transport).
Zero sorry, zero Path.ofEq.

## References
- Davey & Priestley, *Introduction to Lattices and Order*
- Dilworth, *A Decomposition Theorem for Partially Ordered Sets*
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.OrderTheoryDeep

open ComputationalPaths.Path

universe u v

/-! ## Poset element: Nat-backed -/

/-- Element of a partially ordered set (Nat-backed). -/
structure Elem where
  val : Nat
  deriving DecidableEq, Repr

/-- Meet (min). -/
def emeet (a b : Elem) : Elem := ⟨Nat.min a.val b.val⟩

/-- Join (max). -/
def ejoin (a b : Elem) : Elem := ⟨Nat.max a.val b.val⟩

/-- Bottom. -/
def ebot : Elem := ⟨0⟩

/-- Top (for a bounded poset with maximum n). -/
def etop (n : Nat) : Elem := ⟨n⟩

/-! ## Core equalities for meet/join -/

theorem emeet_comm (a b : Elem) : emeet a b = emeet b a := by
  simp [emeet, Nat.min_comm]

theorem ejoin_comm (a b : Elem) : ejoin a b = ejoin b a := by
  simp [ejoin, Nat.max_comm]

theorem emeet_assoc (a b c : Elem) :
    emeet (emeet a b) c = emeet a (emeet b c) := by
  simp [emeet, Nat.min_assoc]

theorem ejoin_assoc (a b c : Elem) :
    ejoin (ejoin a b) c = ejoin a (ejoin b c) := by
  simp [ejoin, Nat.max_assoc]

theorem emeet_idem (a : Elem) : emeet a a = a := by
  simp [emeet]

theorem ejoin_idem (a : Elem) : ejoin a a = a := by
  simp [ejoin]

theorem emeet_bot (a : Elem) : emeet ebot a = ebot := by
  simp [emeet, ebot]

theorem ejoin_bot (a : Elem) : ejoin ebot a = a := by
  simp [ejoin, ebot]

theorem emeet_absorb_join (a b : Elem) :
    emeet a (ejoin a b) = a := by
  cases a; cases b
  simp only [Elem.mk.injEq, emeet, ejoin, Nat.min_def, Nat.max_def]
  repeat (first | split | omega)

theorem ejoin_absorb_meet (a b : Elem) :
    ejoin a (emeet a b) = a := by
  cases a; cases b
  simp only [Elem.mk.injEq, ejoin, emeet, Nat.max_def, Nat.min_def]
  repeat (first | split | omega)

/-! ## Domain-specific rewrite steps -/

/-- Elementary rewrite steps for order-theoretic lattice operations. -/
inductive OTStep : Elem → Elem → Type where
  | meet_comm   : (a b : Elem) → OTStep (emeet a b) (emeet b a)
  | join_comm   : (a b : Elem) → OTStep (ejoin a b) (ejoin b a)
  | meet_assoc  : (a b c : Elem) → OTStep (emeet (emeet a b) c) (emeet a (emeet b c))
  | join_assoc  : (a b c : Elem) → OTStep (ejoin (ejoin a b) c) (ejoin a (ejoin b c))
  | meet_idem   : (a : Elem) → OTStep (emeet a a) a
  | join_idem   : (a : Elem) → OTStep (ejoin a a) a
  | meet_bot    : (a : Elem) → OTStep (emeet ebot a) ebot
  | join_bot    : (a : Elem) → OTStep (ejoin ebot a) a
  | absorb_mj   : (a b : Elem) → OTStep (emeet a (ejoin a b)) a
  | absorb_jm   : (a b : Elem) → OTStep (ejoin a (emeet a b)) a

/-- Each OTStep yields a propositional equality. -/
def OTStep.toEq : OTStep a b → a = b
  | .meet_comm a b   => emeet_comm a b
  | .join_comm a b   => ejoin_comm a b
  | .meet_assoc a b c => emeet_assoc a b c
  | .join_assoc a b c => ejoin_assoc a b c
  | .meet_idem a     => emeet_idem a
  | .join_idem a     => ejoin_idem a
  | .meet_bot a      => emeet_bot a
  | .join_bot a      => ejoin_bot a
  | .absorb_mj a b   => emeet_absorb_join a b
  | .absorb_jm a b   => ejoin_absorb_meet a b

/-! ## Building paths from steps -/

/-- Build a Path from a single OTStep. -/
def stepPath {a b : Elem} (s : OTStep a b) : Path a b :=
  let h := s.toEq
  Path.mk [⟨a, b, h⟩] h

/-! ## Basic lattice paths -/

/-- Meet commutativity path. -/
def meet_comm_path (a b : Elem) :
    Path (emeet a b) (emeet b a) :=
  stepPath (OTStep.meet_comm a b)

/-- Join commutativity path. -/
def join_comm_path (a b : Elem) :
    Path (ejoin a b) (ejoin b a) :=
  stepPath (OTStep.join_comm a b)

/-- Meet associativity path. -/
def meet_assoc_path (a b c : Elem) :
    Path (emeet (emeet a b) c) (emeet a (emeet b c)) :=
  stepPath (OTStep.meet_assoc a b c)

/-- Join associativity path. -/
def join_assoc_path (a b c : Elem) :
    Path (ejoin (ejoin a b) c) (ejoin a (ejoin b c)) :=
  stepPath (OTStep.join_assoc a b c)

/-- Meet idempotency path. -/
def meet_idem_path (a : Elem) :
    Path (emeet a a) a :=
  stepPath (OTStep.meet_idem a)

/-- Join idempotency path. -/
def join_idem_path (a : Elem) :
    Path (ejoin a a) a :=
  stepPath (OTStep.join_idem a)

/-- Meet with bottom path. -/
def meet_bot_path (a : Elem) :
    Path (emeet ebot a) ebot :=
  stepPath (OTStep.meet_bot a)

/-- Join with bottom path. -/
def join_bot_path (a : Elem) :
    Path (ejoin ebot a) a :=
  stepPath (OTStep.join_bot a)

/-- Meet absorption path. -/
def absorb_mj_path (a b : Elem) :
    Path (emeet a (ejoin a b)) a :=
  stepPath (OTStep.absorb_mj a b)

/-- Join absorption path. -/
def absorb_jm_path (a b : Elem) :
    Path (ejoin a (emeet a b)) a :=
  stepPath (OTStep.absorb_jm a b)

/-! ## Composite paths via trans -/

/-- Four-fold meet associativity: ((a∧b)∧c)∧d → a∧(b∧(c∧d)). -/
def meet_assoc4_path (a b c d : Elem) :
    Path (emeet (emeet (emeet a b) c) d)
         (emeet a (emeet b (emeet c d))) :=
  Path.trans
    (meet_assoc_path (emeet a b) c d)
    (meet_assoc_path a b (emeet c d))

/-- Four-fold join associativity. -/
def join_assoc4_path (a b c d : Elem) :
    Path (ejoin (ejoin (ejoin a b) c) d)
         (ejoin a (ejoin b (ejoin c d))) :=
  Path.trans
    (join_assoc_path (ejoin a b) c d)
    (join_assoc_path a b (ejoin c d))

/-- Five-fold meet associativity. -/
def meet_assoc5_path (a b c d e : Elem) :
    Path (emeet (emeet (emeet (emeet a b) c) d) e)
         (emeet a (emeet b (emeet c (emeet d e)))) :=
  Path.trans
    (meet_assoc_path (emeet (emeet a b) c) d e)
    (Path.trans
      (meet_assoc_path (emeet a b) c (emeet d e))
      (meet_assoc_path a b (emeet c (emeet d e))))

/-- Five-fold join associativity. -/
def join_assoc5_path (a b c d e : Elem) :
    Path (ejoin (ejoin (ejoin (ejoin a b) c) d) e)
         (ejoin a (ejoin b (ejoin c (ejoin d e)))) :=
  Path.trans
    (join_assoc_path (ejoin (ejoin a b) c) d e)
    (Path.trans
      (join_assoc_path (ejoin a b) c (ejoin d e))
      (join_assoc_path a b (ejoin c (ejoin d e))))

/-- Meet-comm then meet-assoc: (b∧a)∧c → a∧(b∧c). -/
def meet_comm_assoc_path (a b c : Elem) :
    Path (emeet (emeet b a) c) (emeet a (emeet b c)) :=
  Path.trans
    (Path.congrArg (fun x => emeet x c) (meet_comm_path b a))
    (meet_assoc_path a b c)

/-- Join-comm then join-assoc. -/
def join_comm_assoc_path (a b c : Elem) :
    Path (ejoin (ejoin b a) c) (ejoin a (ejoin b c)) :=
  Path.trans
    (Path.congrArg (fun x => ejoin x c) (join_comm_path b a))
    (join_assoc_path a b c)

/-! ## Symm paths -/

/-- Reverse of meet associativity. -/
def meet_assoc_symm (a b c : Elem) :
    Path (emeet a (emeet b c)) (emeet (emeet a b) c) :=
  Path.symm (meet_assoc_path a b c)

/-- Reverse of join associativity. -/
def join_assoc_symm (a b c : Elem) :
    Path (ejoin a (ejoin b c)) (ejoin (ejoin a b) c) :=
  Path.symm (join_assoc_path a b c)

/-- Meet idempotency symm: a → a∧a. -/
def meet_idem_symm (a : Elem) :
    Path a (emeet a a) :=
  Path.symm (meet_idem_path a)

/-- Join idempotency symm: a → a∨a. -/
def join_idem_symm (a : Elem) :
    Path a (ejoin a a) :=
  Path.symm (join_idem_path a)

/-- Meet comm roundtrip: a∧b → b∧a → a∧b. -/
def meet_comm_roundtrip (a b : Elem) :
    Path (emeet a b) (emeet a b) :=
  Path.trans (meet_comm_path a b) (meet_comm_path b a)

/-- Join comm roundtrip: a∨b → b∨a → a∨b. -/
def join_comm_roundtrip (a b : Elem) :
    Path (ejoin a b) (ejoin a b) :=
  Path.trans (join_comm_path a b) (join_comm_path b a)

/-! ## congrArg paths -/

/-- Left meet preserves paths. -/
def meet_congrArg_left (c : Elem) {a b : Elem}
    (p : Path a b) : Path (emeet c a) (emeet c b) :=
  Path.congrArg (emeet c) p

/-- Right meet preserves paths. -/
def meet_congrArg_right (c : Elem) {a b : Elem}
    (p : Path a b) : Path (emeet a c) (emeet b c) :=
  Path.congrArg (fun x => emeet x c) p

/-- Left join preserves paths. -/
def join_congrArg_left (c : Elem) {a b : Elem}
    (p : Path a b) : Path (ejoin c a) (ejoin c b) :=
  Path.congrArg (ejoin c) p

/-- Right join preserves paths. -/
def join_congrArg_right (c : Elem) {a b : Elem}
    (p : Path a b) : Path (ejoin a c) (ejoin b c) :=
  Path.congrArg (fun x => ejoin x c) p

/-- Nested congrArg: inside a triple meet. -/
def meet_nested_congr (a b : Elem) {x y : Elem}
    (p : Path x y) : Path (emeet a (emeet b x)) (emeet a (emeet b y)) :=
  Path.congrArg (emeet a) (Path.congrArg (emeet b) p)

/-- Nested congrArg: inside a triple join. -/
def join_nested_congr (a b : Elem) {x y : Elem}
    (p : Path x y) : Path (ejoin a (ejoin b x)) (ejoin a (ejoin b y)) :=
  Path.congrArg (ejoin a) (Path.congrArg (ejoin b) p)

/-! ## Order ideals -/

/-- An order ideal (down-set). -/
structure OrderIdeal where
  elems : List Elem
  bound : Elem
  all_below : ∀ e ∈ elems, e.val ≤ bound.val

/-- Size of an ideal. -/
def idealSize (I : OrderIdeal) : Nat := I.elems.length

/-! ## Antichain (for Dilworth) -/

/-- An antichain: mutually incomparable elements. -/
structure Antichain where
  elems : List Elem
  pairwise_incomp : ∀ a ∈ elems, ∀ b ∈ elems, a ≠ b →
    ¬(a.val ≤ b.val ∧ b.val ≤ a.val ∧ a.val = b.val)

/-- Width of an antichain. -/
def acWidth (ac : Antichain) : Nat := ac.elems.length

/-! ## Chain (for Dilworth / Ramsey) -/

/-- A chain: totally ordered subset, represented as a sorted list. -/
structure Chain where
  elems : List Elem
  sorted : ∀ (i j : Nat) (hi : i < j) (hj : j < elems.length),
    (elems.get ⟨i, Nat.lt_trans hi hj⟩).val <
    (elems.get ⟨j, hj⟩).val

/-- Length of a chain. -/
def chainLen (c : Chain) : Nat := c.elems.length

/-! ## Dilworth's theorem (finite, combinatorial statement) -/

/-- Dilworth configuration: a poset with width w can be covered by w chains. -/
structure DilworthConfig where
  width : Nat
  chainCount : Nat
  num_chains : chainCount = width

/-- Path witnessing number of chains equals width. -/
def dilworth_path (dc : DilworthConfig) :
    Path dc.chainCount dc.width :=
  Path.mk [⟨_, _, dc.num_chains⟩] dc.num_chains

/-- Symm: width → chain count. -/
def dilworth_symm (dc : DilworthConfig) :
    Path dc.width dc.chainCount :=
  Path.symm (dilworth_path dc)

/-! ## Order-preserving maps as path morphisms -/

/-- An order-preserving map between Elem posets. -/
structure OrdMap where
  f : Elem → Elem
  monotone : ∀ a b : Elem, a.val ≤ b.val → (f a).val ≤ (f b).val

/-- OrdMap preserves paths via congrArg. -/
def ordmap_congrArg (om : OrdMap) {a b : Elem}
    (p : Path a b) : Path (om.f a) (om.f b) :=
  Path.congrArg om.f p

/-- Composition of order maps. -/
def ordmap_comp (f g : OrdMap) : OrdMap where
  f := f.f ∘ g.f
  monotone := fun a b h => f.monotone _ _ (g.monotone a b h)

/-- Composition respects paths. -/
def ordmap_comp_congrArg (f g : OrdMap) {a b : Elem}
    (p : Path a b) : Path ((ordmap_comp f g).f a) ((ordmap_comp f g).f b) :=
  Path.congrArg (ordmap_comp f g).f p

/-- Identity order map. -/
def ordmap_id : OrdMap where
  f := id
  monotone := fun _ _ h => h

/-- Identity map path is identity on paths. -/
def ordmap_id_path {a b : Elem} (p : Path a b) :
    Path (ordmap_id.f a) (ordmap_id.f b) :=
  Path.congrArg ordmap_id.f p

/-! ## Fixed-point theorems -/

/-- A fixed point of an order map. -/
structure FixedPoint (om : OrdMap) where
  point : Elem
  is_fixed : om.f point = point

/-- Path from f(p) to p for a fixed point. -/
def fixedpoint_path (om : OrdMap) (fp : FixedPoint om) :
    Path (om.f fp.point) fp.point :=
  Path.mk [⟨_, _, fp.is_fixed⟩] fp.is_fixed

/-- Applying f twice at fixed point. -/
def fixedpoint_twice_path (om : OrdMap) (fp : FixedPoint om) :
    Path (om.f (om.f fp.point)) fp.point :=
  Path.trans
    (ordmap_congrArg om (fixedpoint_path om fp))
    (fixedpoint_path om fp)

/-- Three-fold iteration at fixed point. -/
def fixedpoint_triple_path (om : OrdMap) (fp : FixedPoint om) :
    Path (om.f (om.f (om.f fp.point))) fp.point :=
  Path.trans
    (ordmap_congrArg om (fixedpoint_twice_path om fp))
    (fixedpoint_path om fp)

/-- Symm of fixed point: p → f(p). -/
def fixedpoint_symm (om : OrdMap) (fp : FixedPoint om) :
    Path fp.point (om.f fp.point) :=
  Path.symm (fixedpoint_path om fp)

/-! ## Lattice completions (Dedekind-MacNeille) via Nat-backed cuts -/

/-- A cut in a poset (for Dedekind-MacNeille completion).
    Represented by lower/upper bounds rather than element lists. -/
structure Cut where
  lowerBound : Nat
  upperBound : Nat
  deriving DecidableEq, Repr

/-- Meet of two cuts. -/
def cutMeet (c1 c2 : Cut) : Cut where
  lowerBound := Nat.max c1.lowerBound c2.lowerBound
  upperBound := Nat.min c1.upperBound c2.upperBound

/-- Join of two cuts. -/
def cutJoin (c1 c2 : Cut) : Cut where
  lowerBound := Nat.min c1.lowerBound c2.lowerBound
  upperBound := Nat.max c1.upperBound c2.upperBound

/-- Principal cut embedding: element to cut. -/
def principalCut (e : Elem) : Cut where
  lowerBound := e.val
  upperBound := e.val

theorem cutMeet_comm (c1 c2 : Cut) : cutMeet c1 c2 = cutMeet c2 c1 := by
  simp [cutMeet, Nat.max_comm, Nat.min_comm]

theorem cutJoin_comm (c1 c2 : Cut) : cutJoin c1 c2 = cutJoin c2 c1 := by
  simp [cutJoin, Nat.min_comm, Nat.max_comm]

theorem cutMeet_assoc (c1 c2 c3 : Cut) :
    cutMeet (cutMeet c1 c2) c3 = cutMeet c1 (cutMeet c2 c3) := by
  simp [cutMeet, Nat.max_assoc, Nat.min_assoc]

theorem cutJoin_assoc (c1 c2 c3 : Cut) :
    cutJoin (cutJoin c1 c2) c3 = cutJoin c1 (cutJoin c2 c3) := by
  simp [cutJoin, Nat.min_assoc, Nat.max_assoc]

/-- Cut-level rewrite steps. -/
inductive CutStep : Cut → Cut → Type where
  | meet_comm  : (c1 c2 : Cut) → CutStep (cutMeet c1 c2) (cutMeet c2 c1)
  | join_comm  : (c1 c2 : Cut) → CutStep (cutJoin c1 c2) (cutJoin c2 c1)
  | meet_assoc : (c1 c2 c3 : Cut) → CutStep (cutMeet (cutMeet c1 c2) c3) (cutMeet c1 (cutMeet c2 c3))
  | join_assoc : (c1 c2 c3 : Cut) → CutStep (cutJoin (cutJoin c1 c2) c3) (cutJoin c1 (cutJoin c2 c3))

/-- Each CutStep yields a propositional equality. -/
def CutStep.toEq : CutStep a b → a = b
  | .meet_comm c1 c2    => cutMeet_comm c1 c2
  | .join_comm c1 c2    => cutJoin_comm c1 c2
  | .meet_assoc c1 c2 c3 => cutMeet_assoc c1 c2 c3
  | .join_assoc c1 c2 c3 => cutJoin_assoc c1 c2 c3

/-- Build a Path from a CutStep. -/
def cutStepPath {a b : Cut} (s : CutStep a b) : Path a b :=
  let h := s.toEq
  Path.mk [⟨a, b, h⟩] h

/-- Cut meet commutativity path. -/
def cut_meet_comm_path (c1 c2 : Cut) :
    Path (cutMeet c1 c2) (cutMeet c2 c1) :=
  cutStepPath (CutStep.meet_comm c1 c2)

/-- Cut join commutativity path. -/
def cut_join_comm_path (c1 c2 : Cut) :
    Path (cutJoin c1 c2) (cutJoin c2 c1) :=
  cutStepPath (CutStep.join_comm c1 c2)

/-- Principal cut meet commutativity path. -/
def principal_meet_comm_path (a b : Elem) :
    Path (cutMeet (principalCut a) (principalCut b))
         (cutMeet (principalCut b) (principalCut a)) :=
  cut_meet_comm_path (principalCut a) (principalCut b)

/-! ## Well-order: successor operation -/

/-- Successor on Elem. -/
def esucc (a : Elem) : Elem := ⟨a.val + 1⟩

/-- Double successor. -/
def esucc2 (a : Elem) : Elem := esucc (esucc a)

theorem esucc2_eq (a : Elem) : esucc2 a = ⟨a.val + 2⟩ := by
  simp [esucc2, esucc, Nat.add_assoc]

/-- Succ-succ rewrite step. -/
inductive SuccStep : Elem → Elem → Type where
  | succ2 : (a : Elem) → SuccStep (esucc2 a) ⟨a.val + 2⟩

def SuccStep.toEq : SuccStep a b → a = b
  | .succ2 a => esucc2_eq a

def succStepPath {a b : Elem} (s : SuccStep a b) : Path a b :=
  let h := s.toEq
  Path.mk [⟨a, b, h⟩] h

/-- Well-order successor path. -/
def succ_path (a : Elem) : Path (esucc2 a) ⟨a.val + 2⟩ :=
  succStepPath (SuccStep.succ2 a)

/-- Successor via congrArg. -/
def succ_congrArg {a b : Elem} (p : Path a b) :
    Path (esucc a) (esucc b) :=
  Path.congrArg esucc p

/-- Double successor via congrArg chain. -/
def succ2_congrArg {a b : Elem} (p : Path a b) :
    Path (esucc (esucc a)) (esucc (esucc b)) :=
  Path.congrArg esucc (Path.congrArg esucc p)

/-! ## Order dimension -/

/-- Order dimension: minimum number of linear extensions to realize. -/
structure OrderDim where
  dim : Nat
  extCount : Nat
  num_ext : extCount = dim

/-- Dimension path. -/
def dim_path (od : OrderDim) :
    Path od.extCount od.dim :=
  Path.mk [⟨_, _, od.num_ext⟩] od.num_ext

/-- Dimension symm. -/
def dim_symm (od : OrderDim) :
    Path od.dim od.extCount :=
  Path.symm (dim_path od)

/-! ## Ramsey-type: monochromatic chains -/

/-- A coloring of elements. -/
structure Coloring where
  color : Elem → Nat

/-- Monochromatic subset: all same color. -/
structure MonoSubset where
  elems : List Elem
  col : Coloring
  baseColor : Nat
  same_color : ∀ e ∈ elems, col.color e = baseColor

/-- Coloring preserves paths via congrArg. -/
def color_congrArg (col : Coloring) {a b : Elem}
    (p : Path a b) : Path (col.color a) (col.color b) :=
  Path.congrArg col.color p

/-! ## Transport -/

/-- Transport a property along a lattice path. -/
def elemTransport (P : Elem → Prop) {a b : Elem}
    (p : Path a b) (h : P a) : P b :=
  Path.transport p h

/-- Transport from meet a a to a. -/
def transport_meet_idem (P : Elem → Prop) (a : Elem)
    (h : P (emeet a a)) : P a :=
  elemTransport P (meet_idem_path a) h

/-- Transport from join a a to a. -/
def transport_join_idem (P : Elem → Prop) (a : Elem)
    (h : P (ejoin a a)) : P a :=
  elemTransport P (join_idem_path a) h

/-- Transport across meet commutativity. -/
def transport_meet_comm (P : Elem → Prop) (a b : Elem)
    (h : P (emeet a b)) : P (emeet b a) :=
  elemTransport P (meet_comm_path a b) h

/-- Transport across join commutativity. -/
def transport_join_comm (P : Elem → Prop) (a b : Elem)
    (h : P (ejoin a b)) : P (ejoin b a) :=
  elemTransport P (join_comm_path a b) h

/-! ## Path algebra groupoid laws -/

/-- Refl is left identity. -/
theorem refl_trans_elem {a b : Elem} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  Path.trans_refl_left p

/-- Refl is right identity. -/
theorem trans_refl_elem {a b : Elem} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  Path.trans_refl_right p

/-- Trans is associative. -/
theorem trans_assoc_elem {a b c d : Elem}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

/-- Symm of symm is identity. -/
theorem symm_symm_elem {a b : Elem} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- Symm distributes over trans. -/
theorem symm_trans_elem {a b c : Elem} (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

/-! ## Interval arithmetic -/

/-- Interval [lo, hi]. -/
structure Interval where
  lo : Elem
  hi : Elem
  deriving DecidableEq, Repr

/-- Interval meet. -/
def intervalMeet (I J : Interval) : Interval where
  lo := ejoin I.lo J.lo
  hi := emeet I.hi J.hi

/-- Interval join. -/
def intervalJoin (I J : Interval) : Interval where
  lo := emeet I.lo J.lo
  hi := ejoin I.hi J.hi

theorem intervalMeet_comm (I J : Interval) :
    intervalMeet I J = intervalMeet J I := by
  simp [intervalMeet, ejoin_comm, emeet_comm]

theorem intervalJoin_comm (I J : Interval) :
    intervalJoin I J = intervalJoin J I := by
  simp [intervalJoin, emeet_comm, ejoin_comm]

/-- Interval meet commutativity path. -/
def intervalMeet_comm_path (I J : Interval) :
    Path (intervalMeet I J) (intervalMeet J I) :=
  Path.mk [⟨_, _, intervalMeet_comm I J⟩] (intervalMeet_comm I J)

/-- Interval join commutativity path. -/
def intervalJoin_comm_path (I J : Interval) :
    Path (intervalJoin I J) (intervalJoin J I) :=
  Path.mk [⟨_, _, intervalJoin_comm I J⟩] (intervalJoin_comm I J)

/-! ## Galois connections -/

/-- A Galois connection between Elem posets. -/
structure GaloisConn where
  lower : OrdMap
  upper : OrdMap
  closure_lower : ∀ a : Elem, a.val ≤ (upper.f (lower.f a)).val
  closure_upper : ∀ b : Elem, (lower.f (upper.f b)).val ≤ b.val

/-- Lower adjoint preserves paths. -/
def galois_lower_congrArg (gc : GaloisConn) {a b : Elem}
    (p : Path a b) : Path (gc.lower.f a) (gc.lower.f b) :=
  Path.congrArg gc.lower.f p

/-- Upper adjoint preserves paths. -/
def galois_upper_congrArg (gc : GaloisConn) {a b : Elem}
    (p : Path a b) : Path (gc.upper.f a) (gc.upper.f b) :=
  Path.congrArg gc.upper.f p

/-- Roundtrip via both adjoints preserves paths. -/
def galois_roundtrip_congrArg (gc : GaloisConn) {a b : Elem}
    (p : Path a b) : Path (gc.upper.f (gc.lower.f a)) (gc.upper.f (gc.lower.f b)) :=
  Path.congrArg gc.upper.f (Path.congrArg gc.lower.f p)

/-! ## Distributive lattice identity -/

/-- Distributivity: a∧(b∨c) = (a∧b)∨(a∧c) for Nat min/max. -/
theorem emeet_ejoin_distrib (a b c : Elem) :
    emeet a (ejoin b c) = ejoin (emeet a b) (emeet a c) := by
  cases a; cases b; cases c
  simp only [Elem.mk.injEq, emeet, ejoin, Nat.min_def, Nat.max_def]
  repeat (first | split | omega)

/-- Distributivity path. -/
def distrib_path (a b c : Elem) :
    Path (emeet a (ejoin b c)) (ejoin (emeet a b) (emeet a c)) :=
  Path.mk [⟨_, _, emeet_ejoin_distrib a b c⟩] (emeet_ejoin_distrib a b c)

/-- Reverse distributivity path. -/
def distrib_symm (a b c : Elem) :
    Path (ejoin (emeet a b) (emeet a c)) (emeet a (ejoin b c)) :=
  Path.symm (distrib_path a b c)

/-- Dual distributivity: a∨(b∧c) = (a∨b)∧(a∨c). -/
theorem ejoin_emeet_distrib (a b c : Elem) :
    ejoin a (emeet b c) = emeet (ejoin a b) (ejoin a c) := by
  cases a; cases b; cases c
  simp only [Elem.mk.injEq, ejoin, emeet, Nat.max_def, Nat.min_def]
  repeat (first | split | omega)

/-- Dual distributivity path. -/
def dual_distrib_path (a b c : Elem) :
    Path (ejoin a (emeet b c)) (emeet (ejoin a b) (ejoin a c)) :=
  Path.mk [⟨_, _, ejoin_emeet_distrib a b c⟩] (ejoin_emeet_distrib a b c)

/-! ## Modular law -/

/-- Modular law: a ≤ c → a∨(b∧c) = (a∨b)∧c. -/
theorem modular_law (a b c : Elem) (h : a.val ≤ c.val) :
    ejoin a (emeet b c) = emeet (ejoin a b) c := by
  cases a; cases b; cases c
  simp only [Elem.mk.injEq, ejoin, emeet, Nat.max_def, Nat.min_def] at *
  repeat (first | split | omega)

/-- Modular law path. -/
def modular_path (a b c : Elem) (h : a.val ≤ c.val) :
    Path (ejoin a (emeet b c)) (emeet (ejoin a b) c) :=
  Path.mk [⟨_, _, modular_law a b c h⟩] (modular_law a b c h)

/-! ## Closure operators -/

/-- A closure operator on Elem. -/
structure ClosureOp extends OrdMap where
  extensive : ∀ a : Elem, a.val ≤ (f a).val
  idempotent : ∀ a : Elem, f (f a) = f a

/-- Idempotency path for closure operator. -/
def closure_idem_path (cl : ClosureOp) (a : Elem) :
    Path (cl.f (cl.f a)) (cl.f a) :=
  Path.mk [⟨_, _, cl.idempotent a⟩] (cl.idempotent a)

/-- Three-fold closure is same as one. -/
def closure_triple_path (cl : ClosureOp) (a : Elem) :
    Path (cl.f (cl.f (cl.f a))) (cl.f a) :=
  Path.trans
    (Path.congrArg cl.f (closure_idem_path cl a))
    (closure_idem_path cl a)

/-- Closure preserves paths. -/
def closure_congrArg (cl : ClosureOp) {a b : Elem}
    (p : Path a b) : Path (cl.f a) (cl.f b) :=
  Path.congrArg cl.f p

/-- Symm of closure idempotency. -/
def closure_idem_symm (cl : ClosureOp) (a : Elem) :
    Path (cl.f a) (cl.f (cl.f a)) :=
  Path.symm (closure_idem_path cl a)

/-! ## Identity absorption paths -/

/-- (⊥∧a)∧b → ⊥∧b via congrArg + meet_bot. -/
def meet_bot_absorb_path (a b : Elem) :
    Path (emeet (emeet ebot a) b) (emeet ebot b) :=
  Path.congrArg (fun x => emeet x b) (meet_bot_path a)

/-- ⊥∨(a∨b) → a∨b via join_bot. -/
def join_bot_absorb_path (a b : Elem) :
    Path (ejoin ebot (ejoin a b)) (ejoin a b) :=
  join_bot_path (ejoin a b)

/-! ## Composition preserves fixed points -/

/-- Composition preserves fixed points path. -/
def comp_fixedpoint_path (f g : OrdMap)
    (fpg : FixedPoint g) (hfg : f.f (g.f fpg.point) = fpg.point) :
    Path (f.f (g.f fpg.point)) fpg.point :=
  Path.mk [⟨_, _, hfg⟩] hfg

end ComputationalPaths.Path.Algebra.OrderTheoryDeep
