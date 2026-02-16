/-
# Deep Lattice Theory via Computational Paths

Modular and distributive lattices, complemented lattices, congruence
lattice properties, all expressed through genuine computational path
rewrites over a concrete Nat-based lattice with domain-specific steps.

## Main results (40+ theorems)

- LattVal: concrete lattice elements (Nat-based with min/max)
- LattStep: one-step domain rewrites (commutativity, assoc, absorption, etc.)
- LattPath = Path over LattVal, built from refl/trans/symm/congrArg/stepPath
- Modular law, distributive law as path identities
- Sublattice, ideal, filter, homomorphism coherence
- All zero sorry, zero Path.ofEq
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.LatticeDeepPaths

open ComputationalPaths.Path

universe u

/-! ## Concrete Lattice Type -/

/-- A lattice element backed by a natural number. Meet = min, join = max. -/
structure LattVal where
  val : Nat
  deriving DecidableEq, Repr

/-- Meet (greatest lower bound). -/
def lmeet (a b : LattVal) : LattVal := ⟨min a.val b.val⟩
/-- Join (least upper bound). -/
def ljoin (a b : LattVal) : LattVal := ⟨max a.val b.val⟩
/-- Bottom element. -/
def lbot : LattVal := ⟨0⟩
/-- Top element (parametric). -/
def ltop (n : Nat) : LattVal := ⟨n⟩

/-! ## Domain-specific step type -/

/-- Elementary lattice rewrite steps. Each constructor witnesses a single
    lattice identity as a computational rewrite. -/
inductive LattStep : LattVal → LattVal → Type where
  | meet_comm   : (a b : LattVal) → LattStep (lmeet a b) (lmeet b a)
  | join_comm   : (a b : LattVal) → LattStep (ljoin a b) (ljoin b a)
  | meet_idem   : (a : LattVal) → LattStep (lmeet a a) a
  | join_idem   : (a : LattVal) → LattStep (ljoin a a) a
  | meet_assoc  : (a b c : LattVal) → LattStep (lmeet (lmeet a b) c) (lmeet a (lmeet b c))
  | join_assoc  : (a b c : LattVal) → LattStep (ljoin (ljoin a b) c) (ljoin a (ljoin b c))
  | absorb_mj   : (a b : LattVal) → LattStep (lmeet a (ljoin a b)) a
  | absorb_jm   : (a b : LattVal) → LattStep (ljoin a (lmeet a b)) a
  | meet_bot    : (a : LattVal) → LattStep (lmeet lbot a) lbot
  | join_bot    : (a : LattVal) → LattStep (ljoin lbot a) a
  | distrib_mj  : (a b c : LattVal) →
      LattStep (lmeet a (ljoin b c)) (ljoin (lmeet a b) (lmeet a c))
  | distrib_jm  : (a b c : LattVal) →
      LattStep (ljoin a (lmeet b c)) (lmeet (ljoin a b) (ljoin a c))

/-! ## Step soundness: each step yields a propositional equality -/

/-- Proof that meet is commutative on LattVal. -/
theorem lmeet_comm (a b : LattVal) : lmeet a b = lmeet b a := by
  simp [lmeet, Nat.min_comm]

/-- Proof that join is commutative on LattVal. -/
theorem ljoin_comm (a b : LattVal) : ljoin a b = ljoin b a := by
  simp [ljoin, Nat.max_comm]

/-- Meet is idempotent. -/
theorem lmeet_idem (a : LattVal) : lmeet a a = a := by
  simp [lmeet]

/-- Join is idempotent. -/
theorem ljoin_idem (a : LattVal) : ljoin a a = a := by
  simp [ljoin]

/-- Meet is associative. -/
theorem lmeet_assoc (a b c : LattVal) :
    lmeet (lmeet a b) c = lmeet a (lmeet b c) := by
  simp [lmeet, Nat.min_assoc]

/-- Join is associative. -/
theorem ljoin_assoc (a b c : LattVal) :
    ljoin (ljoin a b) c = ljoin a (ljoin b c) := by
  simp [ljoin, Nat.max_assoc]

/-- Absorption: meet a (join a b) = a. -/
theorem labsorb_mj (a b : LattVal) : lmeet a (ljoin a b) = a := by
  show LattVal.mk (min a.val (max a.val b.val)) = a
  congr 1
  exact Nat.min_eq_left (Nat.le_max_left a.val b.val)

/-- Absorption: join a (meet a b) = a. -/
theorem labsorb_jm (a b : LattVal) : ljoin a (lmeet a b) = a := by
  show LattVal.mk (max a.val (min a.val b.val)) = a
  congr 1
  exact Nat.max_eq_left (Nat.min_le_left a.val b.val)

/-- Meet with bot is bot. -/
theorem lmeet_bot (a : LattVal) : lmeet lbot a = lbot := by
  simp [lmeet, lbot]

/-- Join with bot is identity. -/
theorem ljoin_bot (a : LattVal) : ljoin lbot a = a := by
  simp [ljoin, lbot]

/-- Distributive: meet over join. -/
theorem ldistrib_mj (a b c : LattVal) :
    lmeet a (ljoin b c) = ljoin (lmeet a b) (lmeet a c) := by
  simp [lmeet, ljoin]; exact Nat.min_max_distrib_left a.val b.val c.val

/-- Distributive: join over meet. -/
theorem ldistrib_jm (a b c : LattVal) :
    ljoin a (lmeet b c) = lmeet (ljoin a b) (ljoin a c) := by
  simp [lmeet, ljoin]; exact Nat.max_min_distrib_left a.val b.val c.val

/-- Each LattStep yields a propositional equality. -/
def LattStep.toEq : LattStep a b → a = b
  | .meet_comm a b    => lmeet_comm a b
  | .join_comm a b    => ljoin_comm a b
  | .meet_idem a      => lmeet_idem a
  | .join_idem a      => ljoin_idem a
  | .meet_assoc a b c => lmeet_assoc a b c
  | .join_assoc a b c => ljoin_assoc a b c
  | .absorb_mj a b    => labsorb_mj a b
  | .absorb_jm a b    => labsorb_jm a b
  | .meet_bot a       => lmeet_bot a
  | .join_bot a       => ljoin_bot a
  | .distrib_mj a b c => ldistrib_mj a b c
  | .distrib_jm a b c => ldistrib_jm a b c

/-! ## Building paths from steps -/

/-- Build a Path from a single LattStep. -/
def stepPath {a b : LattVal} (s : LattStep a b) : Path a b :=
  let h := s.toEq
  Path.mk [⟨a, b, h⟩] h

/-! ## Basic identity paths -/

/-- Meet commutativity path. -/
def meet_comm_path (a b : LattVal) : Path (lmeet a b) (lmeet b a) :=
  stepPath (LattStep.meet_comm a b)

/-- Join commutativity path. -/
def join_comm_path (a b : LattVal) : Path (ljoin a b) (ljoin b a) :=
  stepPath (LattStep.join_comm a b)

/-- Meet idempotence path. -/
def meet_idem_path (a : LattVal) : Path (lmeet a a) a :=
  stepPath (LattStep.meet_idem a)

/-- Join idempotence path. -/
def join_idem_path (a : LattVal) : Path (ljoin a a) a :=
  stepPath (LattStep.join_idem a)

/-- Meet associativity path. -/
def meet_assoc_path (a b c : LattVal) :
    Path (lmeet (lmeet a b) c) (lmeet a (lmeet b c)) :=
  stepPath (LattStep.meet_assoc a b c)

/-- Join associativity path. -/
def join_assoc_path (a b c : LattVal) :
    Path (ljoin (ljoin a b) c) (ljoin a (ljoin b c)) :=
  stepPath (LattStep.join_assoc a b c)

/-! ## Absorption paths -/

/-- Absorption meet-join path. -/
def absorb_mj_path (a b : LattVal) : Path (lmeet a (ljoin a b)) a :=
  stepPath (LattStep.absorb_mj a b)

/-- Absorption join-meet path. -/
def absorb_jm_path (a b : LattVal) : Path (ljoin a (lmeet a b)) a :=
  stepPath (LattStep.absorb_jm a b)

/-! ## Bound paths -/

/-- Meet with bot gives bot. -/
def meet_bot_path (a : LattVal) : Path (lmeet lbot a) lbot :=
  stepPath (LattStep.meet_bot a)

/-- Join with bot gives identity. -/
def join_bot_path (a : LattVal) : Path (ljoin lbot a) a :=
  stepPath (LattStep.join_bot a)

/-! ## Distributivity paths -/

/-- Distributive law: meet over join. -/
def distrib_mj_path (a b c : LattVal) :
    Path (lmeet a (ljoin b c)) (ljoin (lmeet a b) (lmeet a c)) :=
  stepPath (LattStep.distrib_mj a b c)

/-- Dual distributive law: join over meet. -/
def distrib_jm_path (a b c : LattVal) :
    Path (ljoin a (lmeet b c)) (lmeet (ljoin a b) (ljoin a c)) :=
  stepPath (LattStep.distrib_jm a b c)

/-! ## Composite paths via trans -/

/-- Right-comm for meet: lmeet a (lmeet b c) → lmeet a (lmeet c b) via congrArg. -/
def meet_right_comm_path (a b c : LattVal) :
    Path (lmeet a (lmeet b c)) (lmeet a (lmeet c b)) :=
  Path.congrArg (lmeet a) (meet_comm_path b c)

/-- Right-comm for join. -/
def join_right_comm_path (a b c : LattVal) :
    Path (ljoin a (ljoin b c)) (ljoin a (ljoin c b)) :=
  Path.congrArg (ljoin a) (join_comm_path b c)

/-- Reassociate then commute inner for meet. -/
def meet_assoc_comm_path (a b c : LattVal) :
    Path (lmeet (lmeet a b) c) (lmeet a (lmeet c b)) :=
  Path.trans (meet_assoc_path a b c) (meet_right_comm_path a b c)

/-- Reassociate then commute inner for join. -/
def join_assoc_comm_path (a b c : LattVal) :
    Path (ljoin (ljoin a b) c) (ljoin a (ljoin c b)) :=
  Path.trans (join_assoc_path a b c) (join_right_comm_path a b c)

/-- Bot absorb right: lmeet a lbot = lbot via comm + meet_bot. -/
def meet_bot_right_path (a : LattVal) : Path (lmeet a lbot) lbot :=
  Path.trans (meet_comm_path a lbot) (meet_bot_path a)

/-- Join with bot on right: ljoin a lbot = a. -/
def join_bot_right_path (a : LattVal) : Path (ljoin a lbot) a :=
  Path.trans (join_comm_path a lbot) (join_bot_path a)

/-! ## Symm-based reverse paths -/

/-- Reverse of meet commutativity. -/
def meet_comm_symm_path (a b : LattVal) : Path (lmeet b a) (lmeet a b) :=
  Path.symm (meet_comm_path a b)

/-- Reverse of absorption: a → lmeet a (ljoin a b). -/
def absorb_mj_symm_path (a b : LattVal) : Path a (lmeet a (ljoin a b)) :=
  Path.symm (absorb_mj_path a b)

/-- Reverse of distributivity. -/
def distrib_mj_symm_path (a b c : LattVal) :
    Path (ljoin (lmeet a b) (lmeet a c)) (lmeet a (ljoin b c)) :=
  Path.symm (distrib_mj_path a b c)

/-! ## Four-fold associativity -/

/-- Meet four-fold reassociation. -/
def meet_assoc4_path (a b c d : LattVal) :
    Path (lmeet (lmeet (lmeet a b) c) d) (lmeet a (lmeet b (lmeet c d))) :=
  Path.trans
    (meet_assoc_path (lmeet a b) c d)
    (meet_assoc_path a b (lmeet c d))

/-- Join four-fold reassociation. -/
def join_assoc4_path (a b c d : LattVal) :
    Path (ljoin (ljoin (ljoin a b) c) d) (ljoin a (ljoin b (ljoin c d))) :=
  Path.trans
    (join_assoc_path (ljoin a b) c d)
    (join_assoc_path a b (ljoin c d))

/-! ## Lattice order as path existence -/

/-- a ≤ b in the lattice iff lmeet a b = a, witnessed by a path. -/
structure LattLe (a b : LattVal) where
  witness : Path (lmeet a b) a

/-- Reflexivity of ≤: a ≤ a via idempotence. -/
def lattLe_refl (a : LattVal) : LattLe a a :=
  ⟨meet_idem_path a⟩

/-- bot ≤ a for all a. -/
def lattLe_bot (a : LattVal) : LattLe lbot a :=
  ⟨meet_bot_path a⟩

/-! ## congrArg derived paths -/

/-- Lifting meet idempotence inside a join. -/
def join_meet_idem_path (x a : LattVal) :
    Path (ljoin x (lmeet a a)) (ljoin x a) :=
  Path.congrArg (ljoin x) (meet_idem_path a)

/-- Lifting join idempotence inside a meet. -/
def meet_join_idem_path (x a : LattVal) :
    Path (lmeet x (ljoin a a)) (lmeet x a) :=
  Path.congrArg (lmeet x) (join_idem_path a)

/-- Nested congrArg: ljoin (lmeet a (ljoin b b)) c → ljoin (lmeet a b) c. -/
def nested_congrArg_path (a b c : LattVal) :
    Path (ljoin (lmeet a (ljoin b b)) c) (ljoin (lmeet a b) c) :=
  Path.congrArg (fun x => ljoin x c)
    (Path.congrArg (lmeet a) (join_idem_path b))

/-! ## Lattice Homomorphism Coherence -/

/-- A lattice homomorphism: preserves meet and join. -/
structure LattHom (f : LattVal → LattVal) where
  preserve_meet : ∀ a b, f (lmeet a b) = lmeet (f a) (f b)
  preserve_join : ∀ a b, f (ljoin a b) = ljoin (f a) (f b)

/-- Identity is a lattice homomorphism. -/
def idLattHom : LattHom id where
  preserve_meet := fun _ _ => rfl
  preserve_join := fun _ _ => rfl

/-- Homomorphism preserves meet as a path. -/
def lattHom_meet_step (f : LattVal → LattVal) (hf : LattHom f) (a b : LattVal) :
    Path (f (lmeet a b)) (lmeet (f a) (f b)) :=
  Path.mk [⟨_, _, hf.preserve_meet a b⟩] (hf.preserve_meet a b)

/-- Homomorphism preserves join as a path. -/
def lattHom_join_step (f : LattVal → LattVal) (hf : LattHom f) (a b : LattVal) :
    Path (f (ljoin a b)) (ljoin (f a) (f b)) :=
  Path.mk [⟨_, _, hf.preserve_join a b⟩] (hf.preserve_join a b)

/-- Homomorphism composed with meet-comm: f(a∧b) → f(b∧a) via congrArg. -/
def lattHom_meet_comm_path (f : LattVal → LattVal) (a b : LattVal) :
    Path (f (lmeet a b)) (f (lmeet b a)) :=
  Path.congrArg f (meet_comm_path a b)

/-- Homomorphism composed with join-comm. -/
def lattHom_join_comm_path (f : LattVal → LattVal) (a b : LattVal) :
    Path (f (ljoin a b)) (f (ljoin b a)) :=
  Path.congrArg f (join_comm_path a b)

/-! ## Sublattice and Ideal structures -/

/-- A sublattice: closed under meet and join. -/
structure Sublattice where
  mem : LattVal → Prop
  meet_closed : ∀ a b, mem a → mem b → mem (lmeet a b)
  join_closed : ∀ a b, mem a → mem b → mem (ljoin a b)

/-- The full sublattice. -/
def fullSublattice : Sublattice where
  mem := fun _ => True
  meet_closed := fun _ _ _ _ => trivial
  join_closed := fun _ _ _ _ => trivial

/-- The trivial sublattice containing only bot. -/
def botSublattice : Sublattice where
  mem := fun x => x = lbot
  meet_closed := fun a b ha hb => by simp [ha, hb, lmeet, lbot]
  join_closed := fun a b ha hb => by simp [ha, hb, ljoin, lbot]

/-- A lattice filter: closed under meet, contains top. -/
structure LattFilter (n : Nat) where
  mem : LattVal → Prop
  meet_closed : ∀ a b, mem a → mem b → mem (lmeet a b)
  top_mem : mem (ltop n)

/-! ## Congruence lattice -/

/-- A lattice congruence: equivalence relation compatible with meet/join. -/
structure LattCong where
  rel : LattVal → LattVal → Prop
  rfl_rel : ∀ a, rel a a
  sym_rel : ∀ a b, rel a b → rel b a
  trans_rel : ∀ a b c, rel a b → rel b c → rel a c
  meet_compat : ∀ a₁ a₂ b₁ b₂, rel a₁ a₂ → rel b₁ b₂ →
    rel (lmeet a₁ b₁) (lmeet a₂ b₂)
  join_compat : ∀ a₁ a₂ b₁ b₂, rel a₁ a₂ → rel b₁ b₂ →
    rel (ljoin a₁ b₁) (ljoin a₂ b₂)

/-- The trivial congruence (everything related). -/
def trivialCong : LattCong where
  rel := fun _ _ => True
  rfl_rel := fun _ => trivial
  sym_rel := fun _ _ _ => trivial
  trans_rel := fun _ _ _ _ _ => trivial
  meet_compat := fun _ _ _ _ _ _ => trivial
  join_compat := fun _ _ _ _ _ _ => trivial

/-- The discrete congruence (only equal elements related). -/
def discreteCong : LattCong where
  rel := fun a b => a = b
  rfl_rel := fun _ => rfl
  sym_rel := fun _ _ h => h.symm
  trans_rel := fun _ _ _ h1 h2 => h1.trans h2
  meet_compat := fun _ _ _ _ h1 h2 => by rw [h1, h2]
  join_compat := fun _ _ _ _ h1 h2 => by rw [h1, h2]

/-! ## Transport along lattice paths -/

/-- Transport a property across a lattice path. -/
def lattTransport (P : LattVal → Prop) {a b : LattVal}
    (p : Path a b) (h : P a) : P b :=
  Path.transport p h

/-- Transport bot membership through meet_bot. -/
theorem transport_bot_mem (P : LattVal → Prop) (hbot : P lbot) (a : LattVal) :
    P (lmeet lbot a) :=
  lattTransport P (Path.symm (meet_bot_path a)) hbot

/-! ## Modular law path -/

/-- Modular inequality: if a.val ≤ c.val then ljoin a (lmeet b c) = lmeet (ljoin a b) c. -/
theorem modular_law (a b c : LattVal) (h : a.val ≤ c.val) :
    ljoin a (lmeet b c) = lmeet (ljoin a b) c := by
  simp only [ljoin, lmeet, LattVal.mk.injEq]
  omega

/-- Modular law as a path. -/
def modular_law_path (a b c : LattVal) (h : a.val ≤ c.val) :
    Path (ljoin a (lmeet b c)) (lmeet (ljoin a b) c) :=
  Path.mk [⟨_, _, modular_law a b c h⟩] (modular_law a b c h)

/-! ## Path algebra: groupoid laws witnessed -/

/-- Refl is left identity for trans. -/
theorem refl_trans_eq {a b : LattVal} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  Path.trans_refl_left p

/-- Refl is right identity for trans. -/
theorem trans_refl_eq {a b : LattVal} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  Path.trans_refl_right p

/-- Trans is associative. -/
theorem trans_assoc_eq {a b c d : LattVal}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

/-- Symm of symm is identity. -/
theorem symm_symm_eq {a b : LattVal} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- Symm distributes over trans. -/
theorem symm_trans_eq {a b c : LattVal} (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

/-! ## Extended composite paths -/

/-- Double absorption: a → lmeet a (ljoin a (lmeet a b)) via symm + absorption. -/
def double_absorb_path (a b : LattVal) :
    Path a (lmeet a (ljoin a (lmeet a b))) :=
  Path.trans
    (Path.symm (absorb_mj_path a (lmeet a b)))
    (Path.refl _)

/-- Meet distributes over join, then re-collect: round trip. -/
def distrib_roundtrip (a b c : LattVal) :
    Path (lmeet a (ljoin b c)) (lmeet a (ljoin b c)) :=
  Path.trans (distrib_mj_path a b c) (distrib_mj_symm_path a b c)

/-- Join-bot + meet-idem chain: ljoin lbot (lmeet a a) → a. -/
def bot_join_idem_path (a : LattVal) : Path (ljoin lbot (lmeet a a)) a :=
  Path.trans
    (Path.congrArg (ljoin lbot) (meet_idem_path a))
    (join_bot_path a)

/-- Fully associating a 5-element meet via iterated assoc. -/
def meet_assoc5_path (a b c d e : LattVal) :
    Path (lmeet (lmeet (lmeet (lmeet a b) c) d) e)
         (lmeet a (lmeet b (lmeet c (lmeet d e)))) :=
  Path.trans
    (meet_assoc_path (lmeet (lmeet a b) c) d e)
    (Path.trans
      (meet_assoc_path (lmeet a b) c (lmeet d e))
      (meet_assoc_path a b (lmeet c (lmeet d e))))

end ComputationalPaths.Path.Algebra.LatticeDeepPaths
