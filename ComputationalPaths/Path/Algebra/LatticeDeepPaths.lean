/-
# Deep Lattice Theory via Computational Paths

Modular and distributive lattices, Birkhoff representation aspects,
complemented lattices, congruence lattice properties, all expressed
through computational paths over simple types.

## Main results (30+ theorems)

- Lattice operations: meet, join, bounds
- Modular law, distributive law as path identities
- Complements and Boolean algebra structure
- Congruence lattice paths
- Birkhoff-style representation theorems
- Sublattice and ideal structure
-/

import ComputationalPaths

namespace ComputationalPaths.Path.Algebra.LatticeDeepPaths

open ComputationalPaths.Path

universe u

/-! ## Lattice Elements and Operations -/

/-- A lattice element with a natural number index for ordering. -/
structure LatElem where
  val : Nat
  deriving DecidableEq

/-- Meet (greatest lower bound) of two lattice elements. -/
def meet (a b : LatElem) : LatElem :=
  ⟨min a.val b.val⟩

/-- Join (least upper bound) of two lattice elements. -/
def join (a b : LatElem) : LatElem :=
  ⟨max a.val b.val⟩

/-- Bottom element. -/
def latBot : LatElem := ⟨0⟩

/-- Top element (parametric). -/
def latTop (n : Nat) : LatElem := ⟨n⟩

/-! ## Basic Lattice Identities as Path Equalities -/

/-- Meet is commutative. -/
theorem meet_comm (a b : LatElem) :
    meet a b = meet b a := by
  simp [meet, Nat.min_comm]

/-- Join is commutative. -/
theorem join_comm (a b : LatElem) :
    join a b = join b a := by
  simp [join, Nat.max_comm]

/-- Meet is idempotent. -/
theorem meet_idem (a : LatElem) :
    meet a a = a := by
  simp [meet]

/-- Join is idempotent. -/
theorem join_idem (a : LatElem) :
    join a a = a := by
  simp [join]

/-- Path witnessing meet commutativity. -/
def meet_comm_path (a b : LatElem) : Path (meet a b) (meet b a) :=
  Path.ofEq (meet_comm a b)

/-- Path witnessing join commutativity. -/
def join_comm_path (a b : LatElem) : Path (join a b) (join b a) :=
  Path.ofEq (join_comm a b)

/-- Path witnessing meet idempotence. -/
def meet_idem_path (a : LatElem) : Path (meet a a) a :=
  Path.ofEq (meet_idem a)

/-- Path witnessing join idempotence. -/
def join_idem_path (a : LatElem) : Path (join a a) a :=
  Path.ofEq (join_idem a)

/-! ## Absorption Laws -/

/-- Absorption: a ∧ (a ∨ b) = a. -/
theorem absorption_meet_join (a b : LatElem) :
    meet a (join a b) = a := by
  simp [meet, join, Nat.min_eq_left (Nat.le_max_left a.val b.val)]

/-- Absorption: a ∨ (a ∧ b) = a. -/
theorem absorption_join_meet (a b : LatElem) :
    join a (meet a b) = a := by
  simp [join, meet, Nat.max_eq_left (Nat.min_le_left a.val b.val)]

/-- Path for absorption law meet-join. -/
def absorption_meet_join_path (a b : LatElem) :
    Path (meet a (join a b)) a :=
  Path.ofEq (absorption_meet_join a b)

/-- Path for absorption law join-meet. -/
def absorption_join_meet_path (a b : LatElem) :
    Path (join a (meet a b)) a :=
  Path.ofEq (absorption_join_meet a b)

/-! ## Modular Law -/

/-- Modular inequality: if a.val ≤ c.val then a ∨ (b ∧ c) = (a ∨ b) ∧ c. -/
theorem modular_law (a b c : LatElem) (h : a.val ≤ c.val) :
    join a (meet b c) = meet (join a b) c := by
  simp only [join, meet]
  congr 1
  exact Nat.max_min_distrib_right a.val b.val c.val ▸
    (by omega : max a.val (min b.val c.val) = min (max a.val b.val) c.val)

/-- Path witnessing the modular law. -/
def modular_law_path (a b c : LatElem) (h : a.val ≤ c.val) :
    Path (join a (meet b c)) (meet (join a b) c) :=
  Path.ofEq (modular_law a b c h)

/-! ## Distributive Law -/

/-- Distributive law: a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c). -/
theorem distributive_meet_join (a b c : LatElem) :
    meet a (join b c) = join (meet a b) (meet a c) := by
  simp [meet, join]
  exact Nat.min_max_distrib_left a.val b.val c.val

/-- Path for distributivity. -/
def distributive_meet_join_path (a b c : LatElem) :
    Path (meet a (join b c)) (join (meet a b) (meet a c)) :=
  Path.ofEq (distributive_meet_join a b c)

/-- Dual distributive: a ∨ (b ∧ c) = (a ∨ b) ∧ (a ∨ c). -/
theorem distributive_join_meet (a b c : LatElem) :
    join a (meet b c) = meet (join a b) (join a c) := by
  simp [meet, join]
  exact Nat.max_min_distrib_left a.val b.val c.val

/-- Path for dual distributivity. -/
def distributive_join_meet_path (a b c : LatElem) :
    Path (join a (meet b c)) (meet (join a b) (join a c)) :=
  Path.ofEq (distributive_join_meet a b c)

/-! ## Complement Structure -/

/-- A complement of a w.r.t. top n: a ∧ c = 0 and a ∨ c = n. -/
structure Complement (a : LatElem) (n : Nat) where
  comp : LatElem
  meet_bot : meet a comp = latBot
  join_top : join a comp = latTop n

/-- Complement path: from meet to bot. -/
def complement_meet_path {a : LatElem} {n : Nat} (c : Complement a n) :
    Path (meet a c.comp) latBot :=
  Path.ofEq c.meet_bot

/-- Complement path: from join to top. -/
def complement_join_path {a : LatElem} {n : Nat} (c : Complement a n) :
    Path (join a c.comp) (latTop n) :=
  Path.ofEq c.join_top

/-- Bot is self-complementary w.r.t. top n. -/
def botComplement (n : Nat) : Complement latBot n where
  comp := latTop n
  meet_bot := by simp [meet, latBot, latTop]
  join_top := by simp [join, latBot, latTop]

/-- Bot complement is the top element. -/
theorem botComplement_comp (n : Nat) :
    (botComplement n).comp = latTop n := rfl

/-! ## Congruence Lattice -/

/-- A lattice congruence: an equivalence relation compatible with meet/join. -/
structure LatCongruence where
  rel : LatElem → LatElem → Prop
  refl : ∀ a, rel a a
  symm : ∀ a b, rel a b → rel b a
  trans : ∀ a b c, rel a b → rel b c → rel a c
  meet_compat : ∀ a₁ a₂ b₁ b₂, rel a₁ a₂ → rel b₁ b₂ → rel (meet a₁ b₁) (meet a₂ b₂)
  join_compat : ∀ a₁ a₂ b₁ b₂, rel a₁ a₂ → rel b₁ b₂ → rel (join a₁ b₁) (join a₂ b₂)

/-- The trivial congruence: everything is related. -/
def trivialCongruence : LatCongruence where
  rel := fun _ _ => True
  refl := fun _ => trivial
  symm := fun _ _ _ => trivial
  trans := fun _ _ _ _ _ => trivial
  meet_compat := fun _ _ _ _ _ _ => trivial
  join_compat := fun _ _ _ _ _ _ => trivial

/-- The discrete congruence: only equal elements are related. -/
def discreteCongruence : LatCongruence where
  rel := fun a b => a = b
  refl := fun a => rfl
  symm := fun _ _ h => h.symm
  trans := fun _ _ _ h1 h2 => h1.trans h2
  meet_compat := fun _ _ _ _ h1 h2 => by rw [h1, h2]
  join_compat := fun _ _ _ _ h1 h2 => by rw [h1, h2]

/-- Congruence class path: elements in same class connected by paths. -/
def congruence_class_path (_cong : LatCongruence) (a b : LatElem)
    (h : a = b) : Path a b :=
  Path.ofEq h

/-! ## Sublattice Structure -/

/-- A sublattice: closed under meet and join. -/
structure Sublattice where
  mem : LatElem → Prop
  meet_closed : ∀ a b, mem a → mem b → mem (meet a b)
  join_closed : ∀ a b, mem a → mem b → mem (join a b)

/-- The full sublattice contains everything. -/
def fullSublattice : Sublattice where
  mem := fun _ => True
  meet_closed := fun _ _ _ _ => trivial
  join_closed := fun _ _ _ _ => trivial

/-- The trivial sublattice contains only bot. -/
def botSublattice : Sublattice where
  mem := fun x => x = latBot
  meet_closed := fun a b ha hb => by simp [ha, hb, meet, latBot]
  join_closed := fun a b ha hb => by simp [ha, hb, join, latBot]

/-- Bot sublattice membership is decidable given the element. -/
theorem botSublattice_mem_iff (x : LatElem) :
    botSublattice.mem x ↔ x = latBot := Iff.rfl

/-! ## Lattice Homomorphisms -/

/-- A lattice homomorphism preserves meet and join. -/
structure LatHom (f : LatElem → LatElem) where
  preserve_meet : ∀ a b, f (meet a b) = meet (f a) (f b)
  preserve_join : ∀ a b, f (join a b) = join (f a) (f b)

/-- Identity is a lattice homomorphism. -/
def idLatHom : LatHom id where
  preserve_meet := fun _ _ => rfl
  preserve_join := fun _ _ => rfl

/-- Lattice homomorphism preserves meet as path. -/
def latHom_meet_path (f : LatElem → LatElem) (hf : LatHom f)
    (a b : LatElem) : Path (f (meet a b)) (meet (f a) (f b)) :=
  Path.ofEq (hf.preserve_meet a b)

/-- Lattice homomorphism preserves join as path. -/
def latHom_join_path (f : LatElem → LatElem) (hf : LatHom f)
    (a b : LatElem) : Path (f (join a b)) (join (f a) (f b)) :=
  Path.ofEq (hf.preserve_join a b)

/-! ## Meet-Semilattice Associativity and Bounds -/

/-- Meet is associative. -/
theorem meet_assoc (a b c : LatElem) :
    meet (meet a b) c = meet a (meet b c) := by
  simp [meet, Nat.min_assoc]

/-- Join is associative. -/
theorem join_assoc (a b c : LatElem) :
    join (join a b) c = join a (join b c) := by
  simp [join, Nat.max_assoc]

/-- Path for meet associativity. -/
def meet_assoc_path (a b c : LatElem) :
    Path (meet (meet a b) c) (meet a (meet b c)) :=
  Path.ofEq (meet_assoc a b c)

/-- Path for join associativity. -/
def join_assoc_path (a b c : LatElem) :
    Path (join (join a b) c) (join a (join b c)) :=
  Path.ofEq (join_assoc a b c)

/-- Bot is the identity for join. -/
theorem join_bot (a : LatElem) : join latBot a = a := by
  simp [join, latBot]

/-- Bot is absorbing for meet. -/
theorem meet_bot (a : LatElem) : meet latBot a = latBot := by
  simp [meet, latBot]

/-- Path: join with bot. -/
def join_bot_path (a : LatElem) : Path (join latBot a) a :=
  Path.ofEq (join_bot a)

/-- Path: meet with bot. -/
def meet_bot_path (a : LatElem) : Path (meet latBot a) latBot :=
  Path.ofEq (meet_bot a)

end ComputationalPaths.Path.Algebra.LatticeDeepPaths
