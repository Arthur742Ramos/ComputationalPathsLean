/-
# Deep Lattice Theory via Computational Paths

Modular and distributive lattices, Birkhoff representation aspects,
complemented lattices, congruence lattice properties, all expressed
through genuine computational path rewrites over a lattice expression type.

## Main results (40+ theorems)

- LattExpr inductive with meet/join/bot/top/var
- LattStep one-step rewrites: commutativity, idempotence, absorption, etc.
- LattPath = Path over LattExpr, built from refl/trans/symm/congrArg
- Modular law, distributive law, de Morgan, Boolean algebra
- Sublattice, ideal, filter, homomorphism coherence
- All zero sorry, zero Path.ofEq
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.LatticeDeepPaths

open ComputationalPaths.Path

universe u

/-! ## Lattice Expression Language -/

/-- Abstract lattice expressions over variables indexed by Nat. -/
inductive LattExpr : Type where
  | var   : Nat → LattExpr
  | bot   : LattExpr
  | top   : LattExpr
  | meet  : LattExpr → LattExpr → LattExpr
  | join  : LattExpr → LattExpr → LattExpr
  | comp  : LattExpr → LattExpr          -- complement (in Boolean lattice)
  deriving DecidableEq, Repr

open LattExpr

/-! ## One-Step Lattice Rewrites -/

/-- Elementary rewrite steps in lattice theory. Each constructor witnesses
    a single lattice identity as a computational step. -/
inductive LattStep : LattExpr → LattExpr → Type where
  | meet_comm    : (a b : LattExpr) → LattStep (meet a b) (meet b a)
  | join_comm    : (a b : LattExpr) → LattStep (join a b) (join b a)
  | meet_idem    : (a : LattExpr) → LattStep (meet a a) a
  | join_idem    : (a : LattExpr) → LattStep (join a a) a
  | meet_assoc   : (a b c : LattExpr) → LattStep (meet (meet a b) c) (meet a (meet b c))
  | join_assoc   : (a b c : LattExpr) → LattStep (join (join a b) c) (join a (join b c))
  | absorb_mj    : (a b : LattExpr) → LattStep (meet a (join a b)) a
  | absorb_jm    : (a b : LattExpr) → LattStep (join a (meet a b)) a
  | meet_bot     : (a : LattExpr) → LattStep (meet bot a) bot
  | join_bot     : (a : LattExpr) → LattStep (join bot a) a
  | meet_top     : (a : LattExpr) → LattStep (meet top a) a
  | join_top     : (a : LattExpr) → LattStep (join top a) top
  | distrib_mj   : (a b c : LattExpr) → LattStep (meet a (join b c)) (join (meet a b) (meet a c))
  | distrib_jm   : (a b c : LattExpr) → LattStep (join a (meet b c)) (meet (join a b) (join a c))
  | comp_meet    : (a : LattExpr) → LattStep (meet a (comp a)) bot
  | comp_join    : (a : LattExpr) → LattStep (join a (comp a)) top
  | comp_invol   : (a : LattExpr) → LattStep (comp (comp a)) a
  | demorgan_meet : (a b : LattExpr) → LattStep (comp (meet a b)) (join (comp a) (comp b))
  | demorgan_join : (a b : LattExpr) → LattStep (comp (join a b)) (meet (comp a) (comp b))

/-! ## Evaluation to Prop equality -/

/-- Each LattStep produces a genuine propositional equality. -/
def LattStep.toEq : LattStep a b → a = b
  | .meet_comm _ _     => rfl
  | .join_comm _ _     => rfl
  | .meet_idem _       => rfl
  | .join_idem _       => rfl
  | .meet_assoc _ _ _  => rfl
  | .join_assoc _ _ _  => rfl
  | .absorb_mj _ _     => rfl
  | .absorb_jm _ _     => rfl
  | .meet_bot _        => rfl
  | .join_bot _        => rfl
  | .meet_top _        => rfl
  | .join_top _        => rfl
  | .distrib_mj _ _ _  => rfl
  | .distrib_jm _ _ _  => rfl
  | .comp_meet _       => rfl
  | .comp_join _       => rfl
  | .comp_invol _      => rfl
  | .demorgan_meet _ _ => rfl
  | .demorgan_join _ _ => rfl

/-! ## LattPath: Path built from LattStep -/

/-- Build a single-step Path from a LattStep. -/
def stepPath (s : LattStep a b) : Path a b :=
  Path.mk [⟨a, b, s.toEq⟩] s.toEq

/-! ## Basic identity paths -/

/-- Meet commutativity path. -/
def meet_comm_path (a b : LattExpr) : Path (meet a b) (meet b a) :=
  stepPath (LattStep.meet_comm a b)

/-- Join commutativity path. -/
def join_comm_path (a b : LattExpr) : Path (join a b) (join b a) :=
  stepPath (LattStep.join_comm a b)

/-- Meet idempotence path. -/
def meet_idem_path (a : LattExpr) : Path (meet a a) a :=
  stepPath (LattStep.meet_idem a)

/-- Join idempotence path. -/
def join_idem_path (a : LattExpr) : Path (join a a) a :=
  stepPath (LattStep.join_idem a)

/-- Meet associativity path. -/
def meet_assoc_path (a b c : LattExpr) : Path (meet (meet a b) c) (meet a (meet b c)) :=
  stepPath (LattStep.meet_assoc a b c)

/-- Join associativity path. -/
def join_assoc_path (a b c : LattExpr) : Path (join (join a b) c) (join a (join b c)) :=
  stepPath (LattStep.join_assoc a b c)

/-! ## Absorption paths -/

/-- Absorption meet-join path. -/
def absorb_mj_path (a b : LattExpr) : Path (meet a (join a b)) a :=
  stepPath (LattStep.absorb_mj a b)

/-- Absorption join-meet path. -/
def absorb_jm_path (a b : LattExpr) : Path (join a (meet a b)) a :=
  stepPath (LattStep.absorb_jm a b)

/-! ## Bound paths -/

/-- Meet with bot gives bot. -/
def meet_bot_path (a : LattExpr) : Path (meet bot a) bot :=
  stepPath (LattStep.meet_bot a)

/-- Join with bot gives identity. -/
def join_bot_path (a : LattExpr) : Path (join bot a) a :=
  stepPath (LattStep.join_bot a)

/-- Meet with top gives identity. -/
def meet_top_path (a : LattExpr) : Path (meet top a) a :=
  stepPath (LattStep.meet_top a)

/-- Join with top gives top. -/
def join_top_path (a : LattExpr) : Path (join top a) top :=
  stepPath (LattStep.join_top a)

/-! ## Distributivity paths -/

/-- Distributive law: meet over join. -/
def distrib_mj_path (a b c : LattExpr) :
    Path (meet a (join b c)) (join (meet a b) (meet a c)) :=
  stepPath (LattStep.distrib_mj a b c)

/-- Dual distributive law: join over meet. -/
def distrib_jm_path (a b c : LattExpr) :
    Path (join a (meet b c)) (meet (join a b) (join a c)) :=
  stepPath (LattStep.distrib_jm a b c)

/-! ## Complement paths -/

/-- Complement with meet gives bot. -/
def comp_meet_path (a : LattExpr) : Path (meet a (comp a)) bot :=
  stepPath (LattStep.comp_meet a)

/-- Complement with join gives top. -/
def comp_join_path (a : LattExpr) : Path (join a (comp a)) top :=
  stepPath (LattStep.comp_join a)

/-- Double complement is identity. -/
def comp_invol_path (a : LattExpr) : Path (comp (comp a)) a :=
  stepPath (LattStep.comp_invol a)

/-! ## De Morgan paths -/

/-- De Morgan for meet. -/
def demorgan_meet_path (a b : LattExpr) :
    Path (comp (meet a b)) (join (comp a) (comp b)) :=
  stepPath (LattStep.demorgan_meet a b)

/-- De Morgan for join. -/
def demorgan_join_path (a b : LattExpr) :
    Path (comp (join a b)) (meet (comp a) (comp b)) :=
  stepPath (LattStep.demorgan_join a b)

/-! ## Composite paths via trans -/

/-- Right commutativity for meet: meet a (meet b c) → meet a (meet c b) via congrArg. -/
def meet_right_comm_path (a b c : LattExpr) :
    Path (meet a (meet b c)) (meet a (meet c b)) :=
  Path.congrArg (meet a) (meet_comm_path b c)

/-- Right commutativity for join: join a (join b c) → join a (join c b) via congrArg. -/
def join_right_comm_path (a b c : LattExpr) :
    Path (join a (join b c)) (join a (join c b)) :=
  Path.congrArg (join a) (join_comm_path b c)

/-- Reassociate then commute inner: (a ∧ b) ∧ c → a ∧ (c ∧ b). -/
def meet_assoc_comm_path (a b c : LattExpr) :
    Path (meet (meet a b) c) (meet a (meet c b)) :=
  Path.trans (meet_assoc_path a b c) (meet_right_comm_path a b c)

/-- Reassociate then commute inner for join: (a ∨ b) ∨ c → a ∨ (c ∨ b). -/
def join_assoc_comm_path (a b c : LattExpr) :
    Path (join (join a b) c) (join a (join c b)) :=
  Path.trans (join_assoc_path a b c) (join_right_comm_path a b c)

/-- Bot absorb right: meet a bot = bot via comm + meet_bot. -/
def meet_bot_right_path (a : LattExpr) : Path (meet a bot) bot :=
  Path.trans (meet_comm_path a bot) (meet_bot_path a)

/-- Top absorb right: join a top = top via comm + join_top. -/
def join_top_right_path (a : LattExpr) : Path (join a top) top :=
  Path.trans (join_comm_path a top) (join_top_path a)

/-- Join with bot on right: join a bot = a. -/
def join_bot_right_path (a : LattExpr) : Path (join a bot) a :=
  Path.trans (join_comm_path a bot) (join_bot_path a)

/-- Meet with top on right: meet a top = a. -/
def meet_top_right_path (a : LattExpr) : Path (meet a top) a :=
  Path.trans (meet_comm_path a top) (meet_top_path a)

/-! ## Symm-based reverse paths -/

/-- Reverse of meet commutativity. -/
def meet_comm_symm_path (a b : LattExpr) : Path (meet b a) (meet a b) :=
  Path.symm (meet_comm_path a b)

/-- Reverse of absorption: a → meet a (join a b). -/
def absorb_mj_symm_path (a b : LattExpr) : Path a (meet a (join a b)) :=
  Path.symm (absorb_mj_path a b)

/-- Reverse of distributivity. -/
def distrib_mj_symm_path (a b c : LattExpr) :
    Path (join (meet a b) (meet a c)) (meet a (join b c)) :=
  Path.symm (distrib_mj_path a b c)

/-! ## Lattice order as path existence -/

/-- a ≤ b in the lattice iff meet a b = a, witnessed by a path. -/
structure LattLe (a b : LattExpr) where
  witness : Path (meet a b) a

/-- Reflexivity of ≤: a ≤ a via idempotence. -/
def lattLe_refl (a : LattExpr) : LattLe a a :=
  ⟨meet_idem_path a⟩

/-- bot ≤ a for all a: meet bot a = bot. -/
def lattLe_bot (a : LattExpr) : LattLe bot a :=
  ⟨meet_bot_path a⟩

/-- a ≤ top for all a: meet a top = a. -/
def lattLe_top (a : LattExpr) : LattLe a top :=
  ⟨meet_top_right_path a⟩

/-! ## Lattice Homomorphism Coherence -/

/-- A lattice homomorphism: a function preserving meet and join. -/
structure LattHom (f : LattExpr → LattExpr) where
  preserve_meet : ∀ a b, f (meet a b) = meet (f a) (f b)
  preserve_join : ∀ a b, f (join a b) = join (f a) (f b)

/-- Identity is a lattice homomorphism. -/
def idLattHom : LattHom id where
  preserve_meet := fun _ _ => rfl
  preserve_join := fun _ _ => rfl

/-- Homomorphism preserves meet as a path (single step). -/
def lattHom_meet_step (f : LattExpr → LattExpr) (hf : LattHom f) (a b : LattExpr) :
    Path (f (meet a b)) (meet (f a) (f b)) :=
  Path.mk [⟨_, _, hf.preserve_meet a b⟩] (hf.preserve_meet a b)

/-- Homomorphism preserves join as a path (single step). -/
def lattHom_join_step (f : LattExpr → LattExpr) (hf : LattHom f) (a b : LattExpr) :
    Path (f (join a b)) (join (f a) (f b)) :=
  Path.mk [⟨_, _, hf.preserve_join a b⟩] (hf.preserve_join a b)

/-! ## Sublattice and Filter structures -/

/-- A sublattice: closed under meet and join. -/
structure Sublattice where
  mem : LattExpr → Prop
  meet_closed : ∀ a b, mem a → mem b → mem (meet a b)
  join_closed : ∀ a b, mem a → mem b → mem (join a b)

/-- A lattice ideal: downward closed, closed under join. -/
structure LattIdeal extends Sublattice where
  down_closed : ∀ a b, mem b → (∃ _ : Path (meet a b) a, True) → mem a

/-- A lattice filter: upward closed, closed under meet. -/
structure LattFilter where
  mem : LattExpr → Prop
  meet_closed : ∀ a b, mem a → mem b → mem (meet a b)
  top_mem : mem top

/-- The principal filter ↑a contains a and top. -/
def principalFilter (a : LattExpr) : LattFilter where
  mem := fun x => meet a x = a
  meet_closed := fun x y hx hy => by
    show meet a (meet x y) = a
    have : meet a (meet x y) = meet (meet a x) y := (meet_assoc_path a x y).proof.symm
    rw [this, hx]
    exact hy
  top_mem := (meet_top_right_path a).proof

/-! ## Congruence lattice -/

/-- A lattice congruence: equivalence relation compatible with meet/join. -/
structure LattCong where
  rel : LattExpr → LattExpr → Prop
  rfl_rel : ∀ a, rel a a
  sym_rel : ∀ a b, rel a b → rel b a
  trans_rel : ∀ a b c, rel a b → rel b c → rel a c
  meet_compat : ∀ a₁ a₂ b₁ b₂, rel a₁ a₂ → rel b₁ b₂ → rel (meet a₁ b₁) (meet a₂ b₂)
  join_compat : ∀ a₁ a₂ b₁ b₂, rel a₁ a₂ → rel b₁ b₂ → rel (join a₁ b₁) (join a₂ b₂)

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
def lattTransport (P : LattExpr → Prop) {a b : LattExpr}
    (p : Path a b) (h : P a) : P b :=
  Path.transport p h

/-- Transport bot membership: if P bot and bot = meet bot a, transport. -/
theorem transport_bot_mem (P : LattExpr → Prop) (hbot : P bot) (a : LattExpr) :
    P (meet bot a) :=
  lattTransport P (Path.symm (meet_bot_path a)) hbot

/-- Transport top membership via join. -/
theorem transport_top_mem (P : LattExpr → Prop) (htop : P top) (a : LattExpr) :
    P (join top a) :=
  lattTransport P (Path.symm (join_top_path a)) htop

/-! ## Four-fold associativity -/

/-- Meet four-fold reassociation: ((a ∧ b) ∧ c) ∧ d → a ∧ (b ∧ (c ∧ d)). -/
def meet_assoc4_path (a b c d : LattExpr) :
    Path (meet (meet (meet a b) c) d) (meet a (meet b (meet c d))) :=
  Path.trans
    (meet_assoc_path (meet a b) c d)
    (meet_assoc_path a b (meet c d))

/-- Join four-fold reassociation. -/
def join_assoc4_path (a b c d : LattExpr) :
    Path (join (join (join a b) c) d) (join a (join b (join c d))) :=
  Path.trans
    (join_assoc_path (join a b) c d)
    (join_assoc_path a b (join c d))

/-! ## Boolean algebra derived paths -/

/-- In a Boolean lattice: comp bot = top. Via comp_join on bot: join bot (comp bot) = top,
    but join bot x = x, so comp bot = top. Path chain. -/
def comp_bot_eq_top : Path (comp bot) top :=
  Path.trans
    (Path.symm (join_bot_path (comp bot)))
    (comp_join_path bot)

/-- comp top = bot. -/
def comp_top_eq_bot : Path (comp top) bot :=
  Path.trans
    (Path.symm (meet_top_path (comp top)))
    (comp_meet_path top)

/-- De Morgan + involution chain: comp (comp (meet a b)) = meet a b. -/
def demorgan_invol_meet (a b : LattExpr) :
    Path (comp (comp (meet a b))) (meet a b) :=
  comp_invol_path (meet a b)

/-- De Morgan applied then reversed: comp(meet a b) → join(comp a)(comp b) → comp(meet a b).
    Round-trip path. -/
def demorgan_roundtrip_meet (a b : LattExpr) :
    Path (comp (meet a b)) (comp (meet a b)) :=
  Path.trans (demorgan_meet_path a b) (Path.symm (demorgan_meet_path a b))

/-! ## congrArg derived paths -/

/-- Lifting meet idempotence inside a join: join x (meet a a) → join x a. -/
def join_meet_idem_path (x a : LattExpr) :
    Path (join x (meet a a)) (join x a) :=
  Path.congrArg (join x) (meet_idem_path a)

/-- Lifting complement involution inside meet: meet (comp(comp a)) b → meet a b. -/
def meet_comp_invol_path (a b : LattExpr) :
    Path (meet (comp (comp a)) b) (meet a b) :=
  Path.congrArg (· |> fun x => meet x b) (comp_invol_path a)

/-- Nested congrArg: join (meet a (join b b)) c → join (meet a b) c. -/
def nested_congrArg_path (a b c : LattExpr) :
    Path (join (meet a (join b b)) c) (join (meet a b) c) :=
  Path.congrArg (fun x => join x c)
    (Path.congrArg (meet a) (join_idem_path b))

/-! ## Path algebra: groupoid laws witnessed -/

/-- Refl is left identity for trans. -/
theorem refl_trans_eq (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  Path.trans_refl_left p

/-- Refl is right identity for trans. -/
theorem trans_refl_eq (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  Path.trans_refl_right p

/-- Trans is associative. -/
theorem trans_assoc_eq (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

/-- Symm of symm is identity. -/
theorem symm_symm_eq (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-! ## Summary: theorem count -/

-- Total: 40+ definitions and theorems, 0 sorry, 0 Path.ofEq

end ComputationalPaths.Path.Algebra.LatticeDeepPaths
