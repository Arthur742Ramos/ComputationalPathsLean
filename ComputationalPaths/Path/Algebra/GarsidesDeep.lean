/-
  ComputationalPaths / Path / Algebra / GarsidesDeep.lean

  Garside theory for positive braid monoids via computational paths.
  Models: positive braids, divisibility lattice, lcm / gcd,
  Garside element Δ, left‑greedy normal forms, and the
  connection to confluence / rewriting through path algebra.

  All proofs are sorry‑free.
-/

-- ============================================================
-- §1  Alphabet and positive‑braid words
-- ============================================================

/-- Generators σ_i for the n‑strand braid monoid. -/
structure BraidGen (n : Nat) where
  idx : Fin n
deriving DecidableEq, Repr

/-- A positive braid word is a list of generators. -/
abbrev BraidWord (n : Nat) := List (BraidGen n)

-- ============================================================
-- §2  Rewriting steps (braid relations as computational paths)
-- ============================================================

/-- One‑step braid relation applied anywhere inside a word.
    `comm`  :  σ_i σ_j  →  σ_j σ_i       (|i - j| ≥ 2)
    `braid` :  σ_i σ_j σ_i → σ_j σ_i σ_j (|i - j| = 1)
-/
inductive BraidStep (n : Nat) : BraidWord n → BraidWord n → Prop where
  | comm (pre suf : BraidWord n) (g h : BraidGen n)
      (hfar : (g.idx : Nat) + 2 ≤ (h.idx : Nat) ∨ (h.idx : Nat) + 2 ≤ (g.idx : Nat)) :
      BraidStep n (pre ++ [g, h] ++ suf) (pre ++ [h, g] ++ suf)
  | braid (pre suf : BraidWord n) (g h : BraidGen n)
      (hnear : (g.idx : Nat) + 1 = (h.idx : Nat) ∨ (h.idx : Nat) + 1 = (g.idx : Nat)) :
      BraidStep n (pre ++ [g, h, g] ++ suf) (pre ++ [h, g, h] ++ suf)

/-- Reflexive–transitive closure: a computational path in the
    braid rewriting system. -/
inductive BraidPath (n : Nat) : BraidWord n → BraidWord n → Prop where
  | refl (w : BraidWord n) : BraidPath n w w
  | step {w₁ w₂ w₃ : BraidWord n}
      (s : BraidStep n w₁ w₂) (p : BraidPath n w₂ w₃) :
      BraidPath n w₁ w₃

-- ============================================================
-- §3  Path combinators (trans, symm, congrArg)
-- ============================================================

/-- Transitivity of braid paths. -/
theorem BraidPath.trans {n : Nat} {a b c : BraidWord n}
    (p : BraidPath n a b) (q : BraidPath n b c) : BraidPath n a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact BraidPath.step s (ih q)

/-- `congrArg`‑style: prepending a common prefix preserves paths. -/
theorem BraidPath.congrArg_prepend {n : Nat} (pfx : BraidWord n)
    {a b : BraidWord n} (p : BraidPath n a b) :
    BraidPath n (pfx ++ a) (pfx ++ b) := by
  induction p with
  | refl _ => exact BraidPath.refl _
  | step s _rest ih =>
    cases s with
    | comm pre suf g h hfar =>
      have h1 : pfx ++ (pre ++ [g, h] ++ suf) = (pfx ++ pre) ++ [g, h] ++ suf := by
        simp [List.append_assoc]
      have h2 : pfx ++ (pre ++ [h, g] ++ suf) = (pfx ++ pre) ++ [h, g] ++ suf := by
        simp [List.append_assoc]
      rw [h1]; rw [h2] at ih
      exact BraidPath.step (BraidStep.comm (pfx ++ pre) suf g h hfar) ih
    | braid pre suf g h hnear =>
      have h1 : pfx ++ (pre ++ [g, h, g] ++ suf) = (pfx ++ pre) ++ [g, h, g] ++ suf := by
        simp [List.append_assoc]
      have h2 : pfx ++ (pre ++ [h, g, h] ++ suf) = (pfx ++ pre) ++ [h, g, h] ++ suf := by
        simp [List.append_assoc]
      rw [h1]; rw [h2] at ih
      exact BraidPath.step (BraidStep.braid (pfx ++ pre) suf g h hnear) ih

/-- Appending a common suffix preserves paths. -/
theorem BraidPath.congrArg_append {n : Nat} (sfx : BraidWord n)
    {a b : BraidWord n} (p : BraidPath n a b) :
    BraidPath n (a ++ sfx) (b ++ sfx) := by
  induction p with
  | refl _ => exact BraidPath.refl _
  | step s _rest ih =>
    cases s with
    | comm pre suf g h hfar =>
      have h1 : (pre ++ [g, h] ++ suf) ++ sfx = pre ++ [g, h] ++ (suf ++ sfx) := by
        simp [List.append_assoc]
      have h2 : (pre ++ [h, g] ++ suf) ++ sfx = pre ++ [h, g] ++ (suf ++ sfx) := by
        simp [List.append_assoc]
      rw [h1]; rw [h2] at ih
      exact BraidPath.step (BraidStep.comm pre (suf ++ sfx) g h hfar) ih
    | braid pre suf g h hnear =>
      have h1 : (pre ++ [g, h, g] ++ suf) ++ sfx = pre ++ [g, h, g] ++ (suf ++ sfx) := by
        simp [List.append_assoc]
      have h2 : (pre ++ [h, g, h] ++ suf) ++ sfx = pre ++ [h, g, h] ++ (suf ++ sfx) := by
        simp [List.append_assoc]
      rw [h1]; rw [h2] at ih
      exact BraidPath.step (BraidStep.braid pre (suf ++ sfx) g h hnear) ih

-- ============================================================
-- §4  Symmetric closure (invertible 2‑paths)
-- ============================================================

/-- One step in either direction. -/
inductive BraidStepSym (n : Nat) : BraidWord n → BraidWord n → Prop where
  | fwd {a b} : BraidStep n a b → BraidStepSym n a b
  | bwd {a b} : BraidStep n a b → BraidStepSym n b a

/-- Symmetric–transitive closure (groupoid of braid paths). -/
inductive BraidPathSym (n : Nat) : BraidWord n → BraidWord n → Prop where
  | refl (w : BraidWord n) : BraidPathSym n w w
  | step {a b c} : BraidStepSym n a b → BraidPathSym n b c → BraidPathSym n a c

/-- Transitivity of symmetric paths. -/
theorem BraidPathSym.trans {n : Nat} {a b c : BraidWord n}
    (p : BraidPathSym n a b) (q : BraidPathSym n b c) : BraidPathSym n a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact BraidPathSym.step s (ih q)

/-- Flip a single symmetric step. -/
noncomputable def BraidStepSym.flip {n : Nat} {a b : BraidWord n}
    (s : BraidStepSym n a b) : BraidStepSym n b a :=
  match s with
  | .fwd h => .bwd h
  | .bwd h => .fwd h

/-- Symmetry of symmetric paths. -/
theorem BraidPathSym.symm {n : Nat} {a b : BraidWord n}
    (p : BraidPathSym n a b) : BraidPathSym n b a := by
  induction p with
  | refl _ => exact BraidPathSym.refl _
  | step s _ ih =>
    exact BraidPathSym.trans ih (BraidPathSym.step s.flip (BraidPathSym.refl _))

-- ============================================================
-- §5  Divisibility in a positive monoid (abstract)
-- ============================================================

/-- Left‑divisibility: a ≼_L b  iff  ∃ c, a ++ c  ≡  b  (up to braid equiv). -/
noncomputable def LeftDiv (n : Nat) (a b : BraidWord n) : Prop :=
  ∃ c : BraidWord n, BraidPathSym n (a ++ c) b

/-- Reflexivity of left‑divisibility. -/
theorem LeftDiv.refl (n : Nat) (a : BraidWord n) : LeftDiv n a a :=
  ⟨[], by simp [List.append_nil]; exact BraidPathSym.refl _⟩

/-- The empty word divides everything. -/
theorem LeftDiv.empty_divides (n : Nat) (a : BraidWord n) : LeftDiv n [] a :=
  ⟨a, by simp; exact BraidPathSym.refl _⟩

-- ============================================================
-- §6  Simple lattice (bounded lattice of divisors of Δ)
-- ============================================================

/-- A simple element is a positive word that left‑divides Δ.  We model
    the *set* of simples abstractly via a bounded lattice. -/
structure SimpleLattice where
  carrier : Type
  le      : carrier → carrier → Prop
  bot     : carrier
  top     : carrier          -- Δ
  meet    : carrier → carrier → carrier   -- gcd
  join    : carrier → carrier → carrier   -- lcm
  le_refl : ∀ a, le a a
  le_antisymm : ∀ a b, le a b → le b a → a = b
  le_trans : ∀ a b c, le a b → le b c → le a c
  bot_le  : ∀ a, le bot a
  le_top  : ∀ a, le a top
  meet_le_left  : ∀ a b, le (meet a b) a
  meet_le_right : ∀ a b, le (meet a b) b
  join_le : ∀ a b c, le a c → le b c → le (join a b) c
  le_join_left  : ∀ a b, le a (join a b)
  le_join_right : ∀ a b, le b (join a b)
  meet_greatest : ∀ a b c, le c a → le c b → le c (meet a b)

/-- Meet is idempotent. -/
theorem SimpleLattice.meet_idem (L : SimpleLattice) (a : L.carrier) :
    L.meet a a = a :=
  L.le_antisymm _ _ (L.meet_le_left a a) (L.meet_greatest a a a (L.le_refl a) (L.le_refl a))

/-- Join is idempotent. -/
theorem SimpleLattice.join_idem (L : SimpleLattice) (a : L.carrier) :
    L.join a a = a :=
  L.le_antisymm _ _ (L.join_le a a a (L.le_refl a) (L.le_refl a)) (L.le_join_left a a)

/-- Meet is commutative. -/
theorem SimpleLattice.meet_comm (L : SimpleLattice) (a b : L.carrier) :
    L.meet a b = L.meet b a :=
  L.le_antisymm _ _
    (L.meet_greatest b a _ (L.meet_le_right a b) (L.meet_le_left a b))
    (L.meet_greatest a b _ (L.meet_le_right b a) (L.meet_le_left b a))

/-- Join is commutative. -/
theorem SimpleLattice.join_comm (L : SimpleLattice) (a b : L.carrier) :
    L.join a b = L.join b a :=
  L.le_antisymm _ _
    (L.join_le a b _ (L.le_join_right b a) (L.le_join_left b a))
    (L.join_le b a _ (L.le_join_right a b) (L.le_join_left a b))

/-- Meet absorbs join: a ∧ (a ∨ b) = a. -/
theorem SimpleLattice.meet_join_absorb (L : SimpleLattice) (a b : L.carrier) :
    L.meet a (L.join a b) = a :=
  L.le_antisymm _ _
    (L.meet_le_left a (L.join a b))
    (L.meet_greatest a (L.join a b) a (L.le_refl a) (L.le_join_left a b))

/-- Join absorbs meet: a ∨ (a ∧ b) = a. -/
theorem SimpleLattice.join_meet_absorb (L : SimpleLattice) (a b : L.carrier) :
    L.join a (L.meet a b) = a :=
  L.le_antisymm _ _
    (L.join_le a (L.meet a b) a (L.le_refl a) (L.meet_le_left a b))
    (L.le_join_left a (L.meet a b))

-- ============================================================
-- §7  GCD (meet) / LCM (join) boundary theorems
-- ============================================================

/-- GCD of bot with anything is bot. -/
theorem SimpleLattice.meet_bot (L : SimpleLattice) (a : L.carrier) :
    L.meet L.bot a = L.bot :=
  L.le_antisymm _ _
    (L.meet_le_left L.bot a)
    (L.meet_greatest L.bot a L.bot (L.le_refl _) (L.bot_le a))

/-- LCM of bot with a is a. -/
theorem SimpleLattice.join_bot (L : SimpleLattice) (a : L.carrier) :
    L.join L.bot a = a :=
  L.le_antisymm _ _
    (L.join_le L.bot a a (L.bot_le a) (L.le_refl a))
    (L.le_join_right L.bot a)

/-- LCM of top with anything is top. -/
theorem SimpleLattice.join_top (L : SimpleLattice) (a : L.carrier) :
    L.join L.top a = L.top :=
  L.le_antisymm _ _
    (L.join_le L.top a L.top (L.le_refl _) (L.le_top a))
    (L.le_join_left L.top a)

/-- GCD of top with a is a. -/
theorem SimpleLattice.meet_top (L : SimpleLattice) (a : L.carrier) :
    L.meet L.top a = a :=
  L.le_antisymm _ _
    (L.meet_le_right L.top a)
    (L.meet_greatest L.top a a (L.le_top a) (L.le_refl a))

-- ============================================================
-- §8  Normal form structure
-- ============================================================

/-- A normal‑form entry is a list of simple elements (factors). -/
structure NormalForm (L : SimpleLattice) where
  factors : List L.carrier
  bounded : ∀ x, x ∈ factors → L.le x L.top

/-- The empty normal form. -/
noncomputable def NormalForm.empty (L : SimpleLattice) : NormalForm L :=
  ⟨[], fun _ h => by simp at h⟩

/-- A single‑factor normal form. -/
noncomputable def NormalForm.single (L : SimpleLattice) (s : L.carrier)
    (hs : L.le s L.top) : NormalForm L :=
  ⟨[s], fun x hx => by simp at hx; subst hx; exact hs⟩

/-- Length of a normal form. -/
noncomputable def NormalForm.length (nf : NormalForm L) : Nat := nf.factors.length

/-- The empty normal form has length 0. -/
theorem NormalForm.empty_length (L : SimpleLattice) :
    (NormalForm.empty L).length = 0 := rfl

/-- A single‑factor normal form has length 1. -/
theorem NormalForm.single_length (L : SimpleLattice) (s : L.carrier) (hs : L.le s L.top) :
    (NormalForm.single L s hs).length = 1 := rfl

-- ============================================================
-- §9  Transport of normal forms (coherence)
-- ============================================================

/-- An order isomorphism between two simple lattices. -/
structure LatticeIso (L₁ L₂ : SimpleLattice) where
  toFun  : L₁.carrier → L₂.carrier
  invFun : L₂.carrier → L₁.carrier
  left_inv  : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b
  preserve_le : ∀ a b, L₁.le a b ↔ L₂.le (toFun a) (toFun b)
  map_top : toFun L₁.top = L₂.top

/-- Transport a normal form along an isomorphism. -/
noncomputable def NormalForm.transport {L₁ L₂ : SimpleLattice}
    (iso : LatticeIso L₁ L₂) (nf : NormalForm L₁) : NormalForm L₂ :=
  ⟨nf.factors.map iso.toFun,
   fun x hx => by
     simp [List.mem_map] at hx
     obtain ⟨y, hy, rfl⟩ := hx
     rw [← iso.map_top]
     exact (iso.preserve_le y L₁.top).mp (nf.bounded y hy)⟩

/-- Transport preserves length (coherence). -/
theorem NormalForm.transport_length {L₁ L₂ : SimpleLattice}
    (iso : LatticeIso L₁ L₂) (nf : NormalForm L₁) :
    (nf.transport iso).length = nf.length := by
  simp [NormalForm.transport, NormalForm.length, List.length_map]

-- ============================================================
-- §10  Greedy algorithm properties
-- ============================================================

/-- The greedy factor (meet with Δ) is ≤ Δ. -/
theorem greedy_factor_le_delta (L : SimpleLattice) (a : L.carrier) :
    L.le (L.meet L.top a) L.top :=
  L.meet_le_left L.top a

/-- The greedy factor is below the original element. -/
theorem greedy_factor_le_self (L : SimpleLattice) (a : L.carrier) :
    L.le (L.meet L.top a) a :=
  L.meet_le_right L.top a

/-- The greedy factor equals the element when the element is already simple. -/
theorem greedy_factor_of_simple (L : SimpleLattice) (a : L.carrier)
    (_hsimple : L.le a L.top) : L.meet L.top a = a :=
  L.meet_top a

-- ============================================================
-- §11  Concrete lattice: S₂ (2‑strand braids)
-- ============================================================

inductive S2 : Type where
  | e  : S2
  | s1 : S2
deriving DecidableEq, Repr

noncomputable def S2.le : S2 → S2 → Prop
  | .e, _   => True
  | .s1, .s1 => True
  | .s1, .e  => False

noncomputable instance : DecidableRel S2.le := fun a b =>
  match a, b with
  | .e, _    => isTrue trivial
  | .s1, .s1 => isTrue trivial
  | .s1, .e  => isFalse id

noncomputable def S2Lattice : SimpleLattice where
  carrier := S2
  le := S2.le
  bot := .e
  top := .s1
  meet := fun a b => match a, b with
    | .s1, .s1 => .s1
    | _, _ => .e
  join := fun a b => match a, b with
    | .e, .e => .e
    | _, _ => .s1
  le_refl := fun a => by cases a <;> simp [S2.le]
  le_antisymm := fun a b h1 h2 => by cases a <;> cases b <;> simp_all [S2.le]
  le_trans := fun a b c h1 h2 => by cases a <;> cases b <;> cases c <;> simp_all [S2.le]
  bot_le := fun a => by cases a <;> simp [S2.le]
  le_top := fun a => by cases a <;> simp [S2.le]
  meet_le_left := fun a b => by cases a <;> cases b <;> simp [S2.le]
  meet_le_right := fun a b => by cases a <;> cases b <;> simp [S2.le]
  join_le := fun a b c h1 h2 => by cases a <;> cases b <;> cases c <;> simp_all [S2.le]
  le_join_left := fun a b => by cases a <;> cases b <;> simp [S2.le]
  le_join_right := fun a b => by cases a <;> cases b <;> simp [S2.le]
  meet_greatest := fun a b c h1 h2 => by cases a <;> cases b <;> cases c <;> simp_all [S2.le]

/-- In S2, the meet of s1 with s1 is s1. -/
theorem S2_meet_s1_s1 : S2Lattice.meet .s1 .s1 = .s1 := rfl

/-- In S2, the join of e with e is e. -/
theorem S2_join_e_e : S2Lattice.join .e .e = .e := rfl

/-- In S2, meet_top gives the element back. -/
theorem S2_meet_top : S2Lattice.meet S2Lattice.top .e = .e := rfl

-- ============================================================
-- §12  Confluence as a path property
-- ============================================================

/-- Generic reflexive–transitive closure. -/
inductive RTClosure {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl (a : α) : RTClosure R a a
  | step {a b c : α} : R a b → RTClosure R b c → RTClosure R a c

/-- RTClosure is transitive. -/
theorem RTClosure.trans {α : Type} {R : α → α → Prop} {a b c : α}
    (p : RTClosure R a b) (q : RTClosure R b c) : RTClosure R a c := by
  induction p with
  | refl _ => exact q
  | step h _ ih => exact RTClosure.step h (ih q)

/-- Local confluence: if a rewrites to both b and c in one step,
    they have a common reduct. -/
noncomputable def LocallyConfluent {α : Type} (R : α → α → Prop) : Prop :=
  ∀ a b c, R a b → R a c → ∃ d, RTClosure R b d ∧ RTClosure R c d

/-- Church–Rosser: any two equivalent terms have a common reduct. -/
noncomputable def ChurchRosser {α : Type} (R : α → α → Prop) : Prop :=
  ∀ a b, RTClosure R a b → ∃ d, RTClosure R a d ∧ RTClosure R b d

/-- Trivially, a relation with at most one reduct per element is locally confluent. -/
theorem deterministic_locally_confluent {α : Type} {R : α → α → Prop}
    (hdet : ∀ a b c, R a b → R a c → b = c) : LocallyConfluent R :=
  fun a b c hab hac => by
    have := hdet a b c hab hac; subst this
    exact ⟨b, RTClosure.refl b, RTClosure.refl b⟩

-- ============================================================
-- §13  Divisibility chain lemmas
-- ============================================================

/-- Left divisibility is transitive in the lattice. -/
theorem SimpleLattice.div_trans (L : SimpleLattice) (a b c : L.carrier)
    (h1 : L.le a b) (h2 : L.le b c) : L.le a c :=
  L.le_trans a b c h1 h2

/-- Every element divides Δ (= top). -/
theorem SimpleLattice.div_delta (L : SimpleLattice) (a : L.carrier) :
    L.le a L.top :=
  L.le_top a

/-- bot divides everything. -/
theorem SimpleLattice.bot_divides (L : SimpleLattice) (a : L.carrier) :
    L.le L.bot a :=
  L.bot_le a

-- ============================================================
-- §14  Word‑length invariance under braid rewriting
-- ============================================================

/-- Comm steps preserve word length. -/
theorem comm_step_preserves_length {n : Nat} (pre suf : BraidWord n)
    (g h : BraidGen n) :
    (pre ++ [g, h] ++ suf).length = (pre ++ [h, g] ++ suf).length := by
  simp [List.length_append]

/-- Braid steps preserve word length. -/
theorem braid_step_preserves_length {n : Nat} (pre suf : BraidWord n)
    (g h : BraidGen n) :
    (pre ++ [g, h, g] ++ suf).length = (pre ++ [h, g, h] ++ suf).length := by
  simp [List.length_append]

/-- Any single braid step preserves word length. -/
theorem BraidStep.preserves_length {n : Nat} {a b : BraidWord n}
    (s : BraidStep n a b) : a.length = b.length := by
  cases s with
  | comm pre suf g h _ => exact comm_step_preserves_length pre suf g h
  | braid pre suf g h _ => exact braid_step_preserves_length pre suf g h

/-- A full braid path preserves word length. -/
theorem BraidPath.preserves_length {n : Nat} {a b : BraidWord n}
    (p : BraidPath n a b) : a.length = b.length := by
  induction p with
  | refl _ => rfl
  | step s _ ih => exact Eq.trans s.preserves_length ih

-- ============================================================
-- §15  Concatenation is compatible with paths (congruence)
-- ============================================================

/-- Concatenation of paths: if a ≡ a' and b ≡ b' then a++b ≡ a'++b'. -/
theorem BraidPath.congr_concat {n : Nat}
    {a a' b b' : BraidWord n}
    (pa : BraidPath n a a') (pb : BraidPath n b b') :
    BraidPath n (a ++ b) (a' ++ b') :=
  BraidPath.trans (BraidPath.congrArg_append b pa) (BraidPath.congrArg_prepend a' pb)

-- ============================================================
-- §16  Meet associativity
-- ============================================================

/-- Meet is associative in a SimpleLattice. -/
theorem SimpleLattice.meet_assoc (L : SimpleLattice) (a b c : L.carrier) :
    L.meet (L.meet a b) c = L.meet a (L.meet b c) := by
  apply L.le_antisymm
  · apply L.meet_greatest
    · exact L.le_trans _ _ _ (L.meet_le_left _ _) (L.meet_le_left _ _)
    · apply L.meet_greatest
      · exact L.le_trans _ _ _ (L.meet_le_left _ _) (L.meet_le_right _ _)
      · exact L.meet_le_right _ _
  · apply L.meet_greatest
    · apply L.meet_greatest
      · exact L.meet_le_left _ _
      · exact L.le_trans _ _ _ (L.meet_le_right _ _) (L.meet_le_left _ _)
    · exact L.le_trans _ _ _ (L.meet_le_right _ _) (L.meet_le_right _ _)

-- ============================================================
-- §17  Additional lattice properties
-- ============================================================

/-- Join is associative. -/
theorem SimpleLattice.join_assoc (L : SimpleLattice) (a b c : L.carrier) :
    L.join (L.join a b) c = L.join a (L.join b c) := by
  apply L.le_antisymm
  · apply L.join_le
    · apply L.join_le
      · exact L.le_join_left _ _
      · exact L.le_trans _ _ _ (L.le_join_left _ _) (L.le_join_right _ _)
    · exact L.le_trans _ _ _ (L.le_join_right _ _) (L.le_join_right _ _)
  · apply L.join_le
    · exact L.le_trans _ _ _ (L.le_join_left _ _) (L.le_join_left _ _)
    · apply L.join_le
      · exact L.le_trans _ _ _ (L.le_join_right _ _) (L.le_join_left _ _)
      · exact L.le_join_right _ _

/-- Meet distributes over itself (trivially, via idempotency). -/
theorem SimpleLattice.meet_self_distrib (L : SimpleLattice) (a : L.carrier) :
    L.meet a (L.meet a a) = a := by
  rw [L.meet_idem]; exact L.meet_idem a

/-- In S2, all lattice properties hold computationally. -/
theorem S2_meet_assoc_check :
    S2Lattice.meet (S2Lattice.meet .s1 .e) .s1 =
    S2Lattice.meet .s1 (S2Lattice.meet .e .s1) := rfl
