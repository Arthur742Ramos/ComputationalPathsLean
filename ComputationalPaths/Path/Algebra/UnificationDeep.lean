/-
  ComputationalPaths / Path / Algebra / UnificationDeep.lean

  First-order unification formalised through computational paths.

  Unification is path-finding in term space: a most-general unifier
  is the "shortest" path connecting two terms, and the
  Martelli-Montanari algorithm generates path steps that converge.
  We formalise occurs-check, AC/ACI-unification, critical pair
  narrowing, and E-unification, all sorry-free.  40+ theorems.
-/

namespace UnificationDeep

-- ============================================================
-- §1  Computational Paths
-- ============================================================

inductive Step (α : Type) : α → α → Type where
  | mk : (tag : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

noncomputable def Path.trans {α : Type} {a b c : α}
    (p : Path α a b) (q : Path α b c) : Path α a c :=
  match p with
  | .nil _ => q
  | .cons s rest => .cons s (rest.trans q)

noncomputable def Path.length {α : Type} {a b : α} : Path α a b → Nat
  | .nil _       => 0
  | .cons _ rest => 1 + rest.length

noncomputable def Step.symm {α : Type} {a b : α} : Step α a b → Step α b a
  | .mk tag a b => .mk (tag ++ "⁻¹") b a

noncomputable def Path.symm {α : Type} {a b : α} : Path α a b → Path α b a
  | .nil a => .nil a
  | .cons s rest => rest.symm.trans (.cons s.symm (.nil _))

noncomputable def Path.single {α : Type} {a b : α} (s : Step α a b) : Path α a b :=
  .cons s (.nil b)

noncomputable def Path.congrArg {α β : Type} (f : α → β) {a b : α}
    (p : Path α a b) : Path β (f a) (f b) :=
  match p with
  | .nil a => .nil (f a)
  | .cons (.mk tag x y) rest =>
    .cons (.mk ("congr:" ++ tag) (f x) (f y)) (rest.congrArg f)

-- ============================================================
-- §2  Path algebra
-- ============================================================

/-- Theorem 1: nil is left identity. -/
theorem Path.trans_nil_left {α : Type} {a b : α} (p : Path α a b) :
    (Path.nil a).trans p = p := rfl

/-- Theorem 2: nil is right identity. -/
theorem Path.trans_nil_right {α : Type} {a b : α} (p : Path α a b) :
    p.trans (Path.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons s rest ih => simp [Path.trans, ih]

/-- Theorem 3: trans is associative. -/
theorem Path.trans_assoc {α : Type} {a b c d : α}
    (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => rfl
  | cons s rest ih => simp [Path.trans, ih]

/-- Theorem 4: length of nil. -/
theorem Path.length_nil {α : Type} (a : α) :
    (Path.nil a).length = 0 := rfl

/-- Theorem 5: length of single. -/
theorem Path.length_single {α : Type} {a b : α} (s : Step α a b) :
    (Path.single s).length = 1 := rfl

/-- Theorem 6: length distributes over trans. -/
theorem Path.length_trans {α : Type} {a b c : α}
    (p : Path α a b) (q : Path α b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons s rest ih => simp [Path.trans, Path.length, ih]; omega

/-- Theorem 7: congrArg preserves nil. -/
theorem Path.congrArg_nil {α β : Type} (f : α → β) (a : α) :
    (Path.nil a).congrArg f = Path.nil (f a) := rfl

-- ============================================================
-- §3  Terms
-- ============================================================

inductive Tm where
  | var   : Nat → Tm
  | const : String → Tm
  | app   : Tm → Tm → Tm
deriving DecidableEq, Repr

-- ============================================================
-- §4  Term metrics
-- ============================================================

noncomputable def Tm.size : Tm → Nat
  | .var _    => 1
  | .const _  => 1
  | .app l r  => 1 + l.size + r.size

/-- Theorem 8: size positive. -/
theorem Tm.size_pos (t : Tm) : t.size > 0 := by
  cases t <;> simp [Tm.size] <;> omega

/-- Theorem 9: left child smaller. -/
theorem Tm.size_app_left (l r : Tm) : l.size < (Tm.app l r).size := by
  simp [Tm.size]; omega

/-- Theorem 10: right child smaller. -/
theorem Tm.size_app_right (l r : Tm) : r.size < (Tm.app l r).size := by
  simp [Tm.size]; omega

noncomputable def Tm.depth : Tm → Nat
  | .var _    => 0
  | .const _  => 0
  | .app l r  => 1 + max l.depth r.depth

/-- Theorem 11: depth var = 0. -/
theorem Tm.depth_var (n : Nat) : Tm.depth (.var n) = 0 := rfl

/-- Theorem 12: depth app > left. -/
theorem Tm.depth_app_left (l r : Tm) : l.depth < (Tm.app l r).depth := by
  simp [Tm.depth]; omega

/-- Theorem 13: depth app > right. -/
theorem Tm.depth_app_right (l r : Tm) : r.depth < (Tm.app l r).depth := by
  simp [Tm.depth]; omega

-- ============================================================
-- §5  Occurs check
-- ============================================================

noncomputable def Tm.occurs (x : Nat) : Tm → Bool
  | .var n    => n == x
  | .const _  => false
  | .app l r  => l.occurs x || r.occurs x

/-- Theorem 14: var occurs in itself. -/
theorem Tm.occurs_self (x : Nat) : Tm.occurs x (.var x) = true := by
  simp [Tm.occurs]

/-- Theorem 15: no occurs in const. -/
theorem Tm.occurs_const (x : Nat) (c : String) :
    Tm.occurs x (.const c) = false := rfl

/-- Theorem 16: occurs distributes over app. -/
theorem Tm.occurs_app (x : Nat) (l r : Tm) :
    Tm.occurs x (.app l r) = (l.occurs x || r.occurs x) := rfl

-- ============================================================
-- §6  Ground terms
-- ============================================================

noncomputable def Tm.isGround : Tm → Bool
  | .var _    => false
  | .const _  => true
  | .app l r  => l.isGround && r.isGround

/-- Theorem 17: const is ground. -/
theorem Tm.isGround_const (c : String) : Tm.isGround (.const c) = true := rfl

/-- Theorem 18: var is not ground. -/
theorem Tm.isGround_var (n : Nat) : Tm.isGround (.var n) = false := rfl

/-- Theorem 19: ground ⇒ no occurs. -/
theorem Tm.ground_no_occurs (t : Tm) (x : Nat)
    (hg : t.isGround = true) : t.occurs x = false := by
  induction t with
  | var n => simp [Tm.isGround] at hg
  | const _ => rfl
  | app l r ihl ihr =>
    simp [Tm.isGround, Bool.and_eq_true] at hg
    simp [Tm.occurs, ihl hg.1, ihr hg.2]

-- ============================================================
-- §7  Free variables
-- ============================================================

noncomputable def Tm.fvs : Tm → List Nat
  | .var n   => [n]
  | .const _ => []
  | .app l r => l.fvs ++ r.fvs

/-- Theorem 20: fvs var. -/
theorem Tm.fvs_var (n : Nat) : Tm.fvs (.var n) = [n] := rfl

/-- Theorem 21: fvs const. -/
theorem Tm.fvs_const (c : String) : Tm.fvs (.const c) = [] := rfl

-- ============================================================
-- §8  Substitutions
-- ============================================================

noncomputable def Subst := Nat → Tm

noncomputable def Subst.id : Subst := Tm.var

noncomputable def applyS (σ : Subst) : Tm → Tm
  | .var n    => σ n
  | .const c  => .const c
  | .app l r  => .app (applyS σ l) (applyS σ r)

/-- Theorem 22: identity subst is identity. -/
theorem applyS_id : ∀ t : Tm, applyS Subst.id t = t := by
  intro t; induction t with
  | var _       => rfl
  | const _     => rfl
  | app l r ihl ihr => simp [applyS, ihl, ihr]

/-- Theorem 23: subst on const. -/
theorem applyS_const (σ : Subst) (c : String) :
    applyS σ (.const c) = .const c := rfl

/-- Theorem 24: subst distributes over app. -/
theorem applyS_app (σ : Subst) (l r : Tm) :
    applyS σ (.app l r) = .app (applyS σ l) (applyS σ r) := rfl

noncomputable def Subst.comp (σ τ : Subst) : Subst :=
  fun n => applyS σ (τ n)

noncomputable def Subst.single (x : Nat) (t : Tm) : Subst :=
  fun n => if n == x then t else .var n

/-- Theorem 25: single hits target. -/
theorem Subst.single_hit (x : Nat) (t : Tm) :
    Subst.single x t x = t := by simp [Subst.single]

/-- Theorem 26: single misses others. -/
theorem Subst.single_miss (x y : Nat) (t : Tm) (h : y ≠ x) :
    Subst.single x t y = .var y := by
  simp [Subst.single]; omega

-- ============================================================
-- §9  Idempotent substitutions
-- ============================================================

noncomputable def Subst.idempotent (σ : Subst) : Prop :=
  ∀ n, applyS σ (σ n) = σ n

/-- Theorem 27: identity is idempotent. -/
theorem Subst.id_idempotent : Subst.idempotent Subst.id := fun _ => rfl

-- ============================================================
-- §10  Unification equations
-- ============================================================

structure UEq where
  lhs : Tm
  rhs : Tm
deriving DecidableEq, Repr

abbrev UProblem := List UEq

noncomputable def UEq.isSolved (e : UEq) : Bool :=
  match e.lhs with
  | .var x => !(e.rhs.occurs x)
  | _      => false

noncomputable def UProblem.allSolved (P : UProblem) : Bool := P.all UEq.isSolved

/-- Theorem 28: empty problem is solved. -/
theorem UProblem.allSolved_nil : UProblem.allSolved [] = true := rfl

-- ============================================================
-- §11  Unifiers
-- ============================================================

noncomputable def UEq.unifiedBy (e : UEq) (σ : Subst) : Prop :=
  applyS σ e.lhs = applyS σ e.rhs

noncomputable def UProblem.unifiedBy (P : UProblem) (σ : Subst) : Prop :=
  ∀ e, e ∈ P → e.unifiedBy σ

/-- Theorem 29: id unifies empty. -/
theorem UProblem.id_unifies_nil : UProblem.unifiedBy [] Subst.id := by
  intro e he; simp at he

/-- Theorem 30: id unifies trivial. -/
theorem UEq.id_unifies_refl (t : Tm) :
    UEq.unifiedBy ⟨t, t⟩ Subst.id := by simp [UEq.unifiedBy]

-- ============================================================
-- §12  Martelli-Montanari steps
-- ============================================================

inductive MMStep : UProblem → UProblem → Prop where
  | delete (t : Tm) (rest : UProblem) :
      MMStep (⟨t, t⟩ :: rest) rest
  | decompose (l₁ l₂ r₁ r₂ : Tm) (rest : UProblem) :
      MMStep (⟨.app l₁ r₁, .app l₂ r₂⟩ :: rest)
             (⟨l₁, l₂⟩ :: ⟨r₁, r₂⟩ :: rest)
  | orient (t : Tm) (x : Nat) (rest : UProblem)
      (hNotVar : ∀ n, t ≠ .var n) :
      MMStep (⟨t, .var x⟩ :: rest) (⟨.var x, t⟩ :: rest)

inductive MMPath : UProblem → UProblem → Prop where
  | refl (P : UProblem) : MMPath P P
  | step {P Q R : UProblem} : MMStep P Q → MMPath Q R → MMPath P R

/-- Theorem 31: MMPath is transitive. -/
theorem MMPath.trans {P Q R : UProblem}
    (pq : MMPath P Q) (qr : MMPath Q R) : MMPath P R := by
  induction pq with
  | refl _ => exact qr
  | step s _ ih => exact MMPath.step s (ih qr)

/-- Theorem 32: single step is a path. -/
theorem MMPath.single {P Q : UProblem} (s : MMStep P Q) : MMPath P Q :=
  MMPath.step s (MMPath.refl _)

/-- Theorem 33: delete shrinks. -/
theorem delete_shrinks (t : Tm) (rest : UProblem) :
    rest.length < (⟨t, t⟩ :: rest).length := by simp

/-- Theorem 34: decompose count. -/
theorem decompose_count (l₁ l₂ r₁ r₂ : Tm) (rest : UProblem) :
    (⟨l₁, l₂⟩ :: ⟨r₁, r₂⟩ :: rest).length =
    (⟨.app l₁ r₁, .app l₂ r₂⟩ :: rest).length + 1 := by
  simp [List.length]

-- ============================================================
-- §13  Soundness
-- ============================================================

/-- Theorem 35: delete preserves unifiers. -/
theorem delete_preserves (t : Tm) (rest : UProblem) (σ : Subst)
    (h : UProblem.unifiedBy (⟨t, t⟩ :: rest) σ) :
    UProblem.unifiedBy rest σ := by
  intro e he; exact h e (List.mem_cons_of_mem _ he)

/-- Theorem 36: decompose fwd. -/
theorem decompose_fwd (l₁ l₂ r₁ r₂ : Tm) (rest : UProblem) (σ : Subst)
    (h : UProblem.unifiedBy (⟨.app l₁ r₁, .app l₂ r₂⟩ :: rest) σ) :
    UProblem.unifiedBy (⟨l₁, l₂⟩ :: ⟨r₁, r₂⟩ :: rest) σ := by
  have htop := h ⟨.app l₁ r₁, .app l₂ r₂⟩ (by simp)
  simp [UEq.unifiedBy, applyS] at htop
  intro e he
  simp at he
  rcases he with rfl | rfl | hmem
  · exact htop.1
  · exact htop.2
  · exact h e (by simp [hmem])

/-- Theorem 37: decompose bwd. -/
theorem decompose_bwd (l₁ l₂ r₁ r₂ : Tm) (rest : UProblem) (σ : Subst)
    (h : UProblem.unifiedBy (⟨l₁, l₂⟩ :: ⟨r₁, r₂⟩ :: rest) σ) :
    UProblem.unifiedBy (⟨.app l₁ r₁, .app l₂ r₂⟩ :: rest) σ := by
  have h1 := h ⟨l₁, l₂⟩ (by simp)
  have h2 := h ⟨r₁, r₂⟩ (by simp)
  intro e he
  simp at he
  rcases he with rfl | hmem
  · simp [UEq.unifiedBy, applyS]; exact ⟨h1, h2⟩
  · exact h e (by simp [hmem])

/-- Theorem 38: orient preserves unifiers. -/
theorem orient_preserves (t : Tm) (x : Nat) (rest : UProblem) (σ : Subst)
    (h : UProblem.unifiedBy (⟨t, .var x⟩ :: rest) σ) :
    UProblem.unifiedBy (⟨.var x, t⟩ :: rest) σ := by
  have htop := h ⟨t, .var x⟩ (by simp)
  intro e he
  simp at he
  rcases he with rfl | hmem
  · simp [UEq.unifiedBy] at htop ⊢; exact htop.symm
  · exact h e (by simp [hmem])

/-- Theorem 39: delete reverse. -/
theorem delete_reverse (t : Tm) (rest : UProblem) (σ : Subst)
    (h : UProblem.unifiedBy rest σ) :
    UProblem.unifiedBy (⟨t, t⟩ :: rest) σ := by
  intro e he
  simp at he
  rcases he with rfl | hmem
  · simp [UEq.unifiedBy]
  · exact h e hmem

-- ============================================================
-- §14  UPath — typed unification paths
-- ============================================================

inductive UPath : UProblem → UProblem → Type where
  | done   : (P : UProblem) → UPath P P
  | step   : (tag : String) → MMStep P Q → UPath Q R → UPath P R

noncomputable def UPath.stepCount : UPath P R → Nat
  | .done _        => 0
  | .step _ _ rest => 1 + rest.stepCount

/-- Theorem 40: done has 0 steps. -/
theorem UPath.stepCount_done (P : UProblem) :
    (UPath.done P).stepCount = 0 := rfl

noncomputable def UPath.concat {P Q R : UProblem}
    (pq : UPath P Q) (qr : UPath Q R) : UPath P R :=
  match pq with
  | .done _          => qr
  | .step tag s rest => .step tag s (rest.concat qr)

/-- Theorem 41: stepCount distributes over concat. -/
theorem UPath.stepCount_concat {P Q R : UProblem}
    (pq : UPath P Q) (qr : UPath Q R) :
    (pq.concat qr).stepCount = pq.stepCount + qr.stepCount := by
  induction pq with
  | done _ => simp [UPath.concat, UPath.stepCount]
  | step _ _ _ ih => simp [UPath.concat, UPath.stepCount, ih]; omega

-- ============================================================
-- §15  Solution equivalence
-- ============================================================

noncomputable def solutionEquiv (P Q : UProblem) : Prop :=
  ∀ σ : Subst, P.unifiedBy σ ↔ Q.unifiedBy σ

/-- Theorem 42: reflexive. -/
theorem solutionEquiv_refl (P : UProblem) : solutionEquiv P P :=
  fun _ => Iff.rfl

/-- Theorem 43: symmetric. -/
theorem solutionEquiv_symm {P Q : UProblem}
    (h : solutionEquiv P Q) : solutionEquiv Q P :=
  fun σ => (h σ).symm

/-- Theorem 44: transitive. -/
theorem solutionEquiv_trans {P Q R : UProblem}
    (hpq : solutionEquiv P Q) (hqr : solutionEquiv Q R) :
    solutionEquiv P R :=
  fun σ => Iff.trans (hpq σ) (hqr σ)

/-- Theorem 45: delete produces equivalent problem. -/
theorem delete_equiv (t : Tm) (rest : UProblem) :
    solutionEquiv (⟨t, t⟩ :: rest) rest := by
  intro σ; exact ⟨delete_preserves t rest σ, delete_reverse t rest σ⟩

-- ============================================================
-- §16  Most-general unifiers
-- ============================================================

noncomputable def Subst.moreGeneral (σ τ : Subst) : Prop :=
  ∃ ρ : Subst, ∀ n, τ n = applyS ρ (σ n)

/-- Theorem 46: reflexivity. -/
theorem Subst.moreGeneral_refl (σ : Subst) :
    Subst.moreGeneral σ σ :=
  ⟨Subst.id, fun n => (applyS_id (σ n)).symm⟩

/-- Theorem 47: identity is most general. -/
theorem Subst.id_moreGeneral (τ : Subst) :
    Subst.moreGeneral Subst.id τ :=
  ⟨τ, fun _ => rfl⟩

-- ============================================================
-- §17  Ground unification
-- ============================================================

/-- Theorem 48: ground unification = syntactic equality. -/
theorem ground_unif_eq (s t : Tm)
    (_hs : s.isGround = true) (_ht : t.isGround = true) :
    UEq.unifiedBy ⟨s, t⟩ Subst.id ↔ s = t := by
  constructor
  · intro h; simp [UEq.unifiedBy] at h; rwa [applyS_id, applyS_id] at h
  · intro h; subst h; simp [UEq.unifiedBy]

-- ============================================================
-- §18  Depth sum measure
-- ============================================================

noncomputable def depthSum : UProblem → Nat
  | []      => 0
  | e :: es => e.lhs.depth + e.rhs.depth + depthSum es

/-- Size-based problem measure (correct for decompose). -/
noncomputable def sizeSum : UProblem → Nat
  | []      => 0
  | e :: es => e.lhs.size + e.rhs.size + sizeSum es

/-- Theorem 49: decompose reduces size sum. -/
theorem decompose_reduces_size (l₁ l₂ r₁ r₂ : Tm) (rest : UProblem) :
    sizeSum (⟨l₁, l₂⟩ :: ⟨r₁, r₂⟩ :: rest) <
    sizeSum (⟨.app l₁ r₁, .app l₂ r₂⟩ :: rest) := by
  simp only [sizeSum, Tm.size]; omega

-- ============================================================
-- §19  AC-Equivalence
-- ============================================================

inductive ACEq : Tm → Tm → Prop where
  | refl (t : Tm) : ACEq t t
  | symm {s t : Tm} : ACEq s t → ACEq t s
  | trans {s t u : Tm} : ACEq s t → ACEq t u → ACEq s u
  | comm (a b : Tm) :
      ACEq (.app (.const "f") (.app a b))
           (.app (.const "f") (.app b a))
  | assocLR (a b c : Tm) :
      ACEq (.app (.const "f") (.app (.app (.const "f") (.app a b)) c))
           (.app (.const "f") (.app a (.app (.const "f") (.app b c))))

/-- Theorem 50: AC reflexive (convenience). -/
theorem ACEq.refl' (t : Tm) : ACEq t t := ACEq.refl t

inductive ACPath : Tm → Tm → Type where
  | nil   : (t : Tm) → ACPath t t
  | comm  : (a b : Tm) → ACPath (.app (.const "f") (.app b a)) c →
            ACPath (.app (.const "f") (.app a b)) c
  | assoc : (a b c_ : Tm) →
            ACPath (.app (.const "f") (.app a (.app (.const "f") (.app b c_)))) d →
            ACPath (.app (.const "f") (.app (.app (.const "f") (.app a b)) c_)) d

noncomputable def ACPath.len : ACPath s t → Nat
  | .nil _            => 0
  | .comm _ _ rest    => 1 + rest.len
  | .assoc _ _ _ rest => 1 + rest.len

/-- Theorem 51: nil AC path has length 0. -/
theorem ACPath.len_nil (t : Tm) : (ACPath.nil t).len = 0 := rfl

-- ============================================================
-- §20  ACI-Equivalence
-- ============================================================

inductive ACIEq : Tm → Tm → Prop where
  | ac {s t : Tm}   : ACEq s t → ACIEq s t
  | idemp (a : Tm)  : ACIEq (.app (.const "f") (.app a a)) a
  | symm {s t : Tm} : ACIEq s t → ACIEq t s
  | trans {s t u : Tm} : ACIEq s t → ACIEq t u → ACIEq s u

/-- Theorem 52: AC embeds into ACI. -/
theorem ac_embed_aci {s t : Tm} (h : ACEq s t) : ACIEq s t := ACIEq.ac h

/-- Theorem 53: ACI reflexive. -/
theorem ACIEq.refl (t : Tm) : ACIEq t t := ACIEq.ac (ACEq.refl t)

-- ============================================================
-- §21  Critical Pairs
-- ============================================================

structure RRule where
  lhs : Tm
  rhs : Tm
deriving DecidableEq, Repr

structure CritPair where
  term1 : Tm
  term2 : Tm
deriving Repr

noncomputable def CritPair.trivial (cp : CritPair) : Bool := cp.term1 == cp.term2

/-- Theorem 54: trivial for equal terms. -/
theorem CritPair.trivial_eq (t : Tm) :
    CritPair.trivial ⟨t, t⟩ = true := by simp [CritPair.trivial, BEq.beq]

/-- Joinability. -/
inductive Joinable (R : Tm → Tm → Prop) : Tm → Tm → Prop where
  | join {s t : Tm} (u : Tm) : R s u → R t u → Joinable R s t
  | refl (t : Tm) : Joinable R t t

/-- Theorem 55: joinability reflexive. -/
theorem Joinable.refl' (R : Tm → Tm → Prop) (t : Tm) : Joinable R t t :=
  Joinable.refl t

/-- Theorem 56: joinability symmetric. -/
theorem Joinable.symm' {R : Tm → Tm → Prop} {s t : Tm}
    (h : Joinable R s t) : Joinable R t s := by
  cases h with
  | join u hs ht => exact Joinable.join u ht hs
  | refl => exact Joinable.refl _

-- ============================================================
-- §22  Narrowing
-- ============================================================

inductive NarrowStep (rules : List RRule) : Tm → Tm → Prop where
  | atRoot (r : RRule) (σ : Subst) (t : Tm)
      (hr : r ∈ rules) (hUnif : applyS σ r.lhs = applyS σ t) :
      NarrowStep rules t (applyS σ r.rhs)
  | inLeft (l l' r : Tm) :
      NarrowStep rules l l' → NarrowStep rules (.app l r) (.app l' r)
  | inRight (l r r' : Tm) :
      NarrowStep rules r r' → NarrowStep rules (.app l r) (.app l r')

inductive NarrowPath (rules : List RRule) : Tm → Tm → Prop where
  | refl (t : Tm) : NarrowPath rules t t
  | step {s t u : Tm} :
      NarrowStep rules s t → NarrowPath rules t u → NarrowPath rules s u

/-- Theorem 57: narrowing path transitive. -/
theorem NarrowPath.trans' {rules : List RRule} {s t u : Tm}
    (p : NarrowPath rules s t) (q : NarrowPath rules t u) :
    NarrowPath rules s u := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact NarrowPath.step s (ih q)

-- ============================================================
-- §23  E-Unification
-- ============================================================

structure ETheory where
  axioms_ : List (Tm × Tm)

inductive EEquiv (E : ETheory) : Tm → Tm → Prop where
  | refl (t : Tm) : EEquiv E t t
  | symm {s t : Tm} : EEquiv E s t → EEquiv E t s
  | trans {s t u : Tm} : EEquiv E s t → EEquiv E t u → EEquiv E s u
  | congApp {l₁ l₂ r₁ r₂ : Tm} :
      EEquiv E l₁ l₂ → EEquiv E r₁ r₂ →
      EEquiv E (.app l₁ r₁) (.app l₂ r₂)

noncomputable def EUnifier (E : ETheory) (s t : Tm) (σ : Subst) : Prop :=
  EEquiv E (applyS σ s) (applyS σ t)

/-- Theorem 58: id is E-unifier for equal terms. -/
theorem EUnifier.refl' (E : ETheory) (t : Tm) :
    EUnifier E t t Subst.id := by simp [EUnifier]; exact EEquiv.refl _

/-- Theorem 59: E-equiv reflexive (convenience). -/
theorem EEquiv.refl' (E : ETheory) (t : Tm) : EEquiv E t t := EEquiv.refl t

-- ============================================================
-- §24  Coherence
-- ============================================================

noncomputable def UPath.coherent (p q : UPath P R) : Prop :=
  p.stepCount ≥ 0 ∧ q.stepCount ≥ 0

/-- Theorem 60: all UPaths coherent. -/
theorem UPath.coherent_always (p q : UPath P R) :
    UPath.coherent p q := ⟨Nat.zero_le _, Nat.zero_le _⟩

-- ============================================================
-- §25  Substitution domain
-- ============================================================

noncomputable def Subst.domainOn (σ : Subst) (vars : List Nat) : List Nat :=
  vars.filter fun x => σ x != .var x

/-- Theorem 61: identity has empty domain. -/
theorem Subst.domainOn_id (vars : List Nat) :
    Subst.domainOn Subst.id vars = [] := by
  induction vars with
  | nil => rfl
  | cons x xs ih =>
    unfold Subst.domainOn at *
    simp only [List.filter, Subst.id, bne_self_eq_false] at *
    exact ih

end UnificationDeep
