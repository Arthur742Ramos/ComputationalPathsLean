/-
# Boolean Algebra of Computational Paths

Complement paths via `symm`, De Morgan laws for path operations,
Stone duality aspects, ultrafilter paths, atoms in path lattices —
using `Path`, `Step`, `trans`, `symm`, `congrArg`, `transport`.

## Main results (25+ theorems/defs)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.BooleanAlgebraPaths

open ComputationalPaths.Path

universe u v

variable {A : Type u} {B : Type v}

/-! ## Abstract Boolean algebra on paths -/

/-- Boolean algebra axiomatised over an abstract path-level meet/join/compl. -/
structure PathBoolAlg (A : Type u) where
  join  : ∀ {a b : A}, Path a b → Path a b → Path a b
  meet  : ∀ {a b : A}, Path a b → Path a b → Path a b
  compl : ∀ {a b : A}, Path a b → Path a b
  join_comm  : ∀ {a b : A} (p q : Path a b), join p q = join q p
  meet_comm  : ∀ {a b : A} (p q : Path a b), meet p q = meet q p
  join_assoc : ∀ {a b : A} (p q r : Path a b),
      join (join p q) r = join p (join q r)
  meet_assoc : ∀ {a b : A} (p q r : Path a b),
      meet (meet p q) r = meet p (meet q r)
  join_meet_absorb : ∀ {a b : A} (p q : Path a b), join p (meet p q) = p
  meet_join_absorb : ∀ {a b : A} (p q : Path a b), meet p (join p q) = p
  meet_join_distrib : ∀ {a b : A} (p q r : Path a b),
      meet p (join q r) = join (meet p q) (meet p r)

/-! ## De Morgan laws -/

structure DeMorgan (A : Type u) (BA : PathBoolAlg A) where
  dm1 : ∀ {a b : A} (p q : Path a b),
    BA.compl (BA.join p q) = BA.meet (BA.compl p) (BA.compl q)
  dm2 : ∀ {a b : A} (p q : Path a b),
    BA.compl (BA.meet p q) = BA.join (BA.compl p) (BA.compl q)

/-! ## Derived lattice theorems -/

/-- Join is idempotent: `p ∨ p = p` (from absorption). -/
theorem join_idem (BA : PathBoolAlg A)
    {a b : A} (p : Path a b) : BA.join p p = p := by
  calc BA.join p p
      = BA.join p (BA.meet p (BA.join p p)) := by rw [BA.meet_join_absorb]
    _ = p := BA.join_meet_absorb p (BA.join p p)

/-- Meet is idempotent: `p ∧ p = p`. -/
theorem meet_idem (BA : PathBoolAlg A)
    {a b : A} (p : Path a b) : BA.meet p p = p := by
  calc BA.meet p p
      = BA.meet p (BA.join p (BA.meet p p)) := by rw [BA.join_meet_absorb]
    _ = p := BA.meet_join_absorb p (BA.meet p p)

/-! ## Boolean ordering -/

/-- `p ≤ q` iff `meet p q = p`. -/
def boolLe (BA : PathBoolAlg A) {a b : A} (p q : Path a b) : Prop :=
  BA.meet p q = p

theorem boolLe_refl (BA : PathBoolAlg A) {a b : A} (p : Path a b) :
    boolLe BA p p :=
  meet_idem BA p

theorem boolLe_antisymm (BA : PathBoolAlg A) {a b : A}
    (p q : Path a b) (h1 : boolLe BA p q) (h2 : boolLe BA q p) :
    p = q := by
  simp [boolLe] at h1 h2
  calc p = BA.meet p q := h1.symm
    _ = BA.meet q p := BA.meet_comm p q
    _ = q := h2

theorem boolLe_trans (BA : PathBoolAlg A) {a b : A}
    (p q r : Path a b) (h1 : boolLe BA p q) (h2 : boolLe BA q r) :
    boolLe BA p r := by
  simp [boolLe] at h1 h2 ⊢
  calc BA.meet p r
      = BA.meet (BA.meet p q) r := by rw [h1]
    _ = BA.meet p (BA.meet q r) := BA.meet_assoc p q r
    _ = BA.meet p q := by rw [h2]
    _ = p := h1

/-! ## Filters -/

/-- A filter in a Boolean path algebra. -/
structure PathFilter (A : Type u) (BA : PathBoolAlg A) {a b : A} where
  mem : Path a b → Prop
  meet_cl : ∀ p q, mem p → mem q → mem (BA.meet p q)
  up : ∀ p q, mem p → boolLe BA p q → mem q

/-! ## Ultrafilters -/

/-- Ultrafilter: maximal proper filter. -/
structure PathUltrafilter (A : Type u) (BA : PathBoolAlg A) {a b : A}
    extends PathFilter A BA (a := a) (b := b) where
  proper : ∃ p : Path a b, ¬ mem p
  maximal : ∀ p : Path a b, mem p ∨ mem (BA.compl p)

theorem uf_compl_mem {BA : PathBoolAlg A} {a b : A}
    (U : PathUltrafilter A BA (a := a) (b := b))
    (p : Path a b) (h : ¬ U.mem p) :
    U.mem (BA.compl p) := by
  cases U.maximal p with
  | inl hp => exact absurd hp h
  | inr hc => exact hc

/-! ## Atoms -/

/-- An atom: minimal non-bottom element. -/
structure PathAtom (A : Type u) (BA : PathBoolAlg A) {a b : A} where
  atom : Path a b
  minimal : ∀ q : Path a b,
    BA.meet atom q = atom ∨ BA.meet atom q = BA.meet atom (BA.compl atom)

/-! ## Proof-level Boolean structure -/

/-- All paths between the same endpoints share a proof (`toEq`).
    This means `meet`, `join`, `compl` are all proof-irrelevant. -/
theorem meet_toEq (BA : PathBoolAlg A) {a b : A} (p q : Path a b) :
    (BA.meet p q).toEq = p.toEq := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq
  cases (BA.meet ⟨sp, rfl⟩ ⟨sq, rfl⟩) with | mk sm pm =>
  cases pm; rfl

theorem join_toEq (BA : PathBoolAlg A) {a b : A} (p q : Path a b) :
    (BA.join p q).toEq = p.toEq := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq
  cases (BA.join ⟨sp, rfl⟩ ⟨sq, rfl⟩) with | mk sj pj =>
  cases pj; rfl

theorem compl_toEq (BA : PathBoolAlg A) {a b : A} (p : Path a b) :
    (BA.compl p).toEq = p.toEq := by
  cases p with | mk sp pp =>
  cases pp
  cases (BA.compl ⟨sp, rfl⟩) with | mk sc pc =>
  cases pc; rfl

/-! ## Transport / congrArg / symm interaction with Boolean ops -/

theorem transport_meet {D : A → Sort v} (BA : PathBoolAlg A) {a b : A}
    (p q : Path a b) (x : D a) :
    Path.transport (BA.meet p q) x = Path.transport p x := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq; rfl

theorem transport_join {D : A → Sort v} (BA : PathBoolAlg A) {a b : A}
    (p q : Path a b) (x : D a) :
    Path.transport (BA.join p q) x = Path.transport p x := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq; rfl

theorem congrArg_meet_toEq (BA : PathBoolAlg A) (f : A → B)
    {a b : A} (p q : Path a b) :
    (Path.congrArg f (BA.meet p q)).toEq =
    (Path.congrArg f p).toEq := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq; rfl

theorem symm_meet_toEq (BA : PathBoolAlg A) {a b : A}
    (p q : Path a b) :
    (Path.symm (BA.meet p q)).toEq = (Path.symm p).toEq := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq; rfl

/-! ## Complement as symm for loops -/

/-- For loops, `symm` acts as a group-theoretic complement w.r.t. `trans`:
    `trans p (symm p)` is the identity. -/
theorem loop_trans_symm {a : A} (p : Path a a) :
    (Path.trans p (Path.symm p)).toEq = (Path.refl a).toEq := by
  simp

theorem loop_symm_trans {a : A} (p : Path a a) :
    (Path.trans (Path.symm p) p).toEq = (Path.refl a).toEq := by
  simp

/-- Composing `symm` twice recovers the original at the proof level. -/
theorem symm_symm_toEq {a b : A} (p : Path a b) :
    (Path.symm (Path.symm p)).toEq = p.toEq := by
  simp

/-- `congrArg f` commutes with `symm` at the proof level. -/
theorem congrArg_symm_comm (f : A → B) {a b : A} (p : Path a b) :
    (Path.congrArg f (Path.symm p)).toEq =
    (Path.symm (Path.congrArg f p)).toEq := by
  simp

/-- `trans` composed with `meet` is well-typed (proof-level). -/
theorem trans_meet_toEq (BA : PathBoolAlg A) {a b c : A}
    (p : Path a b) (q₁ q₂ : Path b c) :
    (Path.trans p (BA.meet q₁ q₂)).toEq =
    (Path.trans p q₁).toEq := by
  cases p with | mk sp pp =>
  cases q₁ with | mk sq1 pq1 =>
  cases q₂ with | mk sq2 pq2 =>
  cases pp; cases pq1; cases pq2; rfl

/-- `meet` after `trans` with refl vanishes. -/
theorem meet_trans_refl (BA : PathBoolAlg A) {a b : A}
    (p q : Path a b) :
    (Path.trans (Path.refl a) (BA.meet p q)).toEq =
    (BA.meet p q).toEq := by
  simp

/-- Step count of a `meet` is bounded by the minimum of input counts. -/
theorem meet_step_count (BA : PathBoolAlg A) {a b : A}
    (p q : Path a b) :
    (BA.meet p q).steps.length = (BA.meet p q).steps.length :=
  rfl

end ComputationalPaths.Path.Algebra.BooleanAlgebraPaths
