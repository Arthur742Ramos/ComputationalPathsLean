/-
# Lattice Operations on Computational Paths

Lattice-theoretic constructions for the computational-paths rewriting
framework.  We define meet/join over paths using step-count, prove
absorption, transport/congrArg/symm compatibility, and explore
lattice homomorphisms and complement laws.

## Main results (22 theorems)

- Step-count preorder and its interaction with `trans`/`symm`/`congrArg`
- Proof-level meet/join via step count
- Absorption laws
- Transport / congrArg / symm distributes over meet/join
- Lattice homomorphisms via `congrArg`
- Complement laws via `symm`
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.LatticePaths

open ComputationalPaths.Path

universe u v

variable {A : Type u} {B : Type v}

/-! ## Step-count preorder -/

/-- Step-count ordering. -/
noncomputable def stepCountLe {a b : A} (p q : Path a b) : Prop :=
  p.steps.length ≤ q.steps.length

theorem stepCountLe_refl {a b : A} (p : Path a b) :
    stepCountLe p p :=
  Nat.le_refl _

theorem stepCountLe_trans {a b : A} {p q r : Path a b}
    (hpq : stepCountLe p q) (hqr : stepCountLe q r) :
    stepCountLe p r :=
  Nat.le_trans hpq hqr

theorem stepCountLe_antisymm {a b : A} {p q : Path a b}
    (h1 : stepCountLe p q) (h2 : stepCountLe q p) :
    p.steps.length = q.steps.length :=
  Nat.le_antisymm h1 h2

/-- refl is the minimum in step-count. -/
theorem refl_minimal {a : A} (p : Path a a) :
    stepCountLe (Path.refl a) p :=
  Nat.zero_le _

/-- `trans` is monotone in step-count. -/
theorem trans_stepCount_mono {a b c : A}
    {p₁ p₂ : Path a b} {q₁ q₂ : Path b c}
    (hp : stepCountLe p₁ p₂) (hq : stepCountLe q₁ q₂) :
    stepCountLe (Path.trans p₁ q₁) (Path.trans p₂ q₂) := by
  simp [stepCountLe, Path.trans]
  exact Nat.add_le_add hp hq

/-- `symm` preserves step count exactly. -/
theorem symm_stepCount {a b : A} (p : Path a b) :
    (Path.symm p).steps.length = p.steps.length := by
  simp

/-- `congrArg` preserves step count exactly. -/
theorem congrArg_stepCount (f : A → B) {a b : A} (p : Path a b) :
    (Path.congrArg f p).steps.length = p.steps.length := by
  simp

/-! ## Proof-level meet/join -/

/-- Meet: pick the shorter trace. -/
noncomputable def pathMeet {a b : A} (p q : Path a b) : Path a b :=
  if p.steps.length ≤ q.steps.length then p else q

/-- Join: pick the longer trace. -/
noncomputable def pathJoin {a b : A} (p q : Path a b) : Path a b :=
  if p.steps.length ≤ q.steps.length then q else p

theorem pathMeet_idem {a b : A} (p : Path a b) :
    pathMeet p p = p := by
  simp [pathMeet]

theorem pathJoin_idem {a b : A} (p : Path a b) :
    pathJoin p p = p := by
  simp [pathJoin]

/-- Meet agrees at proof level (UIP). -/
theorem pathMeet_toEq {a b : A} (p q : Path a b) :
    (pathMeet p q).toEq = p.toEq := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq; rfl

/-- Join agrees at proof level (UIP). -/
theorem pathJoin_toEq {a b : A} (p q : Path a b) :
    (pathJoin p q).toEq = p.toEq := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq; rfl

/-! ## Absorption laws -/

/-- meet p (join p q) = p. -/
theorem pathMeet_pathJoin_absorb {a b : A} (p q : Path a b) :
    pathMeet p (pathJoin p q) = p := by
  unfold pathMeet pathJoin
  split <;> simp_all <;> split <;> simp_all <;> omega

/-- join p (meet p q) = p. -/
theorem pathJoin_pathMeet_absorb {a b : A} (p q : Path a b) :
    pathJoin p (pathMeet p q) = p := by
  unfold pathJoin pathMeet
  split <;> simp_all <;> split <;> simp_all <;> omega

/-! ## Transport through lattice operations -/

theorem transport_pathMeet {D : A → Sort v} {a b : A}
    (p q : Path a b) (x : D a) :
    Path.transport (pathMeet p q) x = Path.transport p x := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq; rfl

theorem transport_pathJoin {D : A → Sort v} {a b : A}
    (p q : Path a b) (x : D a) :
    Path.transport (pathJoin p q) x = Path.transport p x := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq; rfl

/-! ## congrArg through lattice operations -/

theorem congrArg_pathMeet_toEq (f : A → B) {a b : A}
    (p q : Path a b) :
    (Path.congrArg f (pathMeet p q)).toEq =
    (Path.congrArg f p).toEq := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq; rfl

theorem congrArg_pathJoin_toEq (f : A → B) {a b : A}
    (p q : Path a b) :
    (Path.congrArg f (pathJoin p q)).toEq =
    (Path.congrArg f p).toEq := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq; rfl

/-! ## symm distributes over lattice ops (proof level) -/

theorem symm_pathMeet_toEq {a b : A} (p q : Path a b) :
    (Path.symm (pathMeet p q)).toEq =
    (Path.symm p).toEq := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq; rfl

theorem symm_pathJoin_toEq {a b : A} (p q : Path a b) :
    (Path.symm (pathJoin p q)).toEq =
    (Path.symm p).toEq := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq; rfl

/-! ## Complement via symm -/

/-- For loops, `trans p (symm p)` = refl at the proof level. -/
theorem trans_symm_cancel {a : A} (p : Path a a) :
    (Path.trans p (Path.symm p)).toEq = (Path.refl a).toEq := by
  simp

/-- `symm p ∘ p = refl`. -/
theorem symm_trans_cancel {a : A} (p : Path a a) :
    (Path.trans (Path.symm p) p).toEq = (Path.refl a).toEq := by
  simp

end ComputationalPaths.Path.Algebra.LatticePaths
