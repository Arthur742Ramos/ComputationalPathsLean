/-
# Basic combinators for computational paths (UIP)

Consequences for the uniqueness of identity proofs principle derived from the
computational-path machinery.

## Key Results

- `UIP` definition and its negation for nonempty types
- Path-collapsing and path-contractibility
- Step counting invariants
- Concrete examples of UIP failure with computational paths
- Proof-irrelevance consequences

## References

- Hedberg, "A coherence theorem for Martin-Löf's type theory"
- Streicher, "Investigations into intensional type theory"
- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
-/

import ComputationalPaths.Path.Basic.Congruence

namespace ComputationalPaths

universe u v

/-- `UIP A` asserts that any two computational paths with the same endpoints
are judgmentally equal, echoing the uniqueness of identity proofs principle. -/
def UIP (A : Type u) : Prop :=
  ∀ {a b : A}, ∀ (p q : Path a b), p = q

/-- A type with an inhabited path space witnesses non-`UIP`: the empty path and
the explicit reflexive rewrite remain distinct. -/
theorem not_uip_of_inhabited {A : Type u} (a : A) : ¬ UIP A := by
  intro h
  have := h (p := Path.refl a) (q := Path.ofEq (rfl : a = a))
  exact Path.refl_ne_ofEq (A := A) a this

/-- As soon as a type is nonempty we can pick a witness and derive
`¬ UIP A` from the inhabited case. -/
theorem not_uip_of_nonempty {A : Type u} (hA : Nonempty A) : ¬ UIP A := by
  classical
  obtain ⟨a⟩ := hA
  exact not_uip_of_inhabited (A := A) a

/-! ## Streicher's K principle -/

/-- Streicher's K principle for computational paths: every self-loop is `refl`. -/
def PathK (A : Type u) : Prop :=
  ∀ {a : A}, ∀ (p : Path a a), p = Path.refl a

/-- K fails for all nonempty types with computational paths. -/
theorem not_pathK_of_nonempty {A : Type u} (hA : Nonempty A) : ¬ PathK A := by
  intro hK
  obtain ⟨a⟩ := hA
  have : Path.ofEq (rfl : a = a) = Path.refl a := hK _
  exact Path.refl_ne_ofEq a this.symm

/-- K fails for any inhabited type. -/
theorem not_pathK_of_inhabited {A : Type u} (a : A) : ¬ PathK A := by
  exact not_pathK_of_nonempty ⟨a⟩

/-! ## Proof-irrelevance for the equality component -/

/-- The `toEq` projection forgets all step information: two paths with the
same endpoints always have the same `toEq`. -/
@[simp] theorem toEq_unique {A : Type u} {a b : A} (p q : Path a b) :
    p.toEq = q.toEq := by
  cases p with
  | mk _ proof_p =>
    cases q with
    | mk _ proof_q =>
      cases proof_p
      cases proof_q
      rfl

/-- Proof irrelevance: `ofEq` always produces the same path regardless
of which equality proof is supplied. -/
@[simp] theorem ofEq_proof_irrelevance {A : Type u} {a b : A}
    (h₁ h₂ : a = b) : Path.ofEq h₁ = Path.ofEq h₂ :=
  Path.ofEq_eq_ofEq h₁ h₂

/-! ## Path contractibility -/

/-- The `toEq` component of any loop is `rfl`. -/
@[simp] theorem toEq_refl_loop {A : Type u} {a : A} (p : Path a a) :
    p.toEq = rfl := by
  cases p with
  | mk _ proof =>
    cases proof
    rfl

/-- Any path from `a` to `a` has the same `toEq` as `Path.refl a`. -/
@[simp] theorem toEq_loop_eq_refl_toEq {A : Type u} {a : A} (p : Path a a) :
    p.toEq = (Path.refl a).toEq := by
  simp

/-! ## Weak UIP: equality of toEq -/

/-- Weak UIP: all paths with the same endpoints agree on their propositional
equality content. This always holds because `Eq` in Lean 4 is proof-irrelevant. -/
theorem weak_uip (A : Type u) {a b : A} (p q : Path a b) :
    p.toEq = q.toEq :=
  toEq_unique p q

/-- The type of propositional equalities `a = b` is a subsingleton,
which is reflected in the path structure. -/
theorem path_proof_subsingleton {A : Type u} {a b : A}
    (p q : Path a b) : p.proof = q.proof := by
  cases p with
  | mk _ h1 =>
    cases q with
    | mk _ h2 =>
      cases h1; cases h2; rfl

/-! ## Step-level distinguishability -/

/-- Two paths differ if and only if their step lists differ. -/
theorem path_eq_iff_steps_eq {A : Type u} {a b : A}
    (p q : Path a b) :
    p = q ↔ p.steps = q.steps := by
  constructor
  · intro h; exact congrArg Path.steps h
  · intro h
    cases p with
    | mk steps_p proof_p =>
      cases q with
      | mk steps_q proof_q =>
        cases proof_p; cases proof_q
        simp at h
        exact congrArg (Path.mk · rfl) h

/-- The step list of `refl` is empty. -/
@[simp] theorem refl_steps_empty' {A : Type u} (a : A) :
    (Path.refl a).steps = [] := rfl

/-- The step list of `ofEq` is a singleton. -/
@[simp] theorem ofEq_steps_singleton' {A : Type u} {a b : A} (h : a = b) :
    (Path.ofEq h).steps = [Step.mk a b h] := rfl

/-- `refl a` and `ofEq rfl` are distinguished by their step lists. -/
theorem refl_ofEq_steps_ne {A : Type u} (a : A) :
    (Path.refl a).steps ≠ (Path.ofEq (rfl : a = a)).steps := by
  simp [Path.refl, Path.ofEq]

/-! ## Transport and UIP interaction -/

/-- Transport along any two paths with the same endpoints gives the same result,
reflecting proof-irrelevance of the underlying equality. -/
@[simp] theorem transport_path_irrelevant {A : Type u} {D : A → Sort v}
    {a b : A} (p q : Path a b) (x : D a) :
    Path.transport (D := D) p x = Path.transport (D := D) q x := by
  cases p with
  | mk _ h1 =>
    cases q with
    | mk _ h2 =>
      cases h1; cases h2; rfl

/-- Substitution along any two paths with the same endpoints agrees. -/
@[simp] theorem subst_path_irrelevant {A : Type u} {D : A → Sort v}
    {a b : A} (x : D a) (p q : Path a b) :
    Path.subst (D := D) x p = Path.subst (D := D) x q :=
  transport_path_irrelevant (D := D) p q x

/-! ## Concrete examples -/

/-- In `Nat`, there exist two distinct paths from 0 to 0. -/
theorem nat_two_distinct_loops :
    ∃ (p q : Path (0 : Nat) 0), p ≠ q := by
  exact ⟨Path.refl 0, Path.ofEq rfl, Path.refl_ne_ofEq 0⟩

/-- In `Bool`, there exist two distinct paths from `true` to `true`. -/
theorem bool_two_distinct_loops :
    ∃ (p q : Path true true), p ≠ q :=
  ⟨Path.refl true, Path.ofEq rfl, Path.refl_ne_ofEq true⟩

/-- The path space between any point and itself always has at least two
distinct elements, as long as the type is inhabited. -/
theorem loop_space_not_subsingleton {A : Type u} (a : A) :
    ¬ Subsingleton (Path a a) := by
  intro ⟨h⟩
  exact Path.refl_ne_ofEq a (h (Path.refl a) (Path.ofEq rfl))

/-- For any type, distinct paths can be constructed by concatenation. -/
theorem three_distinct_loops {A : Type u} (a : A) :
    ∃ (p q r : Path a a), p ≠ q ∧ q ≠ r ∧ p ≠ r := by
  refine ⟨Path.refl a, Path.ofEq rfl, Path.trans (Path.ofEq rfl) (Path.ofEq rfl), ?_, ?_, ?_⟩
  · exact Path.refl_ne_ofEq a
  · intro h
    have := congrArg Path.steps h
    simp [Path.ofEq, Path.trans] at this
  · intro h
    have := congrArg Path.steps h
    simp [Path.refl, Path.trans, Path.ofEq] at this

/-! ## Congruence and UIP -/

/-- `congrArg f` preserves the refl-vs-ofEq distinction. -/
theorem congrArg_preserves_ne {A : Type u} {B : Type v} (f : A → B)
    (a : A) :
    Path.congrArg f (Path.refl a) ≠ Path.congrArg f (Path.ofEq (rfl : a = a)) := by
  intro h
  have := congrArg Path.steps h
  simp [Path.congrArg, Path.refl, Path.ofEq, Step.map] at this

/-- UIP failure is preserved by arbitrary functions: if we have non-UIP for
`A`, then `B` is also non-UIP whenever there is a function `A → B`. -/
theorem not_uip_image {A : Type u} {B : Type u} (f : A → B)
    (hA : Nonempty A) : ¬ UIP B := by
  obtain ⟨a⟩ := hA
  intro hB
  have := hB (Path.congrArg f (Path.refl a)) (Path.congrArg f (Path.ofEq (rfl : a = a)))
  exact congrArg_preserves_ne f a this

/-! ## Step counting -/

/-- The number of steps in a path is a natural invariant. -/
@[simp] def stepCount {A : Type u} {a b : A} (p : Path a b) : Nat :=
  p.steps.length

/-- `refl` has zero steps. -/
@[simp] theorem stepCount_refl {A : Type u} (a : A) :
    stepCount (Path.refl a) = 0 := rfl

/-- `ofEq` has exactly one step. -/
@[simp] theorem stepCount_ofEq {A : Type u} {a b : A} (h : a = b) :
    stepCount (Path.ofEq h) = 1 := rfl

/-- Step count of a concatenation is the sum of the step counts. -/
@[simp] theorem stepCount_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    stepCount (Path.trans p q) = stepCount p + stepCount q := by
  simp [stepCount, Path.trans, List.length_append]

/-- Step count of symmetry equals the original step count. -/
@[simp] theorem stepCount_symm {A : Type u} {a b : A}
    (p : Path a b) :
    stepCount (Path.symm p) = stepCount p := by
  simp [stepCount, Path.symm, List.length_map, List.length_reverse]

/-- Paths with different step counts are necessarily different. -/
theorem ne_of_stepCount_ne {A : Type u} {a b : A}
    {p q : Path a b} (h : stepCount p ≠ stepCount q) :
    p ≠ q := by
  intro heq
  exact h (congrArg stepCount heq)

/-- A path `p` and `trans p (ofEq rfl)` always differ (when a = b). -/
theorem path_ne_trans_ofEq_rfl {A : Type u} {a : A}
    (p : Path a a) :
    p ≠ Path.trans p (Path.ofEq (rfl : a = a)) := by
  apply ne_of_stepCount_ne
  simp

/-! ## Step count preserving operations -/

/-- `congrArg` preserves step count. -/
@[simp] theorem stepCount_congrArg {A : Type u} {B : Type v} {a b : A}
    (f : A → B) (p : Path a b) :
    stepCount (Path.congrArg f p) = stepCount p := by
  simp [stepCount, Path.congrArg, List.length_map]

/-- Helper: n-fold concatenation of `ofEq rfl` loops. -/
def nfoldLoop {A : Type u} (a : A) : Nat → Path a a
  | 0 => Path.refl a
  | n + 1 => Path.trans (nfoldLoop a n) (Path.ofEq (rfl : a = a))

/-- The step count of an n-fold concatenation of `ofEq rfl` loops. -/
theorem stepCount_nfoldLoop {A : Type u} (a : A) (n : Nat) :
    stepCount (nfoldLoop a n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold nfoldLoop
    rw [stepCount_trans, stepCount_ofEq, ih]

/-! ## Path space cardinality -/

/-- The loop space at any point is infinite: for each `n : Nat` there is
a loop with exactly `n` steps. -/
theorem loop_space_infinite {A : Type u} (a : A) :
    Function.Injective (nfoldLoop a) := by
  intro m n h
  have hm := stepCount_nfoldLoop a m
  have hn := stepCount_nfoldLoop a n
  rw [congrArg stepCount h] at hm
  omega

/-- Distinct natural numbers give distinct loops. -/
theorem nfoldLoop_ne {A : Type u} (a : A) {m n : Nat} (h : m ≠ n) :
    nfoldLoop a m ≠ nfoldLoop a n :=
  fun heq => h (loop_space_infinite a heq)

end ComputationalPaths
