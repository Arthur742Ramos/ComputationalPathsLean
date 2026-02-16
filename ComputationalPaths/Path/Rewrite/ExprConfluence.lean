/-
# Confluence witnesses for PathExpr rewrites

This module packages the PathExpr confluence result into a reusable interface,
provides derived combinators for joining expression rewrites, and proves
structural lemmas about the join operation.

## Key Results

- `HasJoinOfRwExpr`: typeclass packaging confluence for PathExpr rewrites
- `instHasJoinOfRwExpr`: canonical instance via `confluence_of_local`
- `join_refl_left`: joining an expression with itself
- `join_swap`: symmetry of join data
- `join_eq`: join implies equality (in the minimal core)
- `join_eval_eq`, `join_eval_path`: eval agreement on joined expressions
- `join_sides_size_eq`: joined sides have equal size
- `join_trans_trans`: composition preserves joinability
- `join_symm_symm`: symmetry preserves joinability
- `join_of_eq`: equal expressions are trivially joinable
- `church_rosser`: existence formulation of confluence

## References

- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
-/

import ComputationalPaths.Path.Rewrite.PathExpr

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace PathExpr

universe u

/-- Join data for two PathExpr rewrites.
    Note: this is `Type`-valued since `Join` is a structure in `Type`. -/
class HasJoinOfRwExpr.{v} : Type (v + 2) where
  join_of_rw {A : Type v} {a b : A}
      {p q r : PathExpr A a b}
      (hq : Rw p q) (hr : Rw p r) :
      Join q r

noncomputable instance instHasJoinOfRwExpr : HasJoinOfRwExpr.{u} where
  join_of_rw := fun hq hr => confluence_of_local hq hr

/-! ## Reflexive join combinators -/

/-- Joining an expression with itself is trivial. -/
def join_refl_left {A : Type u} {a b : A}
    (p : PathExpr A a b) :
    Join p p :=
  { meet := p, left := Rw.refl p, right := Rw.refl p }

/-! ## Symmetry of join data -/

/-- Join data is symmetric: if p joins with q then q joins with p. -/
def join_swap {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (J : Join p q) :
    Join q p :=
  { meet := J.meet, left := J.right, right := J.left }

/-! ## Join implies expression-level equality -/

/-- Two joined expressions are equal (in the minimal core) — alias. -/
theorem join_eq' {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (J : Join p q) :
    p = q :=
  PathExpr.join_eq J

/-- Two joined expressions have the same evaluation under `eval`. -/
theorem join_eval_eq {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (J : Join p q) :
    eval p = eval q := by
  rw [join_eq' J]

/-- Path witness that joined evaluations agree. -/
def join_eval_path {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (J : Join p q) :
    Path (eval p) (eval q) :=
  Path.stepChain (join_eval_eq J)

/-! ## Meet properties -/

/-- The meet equals the left side (in the minimal core). -/
theorem join_meet_eq_left {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (J : Join p q) :
    J.meet = p :=
  (rw_eq_source J.left).symm

/-- The meet equals the right side (in the minimal core). -/
theorem join_meet_eq_right {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (J : Join p q) :
    J.meet = q :=
  (rw_eq_source J.right).symm

/-! ## Join and size -/

/-- Both sides of a join have the same size. -/
theorem join_sides_size_eq {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (J : Join p q) :
    size p = size q := by
  have h := join_eq' J
  rw [h]

/-! ## Join and complexity -/

/-- Both sides of a join have the same complexity. -/
theorem join_sides_complexity_eq {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (J : Join p q) :
    complexity p = complexity q := by
  simp only [complexity]
  exact join_sides_size_eq J

/-! ## Join from equal expressions -/

/-- Equal expressions are trivially joinable. -/
def join_of_eq {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (h : p = q) :
    Join p q := by
  cases h
  exact join_refl_left p

/-! ## Atom-specific lemmas -/

/-- Two atom expressions wrapping the same path are joinable. -/
def join_atom_atom {A : Type u} {a b : A} (p : Path a b) :
    Join (PathExpr.atom p) (PathExpr.atom p) :=
  join_refl_left (PathExpr.atom p)

/-- Eval of an atom join gives a reflexive path. -/
def join_atom_eval_path {A : Type u} {a b : A} (p : Path a b) :
    Path (eval (PathExpr.atom p)) (eval (PathExpr.atom p)) :=
  Path.refl (eval (PathExpr.atom p))

/-- Refl expression is joinable with itself. -/
def join_refl_refl {A : Type u} (a : A) :
    Join (PathExpr.refl a) (PathExpr.refl a) :=
  join_refl_left (PathExpr.refl a)

/-! ## Structural join preservation -/

/-- Symmetry preserves joinability: if p joins with q, then symm p joins with symm q. -/
def join_symm_symm {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (J : Join p q) :
    Join
      (PathExpr.symm p) (PathExpr.symm q) := by
  exact join_of_eq (by rw [join_eq' J])

/-- Transitivity (composition) preserves joinability on both sides. -/
def join_trans_trans {A : Type u} {a b c : A}
    {p₁ q₁ : PathExpr A a b}
    {p₂ q₂ : PathExpr A b c}
    (J₁ : Join p₁ q₁)
    (J₂ : Join p₂ q₂) :
    Join
      (PathExpr.trans p₁ p₂) (PathExpr.trans q₁ q₂) := by
  exact join_of_eq (by rw [join_eq' J₁, join_eq' J₂])

/-! ## Join transitivity -/

/-- Transitivity of join: if p joins with q and q joins with r,
    then p joins with r. -/
def join_trans' {A : Type u} {a b : A}
    {p q r : PathExpr A a b}
    (J₁ : Join p q)
    (J₂ : Join q r) :
    Join p r := by
  exact join_of_eq (by rw [join_eq' J₁, join_eq' J₂])

/-! ## Church-Rosser property -/

/-- The Church-Rosser property follows from confluence:
    any two expressions reachable from the same source are joinable. -/
theorem church_rosser
    {A : Type u} {a b : A}
    {p q r : PathExpr A a b}
    (hq : Rw p q) (hr : Rw p r) :
    ∃ s : PathExpr A a b, Rw q s ∧ Rw r s := by
  let J := confluence_of_local hq hr
  exact ⟨J.meet, J.left, J.right⟩

/-- Church-Rosser specialised to single steps. -/
theorem church_rosser_steps
    {A : Type u} {a b : A}
    {p q r : PathExpr A a b}
    (hq : Step p q) (hr : Step p r) :
    ∃ s : PathExpr A a b, Rw q s ∧ Rw r s :=
  church_rosser (rw_of_step hq) (rw_of_step hr)

/-! ## Unique normal forms -/

/-- In the minimal core, all rewrite targets equal the source. -/
theorem rw_target_eq_source {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (h : Rw p q) : p = q :=
  (rw_eq_source h).symm

/-- Confluence implies unique normal forms: if two expressions are both
    in normal form (i.e., no further steps apply) and are joinable, they
    are equal. -/
theorem unique_normal_forms {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (J : Join p q) :
    p = q :=
  join_eq' J

/-! ## Eval preservation -/

/-- Eval is invariant under Rw chains. -/
theorem eval_invariant_rw {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (h : Rw p q) : eval p = eval q := by
  have := rw_eq_source h
  rw [← this]

/-- Path witness for eval invariance under Rw. -/
def eval_invariant_rw_path {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (h : Rw p q) : Path (eval p) (eval q) :=
  Path.stepChain (eval_invariant_rw h)

/-- Eval is invariant under Step. -/
theorem eval_invariant_step {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (h : Step p q) : eval p = eval q := by
  cases h

/-- Size is monotone under steps (in the minimal core, no steps exist). -/
theorem size_invariant_rw {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (h : Rw p q) : size p = size q := by
  have := rw_eq_source h
  rw [← this]

end PathExpr
end Rewrite
end Path
end ComputationalPaths
