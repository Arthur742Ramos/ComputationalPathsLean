/-
# Path Expressions

Syntax trees for path expressions, with evaluation back to `Path`,
rewriting, and confluence infrastructure.
-/

import ComputationalPaths.Path.Rewrite.Rw
import ComputationalPaths.Path.Rewrite.Confluence

namespace ComputationalPaths
namespace Path
namespace Rewrite

universe u

/-- A `PathExpr` is a syntax tree for building paths from atoms, identity,
symmetry, and transitivity. -/
inductive PathExpr (A : Type u) : A → A → Type (u + 1) where
  | atom {a b : A} (p : Path a b) : PathExpr A a b
  | refl (a : A) : PathExpr A a a
  | symm {a b : A} (e : PathExpr A a b) : PathExpr A b a
  | trans {a b c : A} (e₁ : PathExpr A a b) (e₂ : PathExpr A b c) : PathExpr A a c

namespace PathExpr

/-- Evaluate a `PathExpr` back into a `Path`. -/
noncomputable def eval {A : Type u} {a b : A} : PathExpr A a b → Path a b
  | .atom p => p
  | .refl _ => Path.refl _
  | .symm e => Path.symm (eval e)
  | .trans e₁ e₂ => Path.trans (eval e₁) (eval e₂)

/-- Size of a `PathExpr`. -/
noncomputable def size {A : Type u} {a b : A} : PathExpr A a b → Nat
  | .atom _ => 1
  | .refl _ => 1
  | .symm e => 1 + size e
  | .trans e₁ e₂ => 1 + size e₁ + size e₂

/-- Complexity is the same as size. -/
abbrev complexity {A : Type u} {a b : A} (e : PathExpr A a b) : Nat := size e

/-- Single rewrite step on `PathExpr` (trivial: only reflexivity). -/
inductive Step {A : Type u} {a b : A} : PathExpr A a b → PathExpr A a b → Prop where

/-- Multi-step rewriting (reflexive-transitive closure). -/
inductive Rw {A : Type u} {a b : A} : PathExpr A a b → PathExpr A a b → Prop where
  | refl (p : PathExpr A a b) : Rw p p
  | step {p q r : PathExpr A a b} : Step p q → Rw q r → Rw p r

theorem rw_eq_source {A : Type u} {a b : A} {p q : PathExpr A a b}
    (h : Rw p q) : p = q := by
  induction h with
  | refl _ => rfl
  | step hs _ _ => exact nomatch hs

noncomputable def rw_of_step {A : Type u} {a b : A} {p q : PathExpr A a b}
    (h : Step p q) : Rw p q := nomatch h

/-- Join data for `PathExpr`. -/
structure Join {A : Type u} {a b : A} (p q : PathExpr A a b) where
  meet : PathExpr A a b
  left : Rw p meet
  right : Rw q meet

theorem join_eq {A : Type u} {a b : A} {p q : PathExpr A a b}
    (J : Join p q) : p = q := by
  have h1 := rw_eq_source J.left
  have h2 := rw_eq_source J.right
  exact h1.trans h2.symm

/-- Confluence combinator (trivial since Step is empty). -/
noncomputable def confluence_of_local {A : Type u} {a b : A}
    {p q r : PathExpr A a b}
    (hq : Rw p q) (hr : Rw p r) :
    Join q r := by
  have h1 := rw_eq_source hq  -- p = q
  have h2 := rw_eq_source hr  -- p = r
  subst h1; subst h2
  exact ⟨p, Rw.refl p, Rw.refl p⟩

/-- Normalize an expression (identity in the trivial core). -/
noncomputable def normalize {A : Type u} {a b : A} (e : PathExpr A a b) : PathExpr A a b := e

/-! ## Transitive closure, complexity, termination -/

/-- Transitive closure of `Step` (non-empty rewrite chain). -/
inductive RwPlus {A : Type u} {a b : A} : PathExpr A a b → PathExpr A a b → Prop where
  | single {p q : PathExpr A a b} : Step p q → RwPlus p q
  | cons {p q r : PathExpr A a b} : Step p q → RwPlus q r → RwPlus p r

/-- Every `Step` strictly decreases complexity (vacuously true — `Step` is empty). -/
theorem step_complexity_lt {A : Type u} {a b : A}
    {p q : PathExpr A a b} (h : Step p q) :
    complexity q < complexity p := nomatch h

/-- Every `RwPlus` chain strictly decreases complexity. -/
theorem rwPlus_complexity_lt {A : Type u} {a b : A}
    {p q : PathExpr A a b} (h : RwPlus p q) :
    complexity q < complexity p := by
  induction h with
  | single hs => exact nomatch hs
  | cons hs _ _ => exact nomatch hs

/-- The rewrite system is terminating: no infinite `Step` chains. -/
noncomputable def Terminating (A : Type u) (a b : A) : Prop :=
  ∀ e : PathExpr A a b, Acc (fun q p => Step p q) e

/-- The trivial rewrite system is terminating. -/
theorem terminating (A : Type u) (a b : A) : Terminating A a b :=
  fun e => Acc.intro e (fun _ h => nomatch h)

/-- Evaluation respects `Rw`. -/
theorem eval_rw {A : Type u} {a b : A} {p q : PathExpr A a b}
    (h : Rw p q) : Path.Rw (eval p) (eval q) := by
  have := rw_eq_source h; subst this; exact Path.Rw.refl _

end PathExpr
end Rewrite
end Path
end ComputationalPaths
