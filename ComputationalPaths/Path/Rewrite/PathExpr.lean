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
inductive PathExpr {A : Type u} : (a b : A) → Type (u + 1) where
  | atom {a b : A} (p : Path a b) : PathExpr a b
  | refl (a : A) : PathExpr a a
  | symm {a b : A} (e : PathExpr a b) : PathExpr b a
  | trans {a b c : A} (e₁ : PathExpr a b) (e₂ : PathExpr b c) : PathExpr a c

namespace PathExpr

variable {A : Type u}

/-- Evaluate a `PathExpr` back into a `Path`. -/
def eval {a b : A} : PathExpr (A := A) a b → Path a b
  | .atom p => p
  | .refl _ => Path.refl _
  | .symm e => Path.symm (eval e)
  | .trans e₁ e₂ => Path.trans (eval e₁) (eval e₂)

/-- Size of a `PathExpr`. -/
def size {a b : A} : PathExpr (A := A) a b → Nat
  | .atom _ => 1
  | .refl _ => 1
  | .symm e => 1 + size e
  | .trans e₁ e₂ => 1 + size e₁ + size e₂

/-- Complexity is the same as size. -/
abbrev complexity {a b : A} (e : PathExpr (A := A) a b) : Nat := size e

variable {a b c : A}

/-- Single rewrite step on `PathExpr` (trivial: only reflexivity). -/
inductive Step : PathExpr (A := A) a b →
    PathExpr (A := A) a b → Prop where

/-- Multi-step rewriting (reflexive-transitive closure). -/
inductive Rw : PathExpr (A := A) a b →
    PathExpr (A := A) a b → Prop where
  | refl (p : PathExpr (A := A) a b) : Rw p p
  | step {p q r : PathExpr (A := A) a b} :
      Step p q → Rw q r → Rw p r

theorem rw_eq_source {p q : PathExpr (A := A) a b}
    (h : Rw p q) : p = q := by
  induction h with
  | refl _ => rfl
  | step hs _ _ => exact nomatch hs

def rw_of_step {p q : PathExpr (A := A) a b}
    (h : Step p q) : Rw p q := nomatch h

/-- Join data for `PathExpr`. -/
structure Join (p q : PathExpr (A := A) a b) where
  meet : PathExpr (A := A) a b
  left : Rw p meet
  right : Rw q meet

theorem join_eq {p q : PathExpr (A := A) a b}
    (J : Join p q) : p = q := by
  have h1 := rw_eq_source J.left
  have h2 := rw_eq_source J.right
  exact h1 ▸ h2 ▸ rfl

/-- Confluence combinator (trivial since Step is empty). -/
def confluence_of_local
    {A : Type u} {a b : A}
    {p q r : PathExpr (A := A) a b}
    (hq : Rw p q) (hr : Rw p r) :
    Join q r := by
  have heq_q := rw_eq_source hq -- p = q
  have heq_r := rw_eq_source hr -- p = r
  subst heq_q; subst heq_r
  exact ⟨p, .refl p, .refl p⟩

/-- Normalize an expression (identity in the trivial core). -/
def normalize (e : PathExpr (A := A) a b) :
    PathExpr (A := A) a b := e

end PathExpr
end Rewrite
end Path
end ComputationalPaths
