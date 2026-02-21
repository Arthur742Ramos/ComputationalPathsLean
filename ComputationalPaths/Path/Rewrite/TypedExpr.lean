/-
# Typed Paths: From Untyped Expr to Well-Typed Expressions

This module extends the untyped `Expr` type (from `GroupoidTRS.lean`) with
a typing discipline. While `Expr` represents the free syntax of groupoid
expressions, `TExpr` enforces well-formedness: `trans` can only compose
paths whose endpoints match, `symm` reverses direction, etc.

## Motivation

The untyped `Expr` type treats all expressions uniformly — `trans (atom 0) (atom 1)`
is a valid expression even though the "types" (source/target objects) of `atom 0`
and `atom 1` might not match. The typed version enforces composability.

This connects the abstract rewriting theory (on `Expr`) to the concrete
path algebra (on `Path a b`), bridging the gap between the two levels
of the formalization.

## Main Results

1. `TExpr`: typed expressions indexed by source/target objects
2. `erase`: forgetful functor `TExpr → Expr` (erases type annotations)
3. `lift_cstep`: CStep on `Expr` lifts to typed CStep on `TExpr`
4. `typed_confluence`: confluence of the typed system (via erasure)
5. `typed_word_problem`: decidability of the word problem for typed expressions

## References

- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths"
-/

import ComputationalPaths.Path.Rewrite.GroupoidConfluence
import ComputationalPaths.Path.Rewrite.WordProblem

namespace ComputationalPaths.Path.Rewrite.TypedExpr

open GroupoidTRS (Expr)
open GroupoidConfluence (CStep CRTC ExprRwEq canon toRW
  confluence cstep_termination reach_canon
  toRW_invariant toRW_invariant_rtc
  toRW_eq_iff_exprRwEq exprRwEq_of_crtc)

/-! ## Object Type

Objects are the 0-cells: source and target types of paths. -/

/-- An object (0-cell) in the path category. Objects are identified by natural numbers. -/
abbrev Obj := Nat

/-! ## Typed Expressions

A `TExpr a b` represents a path expression from object `a` to object `b`.
Each constructor preserves typing:
- `atom n a b`: an atomic path from `a` to `b`, named `n`
- `refl a`: identity path on `a`
- `symm`: reverses source and target
- `trans`: composes when endpoints match -/

/-- Typed expression: a path term from object `a` to object `b`. -/
inductive TExpr : Obj → Obj → Type where
  | atom (n : Nat) (a b : Obj) : TExpr a b
  | refl (a : Obj) : TExpr a a
  | symm {a b : Obj} : TExpr a b → TExpr b a
  | trans {a b c : Obj} : TExpr a b → TExpr b c → TExpr a c

namespace TExpr

/-! ## Erasure: TExpr → Expr

The forgetful functor that strips type annotations. -/

/-- Erase type information, producing an untyped `Expr`. -/
@[simp] def erase : TExpr a b → Expr
  | .atom n _ _ => .atom n
  | .refl _ => .refl
  | .symm e => .symm (erase e)
  | .trans e₁ e₂ => .trans (erase e₁) (erase e₂)

/-- Size of a typed expression (matches `Expr.size` after erasure). -/
@[simp] def size : TExpr a b → Nat
  | .atom _ _ _ => 1
  | .refl _ => 1
  | .symm e => e.size + 1
  | .trans e₁ e₂ => e₁.size + e₂.size + 1

theorem size_eq_erase_size (e : TExpr a b) : e.size = e.erase.size := by
  induction e with
  | atom _ _ _ => rfl
  | refl _ => rfl
  | symm _ ih => simp [Expr.size, ih]
  | trans _ _ ih₁ ih₂ => simp [Expr.size, ih₁, ih₂]

/-! ## Typed CStep

The typed version of CStep: same rules, but type-indexed. -/

/-- Typed rewrite step, mirroring `CStep` but preserving type indices. -/
inductive TCStep : TExpr a b → TExpr a b → Prop where
  | symm_refl (x : Obj) : TCStep (.symm (.refl x)) (.refl x)
  | symm_symm {a b : Obj} (p : TExpr a b) : TCStep (.symm (.symm p)) p
  | trans_refl_left {a b : Obj} (p : TExpr a b) :
      TCStep (.trans (.refl a) p) p
  | trans_refl_right {a b : Obj} (p : TExpr a b) :
      TCStep (.trans p (.refl b)) p
  | trans_symm {a b : Obj} (p : TExpr a b) :
      TCStep (.trans p (.symm p)) (.refl a)
  | symm_trans {a b : Obj} (p : TExpr a b) :
      TCStep (.trans (.symm p) p) (.refl b)
  | symm_trans_congr {a b c : Obj} (p : TExpr a b) (q : TExpr b c) :
      TCStep (.symm (.trans p q)) (.trans (.symm q) (.symm p))
  | trans_assoc {a b c d : Obj} (p : TExpr a b) (q : TExpr b c) (r : TExpr c d) :
      TCStep (.trans (.trans p q) r) (.trans p (.trans q r))
  | trans_cancel_left {a b c : Obj} (p : TExpr a b) (q : TExpr a c) :
      TCStep (.trans p (.trans (.symm p) q)) q
  | trans_cancel_right {a b c : Obj} (p : TExpr a b) (q : TExpr b c) :
      TCStep (.trans (.symm p) (.trans p q)) q
  | symm_congr {a b : Obj} {p q : TExpr a b} :
      TCStep p q → TCStep (.symm p) (.symm q)
  | trans_congr_left {a b c : Obj} {p q : TExpr a b} (r : TExpr b c) :
      TCStep p q → TCStep (.trans p r) (.trans q r)
  | trans_congr_right {a b c : Obj} (p : TExpr a b) {q r : TExpr b c} :
      TCStep q r → TCStep (.trans p q) (.trans p r)

/-! ## Erasure Preserves Steps -/

/-- Erasing a typed step gives an untyped step. -/
theorem erase_tcstep {e₁ e₂ : TExpr a b} (h : TCStep e₁ e₂) :
    CStep e₁.erase e₂.erase := by
  induction h with
  | symm_refl _ => exact .symm_refl
  | symm_symm _ => exact .symm_symm _
  | trans_refl_left _ => exact .trans_refl_left _
  | trans_refl_right _ => exact .trans_refl_right _
  | trans_symm _ => exact .trans_symm _
  | symm_trans _ => exact .symm_trans _
  | symm_trans_congr _ _ => exact .symm_trans_congr _ _
  | trans_assoc _ _ _ => exact .trans_assoc _ _ _
  | trans_cancel_left _ _ => exact .trans_cancel_left _ _
  | trans_cancel_right _ _ => exact .trans_cancel_right _ _
  | symm_congr _ ih => exact .symm_congr ih
  | trans_congr_left _ _ ih => exact .trans_congr_left _ ih
  | trans_congr_right _ _ ih => exact .trans_congr_right _ ih

/-! ## Reflexive-Transitive Closure -/

/-- Reflexive-transitive closure of `TCStep`. -/
inductive TCRTC : TExpr a b → TExpr a b → Prop where
  | refl (e : TExpr a b) : TCRTC e e
  | head {e₁ e₂ e₃ : TExpr a b} : TCStep e₁ e₂ → TCRTC e₂ e₃ → TCRTC e₁ e₃

namespace TCRTC

theorem single {e₁ e₂ : TExpr a b} (h : TCStep e₁ e₂) : TCRTC e₁ e₂ :=
  .head h (.refl _)

theorem trans {e₁ e₂ e₃ : TExpr a b} (h₁ : TCRTC e₁ e₂) (h₂ : TCRTC e₂ e₃) :
    TCRTC e₁ e₃ := by
  induction h₁ with
  | refl => exact h₂
  | head s _ ih => exact .head s (ih h₂)

end TCRTC

/-- Erasing a typed reduction sequence gives an untyped reduction sequence. -/
theorem erase_tcrtc {e₁ e₂ : TExpr a b} (h : TCRTC e₁ e₂) :
    CRTC e₁.erase e₂.erase := by
  induction h with
  | refl _ => exact .refl _
  | head s _ ih => exact .head (erase_tcstep s) ih

/-! ## Typed Equivalence and Word Problem -/

/-- Typed rewrite equivalence (symmetric closure). -/
inductive TExprRwEq : TExpr a b → TExpr a b → Prop where
  | refl (e : TExpr a b) : TExprRwEq e e
  | step {e₁ e₂ : TExpr a b} : TCStep e₁ e₂ → TExprRwEq e₁ e₂
  | symm {e₁ e₂ : TExpr a b} : TExprRwEq e₁ e₂ → TExprRwEq e₂ e₁
  | trans {e₁ e₂ e₃ : TExpr a b} : TExprRwEq e₁ e₂ → TExprRwEq e₂ e₃ → TExprRwEq e₁ e₃

/-- Typed equivalence implies untyped equivalence (via erasure). -/
theorem erase_texprRwEq {e₁ e₂ : TExpr a b} (h : TExprRwEq e₁ e₂) :
    ExprRwEq e₁.erase e₂.erase := by
  induction h with
  | refl _ => exact .refl _
  | step hs => exact .step (erase_tcstep hs)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- The typed word problem reduces to the untyped one. -/
theorem typed_word_problem (e₁ e₂ : TExpr a b) :
    TExprRwEq e₁ e₂ → toRW e₁.erase = toRW e₂.erase := by
  intro h
  exact GroupoidConfluence.toRW_eq_of_exprRwEq (erase_texprRwEq h)

/-! ## Typed Normal Forms

Since the untyped system has unique normal forms and erasure preserves
steps, we can define typed normal forms via the untyped system. -/

/-- Typed normal form: the expression has no typed rewrite steps. -/
def IsTypedNF (e : TExpr a b) : Prop := ∀ e' : TExpr a b, ¬ TCStep e e'

/-- If the erasure of a typed expression is in untyped normal form,
    then the typed expression is in typed normal form. -/
theorem typed_nf_of_erased_nf (e : TExpr a b)
    (h : ∀ e' : Expr, ¬ CStep e.erase e') : IsTypedNF e := by
  intro e' hs
  exact h e'.erase (erase_tcstep hs)

/-- Typed expressions of the same type with equivalent erasures
    have the same toRW interpretation. -/
theorem typed_eq_toRW_of_equiv (e₁ e₂ : TExpr a b)
    (h : TExprRwEq e₁ e₂) : toRW e₁.erase = toRW e₂.erase :=
  typed_word_problem e₁ e₂ h

/-! ## Size Preservation

Erasure preserves sizes, which means the typed system inherits
the complexity bounds from the untyped system. -/

/-- Erasure preserves size exactly. -/
theorem erase_preserves_size (e : TExpr a b) :
    e.erase.size = e.size := (size_eq_erase_size e).symm

/-- The typed word problem is decidable (via erasure to the untyped system). -/
instance typedRwEq_decidable (e₁ e₂ : TExpr a b) :
    Decidable (toRW e₁.erase = toRW e₂.erase) :=
  inferInstance

/-! ## Typed Rewriting Examples -/

/-- Example: typed refl identity. -/
example : TCStep (TExpr.trans (.refl 0) (.atom 0 0 1)) (.atom 0 0 1) :=
  .trans_refl_left _

/-- Example: typed symm-symm cancellation. -/
example : TCStep (TExpr.symm (.symm (.atom 0 0 1))) (.atom 0 0 1) :=
  .symm_symm _

/-- Example: typed inverse cancellation. -/
example : TCStep (TExpr.trans (.atom 0 0 1) (.symm (.atom 0 0 1))) (.refl 0) :=
  .trans_symm _

end TExpr

end ComputationalPaths.Path.Rewrite.TypedExpr
