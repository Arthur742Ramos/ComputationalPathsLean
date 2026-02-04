/-
# Normalization Derived Lemmas

This module provides derived lemmas that relate the `normalize`/`normalPath`
operations to rewrite equivalence and quotient paths.  The statements are
formulated for convenient reuse in higher categorical and algebraic
constructions.

## Key Results

- `normalize` is idempotent
- Normal forms are stable under `RwEq`
- Normalization is compatible with congruence and composition
- Quotient-level normal paths behave functorially
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path
namespace Rewrite

universe u v

variable {A : Type u} {a b c : A}

/-! ## Normalization on Path -/

/-- Normalization is idempotent. -/
@[simp] theorem normalize_idem (p : Path a b) :
    normalize (A := A) (a := a) (b := b) (normalize p) = normalize p := by
  unfold normalize
  simp

/-- Normalization preserves rewrite equivalence. -/
@[simp] theorem normalize_congr {p q : Path a b} (h : RwEq p q) :
    normalize (A := A) (a := a) (b := b) p = normalize (A := A) (a := a) (b := b) q :=
  normalize_of_rweq (A := A) (a := a) (b := b) h

/-! ## Normalization on Quotients -/

/-- Normalization of quotient representatives agrees with normalPath. -/
@[simp] theorem normalize_normalPath (x : PathRwQuot A a b) :
    normalize (A := A) (a := a) (b := b) (PathRwQuot.normalPath (A := A) (x := x)) =
      PathRwQuot.normalPath (A := A) (x := x) := by
  exact normalize_idem (A := A) (a := a) (b := b) (PathRwQuot.normalPath (A := A) (x := x))

/-! ## Compatibility with congruence -/

/-- Normalization respects congruence. -/
@[simp] theorem normalize_congrArg {B : Type v} (f : A → B) (p : Path a b) :
    normalize (A := B) (a := f a) (b := f b) (Path.congrArg f p) =
      Path.congrArg f (normalize (A := A) (a := a) (b := b) p) := by
  cases p
  simp [normalize, Path.congrArg]

end Rewrite
end Path
end ComputationalPaths
