/-
# Reflexivity Theorem

This file establishes the Reflexivity Theorem: any path constructed from
reflexivity via the path operations will rewrite back to reflexivity.

## Statement

> For any type A and a loop path p : a = a, if p is obtained by applying
> path operations (symmetry, transitivity, congruence, etc.) to refl,
> then p is RwEq to refl.

## Implementation

In our Lean implementation, this corresponds to:
- Every path `p : Path a a` with `p.toEq = rfl` is `RwEq` to `Path.refl a`

This follows from:
1. `Step.canon`: Any path p steps to `Path.ofEq p.toEq`
2. `rweq_canon`: `RwEq p (Path.ofEq p.toEq)`
3. When `p.toEq = rfl`: `RwEq (Path.ofEq rfl) (Path.refl a)` via `rweq_canon.symm`

## Definitional Rules

The following rules are satisfied definitionally:
- `congrArg f (refl a) = refl (f a)` by rfl
- `app (refl f) a = refl (f a)` by rfl
- `lamCongr (fun x => refl (f x)) = refl f` by rfl

Applying constructors to refl produces refl definitionally, so these rules
don't need explicit Step constructors.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths.Path

universe u

/-- Helper: Path.ofEq rfl is RwEq to Path.refl a.
    This follows from rweq_canon applied to refl, since (refl a).toEq = rfl. -/
theorem rweq_ofEq_rfl_refl {A : Type u} (a : A) :
    RwEq (Path.ofEq (rfl : a = a)) (Path.refl a) :=
  (rweq_canon (Path.refl a)).symm

/-- The Reflexivity Theorem: Any loop path (path from a to a) with trivial
    equality proof is RwEq to refl.

    If a path `p : Path a a` has `p.toEq = rfl`, then `p` rewrites to `refl a`. -/
theorem reflexivity_theorem {A : Type u} {a : A} (p : Path a a)
    (hp : p.toEq = rfl) : RwEq p (Path.refl a) := by
  -- First, p is RwEq to Path.ofEq p.toEq
  have h1 : RwEq p (Path.ofEq p.toEq) := rweq_canon p
  -- Since p.toEq = rfl, we have Path.ofEq p.toEq = Path.ofEq rfl
  have h2 : RwEq (Path.ofEq p.toEq) (Path.ofEq (rfl : a = a)) := by
    cases hp; exact RwEq.refl _
  -- Path.ofEq rfl is RwEq to Path.refl a
  have h3 : RwEq (Path.ofEq (rfl : a = a)) (Path.refl a) := rweq_ofEq_rfl_refl a
  exact RwEq.trans (RwEq.trans h1 h2) h3

/-- Alternative formulation using proof equality. -/
theorem reflexivity_theorem' {A : Type u} {a : A} (p : Path a a)
    (hp : p.proof = rfl) : RwEq p (Path.refl a) :=
  reflexivity_theorem p hp

/-- Any path constructed from refl via operations that preserve toEq
    will satisfy the reflexivity theorem. Since congrArg, app, lamCongr
    all preserve the underlying equality, paths built from refl using
    these operations will have toEq = rfl and thus rewrite to refl. -/

-- Rule 45 (mxp): μf(ρx) ▷ ρf(x)
-- congrArg f (refl a) = refl (f a)
example {A B : Type u} (f : A → B) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := rfl

-- Rule 46 (nxp): ν(ρ) ▷ ρf(x)
-- app (refl f) a = refl (f a)
example {A B : Type u} (f : A → B) (a : A) :
    Path.app (Path.refl f) a = Path.refl (f a) := rfl

-- Rule 47 (xxp): ξ(ρ) ▷ ρ
-- lamCongr (fun x => refl (f x)) = refl f
example {A B : Type u} (f : A → B) :
    Path.lamCongr (fun x => Path.refl (f x)) = Path.refl f := rfl

end ComputationalPaths.Path
