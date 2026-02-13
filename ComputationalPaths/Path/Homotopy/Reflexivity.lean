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
1. `Step.canon`: Any path p steps to `Path.stepChain p.toEq`
2. `rweq_canon`: `RwEq p (Path.stepChain p.toEq)`
3. When `p.toEq = rfl`: `RwEq (Path.stepChain rfl) (Path.refl a)` via `rweq_canon.symm`

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

/-- `Path.stepChain rfl` rewrites to `Path.refl`.

These two paths represent the same identity operation:
- `refl a` has an empty step list `[]`
- `ofEq rfl` has a single identity step `[Step.mk a a rfl]`

We can relate them via the primitive rewrite rule `Step.transport_refl_beta`,
instantiated with a constant family. This avoids the unsound global
canonicalization rule (`Step.canon`). -/
theorem rweq_ofEq_rfl_refl {A : Type u} (a : A) :
    RwEq (Path.stepChain (rfl : a = a)) (Path.refl a) := by
  -- `transport (refl ⋆) a = a` is definitional for the constant family `fun _ => A`.
  simpa using
    (RwEq.step <|
      Step.transport_refl_beta (A := PUnit) (B := fun _ : PUnit => A)
        (a := PUnit.unit) (x := a))

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

/-! ## RwEq example -/

/-- Double symmetry gives a second path witness that is RwEq to the original. -/
theorem rweq_symm_symm {A : Type u} {a b : A} (p : Path a b) :
    RwEq (Path.symm (Path.symm p)) p := by
  exact rweq_ss (p := p)

end ComputationalPaths.Path
