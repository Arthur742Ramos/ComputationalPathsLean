/-
# Higher Path Induction Principles

This module formalizes J-elimination and path induction for computational
paths, expressing elimination through the underlying propositional equality
carried by `Path.toEq`. It also records the resulting path-level UIP statements
and transport lemmas, including compatibility with rewrite equality (`RwEq`).

## Key Results

- `pathJ_toEq`: J-elimination on `Path.toEq`
- `pathJ`: Path induction for motives stable under `toEq`
- `toEq_unique`: uniqueness of identity proofs at the path level
- `transport_eq_pathJ`: transport derived from `pathJ_toEq`
- `transport_of_rweq`: transport respects rewrite equality

## References

- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace HigherPathInduction

universe u v w

variable {A : Type u}

/-! ## J-elimination for computational paths -/

/-- J-eliminator on the underlying propositional equality of paths. -/
def pathJ_toEq {a : A} (C : (b : A) → a = b → Sort v)
    (base : C a rfl) {b : A} (p : Path a b) : C b p.toEq := by
  cases p with
  | mk steps proof =>
      cases proof
      exact base

/-- Path induction for motives that are stable under equality of `toEq`. -/
def pathJ {a : A}
    (C : (b : A) → Path a b → Sort v)
    (respect :
      ∀ {b : A} {p q : Path a b}, p.toEq = q.toEq → C b p → C b q)
    (base : C a (Path.refl a)) {b : A} (p : Path a b) : C b p := by
  cases p with
  | mk steps proof =>
      cases proof
      exact respect (b := a)
        (p := Path.refl a)
        (q := Path.mk steps rfl)
        rfl base

/-! ## Path-level uniqueness of identity proofs -/

/-- Any two equality witnesses extracted from paths are equal. -/
theorem toEq_unique {a b : A} (p q : Path a b) : p.toEq = q.toEq := by
  apply Subsingleton.elim

/-- Canonical `ofEq` witnesses coincide for any two paths with the same endpoints. -/
@[simp] theorem ofEq_toEq_eq {a b : A} (p q : Path a b) :
    Path.stepChain p.toEq = Path.stepChain q.toEq := by
  exact
    Path.stepChain_eq_ofEq (a := a) (b := b) (h₁ := p.toEq) (h₂ := q.toEq)

/-! ## Transport and rewrite equality -/

/-- Transport derived from `pathJ_toEq` agrees with `Path.transport`. -/
theorem transport_eq_pathJ {a b : A} {D : A → Sort v}
    (p : Path a b) (x : D a) :
    pathJ_toEq (C := fun b (_ : a = b) => D b) x p =
      transport (D := D) p x := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

/-- Transport is invariant under rewrite equality. -/
theorem transport_of_rweq {a b : A} {D : A → Sort v}
    {p q : Path a b} (h : RwEq p q) (x : D a) :
    transport (D := D) p x = transport (D := D) q x := by
  exact transport_of_toEq_eq (D := D) (p := p) (q := q) (h := rweq_toEq h) x

/-- Rewrite-equivalent paths induce path-equivalent transported terms. -/
def transport_path_of_rweq {a b : A} {D : A → Type v}
    {p q : Path a b} (h : RwEq p q) (x : D a) :
    Path (transport (D := D) p x) (transport (D := D) q x) :=
  Path.stepChain (transport_of_rweq (D := D) (p := p) (q := q) h x)

/-- Compose transport witnesses along two rewrite equalities. -/
def transport_path_of_rweq_comp {a b : A} {D : A → Type v}
    {p q r : Path a b} (h₁ : RwEq p q) (h₂ : RwEq q r) (x : D a) :
    Path (transport (D := D) p x) (transport (D := D) r x) :=
  Path.trans
    (transport_path_of_rweq (D := D) (p := p) (q := q) h₁ x)
    (transport_path_of_rweq (D := D) (p := q) (q := r) h₂ x)

/-! ## Summary -/

/-!
We recorded J-elimination for computational paths via `toEq`, derived a
path-level UIP statement for equality witnesses, and showed that transport
respects rewrite equality.
-/

end HigherPathInduction
end Path
end ComputationalPaths
