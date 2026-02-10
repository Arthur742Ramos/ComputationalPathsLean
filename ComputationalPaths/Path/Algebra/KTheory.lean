/-
# Algebraic K-theory (K0) via computational paths

This module introduces a lightweight, Path-based K0 construction for strict
monoids.  We model "virtual" objects as formal pairs and identify them up to
stabilization witnessed by `Path`.

## Key Definitions

- `Virtual`: formal pairs of monoid elements
- `stabilize`: stabilization by a monoid element
- `K0Rel`: Path-based stable equivalence
- `K0`: quotient of virtual objects by `K0Rel`
- `K0PointedSet`: pointed-set wrapper for K0

## References

- Weibel, "The K-book"
- Hatcher, "Vector Bundles and K-Theory"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace KTheory

open HomologicalAlgebra

universe u

/-! ## Formal pairs and stabilization -/

/-- Formal pairs of monoid elements, used as virtual objects for K0. -/
def Virtual (M : Type u) : Type u := M × M

/-- Stabilize a virtual object by a monoid element. -/
def stabilize {M : Type u} (S : StrictMonoid M) (x : Virtual M) (c : M) : Virtual M :=
  (S.mul x.1 c, S.mul x.2 c)

/-! ## K0 relation and quotient -/

/-- Stable equivalence using a Path witness after stabilization. -/
def K0Rel {M : Type u} (S : StrictMonoid M) (x y : Virtual M) : Prop :=
  ∃ c : M, Nonempty (Path (stabilize S x c) (stabilize S y c))

/-- K0 of a strict monoid as a quotient by stable Path equivalence. -/
def K0 {M : Type u} (S : StrictMonoid M) : Type u :=
  Quot (K0Rel (S := S))

/-- Embed a monoid element into K0 via the formal pair `(x, 1)`. -/
def toK0 {M : Type u} (S : StrictMonoid M) (x : M) : K0 S :=
  Quot.mk _ (x, S.one)

/-- The basepoint of K0. -/
def zero {M : Type u} (S : StrictMonoid M) : K0 S :=
  toK0 S S.one

/-- Stable equivalence from an explicit equality. -/
theorem k0rel_of_eq {M : Type u} {S : StrictMonoid M}
    {x y : Virtual M} (c : M)
    (h : stabilize S x c = stabilize S y c) : K0Rel S x y :=
  ⟨c, ⟨Path.ofEq h⟩⟩

/-- Reflexivity of the K0 relation. -/
theorem k0rel_refl {M : Type u} (S : StrictMonoid M) (x : Virtual M) : K0Rel S x x := by
  refine ⟨S.one, ?_⟩
  exact ⟨Path.refl (stabilize S x S.one)⟩

/-- Symmetry of the K0 relation. -/
theorem k0rel_symm {M : Type u} {S : StrictMonoid M} {x y : Virtual M} :
    K0Rel S x y → K0Rel S y x := by
  intro h
  rcases h with ⟨c, ⟨p⟩⟩
  exact ⟨c, ⟨Path.symm p⟩⟩

/-! ## Pointed-set wrapper -/

/-- Package K0 as a pointed set. -/
def K0PointedSet {M : Type u} (S : StrictMonoid M) : PointedSet.{u} where
  carrier := K0 S
  zero := zero S

/-! ## Summary

We defined a Path-based stabilization relation on virtual objects of a strict
monoid, formed the quotient K0, and packaged it as a pointed set.
-/

end KTheory
end Algebra
end Path
end ComputationalPaths
