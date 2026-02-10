/-
# Ext Functor for Computational Paths

This module introduces a minimal Ext bifunctor interface where all
functoriality laws are witnessed by computational paths. A trivial
instance is provided to demonstrate the interface without axioms.

## Key Results

- `ExtFunctor`: bifunctor data with Path-valued laws.
- `ExtFunctor.trivial`: constant Ext functor on `PUnit`.

## References

- Weibel, "An Introduction to Homological Algebra", Chapter 3
- Mac Lane, "Homology", Chapter II
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Ext bifunctor data -/

/-- Ext bifunctor data, contravariant in the first argument and covariant in the second. -/
structure ExtFunctor (A : Type u) (B : Type v) where
  /-- Object assignment for Ext. -/
  obj : A → B → Type w
  /-- Contravariant action on the first argument. -/
  map_left : {a a' : A} → Path a a' → (b : B) → obj a' b → obj a b
  /-- Covariant action on the second argument. -/
  map_right : {b b' : B} → Path b b' → (a : A) → obj a b → obj a b'
  /-- Left identity for the contravariant action. -/
  map_left_id : ∀ a b (x : obj a b),
    Path (map_left (Path.refl a) b x) x
  /-- Right identity for the covariant action. -/
  map_right_id : ∀ a b (x : obj a b),
    Path (map_right (Path.refl b) a x) x
  /-- Contravariant composition law. -/
  map_left_comp :
    ∀ {a0 a1 a2 : A} (p : Path a0 a1) (q : Path a1 a2) (b : B) (x : obj a2 b),
      Path (map_left (Path.trans p q) b x)
        (map_left p b (map_left q b x))
  /-- Covariant composition law. -/
  map_right_comp :
    ∀ {b0 b1 b2 : B} (p : Path b0 b1) (q : Path b1 b2) (a : A) (x : obj a b0),
      Path (map_right (Path.trans p q) a x)
        (map_right q a (map_right p a x))
  /-- Interchange law for the two actions. -/
  map_left_right :
    ∀ {a0 a1 : A} {b0 b1 : B} (p : Path a0 a1) (q : Path b0 b1) (x : obj a1 b0),
      Path (map_right q a0 (map_left p b0 x))
        (map_left p b1 (map_right q a1 x))

namespace ExtFunctor

/-- The trivial Ext functor (constant on `PUnit`). -/
def trivial (A : Type u) (B : Type v) : ExtFunctor A B where
  obj := fun _ _ => PUnit
  map_left := by
    intro _ _ _ _ _
    exact PUnit.unit
  map_right := by
    intro _ _ _ _ _
    exact PUnit.unit
  map_left_id := by
    intro _ _ x
    cases x
    exact Path.refl _
  map_right_id := by
    intro _ _ x
    cases x
    exact Path.refl _
  map_left_comp := by
    intro _ _ _ _ _ _ x
    cases x
    exact Path.refl _
  map_right_comp := by
    intro _ _ _ _ _ _ x
    cases x
    exact Path.refl _
  map_left_right := by
    intro _ _ _ _ _ _ x
    cases x
    exact Path.refl _

end ExtFunctor

/-! ## Summary -/

/-!
We introduced a Path-valued Ext bifunctor interface and a trivial
instance that satisfies the functoriality laws by reflexivity.
-/

end Algebra
end Path
end ComputationalPaths
