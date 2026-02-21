/-
# Tor Functor for Computational Paths

This module introduces a lightweight Tor bifunctor on pointed sets,
with functoriality laws witnessed by computational `Path`s.

## Key Definitions

- `TorFunctor`: bifunctor data on pointed sets with Path-based laws.
- `TorFunctor.trivial`: the trivial Tor functor landing in the one-point set.

## References

- Weibel, "An Introduction to Homological Algebra"
- Hatcher, "Algebraic Topology"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra

open HomologicalAlgebra

universe u v w

/-! ## Tor functor data -/

/-- Tor bifunctor data on pointed sets, with functoriality witnessed by `Path`. -/
structure TorFunctor where
  /-- Object map. -/
  mapObj : PointedSet.{u} → PointedSet.{v} → PointedSet.{w}
  /-- Morphism map. -/
  mapMor : {A A' : PointedSet.{u}} → {B B' : PointedSet.{v}} →
      PointedHom A A' → PointedHom B B' → PointedHom (mapObj A B) (mapObj A' B')
  /-- Identity preservation (as a `Path`). -/
  map_id : ∀ A B,
      Path (mapMor (PointedHom.id A) (PointedHom.id B))
        (PointedHom.id (mapObj A B))
  /-- Composition preservation (as a `Path`). -/
  map_comp :
      ∀ {A A' A'' : PointedSet.{u}} {B B' B'' : PointedSet.{v}}
        (f : PointedHom A A') (g : PointedHom A' A'')
        (h : PointedHom B B') (k : PointedHom B' B''),
        Path (mapMor (PointedHom.comp g f) (PointedHom.comp k h))
          (PointedHom.comp (mapMor g k) (mapMor f h))

namespace TorFunctor

private def torTrivialObj : PointedSet.{w} where
  carrier := PUnit
  zero := PUnit.unit

/-- The trivial Tor functor sending every pair to the one-point set. -/
def trivial : TorFunctor.{u, v, w} where
  mapObj := fun _ _ => torTrivialObj
  mapMor := by
    intro A A' B B' f g
    exact PointedHom.id torTrivialObj
  map_id := by
    intro A B
    exact Path.stepChain rfl
  map_comp := by
    intro A A' A'' B B' B'' f g h k
    apply Path.stepChain
    simpa using (PointedHom.id_comp (PointedHom.id torTrivialObj)).symm

end TorFunctor

end Algebra
end Path
end ComputationalPaths
