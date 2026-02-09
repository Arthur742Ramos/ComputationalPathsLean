/-
# Classifying space functor for strict groups

This module packages the delooping construction into the classifying space
functor `B : Groups → Spaces`, and records the naturality of the
`π₁(BG) ≃ G` identification.

## Key Results

- `B`: classifying space functor on objects
- `BMap`: action on group homomorphisms
- `BMap_id`, `BMap_comp`: functoriality
- `piOneBGEquiv`: `π₁(BG) ≃ G`
- `piOneBGEquiv_naturality`: naturality of the equivalence

## References

- HoTT Book, Chapter 6 (classifying spaces)
- de Queiroz et al., SAJL 2016 (computational paths)
-/

import ComputationalPaths.Path.CompPath.DeloopingConstruction
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace CompPath

open Algebra

universe u

/-! ## Classifying space functor -/

/-- Classifying space functor on objects (alias of `BG`). -/
abbrev B (G : Type u) : Type u := BG G

/-- The classifying space map induced by a group homomorphism. -/
def BMap {G H : Type u} {S : StrictGroup G} {T : StrictGroup H} (_ : GroupHom G H S T) :
    B G → B H
  | Delooping.base => Delooping.base

/-- Identity homomorphisms act as the identity on classifying spaces. -/
theorem BMap_id {G : Type u} (S : StrictGroup G) :
    BMap (G := G) (H := G) (S := S) (T := S) (GroupHom.id S) = id := by
  funext x
  cases x
  rfl

/-- Composition of homomorphisms maps to composition of classifying space maps. -/
theorem BMap_comp {G H K : Type u} {S : StrictGroup G} {T : StrictGroup H} {U : StrictGroup K}
    (f : GroupHom G H S T) (g : GroupHom H K T U) :
    BMap (G := G) (H := K) (S := S) (T := U) (GroupHom.comp f g) =
      fun x =>
        BMap (G := H) (H := K) (S := T) (T := U) g
          (BMap (G := G) (H := H) (S := S) (T := T) f x) := by
  funext x
  cases x
  rfl

/-! ## π₁ of classifying spaces -/

/-- Naturality of the `π₁(BG) ≃ G` equivalence. -/
theorem piOneBGEquiv_naturality {G H : Type u} {S : StrictGroup G} {T : StrictGroup H}
    (f : GroupHom G H S T) (x : piOneBG (S := S)) :
    piOneBGEquiv (S := T) (piOneBGMap (S := S) (T := T) f x) =
      f (piOneBGEquiv (S := S) x) := by
  simpa [piOneBGEquiv, piOneBGMap] using
    (deloopingOmegaEncode_map (S := S) (T := T) f x)

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
