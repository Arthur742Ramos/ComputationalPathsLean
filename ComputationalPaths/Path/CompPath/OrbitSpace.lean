/-
# Orbit spaces G/H via computational paths

This module defines the orbit space `G/H` as the quotient of a strict group `G`
by the left action of a subgroup `H`.  We package the induced strict group on
subgroup elements, the left multiplication action, and the resulting orbit
projection with its canonical path.

## Key Results

- `subgroupStrictGroup`: strict group structure on subgroup elements.
- `subgroupLeftAction`: left action of a subgroup on its ambient group.
- `OrbitSpace`, `orbitMap`, `orbitPath`: the quotient `G/H` and its canonical paths.
-/

import ComputationalPaths.Path.EquivariantPaths

namespace ComputationalPaths
namespace Path
namespace CompPath

open Algebra
open EquivariantPaths

universe u

/-! ## Subgroup action data -/

variable {G : Type u} {S : StrictGroup G}

/-- The carrier type of a subgroup. -/
abbrev SubgroupCarrier (H : Subgroup G S) : Type u :=
  {g : G // H.carrier g}

/-- Strict group structure induced by a subgroup. -/
def subgroupStrictGroup (H : Subgroup G S) : StrictGroup (SubgroupCarrier H) := by
  refine
    { mul := ?_
      one := ?_
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      inv := ?_
      mul_left_inv := ?_
      mul_right_inv := ?_ }
  · intro g h
    exact ⟨S.mul g.1 h.1, H.mul_mem g.2 h.2⟩
  · exact ⟨S.one, H.one_mem⟩
  · intro x y z
    apply Subtype.ext
    exact S.mul_assoc x.1 y.1 z.1
  · intro x
    apply Subtype.ext
    exact S.one_mul x.1
  · intro x
    apply Subtype.ext
    exact S.mul_one x.1
  · intro g
    exact ⟨S.inv g.1, H.inv_mem g.2⟩
  · intro x
    apply Subtype.ext
    exact S.mul_left_inv x.1
  · intro x
    apply Subtype.ext
    exact S.mul_right_inv x.1

/-- Left multiplication action of a subgroup on its ambient group. -/
def subgroupLeftAction (H : Subgroup G S) :
    GroupAction (SubgroupCarrier H) (subgroupStrictGroup H) G where
  act := fun h g => S.mul h.1 g
  act_one := by
    intro g
    simpa [subgroupStrictGroup] using (S.one_mul g)
  act_mul := by
    intro g h x
    simpa [subgroupStrictGroup] using (S.mul_assoc g.1 h.1 x)

/-! ## Orbit space G/H -/

/-- Orbit space `G/H` of a subgroup acting by left multiplication. -/
abbrev OrbitSpace (H : Subgroup G S) : Type u :=
  EquivariantPaths.OrbitSpace (A := subgroupLeftAction (S := S) H)

/-- Projection `G → G/H`. -/
def orbitMap (H : Subgroup G S) : G → OrbitSpace (S := S) H :=
  EquivariantPaths.orbitMap (A := subgroupLeftAction (S := S) H)

/-- Path in `G/H` induced by left multiplication by a subgroup element. -/
def orbitPath (H : Subgroup G S) (h : SubgroupCarrier H) (x : G) :
    Path (orbitMap (S := S) H x) (orbitMap (S := S) H (S.mul h.1 x)) :=
  Path.stepChain (EquivariantPaths.orbitMap_act (A := subgroupLeftAction (S := S) H) h x)

/-- Path in `G/H` induced by left multiplication by a member of `H`. -/
def orbitPath_of_mem (H : Subgroup G S) {h : G} (hh : H.carrier h) (x : G) :
    Path (orbitMap (S := S) H x) (orbitMap (S := S) H (S.mul h x)) :=
  orbitPath (H := H) ⟨h, hh⟩ x

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
