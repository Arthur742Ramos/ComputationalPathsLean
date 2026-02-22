/-
# Classifying spaces BG and the Milnor join

This module packages lightweight computational-paths definitions for the
classifying space `BG`, the Milnor join model for `EG`, the bar construction on
strict groups, and group cohomology data attached to `BG`.

## Key Results

- `bgBase`: basepoint of `BG`.
- `BarConstruction`, `barConstruction`: bar construction for strict groups.
- `JoinPower`, `MilnorJoin`, `EG`: Milnor join model for `EG`.
- `egProj`, `UniversalBundle`: universal bundle data `EG → BG`.
- `GroupCohomology`, `GroupCohomologyRing`: cohomology data for `BG`.

## References

- Milnor, "Construction of Universal Bundles"
- May, "Classifying Spaces and Fibrations"
- Brown, "Cohomology of Groups"
-/

import ComputationalPaths.Path.CompPath.DeloopingConstruction
import ComputationalPaths.Path.CompPath.JoinSpace
import ComputationalPaths.Path.Homotopy.LoopSpaceRecognition
import ComputationalPaths.Path.Algebra.GroupStructures

namespace ComputationalPaths
namespace Path
namespace CompPath

open Algebra
open Homotopy

universe u

/-! ## Classifying space basepoint -/

/-- The basepoint of the classifying space `BG`. -/
@[simp] noncomputable def bgBase (G : Type u) : BG G :=
  deloopingBase G

/-! ## Bar construction -/

/-- Bar construction for a strict group, viewed as a strict monoid. -/
abbrev BarConstruction (G : Type u) (S : StrictGroup G) :
    Type (u + 1) :=
  Homotopy.LoopSpaceRecognition.BarConstruction G S.toStrictMonoid

/-- Canonical bar construction on a strict group. -/
noncomputable def barConstruction (G : Type u) (S : StrictGroup G) : BarConstruction G S :=
  Homotopy.LoopSpaceRecognition.canonicalBar G S.toStrictMonoid

/-! ## Milnor join and the universal bundle -/

/-- Iterated join of `G` with itself. -/
noncomputable def JoinPower (G : Type u) : Nat → Type u
  | 0 => G
  | Nat.succ n => Join G (JoinPower G n)

/-- Milnor join: the sigma type of all finite joins of `G`. -/
noncomputable def MilnorJoin (G : Type u) : Type u :=
  Σ n : Nat, JoinPower G n

/-- Include a group element as the first stage of the Milnor join. -/
noncomputable def milnorJoinStage {G : Type u} (g : G) : MilnorJoin G :=
  ⟨0, g⟩

/-- The universal total space `EG`, modeled as the Milnor join. -/
abbrev EG (G : Type u) : Type u :=
  MilnorJoin G

/-- Include a group element into `EG`. -/
noncomputable def egStage {G : Type u} (g : G) : EG G :=
  milnorJoinStage g

/-- The projection `EG → BG`, constant to the basepoint. -/
noncomputable def egProj (G : Type u) : EG G → BG G :=
  fun _ => bgBase G

/-- Data for a universal bundle `EG → BG`. -/
structure UniversalBundle (G : Type u) (S : StrictGroup G) where
  /-- The total space `EG`. -/
  EG : Type u
  /-- The base space `BG`. -/
  BG : Type u
  /-- The projection `EG → BG`. -/
  proj : EG → BG

/-- The canonical Milnor join bundle over `BG`. -/
noncomputable def universalBundle (G : Type u) (S : StrictGroup G) : UniversalBundle G S :=
  { EG := EG G
    BG := BG G
    proj := egProj G }

/-! ## Group cohomology -/

/-- Cohomology groups associated to a classifying space. -/
structure CohomologyGroups where
  /-- The graded groups as a function from degree to a type. -/
  groups : Nat → Type u

/-- A cohomology ring attached to a space. -/
structure CohomologyRing where
  /-- The underlying type. -/
  carrier : Type u

/-- Group cohomology groups associated to `BG`. -/
structure GroupCohomology (G : Type u) (S : StrictGroup G)
    extends CohomologyGroups

/-- Group cohomology rings associated to `BG`. -/
structure GroupCohomologyRing (G : Type u) (S : StrictGroup G)
    extends CohomologyRing

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
