/-
# Stable Splitting and Snaith Splitting

This module records data for stable splittings of pointed spaces and the
Snaith splitting pattern using smash powers and indexed wedges.

## Key Results

- `unitPtd`, `suspPtd`, `iteratedSuspensionPtd`
- `smashPower`, `symmetricSmash`
- `IndexedWedge`, `indexedWedgeIn`
- `PtdEquiv`, `StableSplittingData`, `SnaithSplitting`

## References

- Snaith, "A stable decomposition of Omega Sigma X"
- HoTT Book, Chapter 8
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Homotopy.SuspensionLoop
import ComputationalPaths.Path.Homotopy.PointedMapCategory
import ComputationalPaths.Path.Homotopy.SmashProduct

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace StableSplitting

open PointedMapCategory

universe u v

/-! ## Basic pointed constructions -/

/-- The pointed unit type. -/
def unitPtd : PtdType.{u} :=
  { carrier := ULift Unit, pt := ⟨()⟩ }

/-- Suspension of a pointed type as a pointed type. -/
def suspPtd (X : PtdType.{u}) : PtdType.{u} where
  carrier := SuspensionLoop.Suspension X.carrier
  pt := SuspensionLoop.Suspension.north (X := X.carrier)

/-- Iterated suspension of a pointed type. -/
def iteratedSuspensionPtd : Nat → PtdType.{u} → PtdType.{u}
  | 0, X => X
  | n + 1, X => suspPtd (iteratedSuspensionPtd n X)

/-! ## Smash powers -/

/-- Smash power X^{∧ n}. -/
def smashPower : Nat → PtdType.{u} → PtdType.{u}
  | 0, _ => unitPtd
  | n + 1, X => SmashProduct.Smash X (smashPower n X)

/-- Formal symmetric smash power (symmetric quotient to be added later). -/
abbrev symmetricSmash (n : Nat) (X : PtdType.{u}) : PtdType.{u} :=
  smashPower n X

/-! ## Indexed wedges -/

/-- Relation identifying basepoints across a family of pointed types. -/
inductive IndexedWedgeRel {ι : Type u} (X : ι → PtdType.{v}) :
    (Sigma fun i => (X i).carrier) → (Sigma fun i => (X i).carrier) → Prop
  | base (i j : ι) :
      IndexedWedgeRel (X := X) ⟨i, (X i).pt⟩ ⟨j, (X j).pt⟩
  | refl (x) : IndexedWedgeRel (X := X) x x

/-- Wedge (coproduct) over an index type, identifying basepoints. -/
def IndexedWedge {ι : Type u} [Inhabited ι] (X : ι → PtdType.{v}) :
    PtdType.{max u v} where
  carrier := Quot (IndexedWedgeRel X)
  pt := Quot.mk _ ⟨default, (X default).pt⟩

/-- Inclusion of a summand into the indexed wedge (same-universe version). -/
def indexedWedgeIn {ι : Type u} [Inhabited ι] (X : ι → PtdType.{u}) (i : ι) :
    PtdMap (X i) (IndexedWedge X) where
  toFun := fun x => Quot.mk _ ⟨i, x⟩
  map_pt := by
    apply Quot.sound
    exact IndexedWedgeRel.base (X := X) i default

/-! ## Pointed equivalences -/

/-- Equivalence of pointed types via pointed maps. -/
structure PtdEquiv (X Y : PtdType.{u}) where
  /-- Forward pointed map. -/
  toMap : PtdMap X Y
  /-- Inverse pointed map. -/
  invMap : PtdMap Y X
  /-- Left inverse law. -/
  left_inv : Path (PtdMap.comp invMap toMap) (PtdMap.id X)
  /-- Right inverse law. -/
  right_inv : Path (PtdMap.comp toMap invMap) (PtdMap.id Y)

/-- Identity pointed equivalence. -/
def PtdEquiv.refl (X : PtdType.{u}) : PtdEquiv X X where
  toMap := PtdMap.id X
  invMap := PtdMap.id X
  left_inv := Path.stepChain (PtdMap.id_comp (PtdMap.id X))
  right_inv := Path.stepChain (PtdMap.comp_id (PtdMap.id X))

/-! ## Stable splitting data -/

/-- A stable splitting of X into Y after `level` suspensions. -/
structure StableSplittingData (X Y : PtdType.{u}) where
  /-- The suspension level where the splitting is defined. -/
  level : Nat
  /-- The pointed equivalence at that level. -/
  equiv : PtdEquiv (iteratedSuspensionPtd level X) Y

/-- Trivial stable splitting at level 0. -/
def stableSplittingData_refl (X : PtdType.{u}) : StableSplittingData X X where
  level := 0
  equiv := PtdEquiv.refl X

/-! ## Snaith splitting data -/

/-- Loop-suspension of a pointed type. -/
def loopSigmaPtd (X : PtdType.{u}) : PtdType.{u} :=
  loopPtd (suspPtd X)

/-- Summand in the Snaith splitting: the symmetric smash power. -/
def snaithSummand (X : PtdType.{u}) : Nat → PtdType.{u} :=
  fun n => symmetricSmash (Nat.succ n) X

/-- Wedge of Snaith summands. -/
def snaithWedge (X : PtdType.{u}) : PtdType.{u} :=
  IndexedWedge (snaithSummand X)

/-- Snaith splitting data for a pointed type. -/
structure SnaithSplitting (X : PtdType.{u}) where
  /-- The suspension level where the splitting is defined. -/
  level : Nat
  /-- The pointed equivalence capturing the splitting. -/
  equiv : PtdEquiv (iteratedSuspensionPtd level (loopSigmaPtd X)) (snaithWedge X)

/-! ## Summary -/

-- We packaged stable splitting data, smash powers, indexed wedges, and a
-- Snaith-style splitting interface for pointed spaces.

end StableSplitting
end Homotopy
end Path
end ComputationalPaths
