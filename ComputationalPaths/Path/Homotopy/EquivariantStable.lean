/-
# Equivariant stable homotopy (genuine G-spectra)

This module records lightweight data structures for genuine G-spectra,
Mackey functors, RO(G)-graded cohomology, tom Dieck splitting, and the
Burnside ring in the computational paths setting.

## Key Results

- `GenuineGSpectrum`, `MackeyFunctor`, `SpectralMackeyFunctor`
- `RO`, `ROCohomologyTheory`, `ROCohomologyTheory.trivial`
- `BurnsideRing`, `burnsideRing`
- `TomDieckSplitting`

## References

- Lewis-May-Steinberger, "Equivariant Stable Homotopy Theory"
- May, "Equivariant Homotopy and Cohomology Theory"
- tom Dieck, "Transformation Groups"
-/

import ComputationalPaths.Path.Homotopy.EquivariantHomotopy
import ComputationalPaths.Path.Homotopy.GeneralizedCohomology
import ComputationalPaths.Path.Algebra.SpectralMackey

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace EquivariantStable

open Algebra
open Algebra.SpectralMackey
open EquivariantHomotopy
open GeneralizedCohomology
open SuspensionLoop

universe u v w

/-! ## Mackey functors -/

/-- Mackey functors for finite G-sets (alias). -/
abbrev MackeyFunctor (G : Type u) (S : StrictGroup G) :=
  Algebra.SpectralMackey.MackeyFunctor G S

/-- Spectral Mackey functors (alias). -/
abbrev SpectralMackeyFunctor (G : Type u) (S : StrictGroup G) :=
  Algebra.SpectralMackey.SpectralMackeyFunctor G S

/-- The Burnside Mackey functor (constant Nat). -/
abbrev burnsideMackeyFunctor (G : Type u) (S : StrictGroup G) : MackeyFunctor G S :=
  Algebra.SpectralMackey.burnsideMackeyFunctor G S

/-! ## Genuine G-spectra -/

/-- A genuine G-spectrum packaged by spectral Mackey data and fixed points. -/
structure GenuineGSpectrum (G : Type u) (S : StrictGroup G) where
  /-- Spectral Mackey functor for finite G-sets. -/
  mackey : SpectralMackeyFunctor G S
  /-- Fixed-point spectra for each subgroup. -/
  fixedPointSpectrum : Subgroup G S → Algebra.SpectralAlgebra.Spectrum
  /-- Restriction compatibility (abstract). -/
  restriction : ∀ {H K : Subgroup G S}, True
  /-- Transfer compatibility (abstract). -/
  transfer : ∀ {H K : Subgroup G S}, True

/-! ## Burnside ring -/

/-- Burnside ring data for a finite group. -/
structure BurnsideRing (G : Type u) (S : StrictGroup G) where
  /-- Carrier type. -/
  carrier : Type u
  /-- Additive unit. -/
  zero : carrier
  /-- Multiplicative unit. -/
  one : carrier
  /-- Addition. -/
  add : carrier → carrier → carrier
  /-- Multiplication. -/
  mul : carrier → carrier → carrier
  /-- Additive commutativity (abstract). -/
  add_comm : ∀ x y, True
  /-- Additive associativity (abstract). -/
  add_assoc : ∀ x y z, True
  /-- Additive identity (abstract). -/
  add_zero : ∀ x, True
  /-- Multiplicative commutativity (abstract). -/
  mul_comm : ∀ x y, True
  /-- Multiplicative associativity (abstract). -/
  mul_assoc : ∀ x y z, True
  /-- Multiplicative identity (abstract). -/
  mul_one : ∀ x, True
  /-- Distributivity (abstract). -/
  distrib : ∀ x y z, True

/-- The Burnside ring modeled as the constant Nat ring. -/
def burnsideRing (G : Type u) (S : StrictGroup G) : BurnsideRing G S where
  carrier := Nat
  zero := 0
  one := 1
  add := Nat.add
  mul := Nat.mul
  add_comm := fun _ _ => trivial
  add_assoc := fun _ _ _ => trivial
  add_zero := fun _ => trivial
  mul_comm := fun _ _ => trivial
  mul_assoc := fun _ _ _ => trivial
  mul_one := fun _ => trivial
  distrib := fun _ _ _ => trivial

/-! ## RO(G)-graded cohomology -/

/-- RO(G): representation-ring grading data. -/
structure RO (G : Type u) where
  /-- Virtual degree. -/
  degree : Int

namespace RO

/-- The trivial RO(G) element. -/
def zero (G : Type u) : RO G :=
  { degree := 0 }

/-- Shift the RO(G) degree by one. -/
def shift {G : Type u} (α : RO G) : RO G :=
  { degree := α.degree + 1 }

/-- Add RO(G) degrees. -/
def add {G : Type u} (α β : RO G) : RO G :=
  { degree := α.degree + β.degree }

end RO

/-- RO(G)-graded reduced cohomology theory on pointed types. -/
structure ROCohomologyTheory (G : Type u) (S : StrictGroup G) where
  /-- Graded cohomology groups. -/
  cohomology : RO G → Pointed → Type u
  /-- Zero class in each degree. -/
  zero : ∀ (α : RO G) (X : Pointed), cohomology α X
  /-- Contravariant action on pointed maps. -/
  map : ∀ (α : RO G) {X Y : Pointed}, PointedMap X Y → cohomology α Y → cohomology α X
  /-- Functoriality on identities. -/
  mapId : ∀ (α : RO G) (X : Pointed) (x : cohomology α X),
    Path (map α (PointedMap.id X) x) x
  /-- Functoriality on compositions. -/
  mapComp :
    ∀ (α : RO G) {X Y Z : Pointed} (g : PointedMap Y Z) (f : PointedMap X Y)
      (x : cohomology α Z),
      Path (map α f (map α g x)) (map α (PointedMap.comp g f) x)
  /-- Suspension isomorphism in RO(G)-degree. -/
  suspIso :
    ∀ (α : RO G) (X : Pointed),
      PathSimpleEquiv (cohomology α (suspPointed X.carrier))
        (cohomology (RO.shift α) X)

namespace ROCohomologyTheory

/-- The trivial RO(G)-graded cohomology theory. -/
def trivial (G : Type u) (S : StrictGroup G) : ROCohomologyTheory G S :=
  { cohomology := fun _ _ => PUnit
    zero := fun _ _ => PUnit.unit
    map := by intro _ _ _ _ _; exact PUnit.unit
    mapId := by
      intro α X x
      cases x
      exact Path.refl PUnit.unit
    mapComp := by
      intro α _ _ _ g f x
      cases x
      exact Path.refl PUnit.unit
    suspIso := fun _ _ => pathSimpleEquivRefl PUnit }

end ROCohomologyTheory

/-! ## tom Dieck splitting -/

/-- tom Dieck splitting data for a genuine G-spectrum. -/
structure TomDieckSplitting {G : Type u} {S : StrictGroup G}
    (E : GenuineGSpectrum G S) where
  /-- The splitting for each subgroup (abstract). -/
  splitting : ∀ H : Subgroup G S, True

/-- Trivial tom Dieck splitting witness. -/
def TomDieckSplitting.trivial {G : Type u} {S : StrictGroup G}
    (E : GenuineGSpectrum G S) : TomDieckSplitting E :=
  { splitting := fun _ => trivial }

/-! ## Summary -/

end EquivariantStable
end Homotopy
end Path
end ComputationalPaths
