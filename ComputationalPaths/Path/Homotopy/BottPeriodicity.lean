/-
# Bott Periodicity (computational paths)

This module records an axiom-free interface for Bott periodicity in the
computational paths framework. The definitions are structural: they specify
complex and real Bott periodicity data, clutching constructions, Adams
operations on K-theory, and cannibalistic classes.

## Key Results

- `PointedEquiv`: pointed equivalence between pointed types
- `BottPeriodicityData`: pi2(BU) ~= Int and BU ~= Omega^2 BU
- `RealBottPeriodicityData`: BO ~= Omega^8 BO
- `ClutchingConstruction`: bundle data from a clutching map
- `AdamsOperation`: Adams operations psi^k on K0
- `CannibalisticClass`: cannibalistic class data

## References

- Bott, "The periodicity theorem for the classical groups"
- Atiyah, "K-Theory"
- Hatcher, "Vector Bundles and K-Theory"
-/

import ComputationalPaths.Path.Homotopy.IteratedLoopSpace
import ComputationalPaths.Path.Homotopy.HigherHomotopy
import ComputationalPaths.Path.Homotopy.SuspensionLoop
import ComputationalPaths.Path.Homotopy.FiberBundle
import ComputationalPaths.Path.Homotopy.VectorBundle
import ComputationalPaths.Path.CompPath.SuspensionSpace
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Algebra.KTheory
import ComputationalPaths.Path.Algebra.GroupStructures

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace BottPeriodicity

open SuspensionLoop
open IteratedLoopSpace
open FiberBundle
open Algebra

universe u

/-! ## Pointed equivalences -/

/-- A pointed equivalence between pointed types. -/
structure PointedEquiv (X Y : Pointed) where
  /-- Underlying equivalence. -/
  toEquiv : SimpleEquiv X.carrier Y.carrier
  /-- Basepoint preservation as a path. -/
  map_pt : Path (toEquiv.toFun X.pt) Y.pt

namespace PointedEquiv

/-- Convert a pointed equivalence to a pointed map. -/
def toPointedMap {X Y : Pointed} (e : PointedEquiv X Y) : PointedMap X Y where
  toFun := e.toEquiv.toFun
  map_pt := e.map_pt.toEq

/-- Identity pointed equivalence. -/
def refl (X : Pointed) : PointedEquiv X X where
  toEquiv := SimpleEquiv.refl X.carrier
  map_pt := Path.refl X.pt

end PointedEquiv

/-! ## Bott periodicity data -/

/-- The second homotopy group of a pointed type. -/
abbrev pi2 (X : Pointed) : Type u :=
  HigherHomotopy.PiTwo X.carrier X.pt

/-- Two-fold loop space Omega^2 as a pointed type. -/
noncomputable abbrev omega2 (X : Pointed) : Pointed :=
  OmegaN 2 X

/-- Bott periodicity data for a BU-like pointed space. -/
structure BottPeriodicityData (BU : Pointed) where
  /-- Equivalence pi2(BU) ~= Int. -/
  pi2_equiv_int : SimpleEquiv (pi2 BU) Int
  /-- Pointed equivalence BU ~= Omega^2 BU. -/
  bott_equiv : PointedEquiv BU (omega2 BU)

namespace BottPeriodicityData

/-- The pi2 equivalence from Bott periodicity data. -/
def pi2EquivInt {BU : Pointed} (B : BottPeriodicityData BU) :
    SimpleEquiv (pi2 BU) Int :=
  B.pi2_equiv_int

/-- The Bott equivalence as a pointed map. -/
def bottMap {BU : Pointed} (B : BottPeriodicityData BU) :
    PointedMap BU (omega2 BU) :=
  B.bott_equiv.toPointedMap

end BottPeriodicityData

/-! ## Real Bott periodicity -/

/-- Eight-fold loop space Omega^8 as a pointed type. -/
noncomputable abbrev omega8 (X : Pointed) : Pointed :=
  OmegaN 8 X

/-- Real Bott periodicity data (8-periodicity). -/
structure RealBottPeriodicityData (BO : Pointed) where
  /-- Pointed equivalence BO ~= Omega^8 BO. -/
  bott_equiv : PointedEquiv BO (omega8 BO)

namespace RealBottPeriodicityData

/-- The real Bott equivalence as a pointed map. -/
def bottMap {BO : Pointed} (B : RealBottPeriodicityData BO) :
    PointedMap BO (omega8 BO) :=
  B.bott_equiv.toPointedMap

end RealBottPeriodicityData

/-! ## Clutching construction -/

/-- A pointed sphere-like type used for clutching data. -/
structure SphereData where
  /-- Underlying type. -/
  carrier : Type u
  /-- Basepoint. -/
  base : carrier

namespace SphereData

/-- View a sphere-like type as a pointed type. -/
def toPointed (S : SphereData) : Pointed :=
  { carrier := S.carrier, pt := S.base }

end SphereData

/-- The suspension base used for clutching constructions. -/
def clutchingBase (S : SphereData) : Pointed :=
  { carrier := CompPath.SuspensionCompPath S.carrier
    pt := CompPath.SuspensionCompPath.north (X := S.carrier) }

/-- Clutching construction data for a BU-valued clutching map. -/
structure ClutchingConstruction (S : SphereData) (BU : Pointed) where
  /-- The clutching map on the equator sphere. -/
  clutchingMap : S.carrier → BU.carrier
  /-- Basepoint preservation for the clutching map. -/
  clutching_base : Path (clutchingMap S.base) BU.pt
  /-- Total space of the resulting bundle. -/
  total : Type u
  /-- Model fiber. -/
  fiber : Type u
  /-- Bundle over the suspension base. -/
  bundle : FiberBundleData (clutchingBase S).carrier total fiber

namespace ClutchingConstruction

/-- The clutching map as a pointed map. -/
def clutchingPointedMap {S : SphereData} {BU : Pointed}
    (C : ClutchingConstruction S BU) :
    PointedMap (S.toPointed) BU :=
  { toFun := C.clutchingMap
    map_pt := C.clutching_base.toEq }

end ClutchingConstruction

/-! ## Adams operations on K-theory -/

/-- Adams operations on K0 as a family of endomorphisms. -/
structure AdamsOperation {M : Type u} (S : StrictMonoid M) where
  /-- The Adams operation psi^k. -/
  psi : Nat → KTheory.K0 S → KTheory.K0 S
  /-- psi^1 is the identity. -/
  psi_one : ∀ x, psi 1 x = x
  /-- psi^0 fixes the zero class. -/
  psi_zero : psi 0 (KTheory.zero S) = KTheory.zero S

namespace AdamsOperation

/-- Path-typed psi^1 identity. -/
def psi_one_path {M : Type u} {S : StrictMonoid M}
    (A : AdamsOperation S) (x : KTheory.K0 S) :
    Path (A.psi 1 x) x :=
  Path.ofEq (A.psi_one x)

/-- Path-typed psi^0 on zero. -/
def psi_zero_path {M : Type u} {S : StrictMonoid M}
    (A : AdamsOperation S) :
    Path (A.psi 0 (KTheory.zero S)) (KTheory.zero S) :=
  Path.ofEq A.psi_zero

/-- The trivial Adams operation: all psi^k are the identity. -/
def trivial {M : Type u} (S : StrictMonoid M) : AdamsOperation S where
  psi := fun _ x => x
  psi_one := by intro _; rfl
  psi_zero := rfl

end AdamsOperation

/-! ## Cannibalistic classes -/

/-- Cannibalistic class data associated to Adams operations. -/
structure CannibalisticClass {K B E V M : Type u} (S : StrictMonoid M) where
  /-- The underlying vector bundle. -/
  bundle : VectorBundle.VectorBundleData K B E V
  /-- Adams operations on the relevant K-theory. -/
  adams : AdamsOperation S
  /-- The Adams index k. -/
  k : Nat
  /-- Thom class in K-theory. -/
  thomClass : KTheory.K0 S
  /-- The resulting cannibalistic class. -/
  cannibalistic : KTheory.K0 S
  /-- psi^k applied to the Thom class. -/
  psi_thom : adams.psi k thomClass = cannibalistic

namespace CannibalisticClass

/-- Path-typed psi^k Thom identity. -/
def psi_thom_path {K B E V M : Type u} {S : StrictMonoid M}
    (C : CannibalisticClass (K := K) (B := B) (E := E) (V := V) (S := S)) :
    Path (C.adams.psi C.k C.thomClass) C.cannibalistic :=
  Path.ofEq C.psi_thom

/-- Trivial cannibalistic class built from the zero Thom class. -/
def trivial {K B E V M : Type u} (S : StrictMonoid M)
    (bundle : VectorBundle.VectorBundleData K B E V) :
    CannibalisticClass (K := K) (B := B) (E := E) (V := V) (S := S) :=
  { bundle := bundle
    adams := AdamsOperation.trivial S
    k := 1
    thomClass := KTheory.zero S
    cannibalistic := KTheory.zero S
    psi_thom := rfl }

end CannibalisticClass

/-! ## Summary -/

end BottPeriodicity
end Homotopy
end Path
end ComputationalPaths
