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
noncomputable def toPointedMap {X Y : Pointed} (e : PointedEquiv X Y) : PointedMap X Y where
  toFun := e.toEquiv.toFun
  map_pt := e.map_pt.toEq

/-- Identity pointed equivalence. -/
noncomputable def refl (X : Pointed) : PointedEquiv X X where
  toEquiv := SimpleEquiv.refl X.carrier
  map_pt := Path.refl X.pt

end PointedEquiv

/-! ## Bott periodicity data -/

/-- The second homotopy group of a pointed type (universe-adjusted). -/
abbrev pi2 (X : Pointed) : Type (u + 2) :=
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
noncomputable def pi2EquivInt {BU : Pointed} (B : BottPeriodicityData BU) :
    SimpleEquiv (pi2 BU) Int :=
  B.pi2_equiv_int

/-- The Bott equivalence as a pointed map. -/
noncomputable def bottMap {BU : Pointed} (B : BottPeriodicityData BU) :
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
noncomputable def bottMap {BO : Pointed} (B : RealBottPeriodicityData BO) :
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
noncomputable def toPointed (S : SphereData) : Pointed :=
  { carrier := S.carrier, pt := S.base }

end SphereData

/-- The suspension base used for clutching constructions. -/
noncomputable def clutchingBase (S : SphereData) : Pointed :=
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
noncomputable def clutchingPointedMap {S : SphereData} {BU : Pointed}
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
noncomputable def psi_one_path {M : Type u} {S : StrictMonoid M}
    (A : AdamsOperation S) (x : KTheory.K0 S) :
    Path (A.psi 1 x) x :=
  Path.stepChain (A.psi_one x)

/-- Path-typed psi^0 on zero. -/
noncomputable def psi_zero_path {M : Type u} {S : StrictMonoid M}
    (A : AdamsOperation S) :
    Path (A.psi 0 (KTheory.zero S)) (KTheory.zero S) :=
  Path.stepChain A.psi_zero

/-- The trivial Adams operation: all psi^k are the identity. -/
noncomputable def trivial {M : Type u} (S : StrictMonoid M) : AdamsOperation S where
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
noncomputable def psi_thom_path {K B E V M : Type u} {S : StrictMonoid M}
    (C : CannibalisticClass (K := K) (B := B) (E := E) (V := V) (S := S)) :
    Path (C.adams.psi C.k C.thomClass) C.cannibalistic :=
  Path.stepChain C.psi_thom

/-- Trivial cannibalistic class built from the zero Thom class. -/
noncomputable def trivial {K B E V M : Type u} (S : StrictMonoid M)
    (bundle : VectorBundle.VectorBundleData K B E V) :
    CannibalisticClass (K := K) (B := B) (E := E) (V := V) (S := S) :=
  { bundle := bundle
    adams := AdamsOperation.trivial S
    k := 1
    thomClass := KTheory.zero S
    cannibalistic := KTheory.zero S
    psi_thom := rfl }

end CannibalisticClass

/-! ## Structural theorems -/

namespace PointedEquiv

/-- Converting to a pointed map keeps the recorded basepoint equality. -/
theorem toPointedMap_map_pt {X Y : Pointed} (e : PointedEquiv X Y) :
    (toPointedMap e).map_pt = e.map_pt.toEq :=
  rfl

/-- The identity pointed equivalence induces the identity function. -/
theorem refl_toPointedMap_toFun (X : Pointed) :
    (toPointedMap (refl X)).toFun = id :=
  rfl

/-- The identity pointed equivalence preserves the basepoint via refl. -/
theorem refl_map_pt (X : Pointed) :
    (refl X).map_pt = Path.refl X.pt :=
  rfl

/-- Composing the pointed-map conversion with identity gives the same function. -/
theorem toPointedMap_refl_toFun_eq (X : Pointed) (x : X.carrier) :
    (toPointedMap (refl X)).toFun x = x :=
  rfl

end PointedEquiv

namespace BottPeriodicityData

/-- The Bott map preserves basepoints by construction. -/
theorem bottMap_map_pt {BU : Pointed} (B : BottPeriodicityData BU) :
    (B.bottMap).map_pt = B.bott_equiv.map_pt.toEq :=
  rfl

/-- The pi2 equivalence function from Bott data agrees with the stored equiv. -/
theorem pi2EquivInt_eq {BU : Pointed} (B : BottPeriodicityData BU) :
    B.pi2EquivInt = B.pi2_equiv_int :=
  rfl

/-- The Bott map function agrees with the underlying equivalence. -/
theorem bottMap_toFun {BU : Pointed} (B : BottPeriodicityData BU) :
    (B.bottMap).toFun = B.bott_equiv.toEquiv.toFun :=
  rfl

end BottPeriodicityData

namespace RealBottPeriodicityData

/-- The real Bott map function agrees with the underlying equivalence. -/
theorem bottMap_toFun {BO : Pointed} (B : RealBottPeriodicityData BO) :
    (B.bottMap).toFun = B.bott_equiv.toEquiv.toFun :=
  rfl

/-- The real Bott map preserves basepoints by construction. -/
theorem bottMap_map_pt {BO : Pointed} (B : RealBottPeriodicityData BO) :
    (B.bottMap).map_pt = B.bott_equiv.map_pt.toEq :=
  rfl

end RealBottPeriodicityData

namespace SphereData

/-- The pointed type of a sphere-like type has the same basepoint. -/
theorem toPointed_pt (S : SphereData) : S.toPointed.pt = S.base :=
  rfl

/-- The carrier of the pointed conversion agrees with the original. -/
theorem toPointed_carrier (S : SphereData) : S.toPointed.carrier = S.carrier :=
  rfl

end SphereData

namespace ClutchingConstruction

/-- The clutching pointed map's function is the clutching map. -/
theorem clutchingPointedMap_toFun {S : SphereData} {BU : Pointed}
    (C : ClutchingConstruction S BU) :
    C.clutchingPointedMap.toFun = C.clutchingMap :=
  rfl

/-- The clutching pointed map preserves basepoints via the stored path. -/
theorem clutchingPointedMap_map_pt {S : SphereData} {BU : Pointed}
    (C : ClutchingConstruction S BU) :
    C.clutchingPointedMap.map_pt = C.clutching_base.toEq :=
  rfl

end ClutchingConstruction

namespace AdamsOperation

/-- The trivial Adams operation acts as identity at every index. -/
theorem trivial_psi_eval {M : Type u} (S : StrictMonoid M) (k : Nat) (x : KTheory.K0 S) :
    (AdamsOperation.trivial S).psi k x = x :=
  rfl

/-- The `psi^1` path of the trivial Adams operation is reflexive. -/
theorem trivial_psi_one_path {M : Type u} (S : StrictMonoid M) (x : KTheory.K0 S) :
    AdamsOperation.psi_one_path (AdamsOperation.trivial S) x = Path.stepChain rfl :=
  rfl

/-- psi^1 applied twice is the identity. -/
theorem psi_one_twice {M : Type u} {S : StrictMonoid M} (A : AdamsOperation S)
    (x : KTheory.K0 S) : A.psi 1 (A.psi 1 x) = x := by
  rw [A.psi_one, A.psi_one]

/-- Path witnessing psi^1 ∘ psi^1 = id. -/
noncomputable def psi_one_twice_path {M : Type u} {S : StrictMonoid M}
    (A : AdamsOperation S) (x : KTheory.K0 S) :
    Path (A.psi 1 (A.psi 1 x)) x :=
  Path.trans
    (Path.stepChain (_root_.congrArg (A.psi 1) (A.psi_one x)))
    (Path.stepChain (A.psi_one x))

/-- The trivial Adams operation's psi_zero is reflexive. -/
theorem trivial_psi_zero {M : Type u} (S : StrictMonoid M) :
    (AdamsOperation.trivial S).psi_zero = rfl :=
  rfl

end AdamsOperation

namespace CannibalisticClass

/-- The trivial cannibalistic class has k=1. -/
theorem trivial_k {K B E V M : Type u} (S : StrictMonoid M)
    (bundle : VectorBundle.VectorBundleData K B E V) :
    (CannibalisticClass.trivial S bundle).k = 1 :=
  rfl

/-- The trivial cannibalistic class has zero Thom class. -/
theorem trivial_thomClass {K B E V M : Type u} (S : StrictMonoid M)
    (bundle : VectorBundle.VectorBundleData K B E V) :
    (CannibalisticClass.trivial S bundle).thomClass = KTheory.zero S :=
  rfl

/-- The trivial cannibalistic class equals the zero class. -/
theorem trivial_cannibalistic {K B E V M : Type u} (S : StrictMonoid M)
    (bundle : VectorBundle.VectorBundleData K B E V) :
    (CannibalisticClass.trivial S bundle).cannibalistic = KTheory.zero S :=
  rfl

/-- Path from psi^k(thom) to the cannibalistic class for trivial data. -/
noncomputable def trivial_psi_thom_path {K B E V M : Type u} (S : StrictMonoid M)
    (bundle : VectorBundle.VectorBundleData K B E V) :
    Path
      ((CannibalisticClass.trivial S bundle).adams.psi
        (CannibalisticClass.trivial S bundle).k
        (CannibalisticClass.trivial S bundle).thomClass)
      (CannibalisticClass.trivial S bundle).cannibalistic :=
  Path.refl _

end CannibalisticClass

/-! ## Summary -/

end BottPeriodicity
end Homotopy
end Path
end ComputationalPaths
