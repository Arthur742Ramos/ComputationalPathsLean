/-
# H-spaces, co-H-spaces, and James splitting

This module introduces basic data structures for H-spaces and co-H-spaces,
records a Hopf theorem data package for abelian fundamental groups, and
packages a James splitting equivalence scaffold.

## Key Results

- `HSpace`, `HSpaceAssoc`: multiplication/unit data for H-spaces
- `CoHSpace`: comultiplication/counit data for co-H-spaces
- `HopfTheoremData`, `hopfTheorem`: Hopf theorem packaging for π₁
- `JamesSplittingData`: equivalence scaffold for the James splitting map

## References

- Hopf, "Fibrations and homotopy groups"
- James, "Reduced product spaces"
- HoTT Book, Chapter 8
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Homotopy.PointedMapCategory
import ComputationalPaths.Path.Homotopy.AbelianFundamentalGroup
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.JamesConstruction
import ComputationalPaths.Path.Homotopy.SuspensionLoop

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace HSpaces

open PointedMapCategory

universe u

/-! ## H-spaces -/

variable {X : PtdType.{u}}

/-- An H-space structure on a pointed type. -/
structure HSpace (X : PtdType.{u}) where
  /-- Multiplication map. -/
  mul : PtdMap (PtdProduct X X) X
  /-- Left unit law. -/
  mul_left_unit : ∀ x, mul.toFun (X.pt, x) = x
  /-- Right unit law. -/
  mul_right_unit : ∀ x, mul.toFun (x, X.pt) = x

/-- The multiplication sends the basepoint pair to the basepoint. -/
theorem HSpace.mul_base (h : HSpace X) :
    h.mul.toFun (X.pt, X.pt) = X.pt := by
  simpa using h.mul.map_pt

/-- Path witness for the left unit law. -/
noncomputable def HSpace.mul_left_path (h : HSpace X) (x : X.carrier) :
    Path (h.mul.toFun (X.pt, x)) x :=
  Path.stepChain (h.mul_left_unit x)

/-- Path witness for the right unit law. -/
noncomputable def HSpace.mul_right_path (h : HSpace X) (x : X.carrier) :
    Path (h.mul.toFun (x, X.pt)) x :=
  Path.stepChain (h.mul_right_unit x)

/-- Path witness for the basepoint law. -/
noncomputable def HSpace.mul_base_path (h : HSpace X) :
    Path (h.mul.toFun (X.pt, X.pt)) X.pt :=
  Path.stepChain (HSpace.mul_base h)

/-- Associativity data for an H-space. -/
structure HSpaceAssoc (X : PtdType.{u}) extends HSpace X where
  /-- Associativity law. -/
  mul_assoc : ∀ x y z,
    mul.toFun (mul.toFun (x, y), z) = mul.toFun (x, mul.toFun (y, z))

/-- Path witness for associativity. -/
noncomputable def HSpaceAssoc.mul_assoc_path (h : HSpaceAssoc X) (x y z : X.carrier) :
    Path (h.mul.toFun (h.mul.toFun (x, y), z))
      (h.mul.toFun (x, h.mul.toFun (y, z))) :=
  Path.stepChain (h.mul_assoc x y z)

/-! ## Co-H-spaces -/

/-- A co-H-space structure on a pointed type. -/
structure CoHSpace (X : PtdType.{u}) where
  /-- Comultiplication map. -/
  comul : PtdMap X (PtdCoproduct X X)
  /-- Left counit map. -/
  counit_left : PtdMap (PtdCoproduct X X) X
  /-- Right counit map. -/
  counit_right : PtdMap (PtdCoproduct X X) X
  /-- Left counit law. -/
  left_inv : PtdMap.comp counit_left comul = PtdMap.id X
  /-- Right counit law. -/
  right_inv : PtdMap.comp counit_right comul = PtdMap.id X

/-- Path witness for the left counit law. -/
noncomputable def CoHSpace.left_inv_path (h : CoHSpace X) :
    Path (PtdMap.comp h.counit_left h.comul) (PtdMap.id X) :=
  Path.stepChain h.left_inv

/-- Path witness for the right counit law. -/
noncomputable def CoHSpace.right_inv_path (h : CoHSpace X) :
    Path (PtdMap.comp h.counit_right h.comul) (PtdMap.id X) :=
  Path.stepChain h.right_inv

/-! ## Hopf theorem data -/

/-- Hopf theorem data for an H-space: an abelian π₁ package. -/
structure HopfTheoremData (X : PtdType.{u}) where
  /-- Chosen H-space structure. -/
  hspace : HSpace X
  /-- π₁ multiplication and unit data. -/
  piOneOps : PiOneOps (π₁(X.carrier, X.pt))
  /-- Hopf theorem conclusion: π₁ is abelian. -/
  piOneAbelian : PiOneAbelian (π₁(X.carrier, X.pt)) piOneOps

/-- Extract the Hopf theorem conclusion. -/
theorem hopfTheorem {X : PtdType.{u}} (data : HopfTheoremData X) :
    PiOneAbelian (π₁(X.carrier, X.pt)) data.piOneOps :=
  data.piOneAbelian

/-! ## James splitting -/

/-- Loop space of the suspension of a pointed type. -/
abbrev jamesLoop (X : SuspensionLoop.Pointed) : Type u :=
  LoopSpace (SuspensionLoop.Suspension X.carrier)
    (SuspensionLoop.Suspension.north (X := X.carrier))

/-- Data packaging a James splitting equivalence. -/
structure JamesSplittingData (X : SuspensionLoop.Pointed) where
  /-- Splitting equivalence. -/
  splitEquiv :
    SimpleEquiv (JamesConstruction.JamesConstruction X) (jamesLoop X)
  /-- Forward map agrees with the James construction map. -/
  splitEquiv_toFun :
    splitEquiv.toFun = JamesConstruction.jamesToLoop X

/-- The splitting uses the canonical James map as its forward direction. -/
theorem jamesSplitting_toLoop {X : SuspensionLoop.Pointed} (data : JamesSplittingData X) :
    data.splitEquiv.toFun = JamesConstruction.jamesToLoop X :=
  data.splitEquiv_toFun

/-- Path witness for the left inverse in the James splitting. -/
noncomputable def jamesSplitting_left_path {X : SuspensionLoop.Pointed} (data : JamesSplittingData X)
    (j : JamesConstruction.JamesConstruction X) :
    Path (data.splitEquiv.invFun (data.splitEquiv.toFun j)) j :=
  Path.stepChain (data.splitEquiv.left_inv j)

/-- Path witness for the right inverse in the James splitting. -/
noncomputable def jamesSplitting_right_path {X : SuspensionLoop.Pointed} (data : JamesSplittingData X)
    (l : jamesLoop X) :
    Path (data.splitEquiv.toFun (data.splitEquiv.invFun l)) l :=
  Path.stepChain (data.splitEquiv.right_inv l)

/-! ## Summary -/

-- We introduced H-space/co-H-space data structures, a Hopf theorem package for
-- abelian fundamental groups, and a James splitting equivalence scaffold.

end HSpaces
end Homotopy
end Path
end ComputationalPaths
