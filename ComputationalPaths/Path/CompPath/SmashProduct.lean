/-
# Smash product in the computational paths setting

This module re-exports the pointed smash product from the homotopy library and
adds Path-valued witnesses for collapsing the wedge into the basepoint.

## Key Results

- `Smash`: smash product of pointed types (alias)
- `smashMk`: canonical map from the product into the smash
- `smash_baseL_path`, `smash_baseR_path`: Path witnesses of wedge collapse

## References

- HoTT Book, Chapter 6.7
- May, "A Concise Course in Algebraic Topology"
-/

import ComputationalPaths.Path.Homotopy.SmashProduct

namespace ComputationalPaths
namespace Path
namespace CompPath

open PointedMapCategory

universe u

/-! ## Smash product aliases -/

/-- Smash product of pointed types (alias of `SmashProduct.Smash`). -/
noncomputable abbrev Smash (X Y : PtdType.{u}) : PtdType.{u} :=
  SmashProduct.Smash X Y

/-- Canonical inclusion X × Y → X smash Y. -/
noncomputable abbrev smashMk (X Y : PtdType.{u}) (x : X.carrier) (y : Y.carrier) :
    (Smash X Y).carrier :=
  SmashProduct.smashMk X Y x y

/-- Basepoint of the smash product (alias). -/
abbrev smash_pt (X Y : PtdType.{u}) :
    (Smash X Y).pt = smashMk X Y X.pt Y.pt :=
  SmashProduct.smash_pt X Y

/-- Left basepoint identification (alias). -/
abbrev smash_baseL (X Y : PtdType.{u}) (x : X.carrier) :
    smashMk X Y x Y.pt = (Smash X Y).pt :=
  SmashProduct.smash_baseL X Y x

/-- Right basepoint identification (alias). -/
abbrev smash_baseR (X Y : PtdType.{u}) (y : Y.carrier) :
    smashMk X Y X.pt y = (Smash X Y).pt :=
  SmashProduct.smash_baseR X Y y

/-! ## Path witnesses -/

/-- Path witness for collapsing (x, y0) to the smash basepoint. -/
noncomputable def smash_baseL_path (X Y : PtdType.{u}) (x : X.carrier) :
    Path (smashMk X Y x Y.pt) (Smash X Y).pt :=
  Path.stepChain (smash_baseL X Y x)

/-- Path witness for collapsing (x0, y) to the smash basepoint. -/
noncomputable def smash_baseR_path (X Y : PtdType.{u}) (y : Y.carrier) :
    Path (smashMk X Y X.pt y) (Smash X Y).pt :=
  Path.stepChain (smash_baseR X Y y)

end CompPath
end Path
end ComputationalPaths
