/-
# CW Complex Homotopy and Cellular Approximation

This module introduces cellular maps between CW complexes using Mathlib's CW complex API and
packages the data of a cellular approximation of a continuous map using computational-path
homotopies.

## Key Results

- `IsCellularMap`: continuous maps preserving all skeleta.
- `cellular_id`, `cellular_comp`, `cellular_mapsTo_complex`: basic closure properties.
- `CellularApproximation`: data of a cellular map Path-homotopic to a given map.
- `cellularApproximation_of_cellular`: trivial approximation for a cellular map.

## References

- Hatcher, *Algebraic Topology*, Section 4.1.
-/

import Mathlib.Topology.CWComplex.Classical.Basic
import ComputationalPaths.Path.Homotopy.HoTT

namespace ComputationalPaths
namespace Path
namespace CWComplexHomotopy

open Topology
open scoped Topology
open HoTT

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y]
variable {Z : Type w} [TopologicalSpace Z] [T2Space Z]
variable {C : Set X} [CWComplex C]
variable {D : Set Y} [CWComplex D]
variable {E : Set Z} [CWComplex E]

/-! ## Cellular maps -/

/-- A continuous map is cellular if it preserves every skeleton. -/
def IsCellularMap (C : Set X) (D : Set Y) [CWComplex C] [CWComplex D]
    (f : ContinuousMap X Y) : Prop :=
  ∀ n : ENat, Set.MapsTo f (CWComplex.skeleton (C := C) n) (CWComplex.skeleton (C := D) n)

/-- The identity map on a CW complex is cellular. -/
theorem cellular_id : IsCellularMap C C (ContinuousMap.id X) := by
  intro n x hx
  exact hx

/-- The composition of cellular maps is cellular. -/
theorem cellular_comp {f : ContinuousMap X Y} {g : ContinuousMap Y Z}
    (hf : IsCellularMap C D f)
    (hg : IsCellularMap D E g) :
    IsCellularMap C E (g.comp f) := by
  intro n x hx
  exact hg n (hf n hx)

/-- A cellular map sends the CW complex into the target complex. -/
theorem cellular_mapsTo_complex {f : ContinuousMap X Y}
    (hf : IsCellularMap C D f) : Set.MapsTo f C D := by
  simpa using (hf (⊤ : ENat))

/-! ## Cellular approximation data -/

/-- Data of a cellular approximation of a continuous map. -/
structure CellularApproximation (f : ContinuousMap X Y) : Type (max u v) where
  /-- The approximating cellular map. -/
  map : ContinuousMap X Y
  /-- The approximating map is cellular. -/
  cellular : IsCellularMap C D map
  /-- The approximating map is homotopic to the original map. -/
  homotopic : map ~ᵖ f

/-- A cellular map gives a tautological cellular approximation. -/
def cellularApproximation_of_cellular {f : ContinuousMap X Y}
    (hf : IsCellularMap C D f) :
    CellularApproximation (C := C) (D := D) f :=
  { map := f, cellular := hf, homotopic := homotopy_refl (f := f) }

/-! ## Summary

We introduced cellular maps between CW complexes as maps preserving each skeleton, proved
closure under identity and composition, and packaged cellular approximations as Path homotopies
from a cellular map to a given map.
-/

end CWComplexHomotopy
end Path
end ComputationalPaths
