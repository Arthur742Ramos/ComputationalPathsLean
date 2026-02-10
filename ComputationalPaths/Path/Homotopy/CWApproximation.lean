/-
# CW Approximation Theorem via Computational Paths

This module records a CW approximation statement in the computational-path setting.
We model CW approximation data for maps between CW complexes and provide the
tautological approximation for the identity map.

## Key Results

- `CWApproximationData`: CW approximation data for a map between CW complexes.
- `cwApproximation_of_cellular`: cellular maps admit trivial CW approximations.
- `cwApproximation_id`: the identity map on a CW complex admits a CW approximation.
- `cwApproximation_path`: extract the Path-valued homotopy from a CW approximation.

## References

- Hatcher, *Algebraic Topology*, Section 4.1.
-/

import ComputationalPaths.Path.Homotopy.CWComplexHomotopy

namespace ComputationalPaths
namespace Path
namespace CWApproximation

open Topology
open scoped Topology
open CWComplexHomotopy

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y]
variable {C : Set X} [CWComplex C]
variable {D : Set Y} [CWComplex D]

/-! ## CW approximation data -/

/-- CW approximation data for a map between CW complexes. -/
abbrev CWApproximationData (f : ContinuousMap X Y) : Type (max u v) :=
  CellularApproximation (C := C) (D := D) f

/-- A cellular map admits a CW approximation. -/
def cwApproximation_of_cellular {f : ContinuousMap X Y}
    (hf : IsCellularMap C D f) :
    CWApproximationData (C := C) (D := D) f :=
  cellularApproximation_of_cellular (C := C) (D := D) hf

/-- The identity map on a CW complex admits a CW approximation. -/
def cwApproximation_id :
    CWApproximationData (C := C) (D := C) (ContinuousMap.id X) :=
  cwApproximation_of_cellular (C := C) (D := C) (cellular_id (C := C))

/-- Extract the Path-valued homotopy from a CW approximation. -/
def cwApproximation_path {f : ContinuousMap X Y}
    (approx : CWApproximationData (C := C) (D := D) f) (x : X) :
    Path (approx.map x) (f x) :=
  approx.homotopic x

/-! ## Summary

We packaged CW approximation data for maps between CW complexes, showed cellular
maps admit trivial approximations, and exposed the underlying Path homotopy.
-/

end CWApproximation
end Path
end ComputationalPaths
