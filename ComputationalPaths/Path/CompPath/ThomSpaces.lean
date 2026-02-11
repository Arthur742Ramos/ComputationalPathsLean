/-
# Thom spaces in computational paths

Defines Thom spaces of vector bundles together with Thom classes, Thom
isomorphisms, and basic orientation data in the computational-path framework.

## Key Results

- `ThomSpace`, `ThomClass`, `ThomIsomorphism` (CompPath-level aliases).
- `BundleOrientation`, `OrientedVectorBundle`, `OrientedThomIsomorphism`.

## References

- Thom, "Quelques proprietes globales des varietes differentiables"
- Milnor & Stasheff, "Characteristic Classes"
- Hatcher, "Vector Bundles and K-Theory"
- May, "A Concise Course in Algebraic Topology"
-/

import ComputationalPaths.Path.Homotopy.ThomSpectra
import ComputationalPaths.Path.Homotopy.VectorBundle
import ComputationalPaths.Path.Homotopy.GeneralizedCohomology

namespace ComputationalPaths
namespace Path
namespace CompPath

open Homotopy
open Homotopy.GeneralizedCohomology
open Homotopy.ThomSpectra
open Homotopy.VectorBundle

universe u

/-! ## Thom spaces and Thom classes -/

/-- Thom space (CompPath-level alias). -/
abbrev ThomSpace {K B Total V : Type u} (bundle : VectorBundleData K B Total V) :=
  Homotopy.ThomSpectra.ThomSpace bundle

/-- Thom class (CompPath-level alias). -/
abbrev ThomClass (H : ReducedCohomologyTheory) {K B Total V : Type u}
    (bundle : VectorBundleData K B Total V) (Th : ThomSpace bundle) :=
  Homotopy.ThomSpectra.ThomClass H bundle Th

/-- Thom isomorphism (CompPath-level alias). -/
abbrev ThomIsomorphism (H : ReducedCohomologyTheory) {K B Total V : Type u}
    (bundle : VectorBundleData K B Total V) (Th : ThomSpace bundle) (b0 : B) :=
  Homotopy.ThomSpectra.ThomIsomorphism H bundle Th b0

/-- Basepointed helper used in Thom constructions (alias). -/
abbrev thomBasePointed (B : Type u) (b : B) : SuspensionLoop.Pointed :=
  Homotopy.ThomSpectra.basePointed B b

/-! ## Orientation theory -/

/-- Orientation data for a vector bundle in a reduced cohomology theory. -/
structure BundleOrientation (H : ReducedCohomologyTheory) {K B Total V : Type u}
    (bundle : VectorBundleData K B Total V) where
  /-- Chosen Thom space. -/
  thomSpace : ThomSpace bundle
  /-- Thom class for the chosen Thom space. -/
  thomClass : ThomClass H bundle thomSpace
  /-- Orientation degree matches the bundle rank. -/
  degree_eq_rank : thomClass.degree = bundle.rank
  /-- Compatibility data (abstract). -/
  compatible : True

namespace BundleOrientation

variable {H : ReducedCohomologyTheory}
variable {K B Total V : Type u} {bundle : VectorBundleData K B Total V}

/-- `Path`-typed witness that the Thom degree equals the rank. -/
def degreePath (O : BundleOrientation H bundle) :
    Path O.thomClass.degree bundle.rank :=
  Path.ofEq O.degree_eq_rank

end BundleOrientation

/-- An oriented vector bundle. -/
structure OrientedVectorBundle (H : ReducedCohomologyTheory)
    (K B Total V : Type u) where
  /-- The underlying bundle. -/
  bundle : VectorBundleData K B Total V
  /-- Orientation data. -/
  orientation : BundleOrientation H bundle

/-- Thom isomorphism data for an oriented bundle. -/
structure OrientedThomIsomorphism (H : ReducedCohomologyTheory)
    {K B Total V : Type u} (bundle : VectorBundleData K B Total V) (b0 : B) where
  /-- Orientation data. -/
  orientation : BundleOrientation H bundle
  /-- Thom isomorphism. -/
  isomorphism : ThomIsomorphism H bundle orientation.thomSpace b0
  /-- Degree matches the bundle rank. -/
  degree_eq_rank : isomorphism.degree = bundle.rank
  /-- The Thom class agrees with the orientation class (heterogeneous equality). -/
  class_eq : HEq isomorphism.thomClass orientation.thomClass.thom

namespace OrientedThomIsomorphism

variable {H : ReducedCohomologyTheory}
variable {K B Total V : Type u} {bundle : VectorBundleData K B Total V} {b0 : B}

/-- `Path`-typed witness of degree alignment for the Thom isomorphism. -/
def degreePath (T : OrientedThomIsomorphism H bundle b0) :
    Path T.isomorphism.degree bundle.rank :=
  Path.ofEq T.degree_eq_rank

/-- Heterogeneous witness that the Thom class matches the orientation class. -/
def classPath (T : OrientedThomIsomorphism H bundle b0) :
    HEq T.isomorphism.thomClass T.orientation.thomClass.thom :=
  T.class_eq

end OrientedThomIsomorphism

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
