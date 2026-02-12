/-
# Hopf Fibration (Mathlib interface)

This module packages the Hopf fibration `S³ → S²` with fiber `S¹` using Mathlib's
TopCat spheres. We record the projection, basepoints, and fiber identification
as data, then expose the associated fiber sequence and basic applications.

Key identities additionally carry computational `Path` witnesses.

## Key Results

- `HopfFibrationData`: data for the Hopf projection and fiber identification
- `hopfFiberSeq`: the fiber sequence `S¹ → S³ → S²`
- `hopfFiberSeq_exact`: exactness at the total space
- `hopfInducedPi1Map`: induced map on `π₁` from the Hopf projection

`Path` companions:
- `hopfBaseProj_path`
- `hopfFiberEquiv_roundtrip_path`, `hopfFiberEquiv_fwd_roundtrip_path`
- `hopfFiberIncl_proj_path`, `hopfFiberSeq_exact_path`

## References

- Hatcher, *Algebraic Topology*, Section 4.2
- Hopf fibration `S³ → S²` with fiber `S¹`
-/

import Mathlib.Topology.Category.TopCat.Sphere
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Homotopy.FundamentalGroup

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace HopfFibration

open Fibration

universe u

/-! ## Sphere aliases -/

/-- The 1-sphere `S¹` as a Mathlib `TopCat` sphere. -/
abbrev S1 : Type u := TopCat.sphere (n := 1)

/-- The 2-sphere `S²` as a Mathlib `TopCat` sphere. -/
abbrev S2 : Type u := TopCat.sphere (n := 2)

/-- The 3-sphere `S³` as a Mathlib `TopCat` sphere. -/
abbrev S3 : Type u := TopCat.sphere (n := 3)

/-! ## Hopf fibration data -/

/-- Data for the Hopf fibration `S³ → S²` with fiber `S¹`. -/
structure HopfFibrationData where
  /-- The Hopf projection `S³ → S²`. -/
  proj : S3 → S2
  /-- Basepoint in `S²`. -/
  base : S2
  /-- Basepoint in `S³` lying over `base`. -/
  baseTotal : S3
  /-- The projection sends `baseTotal` to `base`. -/
  base_proj : proj baseTotal = base
  /-- Identification of the fiber over `base` with `S¹`. -/
  fiberEquiv : SimpleEquiv (Fiber proj base) S1

/-! ## Path witnesses for the Hopf data -/

/-- `Path` witnessing the base-projection condition. -/
def hopfBaseProj_path (data : HopfFibrationData) :
    ComputationalPaths.Path (data.proj data.baseTotal) data.base :=
  ComputationalPaths.Path.ofEq data.base_proj

/-- `Path` witnessing that the fiber equivalence round-trip is the identity. -/
def hopfFiberEquiv_roundtrip_path (data : HopfFibrationData)
    (x : Fiber data.proj data.base) :
    ComputationalPaths.Path
      (data.fiberEquiv.invFun (data.fiberEquiv.toFun x)) x :=
  ComputationalPaths.Path.ofEq (data.fiberEquiv.left_inv x)

/-- `Path` witnessing the forward round-trip of the fiber equivalence. -/
def hopfFiberEquiv_fwd_roundtrip_path (data : HopfFibrationData) (x : S1) :
    ComputationalPaths.Path
      (data.fiberEquiv.toFun (data.fiberEquiv.invFun x)) x :=
  ComputationalPaths.Path.ofEq (data.fiberEquiv.right_inv x)

/-! ## Fiber sequence package -/

/-- The fiber of the Hopf projection over the chosen basepoint. -/
abbrev hopfFiber (data : HopfFibrationData) : Type u :=
  Fiber data.proj data.base

/-- Transport in Hopf fibers along a base path. -/
def hopfFiberTransport (data : HopfFibrationData) {b₁ b₂ : S2} (p : Path b₁ b₂) :
    Fiber data.proj b₁ → Fiber data.proj b₂ :=
  Path.transport (D := fun b => Fiber data.proj b) p

/-- Fiber transport along composite paths composes via `Path.trans`. -/
theorem hopfFiberTransport_trans (data : HopfFibrationData) {b₁ b₂ b₃ : S2}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (x : Fiber data.proj b₁) :
    hopfFiberTransport data (Path.trans p q) x =
      hopfFiberTransport data q (hopfFiberTransport data p x) := by
  simpa [hopfFiberTransport] using
    (Path.transport_trans (D := fun b => Fiber data.proj b) p q x)

/-- The Hopf fiber sequence `S¹ → S³ → S²`. -/
def hopfFiberSeq (data : HopfFibrationData) : FiberSeq S1 S3 S2 where
  proj := data.proj
  baseB := data.base
  baseE := data.baseTotal
  base_proj := Path.ofEq data.base_proj
  toFiber := data.fiberEquiv.invFun
  fromFiber := data.fiberEquiv.toFun
  left_inv := data.fiberEquiv.right_inv
  right_inv := data.fiberEquiv.left_inv

/-! ## Applications -/

/-- The inclusion of the Hopf fiber into the total space. -/
def hopfFiberIncl (data : HopfFibrationData) : S1 → S3 :=
  (hopfFiberSeq data).incl

/-- The projection of the fiber inclusion is the Hopf basepoint. -/
def hopfFiberIncl_proj (data : HopfFibrationData) (x : S1) :
    Path (data.proj (hopfFiberIncl data x)) data.base :=
  (hopfFiberSeq data).proj_incl x

/-- `Path` witnessing that the fiber inclusion projects to the base. -/
def hopfFiberIncl_proj_path (data : HopfFibrationData) (x : S1) :
    ComputationalPaths.Path (data.proj (hopfFiberIncl data x)) data.base :=
  (hopfFiberSeq data).proj_incl x

/-- The Hopf fiber sequence is exact at the total space. -/
def hopfFiberSeq_exact (data : HopfFibrationData) :
    IsExactAt (hopfFiberSeq data) := by
  refine { incl_to_base := ?_, base_from_fiber := ?_ }
  · intro f
    exact (hopfFiberSeq data).proj_incl f
  · intro e h
    refine ⟨(hopfFiberSeq data).fromFiber ⟨e, h.toEq⟩, ?_⟩
    have h' := (hopfFiberSeq data).right_inv ⟨e, h.toEq⟩
    have h'' : (hopfFiberSeq data).incl
        ((hopfFiberSeq data).fromFiber ⟨e, h.toEq⟩) = e := by
      simpa [FiberSeq.incl] using _root_.congrArg Fiber.point h'
    exact Path.ofEq h''

/-- `Path` witnessing exactness: incl composed with proj yields the base. -/
def hopfFiberSeq_exact_path (data : HopfFibrationData) (f : S1) :
    ComputationalPaths.Path
      (data.proj ((hopfFiberSeq data).incl f))
      data.base :=
  (hopfFiberSeq data).proj_incl f

/-- The induced map on `π₁` from the Hopf projection. -/
noncomputable def hopfInducedPi1Map (data : HopfFibrationData) :
    π₁(S3, data.baseTotal) → π₁(S2, data.base) :=
  by
    intro α
    refine Eq.ndrec (motive := fun b => π₁(S2, b)) ?_ data.base_proj
    exact Fibration.inducedPi1Map data.proj data.baseTotal α

/-! ## Summary -/

end HopfFibration
end Homotopy
end Path
end ComputationalPaths
