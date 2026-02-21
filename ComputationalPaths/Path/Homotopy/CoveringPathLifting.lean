/-
# Path Lifting Lemmas for Covering Spaces

This module extends `CoveringSpace` with lemmas about transport along projected
paths and the uniqueness of lifted endpoints.

## Key Results

- `fiberTransport_respects_rweq`
- `projPath_transport_eq`
- `lifted_endpoint_eq_of_proj_toEq`

## References

- HoTT Book, Chapter 8.4
-/

import ComputationalPaths.Path.Homotopy.CoveringSpace

namespace ComputationalPaths
namespace Path
namespace CoveringSpace

universe u

variable {A : Type u}

/-! ## Transport and RwEq -/

/-- Fiber transport is invariant under rewrite equivalence of base paths. -/
noncomputable def fiberTransport_respects_rweq {P : A → Type u} {a b : A}
    {p q : Path a b} (h : RwEq p q) (x : P a) :
    fiberTransport (P := P) p x = fiberTransport (P := P) q x := by
  unfold fiberTransport
  exact Path.transport_of_toEq_eq (rweq_toEq h) x

/-! ## Lifted Endpoints -/

/-- The endpoint of a path in the total space is given by transport
along its projection. -/
theorem projPath_transport_eq {P : A → Type u} {a b : A}
    {x : P a} {y : P b}
    (q : Path (TotalPoint a x) (TotalPoint b y)) :
    fiberTransport (P := P) (IsCovering.projPath (P := P) q) x = y := by
  simpa [IsCovering.projPath, proj, TotalPoint, fiberTransport] using
    (sigmaSnd (B := fun a => P a) q).toEq

/-- If a lifted path projects to a base path (at the `toEq` level), then
its endpoint is the transported point. -/
theorem lifted_endpoint_eq_of_proj_toEq {P : A → Type u} {a b : A}
    {x : P a} {y : P b} (p : Path a b)
    (q : Path (TotalPoint a x) (TotalPoint b y))
    (h : (IsCovering.projPath (P := P) q).toEq = p.toEq) :
    y = fiberTransport (P := P) p x := by
  have hproj :
      fiberTransport (P := P) (IsCovering.projPath (P := P) q) x = y :=
    projPath_transport_eq (P := P) (a := a) (b := b) (x := x) (y := y) q
  have htransport :
      fiberTransport (P := P) (IsCovering.projPath (P := P) q) x =
        fiberTransport (P := P) p x := by
    exact Path.transport_of_toEq_eq h x
  calc
    y = fiberTransport (P := P) (IsCovering.projPath (P := P) q) x := by
      symm
      exact hproj
    _ = fiberTransport (P := P) p x := htransport

/-! ## Summary

The path lifting lemmas show that transport depends only on the projection of
a path in the total space, giving a uniqueness statement for lifted endpoints.
-/

end CoveringSpace
end Path
end ComputationalPaths
