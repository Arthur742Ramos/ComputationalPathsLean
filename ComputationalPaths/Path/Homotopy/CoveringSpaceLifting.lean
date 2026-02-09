/-
# Derived Path Lifting Laws for Covering Spaces

This module records additional lemmas about path lifting and transport
in covering spaces, phrased in the computational paths framework.

## Key Results

- `fiberTransport_symm_left`, `fiberTransport_symm_right`
- `proj_pathLift_trans`, `proj_pathLift_symm`

## References

- HoTT Book, Chapter 8.4
-/

import ComputationalPaths.Path.Homotopy.CoveringSpace
import ComputationalPaths.Path.Homotopy.CoveringPathLifting

namespace ComputationalPaths
namespace Path
namespace CoveringSpace

universe u

variable {A : Type u}

/-! ## Fiber Transport Symmetry -/

/-- Transport along a path and its inverse returns the original fiber element. -/
theorem fiberTransport_symm_left {P : A → Type u} {a b : A}
    (p : Path a b) (x : P a) :
    fiberTransport (Path.symm p) (fiberTransport p x) = x := by
  simpa [fiberTransport] using (Path.transport_symm_left (p := p) (x := x))

/-- Transport along an inverse path and back returns the original fiber element. -/
theorem fiberTransport_symm_right {P : A → Type u} {a b : A}
    (p : Path a b) (y : P b) :
    fiberTransport p (fiberTransport (Path.symm p) y) = y := by
  simpa [fiberTransport] using (Path.transport_symm_right (p := p) (y := y))

/-! ## Projection of Lifted Paths -/

/-- The projection of a composed lifted path is the composed projection. -/
theorem proj_pathLift_trans {P : A → Type u} {a b c : A}
    (p : Path a b) (q : Path b c) (x : P a) :
    Path.congrArg proj
        (Path.trans (pathLift (P := P) p x)
          (pathLift (P := P) q (fiberTransport p x))) =
      Path.trans (Path.ofEq p.toEq) (Path.ofEq q.toEq) := by
  calc
    Path.congrArg proj
        (Path.trans (pathLift (P := P) p x)
          (pathLift (P := P) q (fiberTransport p x))) =
        Path.trans
          (Path.congrArg proj (pathLift (P := P) p x))
          (Path.congrArg proj (pathLift (P := P) q (fiberTransport p x))) := by
          simp
    _ = Path.trans (Path.ofEq p.toEq) (Path.ofEq q.toEq) := by
          rw [proj_pathLift_ofEq, proj_pathLift_ofEq]

/-- The projection of a reversed lifted path is the reversed projection. -/
theorem proj_pathLift_symm {P : A → Type u} {a b : A}
    (p : Path a b) (x : P a) :
    Path.congrArg proj (Path.symm (pathLift (P := P) p x)) =
      Path.symm (Path.ofEq p.toEq) := by
  calc
    Path.congrArg proj (Path.symm (pathLift (P := P) p x)) =
        Path.symm (Path.congrArg proj (pathLift (P := P) p x)) := by
          simp
    _ = Path.symm (Path.ofEq p.toEq) := by
          rw [proj_pathLift_ofEq]

/-! ## Transport along Quotient Paths -/

/-- Transport along a rewrite-quotient base path. -/
noncomputable def fiberTransportQuot {P : A → Type u} {a b : A} :
    PathRwQuot A a b → P a → P b :=
  Quot.lift (fun p => fiberTransport (P := P) p)
    (fun _ _ h => funext (fiberTransport_respects_rweq (P := P) h))

/-- Transport along a quotient path represented by a concrete path. -/
@[simp] theorem fiberTransportQuot_mk {P : A → Type u} {a b : A}
    (p : Path a b) (x : P a) :
    fiberTransportQuot (P := P) (a := a) (b := b) (Quot.mk _ p) x =
      fiberTransport (P := P) p x := rfl

/-- Transport along the reflexive quotient path is identity. -/
@[simp] theorem fiberTransportQuot_refl {P : A → Type u} {a : A} (x : P a) :
    fiberTransportQuot (P := P) (a := a) (b := a)
        (PathRwQuot.refl (A := A) a) x = x := by
  simpa [PathRwQuot.refl] using
    (fiberTransportQuot_mk (P := P) (a := a) (b := a) (Path.refl a) x)

/-- Transport along a composite quotient path is successive transport. -/
@[simp] theorem fiberTransportQuot_trans {P : A → Type u} {a b c : A}
    (p : PathRwQuot A a b) (q : PathRwQuot A b c) (x : P a) :
    fiberTransportQuot (P := P) (a := a) (b := c)
        (PathRwQuot.trans p q) x =
      fiberTransportQuot (P := P) (a := b) (b := c) q
        (fiberTransportQuot (P := P) (a := a) (b := b) p x) := by
  refine Quot.inductionOn p (fun p' => ?_)
  refine Quot.inductionOn q (fun q' => ?_)
  simpa [PathRwQuot.trans_mk] using
    (fiberTransport_trans (P := P) (p := p') (q := q') (x := x))

end CoveringSpace
end Path
end ComputationalPaths
