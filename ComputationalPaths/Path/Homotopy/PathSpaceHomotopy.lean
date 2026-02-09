/- 
# Homotopy Properties of Path Spaces

This module packages the core homotopy-theoretic facts about based path spaces:
they are contractible, their evaluation map is a fibration (path lifting), and
the based path space deformation retracts to its basepoint.

## Key Results

- `pathSpaceContr`: based path spaces are contractible
- `pathSpaceEvalLift`: evaluation map has canonical path lifts (fibration)
- `basedPathSpaceDeformationRetract`: deformation retract to the basepoint

## References

- HoTT Book, Sections 2.1 and 8.1
-/

import ComputationalPaths.Path.Homotopy.PathSpaceFibration
import ComputationalPaths.Path.Homotopy.HoTT

namespace ComputationalPaths
namespace Path
namespace PathSpaceHomotopy

open PathSpaceFibration Truncation Fibration HoTT

universe u

/-! ## Contractibility -/

/-- Based path spaces are contractible. -/
abbrev pathSpaceContr (A : Type u) (a : A) : IsContr (PathSpace A a) :=
  PathSpaceFibration.pathSpaceContr A a

/-! ## Evaluation map as a fibration -/

/-- The evaluation (endpoint) map of the based path space. -/
abbrev pathSpaceEval {A : Type u} {a : A} : PathSpace A a → A :=
  pathSpaceProj (A := A) (a := a)

/-- Path lifting for the evaluation map (the fibration structure). -/
noncomputable def pathSpaceEvalLift {A : Type u} {a : A}
    {x y : A} (p : Path x y) (q : LiftEq a x) :
    Path (⟨x, q⟩ : PathSpace A a) ⟨y, Path.transport p q⟩ :=
  Fibration.liftPath (P := fun x => LiftEq a x) p q

/-! ## Deformation retraction -/

/-- A deformation retraction of a type to a chosen point, encoded as a homotopy
from the identity map to the constant map. -/
abbrev DeformationRetractToPoint (A : Type u) (a : A) : Type u :=
  FunHomotopy (A := A) (B := A) (fun x => x) (fun _ => a)

/-- The based path space deformation retracts to its basepoint. -/
def basedPathSpaceDeformationRetract (A : Type u) (a : A) :
    DeformationRetractToPoint (PathSpace A a) (pathSpaceBase A a) :=
  fun x => (pathSpaceContr A a).contr x

/-! ## Summary

We record the contractibility of based path spaces, the fibration structure of
their evaluation map via path lifting, and the induced deformation retract to
the basepoint.
-/

end PathSpaceHomotopy
end Path
end ComputationalPaths
