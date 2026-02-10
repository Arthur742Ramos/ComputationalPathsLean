/-
# Suspension space via computational paths

Defines the suspension Sigma X as a computational-path pushout of two unit points
along a type X, together with the canonical north/south poles and meridian
paths.

## Key Results

- `SuspensionCompPath`: the suspension of a type X.
- `SuspensionCompPath.north`/`south`: the poles of ΣX.
- `SuspensionCompPath.merid`: the meridian path for each x : X.
-/

import ComputationalPaths.Path.CompPath.PushoutCompPath

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Suspension space -/

/-- Suspension as a pushout of two unit points along X. -/
def SuspensionCompPath (X : Type u) : Type u :=
  Pushout PUnit' PUnit' X (fun _ => PUnit'.unit) (fun _ => PUnit'.unit)

namespace SuspensionCompPath

/-- North pole of the suspension. -/
def north {X : Type u} : SuspensionCompPath X :=
  Pushout.inl (A := PUnit') (B := PUnit') (C := X)
    (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) PUnit'.unit

/-- South pole of the suspension. -/
def south {X : Type u} : SuspensionCompPath X :=
  Pushout.inr (A := PUnit') (B := PUnit') (C := X)
    (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) PUnit'.unit

/-- Meridian from the north pole to the south pole. -/
def merid {X : Type u} (x : X) : Path (north (X := X)) (south (X := X)) :=
  Pushout.glue (A := PUnit') (B := PUnit') (C := X)
    (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) x

end SuspensionCompPath

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
