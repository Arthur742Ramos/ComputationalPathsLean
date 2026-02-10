/-
# Join space via computational paths

Defines the join `X * Y` as the computational pushout of the projection maps
`X × Y → X` and `X × Y → Y`.  This provides canonical inclusions and a
`Path`-valued glue constructor without introducing axioms.

## Key Results

- `JoinSpace`: the join type.
- `JoinSpace.inl`/`JoinSpace.inr`: canonical inclusions.
- `JoinSpace.glue`: the join glue path.
-/

import ComputationalPaths.Path.CompPath.PushoutCompPath

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u v

/-! ## Join space -/

/-- Join of `X` and `Y` as the computational pushout of the projections. -/
def JoinSpace (X : Type u) (Y : Type v) : Type (max u v) :=
  Pushout (A := X) (B := Y) (C := X × Y) Prod.fst Prod.snd

namespace JoinSpace

variable {X : Type u} {Y : Type v}

/-- Left inclusion into the join. -/
def inl (x : X) : JoinSpace X Y :=
  Pushout.inl (A := X) (B := Y) (C := X × Y) (f := Prod.fst) (g := Prod.snd) x

/-- Right inclusion into the join. -/
def inr (y : Y) : JoinSpace X Y :=
  Pushout.inr (A := X) (B := Y) (C := X × Y) (f := Prod.fst) (g := Prod.snd) y

/-- Glue path connecting left and right points for each `(x, y)`. -/
def glue (x : X) (y : Y) :
    Path (inl (X := X) (Y := Y) x) (inr (X := X) (Y := Y) y) :=
  Pushout.glue (A := X) (B := Y) (C := X × Y) (f := Prod.fst) (g := Prod.snd) (x, y)

end JoinSpace

/-! ## Compatibility aliases -/

/-- Alias for the join space. -/
abbrev Join (X : Type u) (Y : Type v) : Type (max u v) := JoinSpace X Y

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
