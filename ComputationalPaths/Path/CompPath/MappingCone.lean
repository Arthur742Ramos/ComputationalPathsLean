/-
# Mapping cone via computational pushouts

Defines the mapping cone (cofiber) of a map `f : A -> B` as a pushout of `B`
and `PUnit'` along `A` in the computational-path setting.

## Key Results

- `MappingCone`: the mapping cone type.
- `Cofiber`: alias for the mapping cone.
- `Cofiber.inl`, `Cofiber.basepoint`, `Cofiber.glue`: basic constructors.

## References

- Computational paths pushout construction.
-/

import ComputationalPaths.Path.CompPath.PushoutCompPath

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

variable {A B : Type u}

/-! ## Mapping cone (cofiber) -/

/-- The mapping cone (cofiber) of `f : A -> B` as a pushout of `B` and `1` along `A`. -/
def MappingCone (f : A -> B) : Type u :=
  Pushout B PUnit' A f (fun _ => PUnit'.unit)

/-- Alias for the mapping cone. -/
abbrev Cofiber (f : A -> B) : Type u := MappingCone f

namespace Cofiber

variable (f : A -> B)

/-- Inclusion of `B` into the cofiber. -/
def inl (b : B) : Cofiber f :=
  Pushout.inl (A := B) (B := PUnit') (C := A) (f := f) (g := fun _ => PUnit'.unit) b

/-- The basepoint of the cofiber (the cone point). -/
def basepoint : Cofiber f :=
  Pushout.inr (A := B) (B := PUnit') (C := A) (f := f) (g := fun _ => PUnit'.unit) PUnit'.unit

/-- The gluing path identifying `f a` with the cone point. -/
def glue (a : A) :
    Path (inl (f := f) (f a)) (basepoint (f := f)) :=
  Pushout.glue (A := B) (B := PUnit') (C := A) (f := f) (g := fun _ => PUnit'.unit) a

end Cofiber

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
