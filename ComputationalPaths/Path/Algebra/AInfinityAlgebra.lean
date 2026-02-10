/-
# A-infinity algebras via computational paths

This module introduces a lightweight A-infinity algebra interface where the
coherence data is expressed using the `Path` type.  We model the operations as
a multiary multiplication on lists and record the Stasheff-style insertion law
and unit laws as computational paths.

## Key Definitions

- `AInfinityAlgebra`
- `AInfinityHom`

## References

- Stasheff, "Homotopy associativity of H-spaces" (1963)
- Loday and Vallette, "Algebraic Operads"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v

/-! ## A-infinity algebras -/

/-- Multiary multiplication represented by lists. -/
def AInfinityMul (A : Type u) : Type u := List A → A

/-- A-infinity algebra data with path-based associativity and units. -/
structure AInfinityAlgebra (A : Type u) where
  /-- Multiary multiplication. -/
  mul : AInfinityMul A
  /-- Chosen unit element. -/
  unit : A
  /-- Left unit law as a computational path. -/
  unit_left : ∀ xs : List A, Path (mul (unit :: xs)) (mul xs)
  /-- Right unit law as a computational path. -/
  unit_right : ∀ xs : List A, Path (mul (xs ++ [unit])) (mul xs)
  /-- Stasheff-style insertion law as a computational path. -/
  assoc :
    ∀ (xs ys zs : List A),
      Path (mul (xs ++ [mul ys] ++ zs)) (mul (xs ++ ys ++ zs))

namespace AInfinityAlgebra

variable {A : Type u} (S : AInfinityAlgebra A)

/-- Unary multiplication. -/
def mul1 (x : A) : A := S.mul [x]

/-- Binary multiplication. -/
def mul2 (x y : A) : A := S.mul [x, y]

/-- Ternary multiplication. -/
def mul3 (x y z : A) : A := S.mul [x, y, z]

/-- Associator specialized to binary multiplication. -/
def mul2_assoc (x y z : A) :
    Path (S.mul [S.mul [x, y], z]) (S.mul [x, y, z]) :=
  S.assoc [] [x, y] [z]

/-- Left unit on a single element. -/
def unit_left_one (x : A) : Path (S.mul [S.unit, x]) (S.mul [x]) :=
  S.unit_left [x]

/-- Right unit on a single element. -/
def unit_right_one (x : A) : Path (S.mul [x, S.unit]) (S.mul [x]) :=
  S.unit_right [x]

end AInfinityAlgebra

/-! ## A-infinity morphisms -/

/-- Morphisms preserving the A-infinity multiplication and unit up to paths. -/
structure AInfinityHom (A : Type u) (B : Type v)
    (S : AInfinityAlgebra A) (T : AInfinityAlgebra B) where
  /-- Underlying function. -/
  toFun : A → B
  /-- Multiplication preservation up to a computational path. -/
  map_mul :
    ∀ xs : List A,
      Path (toFun (S.mul xs)) (T.mul (xs.map toFun))
  /-- Unit preservation as a computational path. -/
  map_unit : Path (toFun S.unit) T.unit

namespace AInfinityHom

variable {A : Type u} {B : Type v}
variable {S : AInfinityAlgebra A} {T : AInfinityAlgebra B}

instance : CoeFun (AInfinityHom A B S T) (fun _ => A → B) :=
  ⟨AInfinityHom.toFun⟩

end AInfinityHom

end Algebra
end Path
end ComputationalPaths
