/-
# Configuration spaces via computational paths

Defines ordered configuration spaces as families of points indexed by `Fin n`
with a path-based collision predicate. Two indices are forbidden to coincide
whenever a `Path` connects the corresponding points.

## Key Results

- `NoCollision`: path-based distinctness predicate.
- `ConfigurationSpace`: ordered configurations of `n` points in a type.
- `ConfigurationSpace.points` / `ConfigurationSpace.noCollision`: projections.
- `configurationSpaceEmpty`: the empty configuration (n = 0).
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Collision predicates -/

/-- Path-based collision predicate for a family of points.
    Two distinct indices must not be connected by a path.
    Since `Path` lives in `Type u`, we use function to `False`. -/
def NoCollision {A : Type u} {n : Nat} (f : Fin n → A) : Prop :=
  ∀ {i j : Fin n}, i ≠ j → Path (f i) (f j) → False

/-! ## Configuration spaces -/

/-- Ordered configuration space of `n` points in `A`. -/
def ConfigurationSpace (A : Type u) (n : Nat) : Type u :=
  {f : Fin n → A // NoCollision f}

namespace ConfigurationSpace

variable {A : Type u} {n : Nat}

/-- Underlying family of points. -/
@[simp] def points (c : ConfigurationSpace A n) : Fin n → A := c.1

/-- Collision-free property for configurations. -/
theorem noCollision (c : ConfigurationSpace A n) {i j : Fin n} (h : i ≠ j)
    (p : Path (points c i) (points c j)) : False :=
  c.2 h p

end ConfigurationSpace

/-! ## Empty configuration -/

/-- The unique empty configuration. -/
def configurationSpaceEmpty (A : Type u) : ConfigurationSpace A 0 :=
  ⟨(fun i => nomatch i), fun {i} => nomatch i⟩

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
