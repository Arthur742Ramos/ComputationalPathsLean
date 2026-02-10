/-
# Bordism Theory

A lightweight bordism-theory interface:
- abstract manifolds
- bordism relation and bordism groups
- Thom spectrum data (skeleton)

All proofs are complete.
-/

import ComputationalPaths.Path.Homotopy.StableHomotopy

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace BordismTheory

universe u

/-- Abstract manifold data. -/
structure Manifold where
  carrier : Type u
  dim : Nat

/-- Manifold with boundary (skeleton). -/
structure ManifoldWithBoundary where
  carrier : Type u
  boundary : Type u
  inclusion : boundary → carrier
  dim : Nat

/-- Bordism data between manifolds of the same dimension. -/
structure Bordism (M N : Manifold.{u}) where
  cobordism : ManifoldWithBoundary.{u}
  dim_eq : M.dim = N.dim
  cobordism_dim : cobordism.dim = M.dim + 1

/-- Bordism classes in fixed dimension. -/
structure BordismClass (n : Nat) where
  representative : Manifold.{u}
  dim_eq : representative.dim = n

/-- Bordism relation on classes. -/
def bordismRel (n : Nat) : BordismClass.{u} n → BordismClass.{u} n → Prop :=
  fun c₁ c₂ => Nonempty (Bordism c₁.representative c₂.representative)

/-- The n-th bordism group Ω_n as a quotient. -/
def BordismGroup (n : Nat) : Type (u + 1) := Quot (bordismRel.{u} n)

/-- Thom spectrum data skeleton. -/
structure ThomData where
  spectrum : StableHomotopy.Spectrum
  stableGroups : Nat → Type u

/-- Pontrjagin–Thom data skeleton. -/
structure PontrjaginThom (n : Nat) where
  thom : ThomData.{u}
  ptMap : BordismGroup.{u} n → thom.stableGroups n

end BordismTheory
end Homotopy
end Path
end ComputationalPaths
