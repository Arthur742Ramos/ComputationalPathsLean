/-
# Simplicial Structure on Computational Paths

This module packages a lightweight simplicial structure for computational paths.
We model simplicial objects as indexed families and record face/degeneracy maps
with minimal identities, then instantiate the structure on constant path
families using identity maps.

## Key Results

- `SimplicialPath`: simplicial data for an indexed family
- `pathSimplices`: constant family of loop paths
- `simplicialPath`: simplicial structure on computational paths
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path

universe u

/-! ## Simplicial data -/

/-- A minimal simplicial structure on an indexed family. -/
structure SimplicialPath (X : Nat → Type u) where
  /-- Face maps. -/
  face : (n : Nat) → Nat → X (n + 1) → X n
  /-- Degeneracy maps. -/
  degeneracy : (n : Nat) → Nat → X n → X (n + 1)
  /-- Face maps commute. -/
  face_face :
    ∀ (n : Nat) (i j : Nat) (x : X (n + 2)),
      face n i (face (n + 1) j x) = face n j (face (n + 1) i x)
  /-- Degeneracy maps commute. -/
  degeneracy_degeneracy :
    ∀ (n : Nat) (i j : Nat) (x : X n),
      degeneracy (n + 1) i (degeneracy n j x) =
        degeneracy (n + 1) j (degeneracy n i x)
  /-- Faces cancel degeneracies. -/
  face_degeneracy :
    ∀ (n : Nat) (i j : Nat) (x : X n),
      face n i (degeneracy n j x) = x

/-! ## Simplicial paths -/

/-- Constant family of loop paths at a basepoint. -/
def pathSimplices (A : Type u) (a : A) : Nat → Type u :=
  fun _ => Path a a

/-- Simplicial structure on constant path families via identities. -/
def simplicialPath (A : Type u) (a : A) :
    SimplicialPath (pathSimplices A a) where
  face := fun _ _ x => x
  degeneracy := fun _ _ x => x
  face_face := by
    intro n i j x
    rfl
  degeneracy_degeneracy := by
    intro n i j x
    rfl
  face_degeneracy := by
    intro n i j x
    rfl

/-! ## Summary -/

/-!
We defined a minimal simplicial interface on indexed families and equipped
constant path families with identity face and degeneracy maps.
-/

end Path
end ComputationalPaths
