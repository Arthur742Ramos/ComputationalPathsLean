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
- Simplicial identities (face-face, degeneracy-degeneracy, face-degeneracy)
- Augmented and truncated simplicial objects
- Nerve construction for path spaces
- Coskeletal properties

## References

- May, "Simplicial objects in algebraic topology"
- Friedman, "An elementary illustrated introduction to simplicial sets"
- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path

universe u v

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
      Path (face n i (face (n + 1) j x)) (face n j (face (n + 1) i x))
  /-- Degeneracy maps commute. -/
  degeneracy_degeneracy :
    ∀ (n : Nat) (i j : Nat) (x : X n),
      Path (degeneracy (n + 1) i (degeneracy n j x))
        (degeneracy (n + 1) j (degeneracy n i x))
  /-- Faces cancel degeneracies. -/
  face_degeneracy :
    ∀ (n : Nat) (i j : Nat) (x : X n),
      Path (face n i (degeneracy n j x)) x

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
    exact Path.refl x
  degeneracy_degeneracy := by
    intro n i j x
    exact Path.refl x
  face_degeneracy := by
    intro n i j x
    exact Path.refl x

/-! ## Simplicial identities -/

/-- The face-face identity holds in any simplicial path structure (as a Path). -/
def face_face_path {X : Nat → Type u} (S : SimplicialPath X)
    (n : Nat) (i j : Nat) (x : X (n + 2)) :
    Path (S.face n i (S.face (n + 1) j x))
         (S.face n j (S.face (n + 1) i x)) :=
  S.face_face n i j x

/-- The degeneracy-degeneracy identity holds as a Path. -/
def degeneracy_degeneracy_path {X : Nat → Type u} (S : SimplicialPath X)
    (n : Nat) (i j : Nat) (x : X n) :
    Path (S.degeneracy (n + 1) i (S.degeneracy n j x))
         (S.degeneracy (n + 1) j (S.degeneracy n i x)) :=
  S.degeneracy_degeneracy n i j x

/-- The face-degeneracy identity holds as a Path. -/
def face_degeneracy_path {X : Nat → Type u} (S : SimplicialPath X)
    (n : Nat) (i j : Nat) (x : X n) :
    Path (S.face n i (S.degeneracy n j x)) x :=
  S.face_degeneracy n i j x

/-! ## Augmented simplicial objects -/

/-- An augmented simplicial path structure includes an augmentation map
from the 0-simplices to a base type. -/
structure AugmentedSimplicialPath (X : Nat → Type u) (B : Type u) extends
    SimplicialPath X where
  /-- Augmentation map. -/
  augmentation : X 0 → B
  /-- Augmentation is compatible with the face map on 1-simplices. -/
  augmentation_face :
    ∀ (i : Nat) (x : X 1),
      Path (augmentation (face 0 i x)) (augmentation (face 0 0 x))

/-- Augmented simplicial structure on the constant path family. -/
def augmentedSimplicialPath (A : Type u) (a : A) :
    AugmentedSimplicialPath (pathSimplices A a) (Path a a) where
  toSimplicialPath := simplicialPath A a
  augmentation := fun x => x
  augmentation_face := by
    intro i x
    exact Path.refl x

/-! ## Truncated simplicial objects -/

/-- A truncated simplicial path structure up to level `n`. -/
structure TruncatedSimplicialPath (X : Fin (n + 1) → Type u) where
  /-- Face maps. -/
  face : (k : Fin n) → Nat → X k.succ → X k.castSucc
  /-- Degeneracy maps. -/
  degeneracy : (k : Fin n) → Nat → X k.castSucc → X k.succ

/-- 0-truncated simplicial object: just a type. -/
def trivialTruncated (A : Type u) :
    TruncatedSimplicialPath (n := 0) (fun _ => A) where
  face := fun k => Fin.elim0 k
  degeneracy := fun k => Fin.elim0 k

/-! ## Nerve construction -/

/-- The nerve of a path space at a basepoint is the simplicial set whose
n-simplices are (n+1)-tuples of composable paths. We model this as
iterated loop paths. -/
def nerveSimplices (A : Type u) (a : A) : Nat → Type u
  | 0 => PUnit
  | n + 1 => Path a a × nerveSimplices A a n

/-- The nerve has a natural simplicial structure (using constant face/degeneracy). -/
def nerveSimplicialPath (A : Type u) (a : A) :
    SimplicialPath (nerveSimplices A a) where
  face := fun n _ x => match n, x with
    | 0, _ => PUnit.unit
    | Nat.succ _, (_, rest) => rest
  degeneracy := fun n _ x => match n, x with
    | 0, PUnit.unit => (Path.refl a, PUnit.unit)
    | Nat.succ _, pair => (Path.refl a, pair)
  face_face := fun _ _ _ _ => Path.refl _
  degeneracy_degeneracy := fun _ _ _ _ => Path.refl _
  face_degeneracy := fun n _ _ x => match n, x with
    | 0, PUnit.unit => Path.refl _
    | Nat.succ _, _ => Path.refl _

/-! ## Simplicial maps -/

/-- A simplicial map between two simplicial path structures. -/
structure SimplicialMap {X Y : Nat → Type u}
    (S : SimplicialPath X) (T : SimplicialPath Y) where
  /-- The map on each level. -/
  map : (n : Nat) → X n → Y n
  /-- Compatibility with face maps (up to Path). -/
  map_face : ∀ (n : Nat) (i : Nat) (x : X (n + 1)),
    Path (map n (S.face n i x)) (T.face n i (map (n + 1) x))
  /-- Compatibility with degeneracy maps (up to Path). -/
  map_degeneracy : ∀ (n : Nat) (i : Nat) (x : X n),
    Path (map (n + 1) (S.degeneracy n i x)) (T.degeneracy n i (map n x))

/-- The identity simplicial map. -/
def SimplicialMap.id {X : Nat → Type u} (S : SimplicialPath X) :
    SimplicialMap S S where
  map := fun _ x => x
  map_face := by
    intro n i x
    exact Path.refl _
  map_degeneracy := by
    intro n i x
    exact Path.refl _

/-- Composition of simplicial maps. -/
def SimplicialMap.comp {X Y Z : Nat → Type u}
    {S : SimplicialPath X} {T : SimplicialPath Y} {U : SimplicialPath Z}
    (f : SimplicialMap S T) (g : SimplicialMap T U) :
    SimplicialMap S U where
  map := fun n x => g.map n (f.map n x)
  map_face := by
    intro n i x
    exact Path.trans
      (Path.congrArg (g.map n) (f.map_face n i x))
      (g.map_face n i (f.map (n + 1) x))
  map_degeneracy := by
    intro n i x
    exact Path.trans
      (Path.congrArg (g.map (n + 1)) (f.map_degeneracy n i x))
      (g.map_degeneracy n i (f.map n x))

/-! ## Simplicial homotopy -/

/-- A simplicial homotopy between two simplicial maps. -/
structure SimplicialHomotopy {X Y : Nat → Type u}
    {S : SimplicialPath X} {T : SimplicialPath Y}
    (f g : SimplicialMap S T) where
  /-- The homotopy at each level. -/
  homotopy : (n : Nat) → (x : X n) → Path (f.map n x) (g.map n x)

/-- The trivial homotopy (identity). -/
def SimplicialHomotopy.refl {X Y : Nat → Type u}
    {S : SimplicialPath X} {T : SimplicialPath Y}
    (f : SimplicialMap S T) : SimplicialHomotopy f f where
  homotopy := fun _ x => Path.refl (f.map _ x)

/-- Symmetry of simplicial homotopy. -/
def SimplicialHomotopy.symm {X Y : Nat → Type u}
    {S : SimplicialPath X} {T : SimplicialPath Y}
    {f g : SimplicialMap S T}
    (h : SimplicialHomotopy f g) : SimplicialHomotopy g f where
  homotopy := fun n x => Path.symm (h.homotopy n x)

/-- Transitivity of simplicial homotopy. -/
def SimplicialHomotopy.trans {X Y : Nat → Type u}
    {S : SimplicialPath X} {T : SimplicialPath Y}
    {f g h : SimplicialMap S T}
    (hfg : SimplicialHomotopy f g)
    (hgh : SimplicialHomotopy g h) : SimplicialHomotopy f h where
  homotopy := fun n x => Path.trans (hfg.homotopy n x) (hgh.homotopy n x)

/-! ## Coskeletal properties -/

/-- A simplicial path structure is k-coskeletal if higher-dimensional
simplices are determined by their faces (up to propositional equality). -/
structure IsCoskeletal {X : Nat → Type u} (S : SimplicialPath X)
    (k : Nat) : Prop where
  /-- Joint injectivity of face maps. -/
  face_determines :
    ∀ (x y : X (k + 1)),
      (∀ (i : Nat), S.face k i x = S.face k i y) →
      x = y

/-- The trivial (constant) simplicial structure is 0-coskeletal. -/
theorem constant_is_0_coskeletal (A : Type u) (a : A) :
    IsCoskeletal (simplicialPath A a) 0 :=
  ⟨fun _x _y h => h 0⟩

/-! ## Geometric realization type -/

/-- The geometric realization type collects all simplices. -/
def GeometricRealizationType {X : Nat → Type u}
    (_S : SimplicialPath X) : Type u :=
  (n : Nat) × X n

/-- Inclusion of n-simplices into the realization. -/
def includeSimplices {X : Nat → Type u}
    (S : SimplicialPath X) (n : Nat) (x : X n) :
    GeometricRealizationType S :=
  ⟨n, x⟩

/-- The dimension of a simplex in the realization. -/
def simplexDimension {X : Nat → Type u}
    (_S : SimplicialPath X) (σ : GeometricRealizationType _S) : Nat :=
  σ.1

/-! ## Summary -/

/-!
We defined a minimal simplicial interface on indexed families and equipped
constant path families with identity face and degeneracy maps. We also
defined augmented and truncated simplicial objects, simplicial maps and
their composition, simplicial homotopies, the nerve construction,
coskeletal properties, and geometric realization types.
-/

end Path
end ComputationalPaths
