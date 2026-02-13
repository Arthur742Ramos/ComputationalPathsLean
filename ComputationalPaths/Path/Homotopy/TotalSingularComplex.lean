/-
# Total Singular Complex Functor in the Computational Paths Framework

This module formalizes the total singular complex functor. The singular complex
of a type/space X is the simplicial set whose n-simplices are maps from the
standard n-simplex to X.

## Mathematical Background

A singular n-simplex in X is a map σ : Δⁿ → X. The singular complex Sing(X)
is the simplicial set with these as n-simplices. Face and degeneracy maps
are induced by precomposition with the standard simplicial operators.

## Key Results

| Definition/Theorem | Statement |
|-------------------|-----------|
| `SingularSimplex` | Map from Fin (n+1) to X |
| `SingularComplex` | Simplicial set of singular simplices |
| `face_const` | Face of constant simplex is constant |
| `degen_const` | Degeneracy of constant is constant |
| `singularMap` | Functorial action on singular simplices |
| `singularMap_face` | Singular map commutes with face maps |
| `singularMap_id` | Singular map of id is id |
| `singularMap_comp` | Singular map respects composition |
| `BoundarySquareZero` | ∂² = 0 structure |

## References

- Hatcher, "Algebraic Topology", Section 2.1
- May, "A Concise Course in Algebraic Topology"
-/

import ComputationalPaths.Path.Homotopy.KanComplex
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace TotalSingularComplex

open KanComplex

universe u

/-! ## Singular Simplices

We model a singular n-simplex as a function from Fin (n+1) to X.
This is a simplified combinatorial model: we think of the n-simplex
as having (n+1) vertices and the map sends vertices to points of X.
-/

/-- A singular n-simplex in a type X (vertex map model). -/
@[ext]
structure SingularSimplex (X : Type u) (n : Nat) where
  /-- The map on vertices. -/
  toFun : Fin (n + 1) → X

namespace SingularSimplex

variable {X : Type u}

/-- The i-th face of a singular (n+1)-simplex: omit vertex i. -/
def face {n : Nat} (i : Fin (n + 2)) (σ : SingularSimplex X (n + 1)) :
    SingularSimplex X n where
  toFun := fun j =>
    if j.val < i.val then σ.toFun ⟨j.val, by omega⟩
    else σ.toFun ⟨j.val + 1, by omega⟩

/-- The i-th degeneracy of a singular n-simplex: repeat vertex i. -/
def degen {n : Nat} (i : Fin (n + 1)) (σ : SingularSimplex X n) :
    SingularSimplex X (n + 1) where
  toFun := fun j =>
    if h : j.val ≤ i.val then σ.toFun ⟨j.val, by omega⟩
    else σ.toFun ⟨j.val - 1, by omega⟩

/-- A constant singular simplex at a point. -/
def const (x : X) (n : Nat) : SingularSimplex X n where
  toFun := fun _ => x

/-- Face of a constant simplex is constant. -/
theorem face_const (x : X) (n : Nat) (i : Fin (n + 2)) :
    face i (const x (n + 1)) = const x n := by
  ext j
  simp [face, const]

/-- `Path`-typed face of constant. -/
def face_const_path (x : X) (n : Nat) (i : Fin (n + 2)) :
    Path (face i (const x (n + 1))) (const x n) :=
  Path.stepChain (face_const x n i)

/-- Degeneracy of a constant simplex is constant. -/
theorem degen_const (x : X) (n : Nat) (i : Fin (n + 1)) :
    degen i (const x n) = const x (n + 1) := by
  ext j
  simp [degen, const]

/-- `Path`-typed degeneracy of constant. -/
def degen_const_path (x : X) (n : Nat) (i : Fin (n + 1)) :
    Path (degen i (const x n)) (const x (n + 1)) :=
  Path.stepChain (degen_const x n i)

end SingularSimplex

/-! ## Singular Complex as a Simplicial Set -/

/-- The singular complex of X as an `SSetData`. -/
def singularComplex (X : Type u) : SSetData where
  obj := fun n => SingularSimplex X n
  face := fun n i σ => SingularSimplex.face i σ
  degen := fun n i σ => SingularSimplex.degen i σ

/-- The singular complex applied to a point gives a constant simplicial set. -/
theorem singularComplex_const (X : Type u) (x : X) (n : Nat) (i : Fin (n + 2)) :
    (singularComplex X).face n i (SingularSimplex.const x (n + 1)) =
    SingularSimplex.const x n :=
  SingularSimplex.face_const x n i

/-! ## Boundary and ∂² = 0

The boundary operator is the alternating sum of face maps.
The key identity for ∂² = 0 is the simplicial identity:
  d_i ∘ d_j = d_{j-1} ∘ d_i  for i < j
-/

/-- Signs for the alternating sum boundary: (-1)^i. -/
def boundarySign (i : Nat) : Int :=
  if i % 2 = 0 then 1 else -1

/-- The simplicial identity for face maps: d_i ∘ d_j = d_{j+1} ∘ d_i for i ≤ j.
    In our vertex model, face i (face j σ) agrees with
    face (j+1) (face i σ) when i ≤ j. -/
theorem face_face_identity {X : Type u} {n : Nat}
    (σ : SingularSimplex X (n + 2))
    (i j : Nat) (hi : i < n + 2) (hj : j < n + 2) (hij : i ≤ j) :
    SingularSimplex.face ⟨i, by omega⟩
      (SingularSimplex.face ⟨j + 1, by omega⟩ σ) =
    SingularSimplex.face ⟨j, by omega⟩
      (SingularSimplex.face ⟨i, by omega⟩ σ) := by
  ext ⟨k, hk⟩
  simp [SingularSimplex.face]
  split_ifs with h1 h2 h3 h4 <;> congr 1 <;> omega

/-- `Path`-typed face-face identity. -/
def face_face_path {X : Type u} {n : Nat}
    (σ : SingularSimplex X (n + 2))
    (i j : Nat) (hi : i < n + 2) (hj : j < n + 2) (hij : i ≤ j) :
    Path (SingularSimplex.face ⟨i, by omega⟩
            (SingularSimplex.face ⟨j + 1, by omega⟩ σ))
         (SingularSimplex.face ⟨j, by omega⟩
            (SingularSimplex.face ⟨i, by omega⟩ σ)) :=
  Path.stepChain (face_face_identity σ i j hi hj hij)

/-- ∂² = 0 structure: the signed face maps cancel pairwise. -/
structure BoundarySquareZero (X : Type u) where
  /-- For each pair (i,j) with i ≤ j, the corresponding terms in ∂² cancel. -/
  cancel : ∀ (n : Nat) (σ : SingularSimplex X (n + 2))
    (i j : Nat) (hi : i < n + 2) (hj : j < n + 2) (hij : i ≤ j),
    boundarySign i * boundarySign (j + 1) +
    boundarySign j * boundarySign i = 0

/-! ## Singular Homology Connection -/

/-- Singular homology data: cycles modulo boundaries. -/
structure SingularHomologyData (X : Type u) (n : Nat) where
  /-- The cycles: simplices whose boundary is trivial. -/
  isCycle : SingularSimplex X n → Prop
  /-- The boundaries: simplices that are boundaries of (n+1)-simplices. -/
  isBoundary : SingularSimplex X n → Prop
  /-- Every boundary is a cycle (∂² = 0). -/
  boundary_is_cycle : ∀ σ, isBoundary σ → isCycle σ

/-! ## Functoriality of the Singular Complex -/

/-- A map f : X → Y induces a map on singular simplices. -/
def singularMap {X Y : Type u} (f : X → Y) (n : Nat) :
    SingularSimplex X n → SingularSimplex Y n :=
  fun σ => { toFun := f ∘ σ.toFun }

/-- The singular map preserves face maps. -/
theorem singularMap_face {X Y : Type u} (f : X → Y) (n : Nat)
    (i : Fin (n + 2)) (σ : SingularSimplex X (n + 1)) :
    singularMap f n (SingularSimplex.face i σ) =
    SingularSimplex.face i (singularMap f (n + 1) σ) := by
  ext ⟨j, hj⟩
  simp [singularMap, SingularSimplex.face, Function.comp]
  split_ifs <;> rfl

/-- `Path`-typed functoriality for face maps. -/
def singularMap_face_path {X Y : Type u} (f : X → Y) (n : Nat)
    (i : Fin (n + 2)) (σ : SingularSimplex X (n + 1)) :
    Path (singularMap f n (SingularSimplex.face i σ))
         (SingularSimplex.face i (singularMap f (n + 1) σ)) :=
  Path.stepChain (singularMap_face f n i σ)

/-- The singular map preserves degeneracy maps. -/
theorem singularMap_degen {X Y : Type u} (f : X → Y) (n : Nat)
    (i : Fin (n + 1)) (σ : SingularSimplex X n) :
    singularMap f (n + 1) (SingularSimplex.degen i σ) =
    SingularSimplex.degen i (singularMap f n σ) := by
  ext ⟨j, hj⟩
  simp [singularMap, SingularSimplex.degen, Function.comp]
  split_ifs <;> rfl

/-- Identity map induces identity on singular simplices. -/
theorem singularMap_id {X : Type u} (n : Nat) (σ : SingularSimplex X n) :
    singularMap id n σ = σ := by
  ext j
  simp [singularMap, Function.comp]

/-- `Path`-typed identity. -/
def singularMap_id_path {X : Type u} (n : Nat) (σ : SingularSimplex X n) :
    Path (singularMap id n σ) σ :=
  Path.stepChain (singularMap_id n σ)

/-- Composition of maps induces composition on singular simplices. -/
theorem singularMap_comp {X Y Z : Type u} (f : X → Y) (g : Y → Z)
    (n : Nat) (σ : SingularSimplex X n) :
    singularMap g n (singularMap f n σ) = singularMap (g ∘ f) n σ := by
  ext j
  simp [singularMap, Function.comp]

/-- `Path`-typed composition. -/
def singularMap_comp_path {X Y Z : Type u} (f : X → Y) (g : Y → Z)
    (n : Nat) (σ : SingularSimplex X n) :
    Path (singularMap g n (singularMap f n σ)) (singularMap (g ∘ f) n σ) :=
  Path.stepChain (singularMap_comp f g n σ)

/-! ## Summary

We have formalized:
- Singular n-simplices as vertex maps Fin (n+1) → X
- The singular complex as an SSetData
- Face and degeneracy maps on singular simplices
- The simplicial identity d_i d_{j+1} = d_j d_i for i ≤ j
- Boundary data and the ∂² = 0 structure
- Singular homology data
- Functoriality of the singular complex
- Path witnesses for all key identities
-/

end TotalSingularComplex
end Homotopy
end Path
end ComputationalPaths
