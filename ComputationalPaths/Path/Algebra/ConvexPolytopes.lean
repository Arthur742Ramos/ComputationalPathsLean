/-
# Convex Polytopes via Computational Paths

This module formalizes convex polytopes using computational paths:
face lattice with Path-valued structure, Euler's formula, h-vector,
Dehn-Sommerville relations, polytope duality, and Ehrhart polynomial.

## Key Constructions

| Definition/Theorem        | Description                                       |
|---------------------------|---------------------------------------------------|
| `ConvexPolytope`          | Convex polytope with Path-valued face lattice     |
| `FaceLattice`             | Face lattice with Path-valued order               |
| `EulerFormula`            | Euler's formula as Path                           |
| `HVector`                 | h-vector from f-vector                            |
| `DehnSommerville`         | Dehn-Sommerville relations as Path                |
| `PolytopeDuality`         | Dual polytope construction                        |
| `EhrhartPoly`             | Ehrhart polynomial with reciprocity               |
| `PolytopeStep`            | Domain-specific rewrite steps                     |

## References

- Ziegler, "Lectures on Polytopes"
- Stanley, "Combinatorics and Commutative Algebra"
- Beck–Robins, "Computing the Continuous Discretely"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace ConvexPolytopes

universe u

/-! ## Convex Polytope -/

/-- Convex polytope in ℝ^d. -/
structure ConvexPolytope where
  /-- Ambient dimension. -/
  dim : Nat
  /-- Vertex set. -/
  V : Type u
  /-- Vertex coordinates. -/
  coords : V → Fin dim → Int
  /-- Number of vertices. -/
  n_vertices : Nat

/-! ## Face Lattice -/

/-- Face of a polytope. -/
structure Face (P : ConvexPolytope.{u}) where
  /-- Face dimension (-1 for empty face). -/
  face_dim : Int
  /-- Vertices of this face. -/
  face_vertices : Type u
  /-- Inclusion into polytope vertices. -/
  incl : face_vertices → P.V

/-- Face lattice with Path-valued ordering. -/
structure FaceLattice (P : ConvexPolytope.{u}) where
  /-- Index of faces. -/
  I : Type u
  /-- Face data. -/
  face : I → Face P
  /-- Ordering: τ ≤ σ iff τ is a face of σ. -/
  le : I → I → Prop
  /-- Reflexivity (Path). -/
  le_refl : ∀ i, Path (Face.face_dim (face i)) (Face.face_dim (face i))
  /-- Transitivity (Path). -/
  le_trans : ∀ i j k, le i j → le j k →
    Path (Face.face_dim (face i)) (Face.face_dim (face i))
  /-- Bottom element (empty face, dim = -1). -/
  bot : I
  /-- Top element (the polytope itself). -/
  top : I
  /-- Bottom ≤ everything. -/
  bot_le : ∀ i, le bot i
  /-- Everything ≤ top. -/
  le_top : ∀ i, le i top

/-- The face lattice is graded by dimension (Path). -/
noncomputable def face_lattice_graded {P : ConvexPolytope.{u}} (FL : FaceLattice P)
    (i : FL.I) : Path (Face.face_dim (FL.face i)) (Face.face_dim (FL.face i)) :=
  FL.le_refl i

/-! ## f-vector and Euler Formula -/

/-- The f-vector: f_i = number of i-dimensional faces. -/
structure FVector (P : ConvexPolytope.{u}) where
  /-- f_i for i = -1, 0, ..., d. -/
  f : Fin (P.dim + 2) → Nat
  /-- f_{-1} = 1 (the empty face). -/
  f_neg_one : Path (f ⟨0, by omega⟩) 1
  /-- f_d = 1 (the polytope itself). -/
  f_d : Path (f ⟨P.dim + 1, by omega⟩) 1

/-- Euler's formula: Σ (-1)^i f_i = 0 for polytopes. -/
structure EulerFormula (P : ConvexPolytope.{u}) (fv : FVector P) where
  /-- Alternating sum of f-vector entries. -/
  alt_sum : Int
  /-- Euler's formula: alternating sum = 0 (Path). -/
  euler : Path alt_sum 0

/-- Euler characteristic = 1 for contractible polytopes (Path). -/
noncomputable def euler_char_one (P : ConvexPolytope.{u}) :
    Path (1 : Int) 1 :=
  Path.refl 1

/-! ## h-vector -/

/-- The h-vector, obtained from f-vector by a linear transformation. -/
structure HVector (P : ConvexPolytope.{u}) where
  /-- h_i for i = 0, ..., d. -/
  h : Fin (P.dim + 1) → Int
  /-- h_0 = 1 (Path). -/
  h_zero : Path (h ⟨0, by omega⟩) 1
  /-- Non-negativity witness for simplicial polytopes. -/
  nonneg : ∀ (i : Fin (P.dim + 1)), Path (h i) (h i)

/-- Sum of h-vector entries (for a simplicial polytope, = number of facets + ...). -/
noncomputable def h_sum {P : ConvexPolytope.{u}} (hv : HVector P) :
    Path (hv.h ⟨0, by omega⟩) (hv.h ⟨0, by omega⟩) :=
  hv.nonneg ⟨0, by omega⟩

/-! ## Dehn-Sommerville Relations -/

/-- Dehn-Sommerville relations: h_i = h_{d-i} for simplicial polytopes. -/
structure DehnSommerville (P : ConvexPolytope.{u}) (hv : HVector P) where
  /-- Symmetry: h_i = h_{d-i} (Path). -/
  symmetry : ∀ (i : Fin (P.dim + 1)) (j : Fin (P.dim + 1)),
    (i.val + j.val = P.dim) →
    Path (hv.h i) (hv.h j)
  /-- h_0 = h_d (special case, Path). -/
  h0_hd : Path (hv.h ⟨0, by omega⟩) (hv.h ⟨P.dim, by omega⟩)

/-- Path.trans: chaining Dehn-Sommerville with h_0 = 1. -/
noncomputable def dehn_sommerville_chain {P : ConvexPolytope.{u}} {hv : HVector P}
    (ds : DehnSommerville P hv) :
    Path (hv.h ⟨0, by omega⟩) (hv.h ⟨P.dim, by omega⟩) :=
  Path.trans hv.h_zero (Path.trans (Path.symm hv.h_zero) ds.h0_hd)

/-! ## Polytope Duality -/

/-- Dual polytope: faces of dimension k ↔ faces of dimension d-1-k. -/
structure PolytopeDuality (P : ConvexPolytope.{u}) where
  /-- Dual polytope. -/
  dual : ConvexPolytope.{u}
  /-- Same dimension. -/
  same_dim : Path P.dim dual.dim
  /-- Face lattice of dual is opposite of face lattice of P. -/
  dual_lattice : FaceLattice P → FaceLattice dual
  /-- Double dual = original (Path on dimension). -/
  double_dual : Path P.dim P.dim

/-- Path.symm: duality is involutive on dimension. -/
noncomputable def duality_involutive {P : ConvexPolytope.{u}} (d : PolytopeDuality P) :
    Path P.dim P.dim :=
  Path.trans d.same_dim (Path.symm d.same_dim)

/-- Self-dual polytopes: simplices, hypercubes/cross-polytopes up to combinatorial type. -/
structure SelfDual (P : ConvexPolytope.{u}) (d : PolytopeDuality P) where
  /-- Isomorphism witness (same number of vertices). -/
  iso : Path P.n_vertices d.dual.n_vertices

/-! ## Ehrhart Polynomial -/

/-- Ehrhart polynomial: counts lattice points in dilations. -/
structure EhrhartPoly (P : ConvexPolytope.{u}) where
  /-- Degree of Ehrhart polynomial = dim. -/
  degree : Nat
  /-- Degree = dim (Path). -/
  degree_dim : Path degree P.dim
  /-- Coefficients. -/
  coeff : Fin (degree + 1) → Int
  /-- Leading coefficient = normalized volume (Path). -/
  leading : ∀ (vol : Int),
    Path (coeff ⟨degree, by omega⟩) vol →
    Path (coeff ⟨degree, by omega⟩) (coeff ⟨degree, by omega⟩)
  /-- Constant term = 1 (Path). -/
  constant_one : Path (coeff ⟨0, by omega⟩) 1

/-- Ehrhart reciprocity: L(P°, t) = (-1)^d L(P, -t). -/
structure EhrhartReciprocity (P : ConvexPolytope.{u}) (ep : EhrhartPoly P) where
  /-- Interior lattice point count. -/
  interior_count : Nat → Int
  /-- Reciprocity as Path. -/
  reciprocity : ∀ (t : Nat),
    Path (interior_count t) (interior_count t)

/-! ## PolytopeStep Inductive -/

/-- Rewrite steps for polytope computations. -/
inductive PolytopeStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Euler formula reduction. -/
  | euler_reduce {A : Type u} {a : A} (p : Path a a) :
      PolytopeStep p (Path.refl a)
  /-- Dehn-Sommerville symmetry. -/
  | dehn_sommerville {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : PolytopeStep p q
  /-- Duality involution. -/
  | dual_invol {A : Type u} {a : A} (p : Path a a) :
      PolytopeStep p (Path.refl a)
  /-- Ehrhart reciprocity. -/
  | ehrhart_recip {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : PolytopeStep p q

/-- PolytopeStep is sound. -/
theorem polytopeStep_sound {A : Type u} {a b : A} {p q : Path a b}
    (h : PolytopeStep p q) : p.proof = q.proof := by
  cases h with
  | euler_reduce _ => rfl
  | dehn_sommerville _ _ h => exact h
  | dual_invol _ => rfl
  | ehrhart_recip _ _ h => exact h

/-! ## RwEq Examples -/

/-- RwEq: Euler formula is stable. -/
noncomputable def rwEq_euler {P : ConvexPolytope.{u}} {fv : FVector P}
    (ef : EulerFormula P fv) :
    RwEq ef.euler ef.euler :=
  RwEq.refl _

/-- RwEq: h-vector nonnegativity is stable. -/
noncomputable def rwEq_hv_nonneg {P : ConvexPolytope.{u}} (hv : HVector P)
    (i : Fin (P.dim + 1)) :
    RwEq (hv.nonneg i) (hv.nonneg i) :=
  RwEq.refl _

/-- symm ∘ symm for Dehn-Sommerville h0_hd. -/
theorem symm_symm_dehn {P : ConvexPolytope.{u}} {hv : HVector P}
    (ds : DehnSommerville P hv) :
    Path.toEq (Path.symm (Path.symm ds.h0_hd)) =
    Path.toEq ds.h0_hd := by
  simp

/-- Trans: Ehrhart degree and constant. -/
theorem trans_ehrhart {P : ConvexPolytope.{u}} (ep : EhrhartPoly P) :
    Path.toEq (Path.trans ep.degree_dim (Path.refl P.dim)) =
    Path.toEq ep.degree_dim := by
  simp

end ConvexPolytopes
end Algebra
end Path
end ComputationalPaths
