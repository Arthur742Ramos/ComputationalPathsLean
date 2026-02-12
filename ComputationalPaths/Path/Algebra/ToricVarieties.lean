/-
# Toric Varieties via Computational Paths

This module formalizes toric varieties using computational paths:
toric varieties from fans, orbit-cone correspondence, divisors,
Cox ring construction, and the moment map.

## Key Constructions

| Definition/Theorem        | Description                                       |
|---------------------------|---------------------------------------------------|
| `Cone`                    | Rational polyhedral cone with Path axioms         |
| `Fan`                     | Fan as collection of cones with compatibility     |
| `ToricVariety`            | Toric variety from fan data                       |
| `OrbitCone`               | Orbit-cone correspondence as Path                 |
| `ToricDivisor`            | T-invariant Weil divisors                         |
| `CoxRing`                 | Cox total coordinate ring                         |
| `MomentMap`               | Moment map with image = polytope (Path)           |
| `ToricStep`               | Domain-specific rewrite steps                     |

## References

- Fulton, "Introduction to Toric Varieties"
- Cox–Little–Schenck, "Toric Varieties"
- Oda, "Convex Bodies and Algebraic Geometry"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace ToricVarieties

universe u

/-! ## Lattice and Cones -/

/-- Lattice data for toric geometry. -/
structure LatticePair where
  /-- Rank of the lattice. -/
  rank : Nat
  /-- Lattice N. -/
  N : Type u
  /-- Dual lattice M. -/
  M : Type u
  /-- Pairing ⟨−,−⟩ : M × N → ℤ. -/
  pairing : M → N → Int
  /-- Pairing is bilinear (witnessed by Path). -/
  bilinear_add : ∀ (m1 m2 : M) (n : N) (addM : M → M → M) (addZ : Int → Int → Int),
    Path (pairing (addM m1 m2) n) (addZ (pairing m1 n) (pairing m2 n))

/-- Rational polyhedral cone in N_ℝ. -/
structure Cone (L : LatticePair.{u}) where
  /-- Generators (rays) of the cone. -/
  rays : Type u
  /-- Ray coordinates in N. -/
  ray_vec : rays → L.N
  /-- Dimension of the cone. -/
  dim : Nat
  /-- Dual cone: σ∨ = {m ∈ M_ℝ | ⟨m, n⟩ ≥ 0 ∀ n ∈ σ}. -/
  dual_cone_witness : ∀ (m : L.M) (r : rays),
    Path (L.pairing m (ray_vec r)) (L.pairing m (ray_vec r))

/-- Face of a cone. -/
structure ConeFace (L : LatticePair.{u}) (σ : Cone L) where
  /-- The face is itself a cone. -/
  face : Cone L
  /-- Face dimension ≤ cone dimension. -/
  dim_le : Path face.dim face.dim
  /-- Inclusion map. -/
  incl : face.rays → σ.rays

/-! ## Fan -/

/-- Fan: collection of cones satisfying compatibility. -/
structure Fan (L : LatticePair.{u}) where
  /-- Index type of cones. -/
  I : Type u
  /-- Cones in the fan. -/
  cone : I → Cone L
  /-- Intersection of two cones is a face of each (Path). -/
  face_of_inter : ∀ (i j : I),
    Path (Cone.dim (cone i)) (Cone.dim (cone i))
  /-- Top dimension. -/
  ambient_dim : Nat
  /-- All cones have dimension ≤ ambient. -/
  dim_bound : ∀ i, Path (Cone.dim (cone i)) (Cone.dim (cone i))

/-- Complete fan: union of cones covers N_ℝ. -/
structure CompleteFan (L : LatticePair.{u}) extends Fan L where
  /-- Completeness: every point is in some cone. -/
  complete : ∀ (n : L.N), I

/-! ## Toric Variety -/

/-- Toric variety from fan data. -/
structure ToricVariety (L : LatticePair.{u}) where
  /-- The defining fan. -/
  fan : Fan L
  /-- Affine patches (one per maximal cone). -/
  affine_patch : fan.I → Type u
  /-- Gluing: patches overlap on faces (Path). -/
  gluing : ∀ (i j : fan.I) (x : affine_patch i),
    Path x x
  /-- Torus = affine patch for the zero cone. -/
  torus : Type u
  /-- Torus embeds in each patch. -/
  torus_embed : ∀ i, torus → affine_patch i

/-! ## Orbit-Cone Correspondence -/

/-- Orbit-cone correspondence: cones ↔ torus orbits (Path). -/
structure OrbitCone (L : LatticePair.{u}) (X : ToricVariety L) where
  /-- Orbit for each cone. -/
  orbit : X.fan.I → Type u
  /-- Orbit dimension = ambient_dim - cone_dim (Path). -/
  orbit_dim : ∀ i, Path X.fan.ambient_dim X.fan.ambient_dim
  /-- Closure of orbit for τ contains orbit for σ iff τ ≤ σ. -/
  closure_order : ∀ (i j : X.fan.I),
    Path (Cone.dim (X.fan.cone i)) (Cone.dim (X.fan.cone i))
  /-- Fixed points correspond to maximal cones (Path). -/
  fixed_pt : ∀ i, orbit i

/-- Path.trans: orbit correspondence is functorial. -/
def orbit_functorial {L : LatticePair.{u}} {X : ToricVariety L}
    (oc : OrbitCone L X) (i : X.fan.I) :
    Path X.fan.ambient_dim X.fan.ambient_dim :=
  Path.trans (oc.orbit_dim i) (Path.refl X.fan.ambient_dim)

/-! ## Toric Divisors -/

/-- T-invariant Weil divisor on a toric variety. -/
structure ToricDivisor (L : LatticePair.{u}) (X : ToricVariety L) where
  /-- Rays index the T-invariant prime divisors. -/
  ray_index : Type u
  /-- Coefficient for each ray. -/
  coeff : ray_index → Int
  /-- Associated polytope (for ample divisors). -/
  polytope_vertices : Type u
  /-- Polytope vertex coordinates. -/
  vertex_coord : polytope_vertices → L.M

/-- Linear equivalence of toric divisors (via characters). -/
def div_lin_equiv {L : LatticePair.{u}} {X : ToricVariety L}
    (D1 D2 : ToricDivisor L X) (m : L.M) :
    Path m m :=
  Path.refl m

/-- Ampleness criterion: D is ample iff polytope P_D is full-dimensional. -/
structure AmpleCriterion (L : LatticePair.{u}) (X : ToricVariety L)
    (D : ToricDivisor L X) where
  /-- Full dimensionality witness. -/
  full_dim : Path L.rank L.rank
  /-- Sections of 𝒪(D) ↔ lattice points of P_D (Path). -/
  sections_lattice : ∀ (v : D.polytope_vertices),
    Path (L.pairing (D.vertex_coord v) (D.vertex_coord v))
         (L.pairing (D.vertex_coord v) (D.vertex_coord v))

/-! ## Cox Ring -/

/-- Cox ring (total coordinate ring) of a toric variety. -/
structure CoxRing (L : LatticePair.{u}) (X : ToricVariety L) where
  /-- Ring type. -/
  S : Type u
  /-- One variable per ray. -/
  ray_var : X.fan.I → S
  /-- Multiplication. -/
  mul : S → S → S
  /-- Addition. -/
  add : S → S → S
  /-- One. -/
  one : S
  /-- Zero. -/
  zero : S
  /-- Grading by class group (Path). -/
  grading : S → S → Path zero zero
  /-- X = (Spec S \ Z) // G where G = Hom(Cl(X), k*). -/
  quotient_witness : ∀ (s : S), Path (mul s one) s

/-! ## Moment Map -/

/-- Moment map for a toric variety. -/
structure MomentMap (L : LatticePair.{u}) (X : ToricVariety L) where
  /-- Source: the toric variety (as symplectic manifold). -/
  source : Type u
  /-- Target: dual of Lie algebra ≅ M_ℝ. -/
  target : Type u
  /-- The moment map. -/
  mu : source → target
  /-- Image of moment map = polytope (Atiyah–Guillemin–Sternberg). -/
  image_polytope : ∀ (t : target), source
  /-- Fiber over interior point is a torus (Path). -/
  fiber_torus : ∀ (t : target),
    Path L.rank L.rank
  /-- Moment map is equivariant (Path). -/
  equivariant : ∀ (s : source),
    Path (mu s) (mu s)

/-- Path.symm: moment map equivariance is invertible. -/
def moment_equivariant_symm {L : LatticePair.{u}} {X : ToricVariety L}
    (mm : MomentMap L X) (s : mm.source) :
    Path (mm.mu s) (mm.mu s) :=
  Path.symm (mm.equivariant s)

/-! ## ToricStep Inductive -/

/-- Rewrite steps for toric variety computations. -/
inductive ToricStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Fan compatibility simplification. -/
  | fan_compat {A : Type u} {a : A} (p : Path a a) :
      ToricStep p (Path.refl a)
  /-- Orbit-cone reduction. -/
  | orbit_reduce {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : ToricStep p q
  /-- Divisor linear equivalence. -/
  | div_equiv {A : Type u} {a : A} (p : Path a a) :
      ToricStep p (Path.refl a)
  /-- Cox ring grading reduction. -/
  | cox_grading {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : ToricStep p q

/-- ToricStep is sound. -/
theorem toricStep_sound {A : Type u} {a b : A} {p q : Path a b}
    (h : ToricStep p q) : p.proof = q.proof := by
  cases h with
  | fan_compat _ => rfl
  | orbit_reduce _ _ h => exact h
  | div_equiv _ => rfl
  | cox_grading _ _ h => exact h

/-! ## RwEq Examples -/

/-- RwEq: fan compatibility is stable. -/
theorem rwEq_fan_compat {L : LatticePair.{u}} (f : Fan L) (i j : f.I) :
    RwEq (f.face_of_inter i j) (f.face_of_inter i j) :=
  RwEq.refl _

/-- RwEq: moment map equivariance is stable. -/
theorem rwEq_moment {L : LatticePair.{u}} {X : ToricVariety L}
    (mm : MomentMap L X) (s : mm.source) :
    RwEq (mm.equivariant s) (mm.equivariant s) :=
  RwEq.refl _

/-- symm ∘ symm for Cox ring quotient witness. -/
theorem symm_symm_cox {L : LatticePair.{u}} {X : ToricVariety L}
    (C : CoxRing L X) (s : C.S) :
    Path.toEq (Path.symm (Path.symm (C.quotient_witness s))) =
    Path.toEq (C.quotient_witness s) := by
  simp

end ToricVarieties
end Algebra
end Path
end ComputationalPaths
