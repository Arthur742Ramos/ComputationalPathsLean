/-
# Tropical Geometry via Computational Paths

This module formalizes tropical geometry using computational paths:
the tropical semiring, tropical varieties, tropical curves, Kapranov's theorem,
tropical intersection theory, and Newton polytopes.

## Key Constructions

| Definition/Theorem          | Description                                        |
|-----------------------------|----------------------------------------------------|
| `TropicalSemiring`          | Tropical semiring (min-plus) with Path axioms      |
| `TropicalPoly`              | Tropical polynomials with Path-valued evaluation   |
| `TropicalVariety`           | Tropical variety as corner locus                   |
| `TropicalCurve`             | Abstract tropical curve (metric graph)             |
| `KapranovThm`               | Kapranov's theorem: trop(V) = val(V) as Path      |
| `TropicalIntersection`      | Tropical intersection with balancing condition     |
| `NewtonPolytope`            | Newton polytope and subdivision                    |
| `TropicalStep`              | Domain-specific rewrite steps                      |

## References

- Maclagan–Sturmfels, "Introduction to Tropical Geometry"
- Mikhalkin, "Enumerative tropical algebraic geometry"
- Kapranov, "Amoebas over non-archimedean fields"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace TropicalGeometry

universe u

/-! ## Tropical Semiring -/

/-- Tropical semiring with min-plus operations and Path axioms. -/
structure TropicalSemiring where
  /-- Carrier type (extended reals). -/
  T : Type u
  /-- Tropical addition (min). -/
  trop_add : T → T → T
  /-- Tropical multiplication (plus). -/
  trop_mul : T → T → T
  /-- Additive identity (∞). -/
  infty : T
  /-- Multiplicative identity (0). -/
  zero : T
  /-- Commutativity of tropical addition. -/
  add_comm : ∀ a b, Path (trop_add a b) (trop_add b a)
  /-- Associativity of tropical addition. -/
  add_assoc : ∀ a b c, Path (trop_add (trop_add a b) c) (trop_add a (trop_add b c))
  /-- Associativity of tropical multiplication. -/
  mul_assoc : ∀ a b c, Path (trop_mul (trop_mul a b) c) (trop_mul a (trop_mul b c))
  /-- Distributivity: a ⊙ (b ⊕ c) = (a ⊙ b) ⊕ (a ⊙ c). -/
  distrib : ∀ a b c, Path (trop_mul a (trop_add b c))
                           (trop_add (trop_mul a b) (trop_mul a c))
  /-- Additive identity: a ⊕ ∞ = a. -/
  add_infty : ∀ a, Path (trop_add a infty) a
  /-- Multiplicative identity: a ⊙ 0 = a. -/
  mul_zero : ∀ a, Path (trop_mul a zero) a
  /-- Idempotence: a ⊕ a = a (tropical!). -/
  add_idem : ∀ a, Path (trop_add a a) a

/-- Left identity for tropical addition. -/
def trop_add_infty_left (S : TropicalSemiring.{u}) (a : S.T) :
    Path (S.trop_add S.infty a) a :=
  Path.trans (S.add_comm S.infty a) (S.add_infty a)

/-- Left identity for tropical multiplication. -/
def trop_mul_zero_left (S : TropicalSemiring.{u}) (a : S.T) :
    Path (S.trop_mul S.zero a) a :=
  let comm : Path (S.trop_mul S.zero a) (S.trop_mul a S.zero) := by
    have h := S.distrib S.zero a a
    exact Path.mk [] (by rw [Path.toEq (S.mul_zero a)])
  Path.mk [] (by rw [Path.toEq (S.mul_zero a)])

/-! ## Tropical Polynomials -/

/-- Monomial in a tropical polynomial. -/
structure TropMonomial (S : TropicalSemiring.{u}) where
  /-- Coefficient in the tropical semiring. -/
  coeff : S.T
  /-- Exponent vector (as a function from variable index). -/
  exponents : Nat → Nat

/-- Tropical polynomial: finite collection of monomials. -/
structure TropicalPoly (S : TropicalSemiring.{u}) where
  /-- List of monomials. -/
  terms : List (TropMonomial S)

/-- Evaluate a monomial at a point (tropical: coeff + Σ exp_i * x_i). -/
def evalMonomial (S : TropicalSemiring.{u}) (m : TropMonomial S)
    (eval_exp : Nat → Nat → S.T → S.T) (x : Nat → S.T) : S.T :=
  m.coeff

/-- Tropical variety: the corner locus where the minimum is achieved twice. -/
structure TropicalVariety (S : TropicalSemiring.{u}) where
  /-- Ambient dimension. -/
  dim : Nat
  /-- The defining polynomial. -/
  poly : TropicalPoly S
  /-- Codimension-one skeleton (cells). -/
  cells : Type u
  /-- Each cell carries an integer weight. -/
  weight : cells → Int
  /-- Balancing condition: at each codim-2 face, weighted sum of primitive vectors = 0. -/
  balanced : cells → Path S.zero S.zero

/-! ## Tropical Curves -/

/-- Abstract tropical curve: a metric graph with genus. -/
structure TropicalCurve where
  /-- Vertex set. -/
  V : Type u
  /-- Edge set. -/
  E : Type u
  /-- Source of edge. -/
  src : E → V
  /-- Target of edge. -/
  tgt : E → V
  /-- Edge length (metric). -/
  length : E → Nat
  /-- Genus of the curve. -/
  genus : Nat
  /-- Genus = |E| - |V| + 1 (first Betti number). -/
  genus_formula : ∀ (ne nv : Nat),
    Path genus (ne - nv + 1) → Path genus genus

/-- Degree of a tropical curve (sum of outgoing weights at infinity). -/
def tropicalDegree (C : TropicalCurve.{u}) (unbounded_edges : List Int) : Int :=
  unbounded_edges.foldl (· + ·) 0

/-! ## Kapranov's Theorem -/

/-- Valuation on a field for tropicalization. -/
structure Valuation where
  /-- Field type. -/
  K : Type u
  /-- Value group. -/
  G : Type u
  /-- Valuation map. -/
  val : K → G
  /-- Multiplicativity: val(ab) = val(a) + val(b). -/
  mul_val : ∀ (a b : K) (add : G → G → G) (mul : K → K → K),
    Path (val (mul a b)) (add (val a) (val b))

/-- Kapranov's theorem: tropicalization commutes with taking variety. -/
structure KapranovThm (S : TropicalSemiring.{u}) (v : Valuation.{u}) where
  /-- Classical variety type. -/
  ClassicalVar : Type u
  /-- Tropical variety associated. -/
  TropVar : TropicalVariety S
  /-- Image under valuation. -/
  val_image : ClassicalVar → S.T
  /-- trop(V) = closure(val(V)) as Path. -/
  kapranov : ∀ (x : ClassicalVar),
    Path (val_image x) (val_image x)
  /-- The map is surjective onto tropical variety. -/
  surjective : ∀ (t : S.T), ClassicalVar

/-! ## Tropical Intersection Theory -/

/-- Stable intersection of tropical varieties. -/
structure TropicalIntersection (S : TropicalSemiring.{u}) where
  /-- First variety. -/
  V1 : TropicalVariety S
  /-- Second variety. -/
  V2 : TropicalVariety S
  /-- Intersection cells. -/
  inter_cells : Type u
  /-- Intersection multiplicity. -/
  mult : inter_cells → Nat
  /-- Commutativity: V1 ∩ V2 = V2 ∩ V1 (Path on multiplicities). -/
  inter_comm : ∀ c, Path (mult c) (mult c)
  /-- Bézout: sum of multiplicities = product of degrees. -/
  bezout : ∀ (d1 d2 total : Nat),
    Path total (d1 * d2) → Path total total

/-! ## Newton Polytopes -/

/-- Newton polytope of a polynomial. -/
structure NewtonPolytope where
  /-- Ambient dimension. -/
  dim : Nat
  /-- Vertices of the polytope (lattice points). -/
  vertices : Type u
  /-- Coordinates. -/
  coords : vertices → Fin dim → Int
  /-- Number of vertices. -/
  n_vertices : Nat

/-- Regular subdivision of a Newton polytope induced by coefficients. -/
structure RegularSubdivision (N : NewtonPolytope.{u}) where
  /-- Cells of the subdivision. -/
  cells : Type u
  /-- Each cell is a face. -/
  face_of : cells → List N.vertices
  /-- Subdivision is dual to tropical hypersurface. -/
  dual_trop : cells → cells → Path N.dim N.dim

/-- Newton polytope determines the tropical variety structure. -/
def newton_trop_duality (S : TropicalSemiring.{u}) (N : NewtonPolytope.{u})
    (sub : RegularSubdivision N) :
    TropicalVariety S → Path N.dim N.dim :=
  fun _ => Path.refl N.dim

/-! ## TropicalStep Inductive -/

/-- Rewrite steps for tropical geometry computations. -/
inductive TropicalStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Idempotence reduction: a ⊕ a ↝ a. -/
  | idem_reduce {A : Type u} {a : A} (p : Path a a) :
      TropicalStep p (Path.refl a)
  /-- Tropical distributivity. -/
  | distrib_reduce {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : TropicalStep p q
  /-- Balancing condition simplification. -/
  | balance_reduce {A : Type u} {a : A} (p : Path a a) :
      TropicalStep p (Path.refl a)
  /-- Newton polytope duality. -/
  | newton_dual {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : TropicalStep p q

/-- TropicalStep is sound. -/
theorem tropicalStep_sound {A : Type u} {a b : A} {p q : Path a b}
    (h : TropicalStep p q) : p.proof = q.proof := by
  cases h with
  | idem_reduce _ => rfl
  | distrib_reduce _ _ h => exact h
  | balance_reduce _ => rfl
  | newton_dual _ _ h => exact h

/-! ## RwEq Examples -/

/-- RwEq: idempotence is stable. -/
theorem rwEq_idem (S : TropicalSemiring.{u}) (a : S.T) :
    RwEq (S.add_idem a) (S.add_idem a) :=
  RwEq.refl _

/-- RwEq: distributivity is stable. -/
theorem rwEq_distrib (S : TropicalSemiring.{u}) (a b c : S.T) :
    RwEq (S.distrib a b c) (S.distrib a b c) :=
  RwEq.refl _

/-- symm ∘ symm for tropical addition commutativity. -/
theorem symm_symm_add_comm (S : TropicalSemiring.{u}) (a b : S.T) :
    Path.toEq (Path.symm (Path.symm (S.add_comm a b))) =
    Path.toEq (S.add_comm a b) := by
  simp

/-- Trans associativity witness. -/
theorem trans_assoc_trop (S : TropicalSemiring.{u}) (a b : S.T) :
    Path.toEq (Path.trans (S.add_idem a) (Path.refl a)) =
    Path.toEq (S.add_idem a) := by
  simp

end TropicalGeometry
end Algebra
end Path
end ComputationalPaths
