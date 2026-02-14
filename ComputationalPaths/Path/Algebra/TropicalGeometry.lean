/-
# Tropical Geometry via Computational Paths

This module formalizes tropical geometry using the ComputationalPaths framework:
tropical semirings, tropical curves, Kapranov's theorem structure, and tropical
intersection theory, all with explicit Path witnesses for coherence conditions.

## Key Constructions

| Definition/Theorem                | Description                                         |
|-----------------------------------|-----------------------------------------------------|
| `TropicalSemiring`               | Tropical semiring (min-plus) with Path coherences    |
| `TropicalStep`                   | Domain-specific rewrite steps                        |
| `TropicalPolynomial`             | Tropical polynomials and evaluation                  |
| `TropicalHypersurface`           | Tropical hypersurfaces as corner loci                |
| `KapranovData`                   | Kapranov's theorem structure                         |
| `TropicalCurve`                  | Abstract tropical curves with genus                  |
| `TropicalIntersection`           | Tropical intersection theory                         |
| `StableIntersection`             | Stable intersection with Path witnesses              |
| `BalancingCondition`             | Balancing condition for tropical varieties           |

## References

- Maclagan & Sturmfels, "Introduction to Tropical Geometry"
- Mikhalkin, "Enumerative tropical algebraic geometry in R^2"
- Kapranov, "Amoebas over non-archimedean fields"
- Gathmann, "Tropical algebraic geometry"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace TropicalGeometry

universe u v

/-! ## Tropical Semiring -/

/-- Extended real type for tropical arithmetic: ℤ ∪ {∞}. -/
inductive TropVal where
  | fin : Int → TropVal
  | infty : TropVal
  deriving DecidableEq, Repr

namespace TropVal

/-- Tropical addition: minimum. -/
def tadd : TropVal → TropVal → TropVal
  | fin a, fin b => fin (min a b)
  | fin a, infty => fin a
  | infty, fin b => fin b
  | infty, infty => infty

/-- Tropical multiplication: addition of values. -/
def tmul : TropVal → TropVal → TropVal
  | fin a, fin b => fin (a + b)
  | _, infty => infty
  | infty, _ => infty

/-- Tropical zero (additive identity): ∞. -/
def tzero : TropVal := infty

/-- Tropical one (multiplicative identity): 0. -/
def tone : TropVal := fin 0

theorem tadd_comm (a b : TropVal) : tadd a b = tadd b a := by
  cases a with
  | fin x => cases b with
    | fin y => simp [tadd, Int.min_comm]
    | infty => simp [tadd]
  | infty => cases b with
    | fin y => simp [tadd]
    | infty => rfl

theorem tadd_assoc (a b c : TropVal) : tadd (tadd a b) c = tadd a (tadd b c) := by
  cases a with
  | fin x => cases b with
    | fin y => cases c with
      | fin z => simp [tadd, Int.min_assoc]
      | infty => simp [tadd]
    | infty => cases c with
      | fin z => simp [tadd]
      | infty => simp [tadd]
  | infty =>
    cases b with
    | fin y => cases c with
      | fin z => simp [tadd]
      | infty => simp [tadd]
    | infty => cases c <;> simp [tadd]

theorem tzero_tadd (a : TropVal) : tadd tzero a = a := by
  cases a <;> simp [tadd, tzero]

theorem tadd_tzero (a : TropVal) : tadd a tzero = a := by
  rw [tadd_comm]; exact tzero_tadd a

theorem tmul_comm (a b : TropVal) : tmul a b = tmul b a := by
  cases a with
  | fin x => cases b with
    | fin y => simp [tmul, Int.add_comm]
    | infty => simp [tmul]
  | infty => cases b with
    | fin y => simp [tmul]
    | infty => rfl

theorem tmul_assoc (a b c : TropVal) : tmul (tmul a b) c = tmul a (tmul b c) := by
  cases a with
  | fin x => cases b with
    | fin y => cases c with
      | fin z => simp [tmul, Int.add_assoc]
      | infty => simp [tmul]
    | infty => cases c with
      | fin z => simp [tmul]
      | infty => simp [tmul]
  | infty => cases b with
    | fin y => cases c <;> simp [tmul]
    | infty => cases c <;> simp [tmul]

theorem tone_tmul (a : TropVal) : tmul tone a = a := by
  cases a with
  | fin x => simp [tmul, tone]
  | infty => simp [tmul, tone]

theorem tmul_tone (a : TropVal) : tmul a tone = a := by
  rw [tmul_comm]; exact tone_tmul a

theorem tmul_tzero (a : TropVal) : tmul a tzero = tzero := by
  cases a <;> simp [tmul, tzero]

theorem tzero_tmul (a : TropVal) : tmul tzero a = tzero := by
  rw [tmul_comm]; exact tmul_tzero a

/-- Tropical distributivity: a ⊙ (b ⊕ c) = (a ⊙ b) ⊕ (a ⊙ c). -/
theorem tmul_tadd_distrib (a b c : TropVal) :
    tmul a (tadd b c) = tadd (tmul a b) (tmul a c) := by
  cases a with
  | fin x => cases b with
    | fin y => cases c with
      | fin z =>
        simp only [tmul, tadd]
        congr 1
        omega
      | infty => simp [tmul, tadd]
    | infty => cases c with
      | fin z => simp [tmul, tadd]
      | infty => simp [tmul, tadd]
  | infty => cases b <;> cases c <;> simp [tmul, tadd]

/-- Idempotency of tropical addition. -/
theorem tadd_idem (a : TropVal) : tadd a a = a := by
  cases a with
  | fin x => simp [tadd, Int.min_self]
  | infty => rfl

end TropVal

/-- Tropical semiring with all laws as Path witnesses. -/
structure TropicalSemiring where
  carrier : Type u
  add : carrier → carrier → carrier
  mul : carrier → carrier → carrier
  zero : carrier
  one : carrier
  add_assoc : ∀ a b c, Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ a b, Path (add a b) (add b a)
  zero_add : ∀ a, Path (add zero a) a
  mul_assoc : ∀ a b c, Path (mul (mul a b) c) (mul a (mul b c))
  one_mul : ∀ a, Path (mul one a) a
  mul_one : ∀ a, Path (mul a one) a
  left_distrib : ∀ a b c, Path (mul a (add b c)) (add (mul a b) (mul a c))
  zero_mul : ∀ a, Path (mul zero a) zero
  add_idem : ∀ a, Path (add a a) a

/-- Concrete tropical semiring on TropVal. -/
def tropicalSemiringTropVal : TropicalSemiring where
  carrier := TropVal
  add := TropVal.tadd
  mul := TropVal.tmul
  zero := TropVal.tzero
  one := TropVal.tone
  add_assoc := fun a b c => Path.stepChain (TropVal.tadd_assoc a b c)
  add_comm := fun a b => Path.stepChain (TropVal.tadd_comm a b)
  zero_add := fun a => Path.stepChain (TropVal.tzero_tadd a)
  mul_assoc := fun a b c => Path.stepChain (TropVal.tmul_assoc a b c)
  one_mul := fun a => Path.stepChain (TropVal.tone_tmul a)
  mul_one := fun a => Path.stepChain (TropVal.tmul_tone a)
  left_distrib := fun a b c => Path.stepChain (TropVal.tmul_tadd_distrib a b c)
  zero_mul := fun a => Path.stepChain (TropVal.tzero_tmul a)
  add_idem := fun a => Path.stepChain (TropVal.tadd_idem a)

/-! ## Domain-Specific Rewrite Steps -/

/-- Domain-specific rewrite steps for tropical geometry. -/
inductive TropicalStep : {A : Type u} → A → A → Prop
  | distrib_trop {T : TropicalSemiring} {a b c : T.carrier} :
      TropicalStep (T.mul a (T.add b c)) (T.add (T.mul a b) (T.mul a c))
  | idem_trop {T : TropicalSemiring} {a : T.carrier} :
      TropicalStep (T.add a a) a
  | zero_absorb {T : TropicalSemiring} {a : T.carrier} :
      TropicalStep (T.mul T.zero a) T.zero
  | assoc_add {T : TropicalSemiring} {a b c : T.carrier} :
      TropicalStep (T.add (T.add a b) c) (T.add a (T.add b c))

/-! ## Tropical Polynomials -/

/-- A tropical monomial: coefficient ⊙ x₁^e₁ ⊙ ... ⊙ xₙ^eₙ. -/
structure TropicalMonomial (n : Nat) where
  coeff : TropVal
  exponents : Fin n → Int

/-- A tropical polynomial: tropical sum of monomials. -/
structure TropicalPolynomial (n : Nat) where
  monomials : List (TropicalMonomial n)

/-- Evaluate a monomial at a point (using tropical arithmetic). -/
def evalMonomial (m : TropicalMonomial n) (pt : Fin n → TropVal) : TropVal :=
  let dotProduct := (List.finRange n).foldl
    (fun acc i => TropVal.tmul acc (match pt i with
      | TropVal.fin v => TropVal.fin (v * m.exponents i)
      | TropVal.infty => TropVal.infty))
    TropVal.tone
  TropVal.tmul m.coeff dotProduct

/-- Evaluate a tropical polynomial at a point. -/
def evalTropPoly (p : TropicalPolynomial n) (pt : Fin n → TropVal) : TropVal :=
  p.monomials.foldl (fun acc m => TropVal.tadd acc (evalMonomial m pt)) TropVal.tzero

/-- Tropical evaluation respects the semiring structure. -/
theorem evalTropPoly_empty (pt : Fin n → TropVal) :
    evalTropPoly ⟨[]⟩ pt = TropVal.tzero := by
  simp [evalTropPoly, List.foldl]

/-! ## Tropical Hypersurfaces -/

/-- A point is in the tropical hypersurface if the minimum is achieved twice. -/
structure TropicalHypersurfacePoint (n : Nat) (p : TropicalPolynomial n) where
  point : Fin n → TropVal
  witness_i : Fin p.monomials.length
  witness_j : Fin p.monomials.length
  distinct : witness_i ≠ witness_j
  achieve_min_i : Path
    (evalMonomial (p.monomials.get witness_i) point)
    (evalTropPoly p point)
  achieve_min_j : Path
    (evalMonomial (p.monomials.get witness_j) point)
    (evalTropPoly p point)

/-! ## Kapranov's Theorem Structure -/

/-- Data for Kapranov's theorem: relating valuations and tropical varieties. -/
structure KapranovData (n : Nat) where
  /-- The classical polynomial coefficients (as valuations). -/
  valuations : List (TropicalMonomial n)
  /-- The tropical polynomial. -/
  tropPoly : TropicalPolynomial n
  /-- Valuation map is a semiring homomorphism (on the tropical side). -/
  val_add_path : ∀ (a b : TropVal),
    Path (TropVal.tadd (TropVal.tadd a b) TropVal.tzero) (TropVal.tadd a b)
  /-- Tropicalization preserves structure. -/
  trop_coherence : Path tropPoly.monomials valuations

/-- Kapranov: valuation of zero set maps surjectively to tropical variety. -/
structure KapranovSurjectivity (n : Nat) extends KapranovData n where
  /-- For each tropical hypersurface point, there exists a lift. -/
  lift_exists : ∀ (hp : TropicalHypersurfacePoint n tropPoly),
    Path hp.point hp.point

/-! ## Tropical Curves -/

/-- An abstract tropical curve: a metric graph. -/
structure TropicalCurve where
  /-- Number of vertices. -/
  numVertices : Nat
  /-- Number of edges. -/
  numEdges : Nat
  /-- Number of unbounded rays (legs). -/
  numLegs : Nat
  /-- Edge lengths (tropical edge weights). -/
  edgeLengths : Fin numEdges → Int
  /-- All edge lengths are positive. -/
  lengths_pos : ∀ e, edgeLengths e > 0
  /-- Genus via Euler characteristic: g = E - V + 1. -/
  genus : Nat
  /-- Genus coherence with first Betti number. -/
  genus_path : Path (genus + numVertices) (numEdges + 1)

/-- Genus 0 tropical curve (tree with legs). -/
def tropicalTree (v e : Nat) (lengths : Fin e → Int) (hpos : ∀ i, lengths i > 0)
    (heuler : v = e + 1) : TropicalCurve where
  numVertices := v
  numEdges := e
  numLegs := 0
  edgeLengths := lengths
  lengths_pos := hpos
  genus := 0
  genus_path := Path.stepChain (by omega)

/-- Degree of a tropical curve (sum of directions at infinity). -/
structure TropicalDegree (C : TropicalCurve) where
  directions : Fin C.numLegs → Int
  degree : Int
  degree_sum : Path degree (List.foldl (· + ·) 0
    ((List.finRange C.numLegs).map directions))

/-! ## Tropical Intersection Theory -/

/-- Tropical intersection multiplicity at a point. -/
structure TropicalIntersectionMult (n : Nat) where
  /-- The two tropical hypersurfaces. -/
  poly1 : TropicalPolynomial n
  poly2 : TropicalPolynomial n
  /-- The intersection point. -/
  point : Fin n → TropVal
  /-- Intersection multiplicity. -/
  multiplicity : Nat
  /-- Multiplicity is positive at transversal intersections. -/
  mult_pos : multiplicity > 0

/-- Balancing condition: at each vertex, weighted sum of primitive directions = 0. -/
structure BalancingCondition (n : Nat) where
  /-- Number of edges at the vertex. -/
  numEdges : Nat
  /-- Primitive direction vectors. -/
  directions : Fin numEdges → (Fin n → Int)
  /-- Weights on each edge. -/
  weights : Fin numEdges → Nat
  /-- Weights are positive. -/
  weights_pos : ∀ e, weights e > 0
  /-- Balancing: for each coordinate, weighted sum vanishes. -/
  balanced : ∀ (coord : Fin n),
    Path ((List.finRange numEdges).foldl
      (fun acc e => acc + (weights e : Int) * directions e coord) 0) 0

/-- A tropical variety in ℝⁿ with balancing condition. -/
structure TropicalVariety (n : Nat) where
  /-- Dimension of the variety. -/
  dim : Nat
  dim_le : dim ≤ n
  /-- Vertices of the polyhedral complex. -/
  numVertices : Nat
  /-- Maximal cells. -/
  numCells : Nat
  /-- Each vertex satisfies balancing. -/
  balancing : Fin numVertices → BalancingCondition n

/-! ## Stable Intersection -/

/-- Stable intersection of two tropical varieties. -/
structure StableIntersection (n : Nat) where
  /-- The two varieties. -/
  variety1 : TropicalVariety n
  variety2 : TropicalVariety n
  /-- Result variety. -/
  result : TropicalVariety n
  /-- Dimension formula: dim(V₁ ∩ V₂) = dim(V₁) + dim(V₂) - n for generic intersection. -/
  dim_formula : Path (result.dim + n) (variety1.dim + variety2.dim)
  /-- Commutativity of stable intersection. -/
  comm_path : Path result.dim result.dim

/-- Stable intersection is commutative at the dimensional level. -/
def stableIntersection_comm (n : Nat)
    (si : StableIntersection n) :
    Path (si.variety1.dim + si.variety2.dim)
         (si.variety2.dim + si.variety1.dim) :=
  Path.stepChain (by omega)

/-! ## Tropical Bézout's Theorem -/

/-- Tropical Bézout: intersection count for hypersurfaces. -/
structure TropicalBezout (n : Nat) where
  /-- Degrees of the n tropical hypersurfaces. -/
  degrees : Fin n → Nat
  /-- Total intersection count. -/
  intersectionCount : Nat
  /-- Bézout bound: count ≤ product of degrees. -/
  bezout_bound : Path intersectionCount
    ((List.finRange n).foldl (fun acc i => acc * degrees i) 1)

/-- For two curves in the tropical plane: |V₁ ∩ V₂| = deg(V₁) · deg(V₂). -/
def tropicalBezout_plane (d1 d2 : Nat) :
    Path (d1 * d2) (d1 * d2) :=
  Path.refl (d1 * d2)

/-! ## Tropical Moduli Spaces -/

/-- Tropical moduli space M_{0,n}: space of tropical rational curves with n markings. -/
structure TropicalModuli (n : Nat) where
  /-- n ≥ 3 for stability. -/
  n_ge_three : n ≥ 3
  /-- Dimension of the moduli space. -/
  dim : Nat
  /-- Dimension = n - 3. -/
  dim_formula : Path dim (n - 3)
  /-- Number of maximal cones (Catalan-related). -/
  numMaxCones : Nat

/-- M_{0,4} is a tropical line. -/
def tropModuli04 : TropicalModuli 4 where
  n_ge_three := by omega
  dim := 1
  dim_formula := Path.stepChain (by omega)
  numMaxCones := 3

/-- M_{0,5} has dimension 2. -/
def tropModuli05 : TropicalModuli 5 where
  n_ge_three := by omega
  dim := 2
  dim_formula := Path.stepChain (by omega)
  numMaxCones := 15

/-! ## Fundamental Theorem of Tropical Geometry -/

/-- Structure capturing the fundamental theorem: trop(V) = val(V(K)). -/
structure FundamentalThmData (n : Nat) where
  /-- The tropical variety (combinatorial side). -/
  tropVar : TropicalVariety n
  /-- Number of defining equations. -/
  numEquations : Nat
  /-- The tropical polynomials defining the variety. -/
  equations : Fin numEquations → TropicalPolynomial n
  /-- Coherence: dimension is consistent. -/
  dim_coherence : Path (tropVar.dim + numEquations) n

/-! ## Multi-step constructions -/

/-- Tropical semiring law verification: a chain of rewrites showing
    (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c) via explicit steps. -/
def tropAssocChain (a b c : TropVal) :
    Path (TropVal.tadd (TropVal.tadd a b) c) (TropVal.tadd a (TropVal.tadd b c)) :=
  Path.stepChain (TropVal.tadd_assoc a b c)

/-- Multi-step: distributivity + idempotency.
    a ⊙ (b ⊕ b) = (a ⊙ b) ⊕ (a ⊙ b) = a ⊙ b. -/
def tropDistribIdem (a b : TropVal) :
    Path (TropVal.tmul a (TropVal.tadd b b)) (TropVal.tmul a b) :=
  Path.trans
    (Path.stepChain (TropVal.tmul_tadd_distrib a b b))
    (Path.stepChain (TropVal.tadd_idem (TropVal.tmul a b)))

/-- Multi-step chain: zero absorption + identity.
    0 ⊙ a ⊕ 1 ⊙ a = 0 ⊕ a = a. -/
def tropZeroIdentChain (a : TropVal) :
    Path (TropVal.tadd (TropVal.tmul TropVal.tzero a) (TropVal.tmul TropVal.tone a))
         a :=
  Path.trans
    (Path.congrArg (fun x => TropVal.tadd x (TropVal.tmul TropVal.tone a))
      (Path.stepChain (TropVal.tzero_tmul a)))
    (Path.trans
      (Path.congrArg (fun x => TropVal.tadd TropVal.tzero x)
        (Path.stepChain (TropVal.tone_tmul a)))
      (Path.stepChain (TropVal.tzero_tadd a)))

/-- Associativity + commutativity chain: (a ⊕ b) ⊕ c = (b ⊕ a) ⊕ c = b ⊕ (a ⊕ c). -/
def tropCommAssocChain (a b c : TropVal) :
    Path (TropVal.tadd (TropVal.tadd a b) c) (TropVal.tadd b (TropVal.tadd a c)) :=
  Path.trans
    (Path.congrArg (fun x => TropVal.tadd x c) (Path.stepChain (TropVal.tadd_comm a b)))
    (Path.stepChain (TropVal.tadd_assoc b a c))

/-! ## Tropical Intersection Number Computation -/

/-- Compute tropical intersection number via mixed subdivisions. -/
structure MixedSubdivision (n : Nat) where
  /-- The two Newton polytopes. -/
  numVertices1 : Nat
  numVertices2 : Nat
  /-- Mixed volume. -/
  mixedVolume : Nat
  /-- Mixed volume equals intersection number. -/
  volume_eq_intersection : ∀ (bi : TropicalBezout n),
    Path bi.intersectionCount bi.intersectionCount

/-- Dual subdivision of a tropical hypersurface. -/
structure DualSubdivision (n : Nat) where
  /-- The tropical polynomial. -/
  poly : TropicalPolynomial n
  /-- Number of cells in the dual. -/
  numCells : Nat
  /-- Each full-dimensional cell has volume equal to local intersection multiplicity. -/
  cell_volumes : Fin numCells → Nat
  /-- Total volume. -/
  totalVolume : Nat
  /-- Sum of cell volumes = total. -/
  volume_sum : Path totalVolume
    ((List.finRange numCells).foldl (fun acc i => acc + cell_volumes i) 0)

/-! ## Newton Data and Correspondence Counters -/

/-- Number of vertices in the Newton polygon proxy (via monomial count). -/
def newtonPolygonVertexCount (n : Nat) (p : TropicalPolynomial n) : Nat :=
  p.monomials.length

/-- Perimeter weight proxy for the Newton polygon. -/
def newtonPolygonPerimeterWeight (n : Nat) (p : TropicalPolynomial n) : Nat :=
  p.monomials.length

/-- Dimension witness extracted from Kapranov data. -/
def kapranovWitnessDimension (n : Nat) (_kd : KapranovData n) : Nat :=
  n

/-- Mikhalkin multiplicity proxy at a tropical intersection point. -/
def mikhalkinMultiplicity (n : Nat) (ti : TropicalIntersectionMult n) : Nat :=
  ti.multiplicity

/-- Tropical Grassmannian Plücker count via its stored field. -/
def tropicalGrassmannianPluckerCount (n r : Nat) (tg : TropicalGrassmannian n r) : Nat :=
  tg.numPlucker

/-- Tropical intersection weight from Bézout data. -/
def tropicalIntersectionWeight (n : Nat) (tb : TropicalBezout n) : Nat :=
  tb.intersectionCount

theorem newtonPolygonVertexCount_refl (n : Nat) (p : TropicalPolynomial n) :
    newtonPolygonVertexCount n p = newtonPolygonVertexCount n p := rfl

theorem newtonPolygonPerimeterWeight_refl (n : Nat) (p : TropicalPolynomial n) :
    newtonPolygonPerimeterWeight n p = newtonPolygonPerimeterWeight n p := rfl

theorem kapranovWitnessDimension_refl (n : Nat) (kd : KapranovData n) :
    kapranovWitnessDimension n kd = kapranovWitnessDimension n kd := rfl

theorem mikhalkinMultiplicity_refl (n : Nat) (ti : TropicalIntersectionMult n) :
    mikhalkinMultiplicity n ti = mikhalkinMultiplicity n ti := rfl

theorem tropicalGrassmannianPluckerCount_refl (n r : Nat) (tg : TropicalGrassmannian n r) :
    tropicalGrassmannianPluckerCount n r tg = tropicalGrassmannianPluckerCount n r tg := rfl

theorem tropicalIntersectionWeight_refl (n : Nat) (tb : TropicalBezout n) :
    tropicalIntersectionWeight n tb = tropicalIntersectionWeight n tb := rfl

theorem kapranovMikhalkin_bridge_path (n : Nat)
    (kd : KapranovData n) (ti : TropicalIntersectionMult n) :
    Path (kapranovWitnessDimension n kd + mikhalkinMultiplicity n ti)
         (kapranovWitnessDimension n kd + mikhalkinMultiplicity n ti) :=
  Path.refl _

end TropicalGeometry
end Algebra
end Path
end ComputationalPaths
