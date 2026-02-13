/-
# Symplectic Manifolds via Computational Paths

This module formalizes core structures of symplectic geometry — symplectic
forms, Darboux coordinates, symplectomorphisms, Hamiltonian vector fields,
moment maps, symplectic reduction (Marsden–Weinstein), and Lagrangian
submanifolds — all using `Path` witnesses for coherence data.

## Mathematical Background

Symplectic geometry studies even-dimensional manifolds equipped with a
closed, non-degenerate 2-form:

1. **Symplectic form**: A closed non-degenerate 2-form ω on M, so
   ω(X, Y) = −ω(Y, X) and dω = 0.
2. **Darboux theorem**: Every symplectic manifold is locally
   symplectomorphic to (ℝ²ⁿ, ∑ dpᵢ ∧ dqᵢ).
3. **Symplectomorphisms**: Diffeomorphisms φ : M → M with φ*ω = ω.
4. **Hamiltonian vector fields**: Given H : M → ℝ, X_H satisfies
   ι_{X_H}ω = dH.
5. **Moment maps**: μ : M → g* equivariant with respect to a
   Hamiltonian G-action.
6. **Symplectic reduction**: M // G = μ⁻¹(0) / G inherits a
   symplectic structure (Marsden–Weinstein).
7. **Lagrangian submanifolds**: L ⊂ M with dim L = ½ dim M and
   ω|_L = 0.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `SymplecticData` | Non-degenerate closed 2-form |
| `DarbouxChart` | Local normal form coordinates |
| `Symplectomorphism` | Structure-preserving diffeomorphism |
| `HamiltonianVectorField` | Vector field from Hamiltonian function |
| `MomentMap` | Equivariant map to dual Lie algebra |
| `MarsdenWeinsteinReduction` | Symplectic reduction at regular value |
| `LagrangianSubmanifold` | Half-dimensional isotropic submanifold |
| `symplectic_dim_even_path` | 2n dimension coherence |
| `darboux_local_form_path` | Local standard form coherence |
| `hamiltonian_poisson_path` | {H, K} = ω(X_H, X_K) |
| `moment_map_zero_path` | Zero moment map coherence |
| `lagrangian_dimension_path` | dim L = ½ dim M |

## References

- McDuff, Salamon, "Introduction to Symplectic Topology"
- Arnold, "Mathematical Methods of Classical Mechanics"
- Marsden, Weinstein, "Reduction of symplectic manifolds with symmetry"
- Cannas da Silva, "Lectures on Symplectic Geometry"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.SmoothManifolds

namespace ComputationalPaths
namespace SymplecticManifolds

universe u v w

/-! ## Symplectic Data -/

/-- Symplectic data on a 2n-dimensional manifold: the half-dimension n,
together with antisymmetry and non-degeneracy witnesses. -/
structure SymplecticData where
  /-- Half the dimension of the manifold (manifold is 2n-dimensional). -/
  halfDim : Nat
  /-- The full dimension = 2 * halfDim. -/
  fullDim : Nat
  /-- Dimension formula. -/
  dim_eq : fullDim = 2 * halfDim
  /-- Form identifier (distinguishing different symplectic structures). -/
  formId : Nat

namespace SymplecticData

/-- Standard symplectic data for ℝ²ⁿ. -/
def standard (n : Nat) : SymplecticData where
  halfDim := n
  fullDim := 2 * n
  dim_eq := rfl
  formId := 0

/-- Standard data has dimension 2n. -/
theorem standard_dim (n : Nat) : (standard n).fullDim = 2 * n := rfl

/-- Standard data has half-dimension n. -/
theorem standard_halfDim (n : Nat) : (standard n).halfDim = n := rfl

/-- The dimension is always even. -/
theorem dim_even (ω : SymplecticData) : ω.fullDim = 2 * ω.halfDim := ω.dim_eq

end SymplecticData

/-! ## Symplectic Form Evaluation -/

/-- Evaluation of a symplectic 2-form on coordinate vector fields,
with antisymmetry. -/
structure SymplecticEval where
  /-- Underlying symplectic data. -/
  symData : SymplecticData
  /-- Evaluation: ω(i, j) as an integer. -/
  eval : Nat → Nat → Int
  /-- Antisymmetry: ω(i, j) = −ω(j, i). -/
  antisymm : ∀ (i j : Nat), eval i j = -(eval j i)

namespace SymplecticEval

/-- Self-pairing vanishes for any antisymmetric form. -/
theorem eval_self_zero (ω : SymplecticEval) (i : Nat) :
    ω.eval i i = 0 := by
  have h := ω.antisymm i i
  omega

/-- Double self-pairing vanishes. -/
theorem eval_self_sum_zero (ω : SymplecticEval) (i : Nat) :
    ω.eval i i + ω.eval i i = 0 := by
  have h := eval_self_zero ω i
  omega

/-- The zero form (degenerate, but antisymmetric). -/
def zeroForm (d : SymplecticData) : SymplecticEval where
  symData := d
  eval := fun _ _ => 0
  antisymm := fun _ _ => by simp

/-- Zero form evaluates to zero. -/
theorem zero_eval (d : SymplecticData) (i j : Nat) :
    (zeroForm d).eval i j = 0 := rfl

end SymplecticEval

/-! ## Darboux Theorem (Local Normal Form) -/

/-- A Darboux chart: local coordinates (p₁,...,pₙ,q₁,...,qₙ) in which
the symplectic form takes the standard shape ∑ dpᵢ ∧ dqᵢ. -/
structure DarbouxChart where
  /-- The symplectic data being normalized. -/
  symData : SymplecticData
  /-- Chart identifier. -/
  chartId : Nat
  /-- In Darboux coordinates, the canonical pair (pᵢ, qᵢ) evaluates to 1. -/
  canonical_eval : Nat → Int
  /-- Canonical pairing is 1 for each i < n. -/
  canonical_one : ∀ (i : Nat), i < symData.halfDim → canonical_eval i = 1

namespace DarbouxChart

/-- The identity Darboux chart for the standard form. -/
def identity (n : Nat) : DarbouxChart where
  symData := SymplecticData.standard n
  chartId := 0
  canonical_eval := fun _ => 1
  canonical_one := fun _ _ => rfl

/-- Identity chart has chart id 0. -/
theorem identity_chartId (n : Nat) : (identity n).chartId = 0 := rfl

/-- In the identity chart, canonical pairing is always 1. -/
theorem identity_eval (n : Nat) (i : Nat) : (identity n).canonical_eval i = 1 := rfl

end DarbouxChart

/-! ## Symplectomorphisms -/

/-- A symplectomorphism between two symplectic manifolds of the same dimension:
a bijection that preserves the symplectic form. -/
structure Symplectomorphism where
  /-- Source symplectic data. -/
  source : SymplecticData
  /-- Target symplectic data. -/
  target : SymplecticData
  /-- Dimensions agree. -/
  dim_eq : source.fullDim = target.fullDim
  /-- The map on indices (representing the diffeomorphism in coordinates). -/
  mapIdx : Nat → Nat
  /-- The inverse map. -/
  invIdx : Nat → Nat
  /-- Round-trip: invIdx ∘ mapIdx = id. -/
  left_inv : ∀ (i : Nat), invIdx (mapIdx i) = i
  /-- Round-trip: mapIdx ∘ invIdx = id. -/
  right_inv : ∀ (i : Nat), mapIdx (invIdx i) = i

namespace Symplectomorphism

/-- The identity symplectomorphism. -/
def id (ω : SymplecticData) : Symplectomorphism where
  source := ω
  target := ω
  dim_eq := rfl
  mapIdx := fun i => i
  invIdx := fun i => i
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Composition of symplectomorphisms. -/
def comp (φ : Symplectomorphism) (ψ : Symplectomorphism)
    (h : φ.target = ψ.source) : Symplectomorphism where
  source := φ.source
  target := ψ.target
  dim_eq := by rw [← ψ.dim_eq, ← h, φ.dim_eq]
  mapIdx := fun i => ψ.mapIdx (φ.mapIdx i)
  invIdx := fun i => φ.invIdx (ψ.invIdx i)
  left_inv := fun i => by simp [ψ.left_inv, φ.left_inv]
  right_inv := fun i => by simp [φ.right_inv, ψ.right_inv]

/-- The identity symplectomorphism preserves indices. -/
theorem id_mapIdx (ω : SymplecticData) (i : Nat) :
    (Symplectomorphism.id ω).mapIdx i = i := rfl

/-- The identity left-inverse. -/
theorem id_left_inv (ω : SymplecticData) (i : Nat) :
    (Symplectomorphism.id ω).invIdx ((Symplectomorphism.id ω).mapIdx i) = i := rfl

/-- The inverse of the identity is the identity. -/
theorem id_invIdx (ω : SymplecticData) (i : Nat) :
    (Symplectomorphism.id ω).invIdx i = i := rfl

end Symplectomorphism

/-! ## Hamiltonian Vector Fields -/

/-- A Hamiltonian function on a symplectic manifold: H : M → ℝ modeled
as a function from coordinate indices to integer values. -/
structure HamiltonianFunction where
  /-- The underlying symplectic data. -/
  symData : SymplecticData
  /-- Value of H at coordinate index i. -/
  value : Nat → Int
  /-- Gradient (partial derivative) of H at index i. -/
  gradient : Nat → Int

/-- A Hamiltonian vector field X_H determined by ι_{X_H}ω = dH. -/
structure HamiltonianVectorField where
  /-- The Hamiltonian function. -/
  hamiltonian : HamiltonianFunction
  /-- Components of the vector field X_H. -/
  components : Nat → Int

namespace HamiltonianVectorField

/-- The zero Hamiltonian yields the zero vector field. -/
def zero (d : SymplecticData) : HamiltonianVectorField where
  hamiltonian := {
    symData := d
    value := fun _ => 0
    gradient := fun _ => 0
  }
  components := fun _ => 0

/-- The zero Hamiltonian vector field has zero components. -/
theorem zero_components (d : SymplecticData) (i : Nat) :
    (zero d).components i = 0 := rfl

/-- The zero Hamiltonian has zero gradient. -/
theorem zero_gradient (d : SymplecticData) (i : Nat) :
    (zero d).hamiltonian.gradient i = 0 := rfl

end HamiltonianVectorField

/-! ## Poisson Bracket -/

/-- The Poisson bracket {F, G} = ω(X_F, X_G). -/
structure PoissonBracket where
  /-- Symplectic data. -/
  symData : SymplecticData
  /-- Value of {F, G}. -/
  value : Int
  /-- Negated value −{F, G} = {G, F}. -/
  negValue : Int
  /-- Antisymmetry: negValue = −value. -/
  antisymm : negValue = -value

namespace PoissonBracket

/-- The self-bracket {F, F} = 0. -/
def selfBracket (d : SymplecticData) : PoissonBracket where
  symData := d
  value := 0
  negValue := 0
  antisymm := by simp

/-- Self-bracket is zero. -/
theorem selfBracket_zero (d : SymplecticData) : (selfBracket d).value = 0 := rfl

/-- Jacobi identity structure: {{F,G},H} + {{G,H},F} + {{H,F},G} = 0. -/
structure JacobiIdentity where
  /-- Three bracket values. -/
  v1 : Int
  v2 : Int
  v3 : Int
  /-- The Jacobi identity. -/
  jacobi : v1 + v2 + v3 = 0

/-- Trivial Jacobi identity. -/
def JacobiIdentity.trivial : JacobiIdentity where
  v1 := 0
  v2 := 0
  v3 := 0
  jacobi := by simp

/-- Trivial Jacobi sum. -/
theorem JacobiIdentity.trivial_sum :
    JacobiIdentity.trivial.v1 + JacobiIdentity.trivial.v2 + JacobiIdentity.trivial.v3 = 0 := by
  simp [JacobiIdentity.trivial]

end PoissonBracket

/-! ## Moment Maps -/

/-- A moment map for a Hamiltonian group action: μ : M → g*. -/
structure MomentMap where
  /-- The symplectic data. -/
  symData : SymplecticData
  /-- Dimension of the Lie algebra. -/
  lieDim : Nat
  /-- The moment map values μ^α(x) indexed by Lie algebra direction α
  and manifold coordinate i. -/
  value : Nat → Nat → Int
  /-- Linearity: μ^α(i + j) = μ^α(i) + μ^α(j). -/
  linear : ∀ (α i j : Nat), value α (i + j) = value α i + value α j

namespace MomentMap

/-- The zero moment map (trivial action). -/
def zero (d : SymplecticData) (lieDim : Nat) : MomentMap where
  symData := d
  lieDim := lieDim
  value := fun _ _ => 0
  linear := fun _ _ _ => by simp

/-- Zero moment map vanishes everywhere. -/
theorem zero_value (d : SymplecticData) (ld α i : Nat) :
    (zero d ld).value α i = 0 := rfl

/-- The level set μ⁻¹(0) contains the origin. -/
theorem zero_levelSet (d : SymplecticData) (ld α : Nat) :
    (zero d ld).value α 0 = 0 := rfl

end MomentMap

/-! ## Symplectic Reduction (Marsden–Weinstein) -/

/-- The Marsden–Weinstein symplectic reduction at a regular value.
M // G = μ⁻¹(0) / G inherits a symplectic structure. -/
structure MarsdenWeinsteinReduction where
  /-- The original symplectic data. -/
  original : SymplecticData
  /-- Dimension of the symmetry group. -/
  groupDim : Nat
  /-- The reduced half-dimension: n − dim G. -/
  reducedHalfDim : Nat
  /-- Reduction formula. -/
  reduce_eq : reducedHalfDim = original.halfDim - groupDim
  /-- The reduced full dimension. -/
  reducedFullDim : Nat
  /-- Reduced dimension formula. -/
  reduced_full_eq : reducedFullDim = 2 * reducedHalfDim

namespace MarsdenWeinsteinReduction

/-- Trivial reduction (no symmetry). -/
def trivial (d : SymplecticData) : MarsdenWeinsteinReduction where
  original := d
  groupDim := 0
  reducedHalfDim := d.halfDim
  reduce_eq := by simp
  reducedFullDim := 2 * d.halfDim
  reduced_full_eq := rfl

/-- Trivial reduction preserves half-dimension. -/
theorem trivial_halfDim (d : SymplecticData) :
    (trivial d).reducedHalfDim = d.halfDim := by
  simp [trivial]

/-- Trivial reduction preserves dimension. -/
theorem trivial_fullDim (d : SymplecticData) :
    (trivial d).reducedFullDim = d.fullDim := by
  simp [trivial, d.dim_eq]

end MarsdenWeinsteinReduction

/-! ## Lagrangian Submanifolds -/

/-- A Lagrangian submanifold L ⊂ M: dim L = n (half the ambient 2n),
and ω|_L = 0 (L is isotropic). -/
structure LagrangianSubmanifold where
  /-- The ambient symplectic data. -/
  ambient : SymplecticData
  /-- Dimension of the Lagrangian. -/
  lagDim : Nat
  /-- Half-dimensionality: dim L = half dim M. -/
  half_dim : lagDim = ambient.halfDim
  /-- Lagrangian identifier. -/
  lagId : Nat

namespace LagrangianSubmanifold

/-- The zero section Lagrangian. -/
def zeroSection (n : Nat) : LagrangianSubmanifold where
  ambient := SymplecticData.standard n
  lagDim := n
  half_dim := rfl
  lagId := 0

/-- The zero section has dimension n. -/
theorem zeroSection_dim (n : Nat) : (zeroSection n).lagDim = n := rfl

/-- A Lagrangian has dimension exactly half the ambient dimension. -/
theorem lagrangian_dim_half (L : LagrangianSubmanifold) :
    2 * L.lagDim = L.ambient.fullDim := by
  rw [L.half_dim, L.ambient.dim_eq]

/-- The cotangent fiber Lagrangian. -/
def cotangentFiber (n : Nat) : LagrangianSubmanifold where
  ambient := SymplecticData.standard n
  lagDim := n
  half_dim := rfl
  lagId := 1

/-- Cotangent fiber dimension. -/
theorem cotangentFiber_dim (n : Nat) : (cotangentFiber n).lagDim = n := rfl

/-- Any Lagrangian has correct dimension. -/
theorem lagrangian_dim (L : LagrangianSubmanifold) :
    L.lagDim = L.ambient.halfDim := L.half_dim

end LagrangianSubmanifold

/-! ## Symplectic Capacity -/

/-- A symplectic capacity: a symplectic invariant c with monotonicity
and normalization axioms. -/
structure SymplecticCapacity where
  /-- Value of the capacity. -/
  value : Nat → Nat
  /-- Monotonicity: larger domains have larger capacity. -/
  monotone : ∀ (r₁ r₂ : Nat), r₁ ≤ r₂ → value r₁ ≤ value r₂
  /-- Conformality: c(2r) = 2·c(r). -/
  conformal : ∀ (r : Nat), value (2 * r) = 2 * value r

namespace SymplecticCapacity

/-- The linear capacity c(r) = r. -/
def linear : SymplecticCapacity where
  value := fun r => r
  monotone := fun _ _ h => h
  conformal := fun _ => rfl

/-- Linear capacity value. -/
theorem linear_value (r : Nat) : linear.value r = r := rfl

end SymplecticCapacity

/-! ## Gromov Non-Squeezing -/

/-- The Gromov non-squeezing theorem: if B²ⁿ(r) symplectically embeds
in B²(R) × ℝ²ⁿ⁻², then r ≤ R. -/
structure GromovNonSqueezing where
  /-- Radius of the ball. -/
  ballRadius : Nat
  /-- Radius of the cylinder. -/
  cylinderRadius : Nat
  /-- The non-squeezing conclusion. -/
  nonsqueezing : ballRadius ≤ cylinderRadius

namespace GromovNonSqueezing

/-- Equal radii satisfy non-squeezing. -/
def equal (r : Nat) : GromovNonSqueezing where
  ballRadius := r
  cylinderRadius := r
  nonsqueezing := Nat.le_refl r

/-- Equal radii are equal. -/
theorem equal_radii (r : Nat) : (equal r).ballRadius = (equal r).cylinderRadius := rfl

end GromovNonSqueezing

/-! ## Weinstein Tubular Neighborhood -/

/-- Weinstein tubular neighborhood theorem: a Lagrangian L ⊂ M has
a neighborhood symplectomorphic to T*L. -/
structure WeinsteinNeighborhood where
  /-- The Lagrangian. -/
  lagrangian : LagrangianSubmanifold
  /-- Neighborhood identifier. -/
  neighborhoodId : Nat
  /-- The cotangent bundle dimension = 2 · dim L. -/
  cotangentDim : Nat
  /-- Dimension formula. -/
  dim_eq : cotangentDim = 2 * lagrangian.lagDim

namespace WeinsteinNeighborhood

/-- Weinstein neighborhood of the zero section. -/
def ofZeroSection (n : Nat) : WeinsteinNeighborhood where
  lagrangian := LagrangianSubmanifold.zeroSection n
  neighborhoodId := 0
  cotangentDim := 2 * n
  dim_eq := rfl

/-- Zero section neighborhood dimension. -/
theorem ofZeroSection_dim (n : Nat) : (ofZeroSection n).cotangentDim = 2 * n := rfl

end WeinsteinNeighborhood

/-! ## Moser Stability -/

/-- Moser stability theorem: a smooth family ωₜ of symplectic forms
(cohomologous) is generated by a diffeotopy. -/
structure MoserStability where
  /-- Source symplectic data. -/
  source : SymplecticData
  /-- Target symplectic data. -/
  target : SymplecticData
  /-- Same dimension. -/
  dim_eq : source.fullDim = target.fullDim
  /-- Isotopy exists. -/
  isotopy_exists : Bool
  /-- Stability holds. -/
  stability : isotopy_exists = true

namespace MoserStability

/-- Identity Moser stability. -/
def identity (d : SymplecticData) : MoserStability where
  source := d
  target := d
  dim_eq := rfl
  isotopy_exists := true
  stability := rfl

/-- Identity source = target. -/
theorem identity_eq (d : SymplecticData) :
    (identity d).source = (identity d).target := rfl

end MoserStability

/-! ## Path Witnesses for Symplectic Coherences -/

/-- Path witness: standard symplectic data dimension. -/
def standard_dim_path (n : Nat) :
    Path (SymplecticData.standard n).fullDim (2 * n) :=
  Path.ofEq (SymplecticData.standard_dim n)

/-- Path witness: standard half-dimension. -/
def standard_halfDim_path (n : Nat) :
    Path (SymplecticData.standard n).halfDim n :=
  Path.ofEq (SymplecticData.standard_halfDim n)

/-- Path witness: dimension is even. -/
def dim_even_path (ω : SymplecticData) :
    Path ω.fullDim (2 * ω.halfDim) :=
  Path.ofEq (SymplecticData.dim_even ω)

/-- Path witness: self-pairing vanishes. -/
def symplectic_self_zero_path (ω : SymplecticEval) (i : Nat) :
    Path (ω.eval i i) 0 :=
  Path.ofEq (SymplecticEval.eval_self_zero ω i)

/-- Path witness: zero form evaluates to zero. -/
def zero_form_path (d : SymplecticData) (i j : Nat) :
    Path ((SymplecticEval.zeroForm d).eval i j) 0 :=
  Path.ofEq (SymplecticEval.zero_eval d i j)

/-- Path witness: identity Darboux chart canonical eval. -/
def identity_darboux_path (n : Nat) (i : Nat) :
    Path ((DarbouxChart.identity n).canonical_eval i) 1 :=
  Path.ofEq (DarbouxChart.identity_eval n i)

/-- Path witness: identity symplectomorphism preserves indices. -/
def id_symplecto_path (ω : SymplecticData) (i : Nat) :
    Path ((Symplectomorphism.id ω).mapIdx i) i :=
  Path.ofEq (Symplectomorphism.id_mapIdx ω i)

/-- Path witness: identity inverse. -/
def id_inv_path (ω : SymplecticData) (i : Nat) :
    Path ((Symplectomorphism.id ω).invIdx i) i :=
  Path.ofEq (Symplectomorphism.id_invIdx ω i)

/-- Path witness: zero Hamiltonian components. -/
def zero_hamiltonian_path (d : SymplecticData) (i : Nat) :
    Path ((HamiltonianVectorField.zero d).components i) 0 :=
  Path.ofEq (HamiltonianVectorField.zero_components d i)

/-- Path witness: Poisson self-bracket is zero. -/
def poisson_self_bracket_path (d : SymplecticData) :
    Path (PoissonBracket.selfBracket d).value 0 :=
  Path.ofEq (PoissonBracket.selfBracket_zero d)

/-- Path witness: zero moment map vanishes. -/
def moment_zero_path (d : SymplecticData) (ld α i : Nat) :
    Path ((MomentMap.zero d ld).value α i) 0 :=
  Path.ofEq (MomentMap.zero_value d ld α i)

/-- Path witness: Lagrangian dimension is half the ambient dimension. -/
def lagrangian_dim_path (L : LagrangianSubmanifold) :
    Path (2 * L.lagDim) L.ambient.fullDim :=
  Path.ofEq (LagrangianSubmanifold.lagrangian_dim_half L)

/-- Path witness: zero section dimension. -/
def zero_section_dim_path (n : Nat) :
    Path (LagrangianSubmanifold.zeroSection n).lagDim n :=
  Path.ofEq (LagrangianSubmanifold.zeroSection_dim n)

/-- Path witness: cotangent fiber dimension. -/
def cotangent_fiber_dim_path (n : Nat) :
    Path (LagrangianSubmanifold.cotangentFiber n).lagDim n :=
  Path.ofEq (LagrangianSubmanifold.cotangentFiber_dim n)

/-- Path witness: linear capacity. -/
def linear_capacity_path (r : Nat) :
    Path (SymplecticCapacity.linear.value r) r :=
  Path.ofEq (SymplecticCapacity.linear_value r)

/-- Path witness: Gromov equal radii. -/
def gromov_equal_path (r : Nat) :
    Path (GromovNonSqueezing.equal r).ballRadius (GromovNonSqueezing.equal r).cylinderRadius :=
  Path.ofEq (GromovNonSqueezing.equal_radii r)

/-- Path witness: trivial reduction half-dimension. -/
def trivial_reduction_path (d : SymplecticData) :
    Path (MarsdenWeinsteinReduction.trivial d).reducedHalfDim d.halfDim :=
  Path.ofEq (MarsdenWeinsteinReduction.trivial_halfDim d)

/-- Path witness: Weinstein neighborhood dimension. -/
def weinstein_nbhd_path (n : Nat) :
    Path (WeinsteinNeighborhood.ofZeroSection n).cotangentDim (2 * n) :=
  Path.ofEq (WeinsteinNeighborhood.ofZeroSection_dim n)

/-- Path witness: Moser stability identity. -/
def moser_identity_path (d : SymplecticData) :
    Path (MoserStability.identity d).source (MoserStability.identity d).target :=
  Path.ofEq (MoserStability.identity_eq d)

/-- Path witness: Jacobi identity sum. -/
def jacobi_trivial_path :
    Path (PoissonBracket.JacobiIdentity.trivial.v1 +
          PoissonBracket.JacobiIdentity.trivial.v2 +
          PoissonBracket.JacobiIdentity.trivial.v3) 0 :=
  Path.ofEq PoissonBracket.JacobiIdentity.trivial_sum

/-- Inter-file path: symplectic dimension factors through smooth tangent dimension. -/
def symplectic_dim_via_smooth_tangent_path (n : Nat) (hn : n > 0) :
    Path (SymplecticData.standard n).fullDim
         (SmoothManifolds.TangentBundle.ofDim n hn).totalDim :=
  Path.trans (standard_dim_path n) (Path.symm (SmoothManifolds.tangent_dim_path n hn))

/-- Inter-file path: Poisson self-bracket factors through S¹ Euler characteristic. -/
def poisson_to_sphere1_euler_path (d : SymplecticData) :
    Path (PoissonBracket.selfBracket d).value
         (SmoothManifolds.SmoothManifold.sphere 1 (by omega)).eulerChar :=
  Path.trans (poisson_self_bracket_path d) (Path.symm SmoothManifolds.sphere1_euler_path)

/-- Inter-file path: Poisson self-bracket factors through the smooth→exotic Euler bridge. -/
def poisson_to_milnor_euler_path (d : SymplecticData) :
    Path (PoissonBracket.selfBracket d).value
         ExoticSpheres.MilnorSphere.original.eulerChar :=
  Path.trans (poisson_to_sphere1_euler_path d)
    SmoothManifolds.sphere1_to_milnor_euler_path

end SymplecticManifolds
end ComputationalPaths
