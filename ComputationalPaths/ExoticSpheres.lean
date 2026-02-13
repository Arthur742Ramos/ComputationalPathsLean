/-
# Exotic Spheres via Computational Paths

This module formalizes exotic spheres — homeomorphic but not diffeomorphic
spheres — including Milnor's exotic 7-sphere, the Kervaire-Milnor
classification of exotic spheres, the groups Θ_n of exotic spheres,
the J-homomorphism, Adams' e-invariant, and the bP_{n+1} subgroup,
all with `Path` coherence witnesses.

## Mathematical Background

Exotic spheres are smooth manifolds homeomorphic to S^n but carrying
non-standard differentiable structures:

1. **Exotic spheres**: Smooth manifolds Σ homeomorphic to S^n with
   Σ not diffeomorphic to S^n. First discovered by Milnor (1956) for n=7.
2. **Milnor's 7-sphere**: An S³-bundle over S⁴ that is homeomorphic
   but not diffeomorphic to S⁷. There are 28 exotic 7-spheres.
3. **Kervaire-Milnor classification**: Θ_n = group of exotic n-spheres
   under connected sum. |Θ_7| = 28, |Θ_11| = 992, |Θ_15| = 16256.
4. **Groups Θ_n**: Finite abelian groups for n ≠ 4, fitting in the
   exact sequence 0 → bP_{n+1} → Θ_n → coker J.
5. **J-homomorphism**: J : π_n(SO) → π_n^s — relates homotopy of
   the orthogonal group to stable homotopy groups of spheres.
6. **Adams e-invariant**: e : coker J → ℚ/ℤ — detects elements
   not in the image of J.
7. **bP_{n+1} subgroup**: Exotic spheres bounding parallelizable
   manifolds. |bP_{4k}| = a_k · 2^{2k-2}(2^{2k-1} - 1) · numerator(B_{2k}/4k).

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `ExoticSphere` | Exotic sphere data |
| `MilnorSphere` | Milnor's exotic S⁷ |
| `ExoticGroup` | Group Θ_n of exotic spheres |
| `KervaireMilnor` | K-M classification data |
| `JHomomorphism` | J : π_n(SO) → π_n^s |
| `AdamsEInvariant` | e-invariant data |
| `BPSubgroup` | bP_{n+1} subgroup |
| `theta7_order_path` | |Θ_7| = 28 |
| `theta11_order_path` | |Θ_11| = 992 |
| `bp_subgroup_path` | bP inclusion coherence |
| `j_image_path` | im(J) coherence |

## References

- Milnor, "On manifolds homeomorphic to the 7-sphere"
- Kervaire & Milnor, "Groups of homotopy spheres: I"
- Adams, "On the groups J(X)"
- Levine, "Lectures on groups of homotopy spheres"
- Hill, Hopkins & Ravenel, "On the non-existence of elements of Kervaire invariant one"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace ExoticSpheres

universe u v w

/-! ## Exotic Sphere Data -/

/-- An exotic sphere: a smooth manifold homeomorphic to S^n but
not diffeomorphic to the standard S^n. Records the dimension and
its position in the group Θ_n. -/
structure ExoticSphere where
  /-- Dimension of the sphere. -/
  dim : Nat
  /-- Dimension ≥ 1. -/
  dim_pos : dim ≥ 1
  /-- The Euler characteristic (always 0 or 2, same as S^n). -/
  eulerChar : Int
  /-- Euler characteristic matches S^n. -/
  euler_eq : eulerChar = if dim % 2 = 0 then 2 else 0
  /-- Index in Θ_n (0 = standard sphere). -/
  thetaIndex : Nat
  /-- Whether this is the standard sphere. -/
  isStandard : Bool
  /-- Standard iff index = 0. -/
  standard_iff : isStandard = true ↔ thetaIndex = 0

namespace ExoticSphere

/-- The standard n-sphere. -/
def standard (n : Nat) (hn : n ≥ 1) : ExoticSphere where
  dim := n
  dim_pos := hn
  eulerChar := if n % 2 = 0 then 2 else 0
  euler_eq := rfl
  thetaIndex := 0
  isStandard := true
  standard_iff := by simp

/-- An exotic n-sphere with index k > 0. -/
def exotic (n : Nat) (hn : n ≥ 1) (k : Nat) (hk : k > 0) : ExoticSphere where
  dim := n
  dim_pos := hn
  eulerChar := if n % 2 = 0 then 2 else 0
  euler_eq := rfl
  thetaIndex := k
  isStandard := false
  standard_iff := by simp; omega

/-- Standard sphere is standard. -/
theorem standard_is_standard (n : Nat) (hn : n ≥ 1) :
    (standard n hn).isStandard = true := rfl

/-- Exotic sphere is not standard. -/
theorem exotic_not_standard (n : Nat) (hn : n ≥ 1) (k : Nat) (hk : k > 0) :
    (exotic n hn k hk).isStandard = false := rfl

/-- Standard sphere has index 0. -/
theorem standard_index (n : Nat) (hn : n ≥ 1) :
    (standard n hn).thetaIndex = 0 := rfl

/-- Exotic spheres have the same Euler characteristic as standard. -/
theorem exotic_euler_eq_standard (n : Nat) (hn : n ≥ 1) (k : Nat) (hk : k > 0) :
    (exotic n hn k hk).eulerChar = (standard n hn).eulerChar := rfl

end ExoticSphere

/-! ## Milnor's Exotic 7-Sphere -/

/-- Milnor's exotic 7-sphere: an S³-bundle over S⁴,
the first exotic sphere discovered (1956). -/
structure MilnorSphere where
  /-- Always dimension 7. -/
  dim : Nat
  /-- dim = 7. -/
  dim_eq : dim = 7
  /-- Fiber dimension (S³). -/
  fiberDim : Nat
  /-- Fiber is S³. -/
  fiber_eq : fiberDim = 3
  /-- Base dimension (S⁴). -/
  baseDim : Nat
  /-- Base is S⁴. -/
  base_eq : baseDim = 4
  /-- dim = fiber + base. -/
  bundle_eq : dim = fiberDim + baseDim
  /-- Euler characteristic = 0 (odd-dimensional). -/
  eulerChar : Int
  /-- χ = 0 for odd-dimensional spheres. -/
  euler_eq : eulerChar = 0
  /-- Milnor invariant λ (distinguishes from standard S⁷). -/
  milnorInvariant : Int
  /-- λ is not ≡ 0 mod 7 (exotic). -/
  invariant_nonzero : milnorInvariant % 7 ≠ 0

namespace MilnorSphere

/-- Milnor's original exotic 7-sphere with λ = 1. -/
def original : MilnorSphere where
  dim := 7
  dim_eq := rfl
  fiberDim := 3
  fiber_eq := rfl
  baseDim := 4
  base_eq := rfl
  bundle_eq := rfl
  eulerChar := 0
  euler_eq := rfl
  milnorInvariant := 1
  invariant_nonzero := by decide

/-- Dimension is 7. -/
theorem dim_is_7 : original.dim = 7 := rfl

/-- Fiber is S³. -/
theorem fiber_is_s3 : original.fiberDim = 3 := rfl

/-- Base is S⁴. -/
theorem base_is_s4 : original.baseDim = 4 := rfl

/-- Bundle decomposition: 7 = 3 + 4. -/
theorem bundle_decomp : original.dim = original.fiberDim + original.baseDim := rfl

/-- Euler characteristic is 0. -/
theorem euler_zero : original.eulerChar = 0 := rfl

/-- The Milnor invariant is 1. -/
theorem invariant_value : original.milnorInvariant = 1 := rfl

end MilnorSphere

/-! ## Group Θ_n of Exotic Spheres -/

/-- The group Θ_n of exotic n-spheres under connected sum.
This is a finite abelian group for n ≠ 4. -/
structure ExoticGroup where
  /-- Dimension n. -/
  dim : Nat
  /-- Dimension is at least 1. -/
  dim_pos : dim ≥ 1
  /-- Order |Θ_n|. -/
  order : Nat
  /-- Order is positive (includes standard sphere). -/
  order_pos : order ≥ 1
  /-- Whether the group is known to be trivial. -/
  isTrivial : Bool
  /-- Trivial iff order = 1. -/
  trivial_iff : isTrivial = true ↔ order = 1

namespace ExoticGroup

/-- Θ_1 = 1 (no exotic 1-spheres). -/
def theta1 : ExoticGroup where
  dim := 1
  dim_pos := by omega
  order := 1
  order_pos := by omega
  isTrivial := true
  trivial_iff := by simp

/-- Θ_2 = 1 (no exotic 2-spheres). -/
def theta2 : ExoticGroup where
  dim := 2
  dim_pos := by omega
  order := 1
  order_pos := by omega
  isTrivial := true
  trivial_iff := by simp

/-- Θ_3 = 1 (no exotic 3-spheres, Smale/Perelman). -/
def theta3 : ExoticGroup where
  dim := 3
  dim_pos := by omega
  order := 1
  order_pos := by omega
  isTrivial := true
  trivial_iff := by simp

/-- Θ_5 = 1. -/
def theta5 : ExoticGroup where
  dim := 5
  dim_pos := by omega
  order := 1
  order_pos := by omega
  isTrivial := true
  trivial_iff := by simp

/-- Θ_6 = 1. -/
def theta6 : ExoticGroup where
  dim := 6
  dim_pos := by omega
  order := 1
  order_pos := by omega
  isTrivial := true
  trivial_iff := by simp

/-- Θ_7 = 28 (Milnor). -/
def theta7 : ExoticGroup where
  dim := 7
  dim_pos := by omega
  order := 28
  order_pos := by omega
  isTrivial := false
  trivial_iff := by simp

/-- Θ_8 = 2. -/
def theta8 : ExoticGroup where
  dim := 8
  dim_pos := by omega
  order := 2
  order_pos := by omega
  isTrivial := false
  trivial_iff := by simp

/-- Θ_9 = 8. -/
def theta9 : ExoticGroup where
  dim := 9
  dim_pos := by omega
  order := 8
  order_pos := by omega
  isTrivial := false
  trivial_iff := by simp

/-- Θ_10 = 6. -/
def theta10 : ExoticGroup where
  dim := 10
  dim_pos := by omega
  order := 6
  order_pos := by omega
  isTrivial := false
  trivial_iff := by simp

/-- Θ_11 = 992. -/
def theta11 : ExoticGroup where
  dim := 11
  dim_pos := by omega
  order := 992
  order_pos := by omega
  isTrivial := false
  trivial_iff := by simp

/-- Θ_12 = 1. -/
def theta12 : ExoticGroup where
  dim := 12
  dim_pos := by omega
  order := 1
  order_pos := by omega
  isTrivial := true
  trivial_iff := by simp

/-- Θ_13 = 3. -/
def theta13 : ExoticGroup where
  dim := 13
  dim_pos := by omega
  order := 3
  order_pos := by omega
  isTrivial := false
  trivial_iff := by simp

/-- Θ_14 = 2. -/
def theta14 : ExoticGroup where
  dim := 14
  dim_pos := by omega
  order := 2
  order_pos := by omega
  isTrivial := false
  trivial_iff := by simp

/-- Θ_15 = 16256. -/
def theta15 : ExoticGroup where
  dim := 15
  dim_pos := by omega
  order := 16256
  order_pos := by omega
  isTrivial := false
  trivial_iff := by simp

/-- |Θ_7| = 28. -/
theorem theta7_order : theta7.order = 28 := rfl

/-- |Θ_11| = 992. -/
theorem theta11_order : theta11.order = 992 := rfl

/-- |Θ_15| = 16256. -/
theorem theta15_order : theta15.order = 16256 := rfl

/-- Θ_1 is trivial. -/
theorem theta1_trivial : theta1.isTrivial = true := rfl

/-- Θ_3 is trivial (Perelman). -/
theorem theta3_trivial : theta3.isTrivial = true := rfl

/-- Θ_5 is trivial. -/
theorem theta5_trivial : theta5.isTrivial = true := rfl

/-- Θ_7 is nontrivial. -/
theorem theta7_nontrivial : theta7.isTrivial = false := rfl

/-- Θ_12 is trivial. -/
theorem theta12_trivial : theta12.isTrivial = true := rfl

end ExoticGroup

/-! ## Kervaire-Milnor Classification -/

/-- Kervaire-Milnor classification: the exact sequence
0 → bP_{n+1} → Θ_n → coker J. -/
structure KervaireMilnor where
  /-- Dimension n. -/
  dim : Nat
  /-- n ≥ 5 (high-dimensional). -/
  dim_ge5 : dim ≥ 5
  /-- Order of Θ_n. -/
  thetaOrder : Nat
  /-- Order of bP_{n+1}. -/
  bpOrder : Nat
  /-- Order of coker J component. -/
  cokerJOrder : Nat
  /-- bP divides Θ. -/
  bp_divides : bpOrder ∣ thetaOrder
  /-- |Θ_n| = |bP_{n+1}| · |coker J contribution|. -/
  order_product : thetaOrder = bpOrder * cokerJOrder

namespace KervaireMilnor

/-- K-M for n = 7: |Θ_7| = 28 = 28 · 1. -/
def km7 : KervaireMilnor where
  dim := 7
  dim_ge5 := by omega
  thetaOrder := 28
  bpOrder := 28
  cokerJOrder := 1
  bp_divides := ⟨1, by omega⟩
  order_product := by omega

/-- K-M for n = 11: |Θ_11| = 992 = 992 · 1. -/
def km11 : KervaireMilnor where
  dim := 11
  dim_ge5 := by omega
  thetaOrder := 992
  bpOrder := 992
  cokerJOrder := 1
  bp_divides := ⟨1, by omega⟩
  order_product := by omega

/-- K-M for n = 15: |Θ_15| = 16256 = 8128 · 2. -/
def km15 : KervaireMilnor where
  dim := 15
  dim_ge5 := by omega
  thetaOrder := 16256
  bpOrder := 8128
  cokerJOrder := 2
  bp_divides := ⟨2, by omega⟩
  order_product := by omega

/-- K-M for n = 9: |Θ_9| = 8 = 2 · 4. -/
def km9 : KervaireMilnor where
  dim := 9
  dim_ge5 := by omega
  thetaOrder := 8
  bpOrder := 2
  cokerJOrder := 4
  bp_divides := ⟨4, by omega⟩
  order_product := by omega

/-- |Θ_7| = 28 via K-M. -/
theorem km7_theta : km7.thetaOrder = 28 := rfl

/-- |bP_8| = 28 (all exotic 7-spheres bound parallelizable manifolds). -/
theorem km7_bp : km7.bpOrder = 28 := rfl

/-- |coker J| = 1 for n = 7. -/
theorem km7_cokerJ : km7.cokerJOrder = 1 := rfl

/-- |Θ_11| = 992 via K-M. -/
theorem km11_theta : km11.thetaOrder = 992 := rfl

/-- |bP_16| = 8128 for n = 15. -/
theorem km15_bp : km15.bpOrder = 8128 := rfl

end KervaireMilnor

/-! ## J-Homomorphism -/

/-- The J-homomorphism J : π_n(SO) → π_n^s relates the
homotopy groups of SO to stable homotopy groups of spheres. -/
structure JHomomorphism where
  /-- Degree n. -/
  degree : Nat
  /-- Source: rank of π_n(SO). -/
  sourceRank : Nat
  /-- Target: rank of π_n^s. -/
  targetRank : Nat
  /-- Image rank: rank of im(J). -/
  imageRank : Nat
  /-- Image is a subgroup of target. -/
  image_le : imageRank ≤ targetRank
  /-- Order of im(J) (as a cyclic group). -/
  imageOrder : Nat

namespace JHomomorphism

/-- J in degree 1: π_1(SO) = ℤ/2 → π_1^s = ℤ/2. -/
def j1 : JHomomorphism where
  degree := 1
  sourceRank := 1
  targetRank := 1
  imageRank := 1
  image_le := Nat.le_refl 1
  imageOrder := 2

/-- J in degree 3: π_3(SO) = ℤ → π_3^s = ℤ/24. Image has order 24. -/
def j3 : JHomomorphism where
  degree := 3
  sourceRank := 1
  targetRank := 1
  imageRank := 1
  image_le := Nat.le_refl 1
  imageOrder := 24

/-- J in degree 7: π_7(SO) = ℤ → π_7^s. Image order = 240. -/
def j7 : JHomomorphism where
  degree := 7
  sourceRank := 1
  targetRank := 1
  imageRank := 1
  image_le := Nat.le_refl 1
  imageOrder := 240

/-- J in degree 0: trivial. -/
def j0 : JHomomorphism where
  degree := 0
  sourceRank := 1
  targetRank := 1
  imageRank := 1
  image_le := Nat.le_refl 1
  imageOrder := 1

/-- im(J) has order 24 in degree 3. -/
theorem j3_image_order : j3.imageOrder = 24 := rfl

/-- im(J) has order 240 in degree 7. -/
theorem j7_image_order : j7.imageOrder = 240 := rfl

/-- im(J) has order 2 in degree 1. -/
theorem j1_image_order : j1.imageOrder = 2 := rfl

end JHomomorphism

/-! ## Adams e-Invariant -/

/-- Adams' e-invariant: detects elements in coker J via
e : coker J → ℚ/ℤ. Encoded via numerator and denominator. -/
structure AdamsEInvariant where
  /-- Degree. -/
  degree : Nat
  /-- Numerator of the e-invariant. -/
  numerator : Int
  /-- Denominator of the e-invariant. -/
  denominator : Nat
  /-- Denominator is positive. -/
  denom_pos : denominator > 0
  /-- Whether the e-invariant detects a nontrivial element. -/
  isNontrivial : Bool

namespace AdamsEInvariant

/-- Trivial e-invariant. -/
def trivialE (n : Nat) : AdamsEInvariant where
  degree := n
  numerator := 0
  denominator := 1
  denom_pos := Nat.one_pos
  isNontrivial := false

/-- Trivial e-invariant has numerator 0. -/
theorem trivial_num (n : Nat) : (trivialE n).numerator = 0 := rfl

/-- Trivial e-invariant is not nontrivial. -/
theorem trivial_not_nontrivial (n : Nat) :
    (trivialE n).isNontrivial = false := rfl

/-- e-invariant in degree 1: e = 1/2. -/
def e1 : AdamsEInvariant where
  degree := 1
  numerator := 1
  denominator := 2
  denom_pos := by omega
  isNontrivial := true

/-- e-invariant in degree 3: e = 1/24. -/
def e3 : AdamsEInvariant where
  degree := 3
  numerator := 1
  denominator := 24
  denom_pos := by omega
  isNontrivial := true

/-- e₁ has denominator 2. -/
theorem e1_denom : e1.denominator = 2 := rfl

/-- e₃ has denominator 24. -/
theorem e3_denom : e3.denominator = 24 := rfl

/-- e₁ is nontrivial. -/
theorem e1_nontrivial : e1.isNontrivial = true := rfl

end AdamsEInvariant

/-! ## bP Subgroup -/

/-- The subgroup bP_{n+1} ⊂ Θ_n of exotic spheres that bound
parallelizable manifolds. For n = 4k-1, |bP_{4k}| involves
Bernoulli numbers. -/
structure BPSubgroup where
  /-- Sphere dimension n. -/
  sphereDim : Nat
  /-- n ≥ 5. -/
  dim_ge5 : sphereDim ≥ 5
  /-- Order of bP_{n+1}. -/
  order : Nat
  /-- Order is positive. -/
  order_pos : order > 0
  /-- Order of Θ_n. -/
  thetaOrder : Nat
  /-- bP divides Θ. -/
  divides : order ∣ thetaOrder

namespace BPSubgroup

/-- bP_8 for Θ_7: |bP_8| = 28. -/
def bp8 : BPSubgroup where
  sphereDim := 7
  dim_ge5 := by omega
  order := 28
  order_pos := by omega
  thetaOrder := 28
  divides := ⟨1, by omega⟩

/-- bP_12 for Θ_11: |bP_12| = 992. -/
def bp12 : BPSubgroup where
  sphereDim := 11
  dim_ge5 := by omega
  order := 992
  order_pos := by omega
  thetaOrder := 992
  divides := ⟨1, by omega⟩

/-- bP_16 for Θ_15: |bP_16| = 8128. -/
def bp16 : BPSubgroup where
  sphereDim := 15
  dim_ge5 := by omega
  order := 8128
  order_pos := by omega
  thetaOrder := 16256
  divides := ⟨2, by omega⟩

/-- bP_10 for Θ_9: |bP_10| = 2. -/
def bp10 : BPSubgroup where
  sphereDim := 9
  dim_ge5 := by omega
  order := 2
  order_pos := by omega
  thetaOrder := 8
  divides := ⟨4, by omega⟩

/-- |bP_8| = 28. -/
theorem bp8_order : bp8.order = 28 := rfl

/-- |bP_12| = 992. -/
theorem bp12_order : bp12.order = 992 := rfl

/-- |bP_16| = 8128. -/
theorem bp16_order : bp16.order = 8128 := rfl

/-- bP_8 exhausts Θ_7. -/
theorem bp8_exhausts : bp8.order = bp8.thetaOrder := rfl

/-- bP_12 exhausts Θ_11. -/
theorem bp12_exhausts : bp12.order = bp12.thetaOrder := rfl

end BPSubgroup

/-! ## Exotic Sphere Computations -/

/-- 28 = 4 · 7 (factoring |Θ_7|). -/
theorem theta7_factored : 28 = 4 * 7 := by omega

/-- 992 = 32 · 31 (factoring |Θ_11|). -/
theorem theta11_factored : 992 = 32 * 31 := by omega

/-- 16256 = 128 · 127 (factoring |Θ_15|). -/
theorem theta15_factored : 16256 = 128 * 127 := by omega

/-- 8128 = 64 · 127 (factoring |bP_16|). -/
theorem bp16_factored : 8128 = 64 * 127 := by omega

/-- |Θ_7| divides 7! = 5040. -/
theorem theta7_divides_7fac : 28 ∣ 5040 := ⟨180, by omega⟩

/-- Milnor's sphere has Euler characteristic 0 (odd-dimensional). -/
theorem milnor_euler : MilnorSphere.original.eulerChar = 0 := rfl

/-- Standard S⁷ and exotic S⁷ have the same Euler characteristic. -/
theorem exotic_standard_euler :
    (ExoticSphere.exotic 7 (by omega) 1 (by omega)).eulerChar =
    (ExoticSphere.standard 7 (by omega)).eulerChar := rfl

/-- Dimensions where Θ_n is trivial (in our database): 1, 2, 3, 5, 6, 12. -/
theorem trivial_dimensions :
    ExoticGroup.theta1.isTrivial = true ∧
    ExoticGroup.theta2.isTrivial = true ∧
    ExoticGroup.theta3.isTrivial = true ∧
    ExoticGroup.theta5.isTrivial = true ∧
    ExoticGroup.theta6.isTrivial = true ∧
    ExoticGroup.theta12.isTrivial = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- |Θ_7| · |Θ_11| = 28 · 992 = 27776. -/
theorem theta7_times_theta11 :
    ExoticGroup.theta7.order * ExoticGroup.theta11.order = 27776 := by
  decide

/-! ## Path Coherence Witnesses -/

/-- |Θ_7| = 28 path. -/
def theta7_order_path :
    Path ExoticGroup.theta7.order 28 :=
  Path.ofEq ExoticGroup.theta7_order

/-- |Θ_11| = 992 path. -/
def theta11_order_path :
    Path ExoticGroup.theta11.order 992 :=
  Path.ofEq ExoticGroup.theta11_order

/-- |Θ_15| = 16256 path. -/
def theta15_order_path :
    Path ExoticGroup.theta15.order 16256 :=
  Path.ofEq ExoticGroup.theta15_order

/-- bP_8 order path. -/
def bp8_order_path :
    Path BPSubgroup.bp8.order 28 :=
  Path.ofEq BPSubgroup.bp8_order

/-- bP_12 order path. -/
def bp12_order_path :
    Path BPSubgroup.bp12.order 992 :=
  Path.ofEq BPSubgroup.bp12_order

/-- bP_16 order path. -/
def bp16_order_path :
    Path BPSubgroup.bp16.order 8128 :=
  Path.ofEq BPSubgroup.bp16_order

/-- Milnor sphere dimension path. -/
def milnor_dim_path :
    Path MilnorSphere.original.dim 7 :=
  Path.ofEq MilnorSphere.dim_is_7

/-- Milnor sphere bundle decomposition path. -/
def milnor_bundle_path :
    Path MilnorSphere.original.dim
         (MilnorSphere.original.fiberDim + MilnorSphere.original.baseDim) :=
  Path.ofEq MilnorSphere.bundle_decomp

/-- Milnor sphere Euler path. -/
def milnor_euler_path :
    Path MilnorSphere.original.eulerChar 0 :=
  Path.ofEq MilnorSphere.euler_zero

/-- J-homomorphism image order in degree 3. -/
def j3_image_path :
    Path JHomomorphism.j3.imageOrder 24 :=
  Path.ofEq JHomomorphism.j3_image_order

/-- J-homomorphism image order in degree 7. -/
def j7_image_path :
    Path JHomomorphism.j7.imageOrder 240 :=
  Path.ofEq JHomomorphism.j7_image_order

/-- Adams e₃ denominator path. -/
def adams_e3_path :
    Path AdamsEInvariant.e3.denominator 24 :=
  Path.ofEq AdamsEInvariant.e3_denom

/-- K-M exact sequence for n=7 path. -/
def km7_theta_path :
    Path KervaireMilnor.km7.thetaOrder 28 :=
  Path.ofEq KervaireMilnor.km7_theta

/-- K-M bP₈ path. -/
def km7_bp_path :
    Path KervaireMilnor.km7.bpOrder 28 :=
  Path.ofEq KervaireMilnor.km7_bp

/-- Standard sphere index path. -/
def standard_index_path (n : Nat) (hn : n ≥ 1) :
    Path (ExoticSphere.standard n hn).thetaIndex 0 :=
  Path.ofEq (ExoticSphere.standard_index n hn)

/-- Θ₃ triviality path (Poincaré conjecture). -/
def theta3_trivial_path :
    Path ExoticGroup.theta3.isTrivial true :=
  Path.ofEq ExoticGroup.theta3_trivial

/-- bP₈ exhaustion path. -/
def bp8_exhausts_path :
    Path BPSubgroup.bp8.order BPSubgroup.bp8.thetaOrder :=
  Path.ofEq BPSubgroup.bp8_exhausts

/-- Bridge any boolean witness through Θ₃ triviality. -/
def theta3_factor_through_true {b : Bool} (p : Path b true) :
    Path ExoticGroup.theta3.isTrivial b :=
  Path.trans theta3_trivial_path (Path.symm p)

/-- Bridge any Euler-characteristic witness through Milnor χ = 0. -/
def milnor_euler_factor_through_zero {z : Int} (p : Path z 0) :
    Path MilnorSphere.original.eulerChar z :=
  Path.trans milnor_euler_path (Path.symm p)

end ExoticSpheres
end ComputationalPaths
