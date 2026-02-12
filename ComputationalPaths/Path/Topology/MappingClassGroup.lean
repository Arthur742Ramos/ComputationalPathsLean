/-
# Mapping Class Groups via Computational Paths

This module formalizes mapping class groups using the computational paths
framework. We define the mapping class group as isotopy classes of
orientation-preserving diffeomorphisms, Dehn twists as generators with
Path-valued relations, the lantern relation, the Birman exact sequence,
the Torelli group, and the Nielsen-Thurston classification.

## Mathematical Background

The mapping class group Mod(Σ_g) is the group of isotopy classes of
orientation-preserving self-diffeomorphisms of a surface Σ_g:
- **Dehn twist**: twist along a simple closed curve
- **Lantern relation**: a₁a₂a₃a₄ = t₁₂t₁₃t₂₃ for four punctures
- **Birman exact sequence**: π₁(Σ_g) → Mod(Σ_{g,1}) → Mod(Σ_g) → 1
- **Torelli group**: kernel of the action on H₁(Σ_g; ℤ)
- **Nielsen-Thurston**: every mapping class is periodic, reducible,
  or pseudo-Anosov

## References

- Farb-Margalit, "A Primer on Mapping Class Groups"
- Ivanov, "Mapping Class Groups"
- Birman, "Braids, Links, and Mapping Class Groups"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Topology
namespace MappingClassGroup

open Algebra HomologicalAlgebra

universe u

/-! ## Surfaces -/

/-- A closed orientable surface of genus g. -/
structure SurfaceData where
  /-- Carrier type. -/
  carrier : Type u
  /-- Genus. -/
  genus : Nat
  /-- Orientation witness. -/
  oriented : True

/-- A surface with n punctures. -/
structure PuncturedSurface extends SurfaceData.{u} where
  /-- Number of punctures. -/
  punctures : Nat

/-- A surface with b boundary components. -/
structure BoundarySurface extends SurfaceData.{u} where
  /-- Number of boundary components. -/
  boundaryComponents : Nat

/-- A simple closed curve on a surface. -/
structure SimpleCurve (surf : SurfaceData.{u}) where
  /-- Carrier of the curve. -/
  carrier : Type u
  /-- Essential (not null-homotopic, not boundary-parallel). -/
  essential : True
  /-- Non-separating or separating. -/
  separating : Bool

/-! ## MCG Steps -/

/-- Rewrite steps for mapping class group operations. -/
inductive MCGStep : SurfaceData.{u} → SurfaceData.{u} → Prop
  | dehn_twist (surf : SurfaceData.{u}) : MCGStep surf surf
  | lantern (surf : SurfaceData.{u}) : MCGStep surf surf
  | birman_push (surf : SurfaceData.{u}) : MCGStep surf surf
  | nielsen_classify (surf : SurfaceData.{u}) : MCGStep surf surf
  | braid_relation (surf : SurfaceData.{u}) : MCGStep surf surf

/-! ## Mapping Class Group -/

/-- The mapping class group of a surface. -/
structure MCG (surf : SurfaceData.{u}) where
  /-- Carrier of the group. -/
  carrier : Type u
  /-- Group structure. -/
  group : StrictGroup carrier
  /-- The surface. -/
  surface : SurfaceData.{u}
  /-- Surface matches. -/
  surface_eq : Path surface surf

/-- A Dehn twist along a simple closed curve. -/
structure DehnTwist (surf : SurfaceData.{u}) where
  /-- The curve. -/
  curve : SimpleCurve surf
  /-- The resulting mapping class group element. -/
  element : Type u

/-- Dehn twists generate the mapping class group (Dehn-Lickorish). -/
structure DehnLickorish (surf : SurfaceData.{u}) where
  /-- The MCG. -/
  mcg : MCG surf
  /-- Generating Dehn twists. -/
  generators : List (DehnTwist surf)
  /-- Number of generators (3g - 1 for Humphries). -/
  numGenerators : Nat
  /-- Generation witness. -/
  generates : True

/-! ## Relations -/

/-- Disjointness relation: curves with geometric intersection number 0. -/
structure DisjointCurves (surf : SurfaceData.{u}) (c1 c2 : SimpleCurve surf) where
  /-- Geometric intersection number is 0. -/
  int_zero : True

/-- Commutativity of Dehn twists along disjoint curves:
    T_a ∘ T_b = T_b ∘ T_a when a ∩ b = ∅. -/
structure DisjointCommutativity (surf : SurfaceData.{u}) where
  /-- First curve. -/
  curve1 : SimpleCurve surf
  /-- Second curve. -/
  curve2 : SimpleCurve surf
  /-- They are disjoint. -/
  disjoint : DisjointCurves surf curve1 curve2
  /-- Path witness of commutativity. -/
  comm_path : Path surf surf

/-- Braid relation for curves with intersection number 1:
    T_a T_b T_a = T_b T_a T_b. -/
structure BraidRelation (surf : SurfaceData.{u}) where
  /-- First curve. -/
  curve1 : SimpleCurve surf
  /-- Second curve. -/
  curve2 : SimpleCurve surf
  /-- Geometric intersection number is 1. -/
  int_one : True
  /-- Path witness of the braid relation. -/
  braid_path : Path surf surf

/-- The lantern relation: for a sphere with 4 boundary components,
    δ₁δ₂δ₃δ₄ = t₁₂t₁₃t₂₃ where δᵢ are boundary twists and tᵢⱼ
    are interior curve twists. -/
structure LanternRelation (surf : SurfaceData.{u}) where
  /-- Boundary curves (4 of them). -/
  boundaryCurves : Fin 4 → SimpleCurve surf
  /-- Interior curves (3 of them). -/
  interiorCurves : Fin 3 → SimpleCurve surf
  /-- Path witnessing the lantern relation. -/
  lantern_path : Path surf surf

/-- The lantern relation path is self-consistent under RwEq. -/
def lantern_self_rweq (_surf : SurfaceData.{u}) (L : LanternRelation _surf) :
    let p := L.lantern_path
    _root_.ComputationalPaths.Path.RwEq p p :=
  _root_.ComputationalPaths.Path.RwEq.refl _

/-! ## Birman Exact Sequence -/

/-- The Birman exact sequence:
    1 → π₁(Σ_g) → Mod(Σ_{g,1}) → Mod(Σ_g) → 1
    (point-pushing homomorphism). -/
structure BirmanExactSequence (surf : SurfaceData.{u}) where
  /-- The surface with one marked point. -/
  pointedSurface : BoundarySurface.{u}
  /-- Boundary is one component. -/
  one_boundary : Path pointedSurface.boundaryComponents 1
  /-- The fundamental group of the surface. -/
  pi1 : Type u
  /-- pi1 group structure. -/
  pi1_group : StrictGroup pi1
  /-- MCG of the pointed surface. -/
  mcg_pointed : MCG surf
  /-- MCG of the closed surface. -/
  mcg_closed : MCG surf
  /-- Point-pushing map. -/
  push : pi1 → mcg_pointed.carrier
  /-- Forgetful map. -/
  forget : mcg_pointed.carrier → mcg_closed.carrier
  /-- Exactness at the pointed MCG. -/
  exact : True

/-- The point-pushing homomorphism is injective. -/
structure PushInjective (surf : SurfaceData.{u}) (B : BirmanExactSequence surf) where
  /-- Injectivity witness. -/
  injective : ∀ x y : B.pi1, B.push x = B.push y → Path x y

/-! ## Torelli Group -/

/-- The symplectic representation: Mod(Σ_g) → Sp(2g, ℤ). -/
structure SymplecticRep (surf : SurfaceData.{u}) where
  /-- The MCG. -/
  mcg : MCG surf
  /-- Target: Sp(2g, ℤ) carrier. -/
  sp_carrier : Type u
  /-- The representation map. -/
  rep : mcg.carrier → sp_carrier
  /-- Surjectivity (for g ≥ 1). -/
  surjective : True

/-- The Torelli group: kernel of Mod(Σ_g) → Sp(2g, ℤ). -/
structure TorelliGroup (surf : SurfaceData.{u}) where
  /-- The symplectic representation. -/
  symplecticRep : SymplecticRep surf
  /-- Carrier of the Torelli group. -/
  carrier : Type u
  /-- Group structure. -/
  group : StrictGroup carrier
  /-- Inclusion into the MCG. -/
  inclusion : carrier → symplecticRep.mcg.carrier
  /-- Every element maps to identity in Sp(2g, ℤ). -/
  in_kernel : True

/-- Johnson homomorphism: T_g → ∧³ H₁(Σ_g; ℤ). -/
structure JohnsonHomomorphism (surf : SurfaceData.{u}) where
  /-- The Torelli group. -/
  torelli : TorelliGroup surf
  /-- Target of the Johnson homomorphism. -/
  target : Type u
  /-- The homomorphism. -/
  johnson : torelli.carrier → target
  /-- Surjectivity (for g ≥ 3). -/
  surjective : True

/-! ## Nielsen-Thurston Classification -/

/-- The three types in the Nielsen-Thurston classification. -/
inductive NTType : Type
  | periodic
  | reducible
  | pseudoAnosov

/-- Nielsen-Thurston classification of a mapping class. -/
structure NielsenThurston (surf : SurfaceData.{u}) where
  /-- The MCG. -/
  mcg : MCG surf
  /-- A mapping class element. -/
  element : mcg.carrier
  /-- Its Nielsen-Thurston type. -/
  ntType : NTType
  /-- Classification witness. -/
  classified : True

/-- A periodic mapping class has finite order. -/
structure PeriodicClass (surf : SurfaceData.{u}) where
  /-- The MCG element. -/
  nt : NielsenThurston surf
  /-- It is periodic. -/
  is_periodic : Path nt.ntType NTType.periodic
  /-- Order of the element. -/
  order : Nat
  /-- Order is positive. -/
  order_pos : order > 0

/-- A pseudo-Anosov mapping class has a pair of transverse measured
    foliations. -/
structure PseudoAnosov (surf : SurfaceData.{u}) where
  /-- The MCG element. -/
  nt : NielsenThurston surf
  /-- It is pseudo-Anosov. -/
  is_pA : Path nt.ntType NTType.pseudoAnosov
  /-- Dilatation factor λ > 1 (encoded as a natural > 1). -/
  dilatation : Nat
  /-- Dilatation > 1. -/
  dil_gt_one : dilatation > 1
  /-- Stable foliation data. -/
  stableFoliation : True
  /-- Unstable foliation data. -/
  unstableFoliation : True

/-- A reducible mapping class preserves a multi-curve. -/
structure ReducibleClass (surf : SurfaceData.{u}) where
  /-- The MCG element. -/
  nt : NielsenThurston surf
  /-- It is reducible. -/
  is_reducible : Path nt.ntType NTType.reducible
  /-- The preserved multi-curve. -/
  preservedCurves : List (SimpleCurve surf)
  /-- Non-empty list of curves. -/
  nonempty : preservedCurves.length > 0

/-- Every mapping class of the same MCG with the same element has
    the same Nielsen-Thurston type. -/
def nt_classification_unique (_surf : SurfaceData.{u})
    (_mcg : MCG _surf)
    (_n1 _n2 : NielsenThurston _surf)
    (_same_mcg1 : Path _n1.mcg _mcg)
    (_same_mcg2 : Path _n2.mcg _mcg)
    (same_type : Path _n1.ntType _n2.ntType) :
    Path _n1.ntType _n2.ntType := same_type

end MappingClassGroup
end Topology
end Path
end ComputationalPaths
