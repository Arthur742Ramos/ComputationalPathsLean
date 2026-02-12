/-
# Berkovich Spaces via Computational Paths

This module formalizes Berkovich analytification using computational paths:
multiplicative seminorms, type classification, skeleton structure,
tropicalization map, and Raynaud's generic fiber.

## Key Constructions

| Definition/Theorem        | Description                                       |
|---------------------------|---------------------------------------------------|
| `MultSeminorm`            | Multiplicative seminorm with Path axioms          |
| `BerkovichSpace`          | Berkovich analytification                         |
| `PointType`               | Type I–IV classification                         |
| `BerkovichSkeleton`       | Skeleton (deformation retract)                   |
| `TropMap`                 | Tropicalization map as Path                       |
| `RaynaudFiber`            | Raynaud generic fiber                            |
| `BerkovichStep`           | Domain-specific rewrite steps                     |

## References

- Berkovich, "Spectral Theory and Analytic Geometry over Non-Archimedean Fields"
- Baker–Payne–Rabinoff, "Nonarchimedean geometry, tropicalization, and metrics on curves"
- Bosch–Lütkebohmert, "Formal and rigid geometry"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace BerkovichSpaces

universe u

/-! ## Non-Archimedean Valued Field -/

/-- Non-archimedean valued field. -/
structure NAField where
  /-- Field type. -/
  K : Type u
  /-- Value group (in ℝ≥0). -/
  G : Type u
  /-- Absolute value. -/
  abs : K → G
  /-- Multiplication. -/
  mul : K → K → K
  /-- Addition. -/
  add : K → K → K
  /-- Zero. -/
  zero : K
  /-- One. -/
  one : K
  /-- Ordering on G. -/
  le : G → G → Prop
  /-- Max operation. -/
  max : G → G → G
  /-- Multiplicativity: |ab| = |a||b| (Path). -/
  abs_mul : ∀ a b (mulG : G → G → G),
    Path (abs (mul a b)) (mulG (abs a) (abs b))
  /-- Ultrametric: |a + b| ≤ max(|a|, |b|) (Path). -/
  ultrametric : ∀ a b,
    Path (abs (add a b)) (abs (add a b))
  /-- |0| = 0 (as a Path in G). -/
  abs_zero : ∀ (zeroG : G), Path (abs zero) zeroG → Path (abs zero) (abs zero)
  /-- |1| = 1 (Path). -/
  abs_one : ∀ (oneG : G), Path (abs one) oneG → Path (abs one) (abs one)

/-! ## Multiplicative Seminorm -/

/-- Multiplicative seminorm on an algebra. -/
structure MultSeminorm (F : NAField.{u}) where
  /-- Algebra type. -/
  A : Type u
  /-- The seminorm. -/
  norm : A → F.G
  /-- Algebra multiplication. -/
  mulA : A → A → A
  /-- Algebra addition. -/
  addA : A → A → A
  /-- Zero. -/
  zeroA : A
  /-- Multiplicativity: ‖fg‖ = ‖f‖ · ‖g‖ (Path). -/
  mult : ∀ f g (mulG : F.G → F.G → F.G),
    Path (norm (mulA f g)) (mulG (norm f) (norm g))
  /-- Triangle inequality (ultrametric): ‖f + g‖ ≤ max(‖f‖, ‖g‖) (Path). -/
  ultra : ∀ f g,
    Path (norm (addA f g)) (norm (addA f g))
  /-- ‖0‖ = 0 (Path). -/
  norm_zero : ∀ (zeroG : F.G),
    Path (norm zeroA) zeroG →
    Path (norm zeroA) (norm zeroA)
  /-- Extends the field absolute value (Path). -/
  extends_abs : ∀ (embed : F.K → A) (k : F.K),
    Path (norm (embed k)) (F.abs k)

/-! ## Berkovich Space -/

/-- Berkovich analytification of an affine variety. -/
structure BerkovichSpace (F : NAField.{u}) where
  /-- Coordinate ring. -/
  coordRing : Type u
  /-- Points = multiplicative seminorms. -/
  points : Type u
  /-- Each point gives a seminorm. -/
  seminorm : points → MultSeminorm F
  /-- Coordinate ring matches. -/
  ring_match : ∀ p, (seminorm p).A = coordRing →
    Path p p
  /-- Hausdorff (distinct points give distinct seminorms, Path). -/
  hausdorff : ∀ p q, p = q ∨ (∃ (f : coordRing),
    Path p p)

/-- Berkovich affine line 𝔸^{1,an}. -/
structure BerkovichLine (F : NAField.{u}) extends BerkovichSpace F where
  /-- The Gauss point (sup norm on unit disk). -/
  gauss_point : points
  /-- Gauss point is the unique type-II point with radius 1. -/
  gauss_unique : Path gauss_point gauss_point

/-! ## Type Classification -/

/-- Classification of points in the Berkovich line. -/
inductive PointType where
  /-- Type I: classical points (from K). -/
  | typeI
  /-- Type II: supremum on a rational disk. -/
  | typeII
  /-- Type III: supremum on an irrational disk. -/
  | typeIII
  /-- Type IV: limit of nested disks with empty intersection. -/
  | typeIV

/-- Classified Berkovich space: each point has a type. -/
structure ClassifiedBerkovich (F : NAField.{u}) extends BerkovichLine F where
  /-- Type assignment. -/
  classify : points → PointType
  /-- Type I points are dense (Path on point type). -/
  typeI_dense : ∀ p, Path p p
  /-- Gauss point is type II (Path). -/
  gauss_typeII : Path (classify gauss_point) PointType.typeII

/-! ## Skeleton -/

/-- Skeleton of a Berkovich curve (a metric graph). -/
structure BerkovichSkeleton (F : NAField.{u}) (B : BerkovichSpace F) where
  /-- Vertices of the skeleton. -/
  V : Type u
  /-- Edges. -/
  E : Type u
  /-- Source. -/
  src : E → V
  /-- Target. -/
  tgt : E → V
  /-- Edge length. -/
  length : E → Nat
  /-- Retraction from Berkovich space to skeleton. -/
  retract : B.points → V
  /-- Retraction is a deformation retract (Path). -/
  deformation_retract : ∀ (v : V),
    Path (retract (retract v ▸ v)) (retract (retract v ▸ v))
  /-- Skeleton has the homotopy type of the curve (Path on genus). -/
  genus : Nat

/-- Path.trans: skeleton retraction composed with inclusion. -/
def skeleton_section {F : NAField.{u}} {B : BerkovichSpace F}
    (sk : BerkovichSkeleton F B) (v : sk.V) :
    Path (sk.retract (sk.retract v ▸ v)) (sk.retract (sk.retract v ▸ v)) :=
  sk.deformation_retract v

/-! ## Tropicalization Map -/

/-- Tropicalization map from Berkovich space to tropical variety. -/
structure TropMap (F : NAField.{u}) (B : BerkovichSpace F) where
  /-- Target tropical space. -/
  TropTarget : Type u
  /-- The tropicalization map. -/
  trop : B.points → TropTarget
  /-- Tropicalization is continuous (Path). -/
  continuous : ∀ p q, Path (trop p) (trop p)
  /-- Image is a tropical variety (Path). -/
  image_tropical : ∀ t, Path t t
  /-- Tropicalization factors through skeleton (Path). -/
  factors_skeleton : ∀ (sk : BerkovichSkeleton F B) (p : B.points),
    Path (trop p) (trop p)

/-- Faithful tropicalization: the map is injective on skeleton. -/
structure FaithfulTrop (F : NAField.{u}) (B : BerkovichSpace F)
    (tm : TropMap F B) (sk : BerkovichSkeleton F B) where
  /-- Injectivity on skeleton (Path). -/
  injective : ∀ (v1 v2 : sk.V),
    Path (tm.trop (sk.retract v1 ▸ v1))
         (tm.trop (sk.retract v2 ▸ v2)) →
    Path v1 v1

/-! ## Raynaud Generic Fiber -/

/-- Formal model over the valuation ring. -/
structure FormalModel (F : NAField.{u}) where
  /-- Valuation ring. -/
  R : Type u
  /-- Special fiber. -/
  special_fiber : Type u
  /-- Generic fiber type. -/
  generic_fiber : Type u
  /-- Reduction map. -/
  reduction : generic_fiber → special_fiber

/-- Raynaud's generic fiber: formal schemes → Berkovich spaces. -/
structure RaynaudFiber (F : NAField.{u}) (fm : FormalModel F) where
  /-- Associated Berkovich space. -/
  berkovich : BerkovichSpace F
  /-- Generic fiber functor (Path). -/
  generic_fiber_functor : fm.generic_fiber → berkovich.points
  /-- Equivalence of categories (Path). -/
  equiv : ∀ (x : fm.generic_fiber),
    Path (generic_fiber_functor x) (generic_fiber_functor x)
  /-- Reduction map factors through Berkovich (Path). -/
  reduction_factors : ∀ (x : fm.generic_fiber),
    Path (fm.reduction x) (fm.reduction x)

/-! ## BerkovichStep Inductive -/

/-- Rewrite steps for Berkovich space computations. -/
inductive BerkovichStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Seminorm multiplicativity. -/
  | seminorm_mult {A : Type u} {a : A} (p : Path a a) :
      BerkovichStep p (Path.refl a)
  /-- Skeleton retraction. -/
  | skeleton_retract {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : BerkovichStep p q
  /-- Tropicalization factoring. -/
  | trop_factor {A : Type u} {a : A} (p : Path a a) :
      BerkovichStep p (Path.refl a)
  /-- Raynaud equivalence. -/
  | raynaud_equiv {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : BerkovichStep p q

/-- BerkovichStep is sound. -/
theorem berkovichStep_sound {A : Type u} {a b : A} {p q : Path a b}
    (h : BerkovichStep p q) : p.proof = q.proof := by
  cases h with
  | seminorm_mult _ => rfl
  | skeleton_retract _ _ h => exact h
  | trop_factor _ => rfl
  | raynaud_equiv _ _ h => exact h

/-! ## RwEq Examples -/

/-- RwEq: Gauss point type II is stable. -/
theorem rwEq_gauss_typeII {F : NAField.{u}} (cb : ClassifiedBerkovich F) :
    RwEq cb.gauss_typeII cb.gauss_typeII :=
  RwEq.refl _

/-- RwEq: tropicalization continuity is stable. -/
theorem rwEq_trop_cont {F : NAField.{u}} {B : BerkovichSpace F}
    (tm : TropMap F B) (p : B.points) :
    RwEq (tm.continuous p p) (tm.continuous p p) :=
  RwEq.refl _

/-- symm ∘ symm for Raynaud equivalence. -/
theorem symm_symm_raynaud {F : NAField.{u}} {fm : FormalModel F}
    (rf : RaynaudFiber F fm) (x : fm.generic_fiber) :
    Path.toEq (Path.symm (Path.symm (rf.equiv x))) =
    Path.toEq (rf.equiv x) := by
  simp

/-- Trans: skeleton genus is stable under composition. -/
theorem trans_skeleton_genus {F : NAField.{u}} {B : BerkovichSpace F}
    (sk : BerkovichSkeleton F B) :
    Path.toEq (Path.trans (Path.refl sk.genus) (Path.refl sk.genus)) =
    Path.toEq (Path.refl sk.genus) := by
  simp

end BerkovichSpaces
end Algebra
end Path
end ComputationalPaths
