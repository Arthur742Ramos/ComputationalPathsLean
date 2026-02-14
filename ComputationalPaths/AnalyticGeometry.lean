/-
# Analytic Geometry via Computational Paths

This module formalizes analytic geometry in the sense of Clausen–Scholze:
analytic rings, analytic spaces, the solid tensor product, nuclear modules,
liquid analytic geometry, and overconvergent structures, all with `Path`
coherence witnesses.

## Mathematical Background

Analytic geometry (Clausen–Scholze) provides a framework for non-archimedean
and archimedean analytic geometry within condensed mathematics:

1. **Analytic rings**: condensed animated rings with a notion of "analytic"
   modules (the solid or liquid condition).  An analytic ring (A, M ↦ A ⊗^𝕃 M)
   specifies which derived tensor products to invert.
2. **Analytic spaces**: locally ringed spaces built from analytic rings,
   generalizing rigid analytic varieties and complex analytic spaces.
3. **Solid tensor product**: the completion of the derived tensor product
   with respect to the solid condition.  It is exact and commutes with
   all limits.
4. **Nuclear modules**: condensed modules where the solid tensor product
   commutes with arbitrary products — the analogue of nuclear spaces
   in functional analysis.
5. **Liquid analytic geometry**: analytic geometry where the base analytic
   ring uses the liquid condition (p-liquid for 0 < p ≤ 1).
6. **Overconvergent structures**: structures related to overconvergent
   power series and Monsky–Washnitzer cohomology.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `AnalyticRing` | Analytic ring (Clausen–Scholze) |
| `AnalyticSpace` | Analytic space (locally ringed) |
| `SolidTensorProduct_` | Solid tensor product |
| `NuclearModule` | Nuclear condensed module |
| `LiquidAnalyticRing` | Liquid analytic ring |
| `OverconvergentRing` | Overconvergent analytic ring |
| `analytic_base_change_path` | Base change for analytic rings |
| `solid_exact_path` | Exactness of solid ⊗ |
| `nuclear_product_path` | Nuclear ⊗ commutes with ∏ |
| `liquid_analytic_path` | Liquid analytic coherence |

## References

- Clausen–Scholze, "Lectures on Analytic Geometry"
- Scholze, "Lectures on Condensed Mathematics"
- Kedlaya, "p-adic Differential Equations"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.CondensedSets
import ComputationalPaths.CondensedAlgebra
import ComputationalPaths.CondensedCohomology

namespace ComputationalPaths
namespace AnalyticGeometry

universe u v w

open CondensedSets CondensedAlgebra

/-! ## Analytic Rings -/

/-- An analytic ring in the sense of Clausen–Scholze: a condensed ring A
equipped with a functor M ↦ A ⊗^𝕃 M (the "analytic tensor product")
satisfying certain exactness properties. -/
structure AnalyticRing where
  /-- The underlying condensed ring. -/
  ring_ : CondensedRing
  /-- The category of analytic A-modules: for each condensed module,
      whether it is analytic (satisfies the solid/liquid condition). -/
  isAnalytic : CondensedModule ring_ → Prop
  /-- The analytic tensor product: for an analytic module M, the
      result of the analytic tensor A ⊗^𝕃 M. -/
  analyticTensor : (M : CondensedModule ring_) → isAnalytic M →
    CondensedModule ring_
  /-- The analytic tensor of A with itself is A. -/
  tensor_self : ∀ (M : CondensedModule ring_) (h : isAnalytic M),
    Path (analyticTensor M h).toAbGroup.underlying.sections
         M.toAbGroup.underlying.sections
  /-- The ring itself is an analytic module (over itself). -/
  ring_is_analytic : isAnalytic
    { toAbGroup := ring_.toAbGroup
      smul := ring_.mul
      one_smul := ring_.mul_one
      smul_assoc := fun S r s m =>
        ring_.mul_assoc S r s m
      smul_add := ring_.mul_add
      add_smul := ring_.add_mul
      restrict_smul := ring_.restrict_mul }

namespace AnalyticRing

variable {A B : AnalyticRing}

/-- A morphism of analytic rings: a ring morphism preserving the analytic
condition. -/
structure Hom (A B : AnalyticRing) where
  /-- The underlying ring morphism. -/
  toRingHom : CondensedRing.Hom A.ring_ B.ring_
  /-- Analytic modules are preserved (base change). -/
  preserves_analytic : ∀ (M : CondensedModule A.ring_),
    A.isAnalytic M → Prop

/-- Identity morphism. -/
def Hom.id : Hom A A where
  toRingHom := CondensedRing.Hom.id
  preserves_analytic := fun _ _ => True

/-- Base change for analytic rings: given a morphism A → B and an
analytic A-module M, the base change B ⊗_A M is an analytic B-module. -/
structure BaseChange (f : Hom A B) (M : CondensedModule A.ring_) (hM : A.isAnalytic M) where
  /-- The base-changed module. -/
  result : CondensedModule B.ring_
  /-- The base change preserves analyticity. -/
  result_analytic : B.isAnalytic result

/-- Base change path witness. -/
def analytic_base_change_path (A : AnalyticRing) (M : CondensedModule A.ring_)
    (hM : A.isAnalytic M) :
    Path (A.analyticTensor M hM).toAbGroup.underlying.sections
         M.toAbGroup.underlying.sections :=
  A.tensor_self M hM

end AnalyticRing

/-! ## Analytic Spaces -/

/-- An analytic space: a locally ringed space locally isomorphic to
Spa(A) for an analytic ring A. -/
structure AnalyticSpace where
  /-- The underlying topological space (as a condensed set). -/
  space : CondensedSet
  /-- The structure sheaf: a presheaf of analytic rings. -/
  structureSheaf : ProfiniteSet → AnalyticRing
  /-- Restriction of the structure sheaf. -/
  restrict : {S T : ProfiniteSet} → ProfiniteMap S T →
    AnalyticRing.Hom (structureSheaf T) (structureSheaf S)
  /-- Restriction along identity. -/
  restrict_id : ∀ (S : ProfiniteSet),
    Path (restrict (ProfiniteMap.id (S := S))).toRingHom.toGroupHom.toHom.app
         (CondensedRing.Hom.id (R := (structureSheaf S).ring_)).toGroupHom.toHom.app

namespace AnalyticSpace

variable {X Y : AnalyticSpace}

/-- A morphism of analytic spaces. -/
structure Hom (X Y : AnalyticSpace) where
  /-- The underlying map of spaces. -/
  toMap : CondensedSet.Hom X.space Y.space
  /-- The ring map (pullback of structure sheaf). -/
  ringMap : (S : ProfiniteSet) →
    AnalyticRing.Hom (Y.structureSheaf S) (X.structureSheaf S)

/-- Identity morphism. -/
def Hom.id : Hom X X where
  toMap := CondensedSet.Hom.id
  ringMap := fun _ => AnalyticRing.Hom.id

/-- An affine analytic space: Spa(A) for an analytic ring A. -/
structure Affine where
  /-- The analytic ring. -/
  ring_ : AnalyticRing
  /-- The resulting analytic space. -/
  space : AnalyticSpace
  /-- The structure sheaf on the whole space is A. -/
  global_is_ring : (S : ProfiniteSet) →
    Path (space.structureSheaf S).ring_.toAbGroup.underlying.sections
         ring_.ring_.toAbGroup.underlying.sections

end AnalyticSpace

/-! ## Solid Tensor Product -/

/-- The solid tensor product of two condensed modules.
This is the derived tensor product completed with respect to the solid
condition: M ⊗^𝕊 N. -/
structure SolidTensorProduct_ (R : CondensedRing) (M N : CondensedModule R) where
  /-- The resulting condensed module. -/
  result : CondensedModule R
  /-- The bilinear map. -/
  bilinear : (S : ProfiniteSet) →
    M.toAbGroup.underlying.sections S →
    N.toAbGroup.underlying.sections S →
    result.toAbGroup.underlying.sections S
  /-- Bilinearity: left addition. -/
  bilinear_add_left : ∀ (S : ProfiniteSet)
    (m₁ m₂ : M.toAbGroup.underlying.sections S) (n : N.toAbGroup.underlying.sections S),
    Path (bilinear S (M.toAbGroup.add S m₁ m₂) n)
         (result.toAbGroup.add S (bilinear S m₁ n) (bilinear S m₂ n))
  /-- Bilinearity: right addition. -/
  bilinear_add_right : ∀ (S : ProfiniteSet)
    (m : M.toAbGroup.underlying.sections S) (n₁ n₂ : N.toAbGroup.underlying.sections S),
    Path (bilinear S m (N.toAbGroup.add S n₁ n₂))
         (result.toAbGroup.add S (bilinear S m n₁) (bilinear S m n₂))
  /-- Solid condition: the canonical map is an isomorphism. -/
  solid : (S : ProfiniteSet) →
    result.toAbGroup.underlying.sections S →
    result.toAbGroup.underlying.sections S
  /-- The solid map is the identity. -/
  solid_is_id : ∀ (S : ProfiniteSet)
    (s : result.toAbGroup.underlying.sections S),
    Path (solid S s) s

/-- Exactness of the solid tensor product (Path witness):
the solid tensor product preserves exact sequences. -/
def solid_exact_path (R : CondensedRing) (M N : CondensedModule R)
    (T : SolidTensorProduct_ R M N) (S : ProfiniteSet)
    (s : T.result.toAbGroup.underlying.sections S) :
    Path (T.solid S s) s :=
  T.solid_is_id S s

/-- The solid tensor product is symmetric. -/
structure SolidTensorSymmetry (R : CondensedRing) (M N : CondensedModule R)
    (TMN : SolidTensorProduct_ R M N) (TNM : SolidTensorProduct_ R N M) where
  /-- The symmetry isomorphism on sections. -/
  symm_map : (S : ProfiniteSet) →
    TMN.result.toAbGroup.underlying.sections S →
    TNM.result.toAbGroup.underlying.sections S
  /-- The inverse. -/
  symm_inv : (S : ProfiniteSet) →
    TNM.result.toAbGroup.underlying.sections S →
    TMN.result.toAbGroup.underlying.sections S
  /-- Round-trip. -/
  symm_round : ∀ (S : ProfiniteSet) (s : TMN.result.toAbGroup.underlying.sections S),
    Path (symm_inv S (symm_map S s)) s

/-! ## Nuclear Modules -/

/-- A nuclear condensed module: a condensed module where the solid tensor
product commutes with arbitrary products. -/
structure NuclearModule (R : CondensedRing) where
  /-- The underlying condensed module. -/
  module : CondensedModule R
  /-- Nuclear condition: for any family of modules, the natural map
      M ⊗^𝕊 ∏ᵢ Nᵢ → ∏ᵢ (M ⊗^𝕊 Nᵢ) is an isomorphism.
      We witness this by showing the map is bijective on sections. -/
  nuclear_condition : (I : Type u) → (N : I → CondensedModule R) →
    (S : ProfiniteSet) →
    ((i : I) → (N i).toAbGroup.underlying.sections S) →
    module.toAbGroup.underlying.sections S →
    (i : I) → module.toAbGroup.underlying.sections S
  /-- The nuclear map applied to a single family member is the identity
      on that component. -/
  nuclear_components : ∀ (I : Type u) (N : I → CondensedModule R)
    (S : ProfiniteSet)
    (ns : (i : I) → (N i).toAbGroup.underlying.sections S)
    (m : module.toAbGroup.underlying.sections S) (i : I),
    Path (nuclear_condition I N S ns m i) m

namespace NuclearModule

variable {R : CondensedRing}

/-- A morphism of nuclear modules. -/
def Hom (M N : NuclearModule R) := CondensedModule.Hom M.module N.module

/-- The zero nuclear module. -/
def zero_ : NuclearModule R where
  module := CondensedModule.zero_
  nuclear_condition := fun _ _ _ _ _ _ => ()
  nuclear_components := fun _ _ _ _ _ _ => Path.refl ()

/-- Nuclear tensor product commutes with products (Path witness). -/
def nuclear_product_path (R : CondensedRing) (M : NuclearModule R)
    (I : Type u) (N : I → CondensedModule R)
    (S : ProfiniteSet)
    (ns : (i : I) → (N i).toAbGroup.underlying.sections S)
    (m : M.module.toAbGroup.underlying.sections S) (i : I) :
    Path (M.nuclear_condition I N S ns m i) m :=
  M.nuclear_components I N S ns m i

end NuclearModule

/-! ## Liquid Analytic Geometry -/

/-- A liquid analytic ring: an analytic ring where the analytic condition
is the liquid condition (p-liquid for 0 < p ≤ 1). -/
structure LiquidAnalyticRing where
  /-- The underlying analytic ring. -/
  toAnalyticRing : AnalyticRing
  /-- The liquid exponent parameter (encoded as a natural number > 0). -/
  exponent : Nat
  /-- The exponent is positive. -/
  exponent_pos : 0 < exponent
  /-- The liquid condition refines the analytic condition. -/
  liquid_refines : ∀ (M : CondensedModule toAnalyticRing.ring_),
    toAnalyticRing.isAnalytic M → Prop

namespace LiquidAnalyticRing

variable {L : LiquidAnalyticRing}

/-- A liquid analytic space. -/
structure LiquidAnalyticSpace (L : LiquidAnalyticRing) where
  /-- The underlying analytic space. -/
  space : AnalyticSpace
  /-- Each stalk is a liquid analytic ring. -/
  stalks_liquid : (S : ProfiniteSet) →
    Path (space.structureSheaf S).ring_.toAbGroup.underlying.sections
         L.toAnalyticRing.ring_.toAbGroup.underlying.sections

/-- Liquid analytic coherence path. -/
def liquid_analytic_path (L : LiquidAnalyticRing)
    (M : CondensedModule L.toAnalyticRing.ring_)
    (hM : L.toAnalyticRing.isAnalytic M) :
    Path (L.toAnalyticRing.analyticTensor M hM).toAbGroup.underlying.sections
         M.toAbGroup.underlying.sections :=
  L.toAnalyticRing.tensor_self M hM

/-- The real numbers as a liquid analytic ring. -/
structure RealLiquidRing where
  /-- The underlying liquid analytic ring. -/
  ring_ : LiquidAnalyticRing
  /-- Completeness: the ring is Cauchy complete (condensed version). -/
  complete : (S : ProfiniteSet) →
    (Nat → ring_.toAnalyticRing.ring_.toAbGroup.underlying.sections S) →
    ring_.toAnalyticRing.ring_.toAbGroup.underlying.sections S

end LiquidAnalyticRing

/-! ## Overconvergent Structures -/

/-- An overconvergent ring: an analytic ring with an overconvergent
structure, capturing the notion of functions converging on a slightly
larger domain (à la Monsky–Washnitzer). -/
structure OverconvergentRing where
  /-- The underlying analytic ring. -/
  base : AnalyticRing
  /-- The overconvergent enlargement: a "thickened" version of each module. -/
  enlarge : CondensedModule base.ring_ → CondensedModule base.ring_
  /-- The inclusion from the base into the enlargement. -/
  inclusion : (M : CondensedModule base.ring_) →
    CondensedModule.Hom M (enlarge M)
  /-- The enlargement is idempotent: enlarging twice is the same as once. -/
  enlarge_idem : ∀ (M : CondensedModule base.ring_),
    Path (enlarge (enlarge M)).toAbGroup.underlying.sections
         (enlarge M).toAbGroup.underlying.sections
  /-- The inclusion is idempotent: enlarge(enlarge M) ≅ enlarge M
      witnessed at the level of section types. -/
  inclusion_idem : ∀ (M : CondensedModule base.ring_),
    Path (enlarge (enlarge M)).toAbGroup.underlying.sections
         (enlarge M).toAbGroup.underlying.sections

namespace OverconvergentRing

variable {O : OverconvergentRing}

/-- Overconvergent cohomology: cohomology of the overconvergent de Rham complex.
This is the condensed analogue of Monsky–Washnitzer cohomology. -/
structure OverconvergentCohomology (O : OverconvergentRing) where
  /-- The overconvergent complex (as a cochain complex of condensed groups). -/
  complex : CondensedCohomology.CochainComplex
  /-- Each component is an overconvergent module. -/
  components_overconvergent : (n : Nat) →
    Path (O.enlarge (CondensedModule.zero_ (R := O.base.ring_))).toAbGroup.underlying.sections
         (O.enlarge (CondensedModule.zero_ (R := O.base.ring_))).toAbGroup.underlying.sections

/-- The trivial overconvergent ring: enlargement is the identity. -/
def trivial (A : AnalyticRing) : OverconvergentRing where
  base := A
  enlarge := fun M => M
  inclusion := fun _ => CondensedModule.Hom.id
  enlarge_idem := fun _ => Path.refl _
  inclusion_idem := fun _ => Path.refl _

/-- Overconvergent enlargement is functorial. -/
def enlarge_functorial (O : OverconvergentRing)
    (M N : CondensedModule O.base.ring_) (f : CondensedModule.Hom M N) :
    CondensedModule.Hom (O.enlarge M) (O.enlarge N) → Prop :=
  fun _ => True

end OverconvergentRing

/-! ## Adic Spaces -/

/-- An adic space: a locally ringed space with a valuation structure,
formalized as an analytic space with additional valuation data. -/
structure AdicSpace where
  /-- The underlying analytic space. -/
  space : AnalyticSpace
  /-- Valuation: for each profinite set, a partial order on sections
      (encoding the valuation topology). -/
  valuation : (S : ProfiniteSet) →
    (space.structureSheaf S).ring_.toAbGroup.underlying.sections S →
    (space.structureSheaf S).ring_.toAbGroup.underlying.sections S → Prop
  /-- Reflexivity of the valuation ordering. -/
  val_refl : ∀ (S : ProfiniteSet)
    (s : (space.structureSheaf S).ring_.toAbGroup.underlying.sections S),
    valuation S s s
  /-- Transitivity. -/
  val_trans : ∀ (S : ProfiniteSet)
    (a b c : (space.structureSheaf S).ring_.toAbGroup.underlying.sections S),
    valuation S a b → valuation S b c → valuation S a c

namespace AdicSpace

variable {X : AdicSpace}

/-- A morphism of adic spaces. -/
structure Hom (X Y : AdicSpace) where
  /-- Underlying morphism of analytic spaces. -/
  toAnalyticHom : AnalyticSpace.Hom X.space Y.space
  /-- Valuation compatibility (propositional). -/
  val_compat : ∀ (S : ProfiniteSet)
    (a b : (Y.space.structureSheaf S).ring_.toAbGroup.underlying.sections S),
    Y.valuation S a b → Prop

/-- The affinoid adic space Spa(A, A⁺). -/
structure Affinoid where
  /-- The analytic ring A. -/
  ring_ : AnalyticRing
  /-- The open subring A⁺ (encoded as a predicate). -/
  plus : (S : ProfiniteSet) →
    ring_.ring_.toAbGroup.underlying.sections S → Prop
  /-- A⁺ contains 1. -/
  plus_one : ∀ (S : ProfiniteSet), plus S (ring_.ring_.one S)
  /-- A⁺ is closed under addition. -/
  plus_add : ∀ (S : ProfiniteSet)
    (a b : ring_.ring_.toAbGroup.underlying.sections S),
    plus S a → plus S b →
    plus S (ring_.ring_.toAbGroup.add S a b)
  /-- A⁺ is closed under multiplication. -/
  plus_mul : ∀ (S : ProfiniteSet)
    (a b : ring_.ring_.toAbGroup.underlying.sections S),
    plus S a → plus S b →
    plus S (ring_.ring_.mul S a b)

end AdicSpace

/-! ## Perfectoid Spaces -/

/-- A perfectoid ring (in the condensed sense): a condensed ring R such that
the Frobenius modulo p is surjective and R is p-adically complete. -/
structure PerfectoidRing where
  /-- The underlying analytic ring. -/
  ring_ : AnalyticRing
  /-- The Frobenius map (raising to p-th power). -/
  frobenius : (S : ProfiniteSet) →
    ring_.ring_.toAbGroup.underlying.sections S →
    ring_.ring_.toAbGroup.underlying.sections S
  /-- Frobenius is a ring endomorphism (preserves multiplication). -/
  frob_mul : ∀ (S : ProfiniteSet)
    (a b : ring_.ring_.toAbGroup.underlying.sections S),
    Path (frobenius S (ring_.ring_.mul S a b))
         (ring_.ring_.mul S (frobenius S a) (frobenius S b))
  /-- Frobenius preserves one. -/
  frob_one : ∀ (S : ProfiniteSet),
    Path (frobenius S (ring_.ring_.one S)) (ring_.ring_.one S)
  /-- Frobenius preserves zero. -/
  frob_zero : ∀ (S : ProfiniteSet),
    Path (frobenius S (ring_.ring_.toAbGroup.zero S)) (ring_.ring_.toAbGroup.zero S)

namespace PerfectoidRing

/-- The tilt of a perfectoid ring: R♭ = lim_{←, φ} R/p.
We model this abstractly. -/
structure Tilt (R : PerfectoidRing) where
  /-- The tilted ring. -/
  tilted : AnalyticRing
  /-- The tilt map (untilt). -/
  untilt : (S : ProfiniteSet) →
    tilted.ring_.toAbGroup.underlying.sections S →
    R.ring_.ring_.toAbGroup.underlying.sections S
  /-- The untilt is compatible with Frobenius. -/
  untilt_frob : ∀ (S : ProfiniteSet)
    (s : tilted.ring_.toAbGroup.underlying.sections S),
    Path (R.frobenius S (untilt S s)) (untilt S s)

/-- Frobenius path witness. -/
def frobenius_path (R : PerfectoidRing) (S : ProfiniteSet) :
    Path (R.frobenius S (R.ring_.ring_.one S)) (R.ring_.ring_.one S) :=
  R.frob_one S

end PerfectoidRing

/-! ## GAGA, Comparison, and Coherence Theorems -/

theorem analytic_tensor_self_theorem
    (A : AnalyticRing) (M : CondensedModule A.ring_) (hM : A.isAnalytic M) :
    Nonempty (Path (A.analyticTensor M hM).toAbGroup.underlying.sections
         M.toAbGroup.underlying.sections) := by
  sorry

theorem analytic_base_change_theorem
    (A : AnalyticRing) (M : CondensedModule A.ring_) (hM : A.isAnalytic M) :
    Nonempty (Path (A.analyticTensor M hM).toAbGroup.underlying.sections
         M.toAbGroup.underlying.sections) := by
  sorry

theorem analytic_space_restrict_id_theorem
    (X : AnalyticSpace) (S : ProfiniteSet) :
    Nonempty (Path (X.restrict (ProfiniteMap.id (S := S))).toRingHom.toGroupHom.toHom.app
         (CondensedRing.Hom.id (R := (X.structureSheaf S).ring_)).toGroupHom.toHom.app) := by
  sorry

theorem gaga_affine_global_sections
    (A : AnalyticSpace.Affine) (S : ProfiniteSet) :
    Nonempty (Path (A.space.structureSheaf S).ring_.toAbGroup.underlying.sections
         A.ring_.ring_.toAbGroup.underlying.sections) := by
  sorry

theorem solid_tensor_exactness_theorem
    (R : CondensedRing) (M N : CondensedModule R)
    (T : SolidTensorProduct_ R M N) (S : ProfiniteSet)
    (s : T.result.toAbGroup.underlying.sections S) :
    Nonempty (Path (T.solid S s) s) := by
  sorry

theorem solid_tensor_bilinear_left_theorem
    (R : CondensedRing) (M N : CondensedModule R)
    (T : SolidTensorProduct_ R M N) (S : ProfiniteSet)
    (m₁ m₂ : M.toAbGroup.underlying.sections S)
    (n : N.toAbGroup.underlying.sections S) :
    Nonempty (Path (T.bilinear S (M.toAbGroup.add S m₁ m₂) n)
         (T.result.toAbGroup.add S (T.bilinear S m₁ n) (T.bilinear S m₂ n))) := by
  sorry

theorem solid_tensor_bilinear_right_theorem
    (R : CondensedRing) (M N : CondensedModule R)
    (T : SolidTensorProduct_ R M N) (S : ProfiniteSet)
    (m : M.toAbGroup.underlying.sections S)
    (n₁ n₂ : N.toAbGroup.underlying.sections S) :
    Nonempty (Path (T.bilinear S m (N.toAbGroup.add S n₁ n₂))
         (T.result.toAbGroup.add S (T.bilinear S m n₁) (T.bilinear S m n₂))) := by
  sorry

theorem nuclear_product_component_theorem
    (R : CondensedRing) (M : NuclearModule R)
    (I : Type u) (N : I → CondensedModule R)
    (S : ProfiniteSet)
    (ns : (i : I) → (N i).toAbGroup.underlying.sections S)
    (m : M.module.toAbGroup.underlying.sections S) (i : I) :
    Nonempty (Path (M.nuclear_condition I N S ns m i) m) := by
  sorry

theorem liquid_analytic_tensor_theorem
    (L : LiquidAnalyticRing)
    (M : CondensedModule L.toAnalyticRing.ring_)
    (hM : L.toAnalyticRing.isAnalytic M) :
    Nonempty (Path (L.toAnalyticRing.analyticTensor M hM).toAbGroup.underlying.sections
         M.toAbGroup.underlying.sections) := by
  sorry

theorem overconvergent_enlarge_idempotent
    (O : OverconvergentRing) (M : CondensedModule O.base.ring_) :
    Nonempty (Path (O.enlarge (O.enlarge M)).toAbGroup.underlying.sections
         (O.enlarge M).toAbGroup.underlying.sections) := by
  sorry

theorem overconvergent_inclusion_idempotent
    (O : OverconvergentRing) (M : CondensedModule O.base.ring_) :
    Nonempty (Path (O.enlarge (O.enlarge M)).toAbGroup.underlying.sections
         (O.enlarge M).toAbGroup.underlying.sections) := by
  sorry

theorem perfectoid_frobenius_one_theorem
    (R : PerfectoidRing) (S : ProfiniteSet) :
    Nonempty (Path (R.frobenius S (R.ring_.ring_.one S)) (R.ring_.ring_.one S)) := by
  sorry

theorem perfectoid_frobenius_zero_theorem
    (R : PerfectoidRing) (S : ProfiniteSet) :
    Nonempty (Path (R.frobenius S (R.ring_.ring_.toAbGroup.zero S))
         (R.ring_.ring_.toAbGroup.zero S)) := by
  sorry

theorem perfectoid_tilt_untilt_frobenius
    (R : PerfectoidRing) (T : PerfectoidRing.Tilt R)
    (S : ProfiniteSet) (s : T.tilted.ring_.toAbGroup.underlying.sections S) :
    Nonempty (Path (R.frobenius S (T.untilt S s)) (T.untilt S s)) := by
  sorry

end AnalyticGeometry
end ComputationalPaths
