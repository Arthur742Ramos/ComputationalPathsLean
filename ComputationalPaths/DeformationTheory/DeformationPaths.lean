import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Deformation.PathInfrastructure

/-!
# Formal deformations of path structures

This module formalises **formal deformations** of computational-path structures:

* `FormalDeformationData` — an algebraic structure carrying a base point,
  a family of deformed operations parametrised by a formal parameter, and
  path-preserving witnesses for each operation.
* `MaurerCartanViaPaths` — the Maurer-Cartan equation expressed as a
  computational-path equation `d α + ½[α,α] = 0`, with the equality
  witnessed by an explicit `Path`, not a propositional assertion.
* `DeformationFunctor` — the deformation functor from Artinian path data
  to sets of Maurer-Cartan elements, with path-preserving functoriality.
* `GaugeEquivalenceData` — gauge transformations between Maurer-Cartan
  solutions, recorded as paths in the deformation space.

Throughout, every algebraic identity is a `Path`, and every coherence
condition is a `RwEq` between paths.
-/

namespace ComputationalPaths
namespace DeformationTheory

open Path

universe u v

/-! ## Formal deformation data -/

/-- A formal deformation of a path-algebraic structure.

The `base` field records the undeformed algebra, `deformed` records the
formal-parameter family, and the compatibility paths witness that setting
the parameter to zero recovers the base. -/
structure FormalDeformationData (A : Type u) where
  /-- Base (undeformed) zero element. -/
  zero : A
  /-- Addition in the base algebra. -/
  add : A → A → A
  /-- Differential / derivation in the base algebra. -/
  diff : A → A
  /-- Lie bracket in the base algebra. -/
  bracket : A → A → A
  /-- Deformed addition, parametrised by a formal element `t : A`. -/
  addDef : A → A → A → A
  /-- Deformed bracket, parametrised by `t : A`. -/
  bracketDef : A → A → A → A
  /-- Path-functoriality of `add`. -/
  addPath :
    {x₁ x₂ y₁ y₂ : A} →
      Path x₁ x₂ → Path y₁ y₂ →
        Path (add x₁ y₁) (add x₂ y₂)
  /-- Path-functoriality of `diff`. -/
  diffPath : {x y : A} → Path x y → Path (diff x) (diff y)
  /-- Path-functoriality of `bracket`. -/
  bracketPath :
    {x₁ x₂ y₁ y₂ : A} →
      Path x₁ x₂ → Path y₁ y₂ →
        Path (bracket x₁ y₁) (bracket x₂ y₂)
  /-- Path-functoriality of the deformed addition. -/
  addDefPath :
    {t₁ t₂ x₁ x₂ y₁ y₂ : A} →
      Path t₁ t₂ → Path x₁ x₂ → Path y₁ y₂ →
        Path (addDef t₁ x₁ y₁) (addDef t₂ x₂ y₂)
  /-- Path-functoriality of the deformed bracket. -/
  bracketDefPath :
    {t₁ t₂ x₁ x₂ y₁ y₂ : A} →
      Path t₁ t₂ → Path x₁ x₂ → Path y₁ y₂ →
        Path (bracketDef t₁ x₁ y₁) (bracketDef t₂ x₂ y₂)
  /-- At `t = zero`, the deformed addition reduces to the base addition. -/
  addDefBase : ∀ x y : A, Path (addDef zero x y) (add x y)
  /-- At `t = zero`, the deformed bracket reduces to the base bracket. -/
  bracketDefBase : ∀ x y : A, Path (bracketDef zero x y) (bracket x y)

namespace FormalDeformationData

variable {A : Type u} (D : FormalDeformationData A)

/-- The base-point recovery path for addition is rewrite-cancelable. -/
@[simp] theorem addDefBaseCancelLeft (x y : A) :
    RwEq
      (Path.trans (Path.symm (D.addDefBase x y)) (D.addDefBase x y))
      (Path.refl (D.add x y)) :=
  rweq_cmpA_inv_left (D.addDefBase x y)

/-- The base-point recovery path for bracket is rewrite-cancelable. -/
@[simp] theorem bracketDefBaseCancelLeft (x y : A) :
    RwEq
      (Path.trans (Path.symm (D.bracketDefBase x y)) (D.bracketDefBase x y))
      (Path.refl (D.bracket x y)) :=
  rweq_cmpA_inv_left (D.bracketDefBase x y)

/-- Symmetry of the base-recovery path for the deformed addition. -/
@[simp] theorem addDefBaseCancelRight (x y : A) :
    RwEq
      (Path.trans (D.addDefBase x y) (Path.symm (D.addDefBase x y)))
      (Path.refl (D.addDef D.zero x y)) :=
  rweq_cmpA_inv_right (D.addDefBase x y)

/-- Symmetry of the base-recovery path for the deformed bracket. -/
@[simp] theorem bracketDefBaseCancelRight (x y : A) :
    RwEq
      (Path.trans (D.bracketDefBase x y) (Path.symm (D.bracketDefBase x y)))
      (Path.refl (D.bracketDef D.zero x y)) :=
  rweq_cmpA_inv_right (D.bracketDefBase x y)

end FormalDeformationData

/-! ## Maurer-Cartan equation via paths -/

/-- Maurer-Cartan curvature in a formal deformation:
`curv(α) = diff(α) + bracket(α, α)`. -/
def formalCurvature {A : Type u} (D : FormalDeformationData A) (α : A) : A :=
  D.add (D.diff α) (D.bracket α α)

/-- A Maurer-Cartan element in a formal deformation is an element `α`
together with an explicit computational path witnessing
`diff(α) + [α,α] = 0`. -/
structure MaurerCartanViaPaths {A : Type u} (D : FormalDeformationData A) where
  element : A
  equation : Path (formalCurvature D element) D.zero

namespace MaurerCartanViaPaths

variable {A : Type u} {D : FormalDeformationData A}

/-- Primitive normalization: appending refl on the right is removable. -/
def equationStep (mc : MaurerCartanViaPaths D) :
    Path.Step (Path.trans mc.equation (Path.refl D.zero)) mc.equation :=
  Path.Step.trans_refl_right mc.equation

@[simp] theorem equationRweq (mc : MaurerCartanViaPaths D) :
    RwEq (Path.trans mc.equation (Path.refl D.zero)) mc.equation :=
  rweq_of_step (equationStep mc)

@[simp] theorem equationCancelLeft (mc : MaurerCartanViaPaths D) :
    RwEq (Path.trans (Path.symm mc.equation) mc.equation) (Path.refl D.zero) :=
  rweq_cmpA_inv_left mc.equation

@[simp] theorem equationCancelRight (mc : MaurerCartanViaPaths D) :
    RwEq
      (Path.trans mc.equation (Path.symm mc.equation))
      (Path.refl (formalCurvature D mc.element)) :=
  rweq_cmpA_inv_right mc.equation

/-- Transport an MC solution along a path in the carrier. -/
def transportAlongPath (mc : MaurerCartanViaPaths D)
    {β : A} (p : Path mc.element β) :
    MaurerCartanViaPaths D where
  element := β
  equation :=
    Path.trans
      (D.addPath
        (D.diffPath (Path.symm p))
        (D.bracketPath (Path.symm p) (Path.symm p)))
      (Path.trans mc.equation (Path.refl D.zero))

/-- Normalization: the transported MC equation simplifies via trans_refl. -/
@[simp] theorem transportAlongPathRweq
    (mc : MaurerCartanViaPaths D) {β : A} (p : Path mc.element β) :
    RwEq
      (Path.trans (transportAlongPath mc p).equation (Path.refl D.zero))
      (transportAlongPath mc p).equation :=
  rweq_of_step (Path.Step.trans_refl_right _)

end MaurerCartanViaPaths

/-! ## Gauge equivalence -/

/-- Gauge transformation data: two MC solutions related by a gauge path. -/
structure GaugeEquivalenceData {A : Type u} (D : FormalDeformationData A)
    (mc₁ mc₂ : MaurerCartanViaPaths D) where
  /-- The gauge element performing the transformation. -/
  gauge : A
  /-- Path witnessing that the gauge sends `mc₁.element` to `mc₂.element`. -/
  action : Path mc₁.element mc₂.element
  /-- Coherence: the MC equations are compatible through the gauge,
      witnessed by a path between the curvature terms. -/
  coherence : Path (formalCurvature D mc₁.element) (formalCurvature D mc₂.element)
  /-- The coherence path composes correctly with the MC equations. -/
  equationCompat :
    RwEq
      (Path.trans coherence mc₂.equation)
      mc₁.equation

namespace GaugeEquivalenceData

variable {A : Type u} {D : FormalDeformationData A}
variable {mc₁ mc₂ mc₃ : MaurerCartanViaPaths D}

/-- Reflexive gauge equivalence: every MC element is gauge-equivalent to itself. -/
def refl (mc : MaurerCartanViaPaths D) : GaugeEquivalenceData D mc mc where
  gauge := D.zero
  action := Path.refl mc.element
  coherence := Path.refl (formalCurvature D mc.element)
  equationCompat :=
    rweq_of_step (Path.Step.trans_refl_left mc.equation)

/-- Inverse gauge: if `mc₁ ~ mc₂` then `mc₂ ~ mc₁`. -/
def symm (g : GaugeEquivalenceData D mc₁ mc₂) :
    GaugeEquivalenceData D mc₂ mc₁ where
  gauge := g.gauge
  action := Path.symm g.action
  coherence := Path.symm g.coherence
  equationCompat :=
    by
      have h₁ :
          RwEq (Path.trans (Path.symm g.coherence) mc₁.equation)
            (Path.trans (Path.symm g.coherence) (Path.trans g.coherence mc₂.equation)) :=
        rweq_trans_congr_right (Path.symm g.coherence) (rweq_symm g.equationCompat)
      have h₂ :
          RwEq
            (Path.trans (Path.symm g.coherence) (Path.trans g.coherence mc₂.equation))
            (Path.trans (Path.trans (Path.symm g.coherence) g.coherence) mc₂.equation) :=
        rweq_symm (rweq_tt (Path.symm g.coherence) g.coherence mc₂.equation)
      have h₃ :
          RwEq
            (Path.trans (Path.trans (Path.symm g.coherence) g.coherence) mc₂.equation)
            (Path.trans (Path.refl (formalCurvature D mc₂.element)) mc₂.equation) :=
        rweq_trans_congr_left mc₂.equation (rweq_cmpA_inv_left g.coherence)
      exact rweq_trans h₁
        (rweq_trans h₂
          (rweq_trans h₃ (rweq_cmpA_refl_left mc₂.equation)))

end GaugeEquivalenceData

/-! ## Deformation functors -/

/-- An Artinian path datum: a base-preserving map between formal deformation
structures. This models a morphism in the category of local Artinian
algebras, in the path-algebraic framework. -/
structure ArtinianMorphism {A : Type u} {B : Type v}
    (DA : FormalDeformationData A)
    (DB : FormalDeformationData B) where
  /-- Underlying map on carriers. -/
  f : A → B
  /-- Path-functoriality of `f`. -/
  mapPath : {x y : A} → Path x y → Path (f x) (f y)
  /-- Compatibility: `f` preserves addition up to path. -/
  preservesAdd : ∀ x y : A, Path (f (DA.add x y)) (DB.add (f x) (f y))
  /-- Compatibility: `f` preserves the differential up to path. -/
  preservesDiff : ∀ x : A, Path (f (DA.diff x)) (DB.diff (f x))
  /-- Compatibility: `f` preserves the bracket up to path. -/
  preservesBracket : ∀ x y : A, Path (f (DA.bracket x y)) (DB.bracket (f x) (f y))
  /-- Compatibility: `f` preserves zero up to path. -/
  preservesZero : Path (f DA.zero) DB.zero

namespace ArtinianMorphism

variable {A : Type u} {B : Type v}
variable {DA : FormalDeformationData A} {DB : FormalDeformationData B}

/-- An Artinian morphism maps MC elements to MC elements. -/
def mapMaurerCartan (φ : ArtinianMorphism DA DB)
    (mc : MaurerCartanViaPaths DA) :
    MaurerCartanViaPaths DB where
  element := φ.f mc.element
  equation :=
    Path.trans
      (DB.addPath
        (Path.symm (φ.preservesDiff mc.element))
        (Path.symm (φ.preservesBracket mc.element mc.element)))
      (Path.trans
        (Path.symm (φ.preservesAdd (DA.diff mc.element) (DA.bracket mc.element mc.element)))
        (Path.trans
          (φ.mapPath mc.equation)
          φ.preservesZero))

/-- Normalization step for mapped MC equations. -/
@[simp] theorem mapMaurerCartanRweq (φ : ArtinianMorphism DA DB)
    (mc : MaurerCartanViaPaths DA) :
    RwEq
      (Path.trans (φ.mapMaurerCartan mc).equation (Path.refl DB.zero))
      (φ.mapMaurerCartan mc).equation :=
  rweq_of_step (Path.Step.trans_refl_right _)

/-- Cancellation: the mapped MC equation is left-cancelable. -/
@[simp] theorem mapMaurerCartanCancelLeft (φ : ArtinianMorphism DA DB)
    (mc : MaurerCartanViaPaths DA) :
    RwEq
      (Path.trans
        (Path.symm (φ.mapMaurerCartan mc).equation)
        (φ.mapMaurerCartan mc).equation)
      (Path.refl DB.zero) :=
  rweq_cmpA_inv_left (φ.mapMaurerCartan mc).equation

end ArtinianMorphism

/-- Identity Artinian morphism. -/
def ArtinianMorphism.id {A : Type u} (DA : FormalDeformationData A) :
    ArtinianMorphism DA DA where
  f := _root_.id
  mapPath := fun p => p
  preservesAdd := fun _ _ => Path.refl _
  preservesDiff := fun _ => Path.refl _
  preservesBracket := fun _ _ => Path.refl _
  preservesZero := Path.refl _

/-- The identity Artinian morphism preserves MC elements up to path. -/
@[simp] theorem ArtinianMorphism.id_mapMaurerCartan_element
    {A : Type u} (DA : FormalDeformationData A)
    (mc : MaurerCartanViaPaths DA) :
    ((ArtinianMorphism.id DA).mapMaurerCartan mc).element = mc.element :=
  rfl

/-! ## Infinitesimal deformations -/

/-- An infinitesimal deformation records a first-order perturbation
together with the path witnessing the linearised Maurer-Cartan equation
(i.e. the equation `diff(α) = 0`). -/
structure InfinitesimalDeformation {A : Type u}
    (D : FormalDeformationData A) where
  element : A
  cocycle : Path (D.diff element) D.zero

namespace InfinitesimalDeformation

variable {A : Type u} {D : FormalDeformationData A}

/-- Normalization step for infinitesimal cocycle equations. -/
@[simp] theorem cocycleRweq (inf : InfinitesimalDeformation D) :
    RwEq (Path.trans inf.cocycle (Path.refl D.zero)) inf.cocycle :=
  rweq_of_step (Path.Step.trans_refl_right _)

/-- Cancellation: the cocycle is left-cancelable. -/
@[simp] theorem cocycleCancelLeft (inf : InfinitesimalDeformation D) :
    RwEq (Path.trans (Path.symm inf.cocycle) inf.cocycle) (Path.refl D.zero) :=
  rweq_cmpA_inv_left inf.cocycle

/-- Every MC element projects to an infinitesimal deformation when
the bracket term vanishes (which is higher-order).

Given `mc.equation : Path (add (diff x) (bracket x x)) zero` and
`bracketVanishes : Path (bracket x x) zero`, we compose paths to get
`Path (diff x) zero`. -/
def ofMaurerCartan (mc : MaurerCartanViaPaths D)
    (bracketVanishes : Path (D.bracket mc.element mc.element) D.zero)
    (addZeroRight : Path (D.add (D.diff mc.element) D.zero) (D.diff mc.element)) :
    InfinitesimalDeformation D where
  element := mc.element
  cocycle :=
    Path.trans
      (Path.symm addZeroRight)
      (Path.trans
        (D.addPath (Path.refl (D.diff mc.element)) (Path.symm bracketVanishes))
        mc.equation)

end InfinitesimalDeformation

/-! ## Formal moduli: deformation equivalence -/

/-- Two formal deformation data are equivalent when there exist
mutually inverse Artinian morphisms with path coherence. -/
structure DeformationEquivalence {A : Type u}
    (D₁ D₂ : FormalDeformationData A) where
  forward : ArtinianMorphism D₁ D₂
  backward : ArtinianMorphism D₂ D₁
  /-- Round-trip `backward ∘ forward` is path-equivalent to identity on elements. -/
  leftInverse : ∀ x : A, Path (backward.f (forward.f x)) x
  /-- Round-trip `forward ∘ backward` is path-equivalent to identity on elements. -/
  rightInverse : ∀ x : A, Path (forward.f (backward.f x)) x

namespace DeformationEquivalence

variable {A : Type u} {D₁ D₂ : FormalDeformationData A}

/-- The left-inverse path is rewrite-cancelable. -/
@[simp] theorem leftInverseCancelLeft (eq : DeformationEquivalence D₁ D₂) (x : A) :
    RwEq
      (Path.trans (Path.symm (eq.leftInverse x)) (eq.leftInverse x))
      (Path.refl x) :=
  rweq_cmpA_inv_left (eq.leftInverse x)

/-- The right-inverse path is rewrite-cancelable. -/
@[simp] theorem rightInverseCancelLeft (eq : DeformationEquivalence D₁ D₂) (x : A) :
    RwEq
      (Path.trans (Path.symm (eq.rightInverse x)) (eq.rightInverse x))
      (Path.refl x) :=
  rweq_cmpA_inv_left (eq.rightInverse x)

/-- Reflexive deformation equivalence. -/
def refl (D : FormalDeformationData A) : DeformationEquivalence D D where
  forward := ArtinianMorphism.id D
  backward := ArtinianMorphism.id D
  leftInverse := fun _ => Path.refl _
  rightInverse := fun _ => Path.refl _

/-- Symmetric deformation equivalence. -/
def symm (e : DeformationEquivalence D₁ D₂) : DeformationEquivalence D₂ D₁ where
  forward := e.backward
  backward := e.forward
  leftInverse := e.rightInverse
  rightInverse := e.leftInverse

end DeformationEquivalence

end DeformationTheory
end ComputationalPaths
