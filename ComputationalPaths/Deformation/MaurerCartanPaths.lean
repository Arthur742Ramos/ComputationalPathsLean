import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Deformation paths: Maurer-Cartan equations

This module models Maurer-Cartan equations as explicit computational paths and
records path-preserving transport and gauge operations.
-/

namespace ComputationalPaths
namespace Deformation
namespace MaurerCartanPaths

open Path

universe u

/-- Differential graded Lie-style data with path-preserving operations. -/
structure DGLiePathData (A : Type u) where
  zero : A
  add : A → A → A
  diff : A → A
  bracket : A → A → A
  addPath :
    {x₁ x₂ y₁ y₂ : A} →
      Path x₁ x₂ → Path y₁ y₂ →
        Path (add x₁ y₁) (add x₂ y₂)
  diffPath : {x y : A} → Path x y → Path (diff x) (diff y)
  bracketPath :
    {x₁ x₂ y₁ y₂ : A} →
      Path x₁ x₂ → Path y₁ y₂ →
        Path (bracket x₁ y₁) (bracket x₂ y₂)

/-- Truncated Maurer-Cartan curvature term `d α + [α, α]`. -/
def curvature {A : Type u} (L : DGLiePathData A) (x : A) : A :=
  L.add (L.diff x) (L.bracket x x)

/-- Maurer-Cartan element represented by a path-valued equation. -/
structure MaurerCartanElement {A : Type u} (L : DGLiePathData A) where
  element : A
  equation : Path (curvature L element) L.zero

/-- Atomic rewrite steps for Maurer-Cartan path normalization. -/
inductive MaurerCartanStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  | contract_right {A : Type u} {a b : A} (p : Path a b) :
      MaurerCartanStep (Path.trans p (Path.refl b)) p

/-- Maurer-Cartan rewrite steps induce rewrite equivalence. -/
noncomputable def MaurerCartanStep.to_rweq {A : Type u} {a b : A} {p q : Path a b}
    (h : MaurerCartanStep p q) : RwEq p q := by
  cases h
  exact rweq_of_step (Path.Step.trans_refl_right _)

namespace MaurerCartanElement

variable {A : Type u} {L : DGLiePathData A}

/-- Primitive normalization step for an MC equation. -/
def equationStep (mc : MaurerCartanElement L) :
    Path.Step (Path.trans mc.equation (Path.refl L.zero)) mc.equation :=
  Path.Step.trans_refl_right mc.equation

noncomputable def equationRweq (mc : MaurerCartanElement L) :
    RwEq (Path.trans mc.equation (Path.refl L.zero)) mc.equation :=
  rweq_of_step (equationStep mc)

noncomputable def equationCancelLeft (mc : MaurerCartanElement L) :
    RwEq (Path.trans (Path.symm mc.equation) mc.equation) (Path.refl L.zero) :=
  rweq_cmpA_inv_left mc.equation

noncomputable def equationCancelRight (mc : MaurerCartanElement L) :
    RwEq
      (Path.trans mc.equation (Path.symm mc.equation))
      (Path.refl (curvature L mc.element)) :=
  rweq_cmpA_inv_right mc.equation

/-- Transport an MC solution along a path in the underlying carrier. -/
def transport {β : A} (mc : MaurerCartanElement L) (p : Path mc.element β) :
    MaurerCartanElement L where
  element := β
  equation :=
    Path.trans
      (Path.symm (L.addPath (L.diffPath p) (L.bracketPath p p)))
      mc.equation

/-- Primitive normalization step for transported MC equations. -/
def transportStep {β : A} (mc : MaurerCartanElement L) (p : Path mc.element β) :
    Path.Step
      (Path.trans (transport mc p).equation (Path.refl L.zero))
      (transport mc p).equation :=
  Path.Step.trans_refl_right (transport mc p).equation

noncomputable def transportRweq {β : A} (mc : MaurerCartanElement L) (p : Path mc.element β) :
    RwEq
      (Path.trans (transport mc p).equation (Path.refl L.zero))
      (transport mc p).equation :=
  rweq_of_step (transportStep mc p)

end MaurerCartanElement

/-- Path-preserving gauge action on a DGLie path package. -/
structure GaugeAction {A : Type u} (L : DGLiePathData A) where
  act : A → A
  actPath : {x y : A} → Path x y → Path (act x) (act y)
  preserveCurvature : ∀ x : A, Path (curvature L (act x)) (curvature L x)

namespace GaugeAction

variable {A : Type u} {L : DGLiePathData A}

/-- Gauge actions send Maurer-Cartan elements to Maurer-Cartan elements. -/
def onMaurerCartan (G : GaugeAction L) (mc : MaurerCartanElement L) :
    MaurerCartanElement L where
  element := G.act mc.element
  equation := Path.trans (G.preserveCurvature mc.element) mc.equation

noncomputable def onMaurerCartanRweq (G : GaugeAction L) (mc : MaurerCartanElement L) :
    RwEq
      (Path.trans (onMaurerCartan G mc).equation (Path.refl L.zero))
      (onMaurerCartan G mc).equation :=
  rweq_of_step (Path.Step.trans_refl_right (onMaurerCartan G mc).equation)

end GaugeAction

end MaurerCartanPaths
end Deformation
end ComputationalPaths
