import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Deformation paths: L-infinity algebras

This module packages L-infinity Maurer-Cartan data and path-preserving
L-infinity morphisms.
-/

namespace ComputationalPaths
namespace Deformation
namespace LInfinityPaths

open Path

universe u v

/-- Truncated L-infinity structure with path-preserving operations. -/
structure LInfinityPathData (A : Type u) where
  zero : A
  add : A → A → A
  l1 : A → A
  l2 : A → A → A
  addPath :
    {x₁ x₂ y₁ y₂ : A} →
      Path x₁ x₂ → Path y₁ y₂ →
        Path (add x₁ y₁) (add x₂ y₂)
  l1Path : {x y : A} → Path x y → Path (l1 x) (l1 y)
  l2Path :
    {x₁ x₂ y₁ y₂ : A} →
      Path x₁ x₂ → Path y₁ y₂ →
        Path (l2 x₁ y₁) (l2 x₂ y₂)
  l1Squared : ∀ x : A, Path (l1 (l1 x)) zero

/-- Truncated L-infinity Maurer-Cartan curvature `l₁ α + l₂(α, α)`. -/
def curvature {A : Type u} (L : LInfinityPathData A) (x : A) : A :=
  L.add (L.l1 x) (L.l2 x x)

/-- Maurer-Cartan element in a truncated L-infinity algebra. -/
structure MaurerCartanElement {A : Type u} (L : LInfinityPathData A) where
  element : A
  equation : Path (curvature L element) L.zero

/-- Atomic rewrite steps for L-infinity Maurer-Cartan path normalization. -/
inductive LInfinityStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  | contract_right {A : Type u} {a b : A} (p : Path a b) :
      LInfinityStep (Path.trans p (Path.refl b)) p

/-- L-infinity rewrite steps induce rewrite equivalence. -/
theorem LInfinityStep.to_rweq {A : Type u} {a b : A} {p q : Path a b}
    (h : LInfinityStep p q) : RwEq p q := by
  cases h
  exact rweq_of_step (Path.Step.trans_refl_right _)

namespace MaurerCartanElement

variable {A : Type u} {L : LInfinityPathData A}

/-- Primitive normalization step for an L-infinity MC equation. -/
def equationStep (mc : MaurerCartanElement L) :
    Path.Step (Path.trans mc.equation (Path.refl L.zero)) mc.equation :=
  Path.Step.trans_refl_right mc.equation

@[simp] theorem equationRweq (mc : MaurerCartanElement L) :
    RwEq (Path.trans mc.equation (Path.refl L.zero)) mc.equation :=
  rweq_of_step (equationStep mc)

@[simp] theorem equationCancelLeft (mc : MaurerCartanElement L) :
    RwEq (Path.trans (Path.symm mc.equation) mc.equation) (Path.refl L.zero) :=
  rweq_cmpA_inv_left mc.equation

@[simp] theorem equationCancelRight (mc : MaurerCartanElement L) :
    RwEq
      (Path.trans mc.equation (Path.symm mc.equation))
      (Path.refl (curvature L mc.element)) :=
  rweq_cmpA_inv_right mc.equation

end MaurerCartanElement

/-- Path-preserving truncated L-infinity morphism. -/
structure LInfinityMorphismPathData {A : Type u} {B : Type v}
    (L : LInfinityPathData A) (M : LInfinityPathData B) where
  f1 : A → B
  mapPath : {x y : A} → Path x y → Path (f1 x) (f1 y)
  preservesAdd : ∀ x y : A, Path (f1 (L.add x y)) (M.add (f1 x) (f1 y))
  preservesL1 : ∀ x : A, Path (f1 (L.l1 x)) (M.l1 (f1 x))
  preservesL2 : ∀ x y : A, Path (f1 (L.l2 x y)) (M.l2 (f1 x) (f1 y))
  preservesZero : Path (f1 L.zero) M.zero

/-- Morphisms map MC elements to MC elements through path-preserving transport. -/
def mapMaurerCartan {A : Type u} {B : Type v}
    {L : LInfinityPathData A} {M : LInfinityPathData B}
    (φ : LInfinityMorphismPathData L M)
    (α : MaurerCartanElement L) :
    MaurerCartanElement M where
  element := φ.f1 α.element
  equation :=
    Path.trans
      (M.addPath
        (Path.symm (φ.preservesL1 α.element))
        (Path.symm (φ.preservesL2 α.element α.element)))
      (Path.trans
        (Path.symm (φ.preservesAdd (L.l1 α.element) (L.l2 α.element α.element)))
        (Path.trans
          (φ.mapPath α.equation)
          φ.preservesZero))

/-- Primitive normalization step for mapped MC equations. -/
def mapMaurerCartanStep {A : Type u} {B : Type v}
    {L : LInfinityPathData A} {M : LInfinityPathData B}
    (φ : LInfinityMorphismPathData L M)
    (α : MaurerCartanElement L) :
    Path.Step
      (Path.trans (mapMaurerCartan φ α).equation (Path.refl M.zero))
      (mapMaurerCartan φ α).equation :=
  Path.Step.trans_refl_right (mapMaurerCartan φ α).equation

@[simp] theorem mapMaurerCartanRweq {A : Type u} {B : Type v}
    {L : LInfinityPathData A} {M : LInfinityPathData B}
    (φ : LInfinityMorphismPathData L M)
    (α : MaurerCartanElement L) :
    RwEq
      (Path.trans (mapMaurerCartan φ α).equation (Path.refl M.zero))
      (mapMaurerCartan φ α).equation :=
  rweq_of_step (mapMaurerCartanStep φ α)

@[simp] theorem mapMaurerCartanCancelLeft {A : Type u} {B : Type v}
    {L : LInfinityPathData A} {M : LInfinityPathData B}
    (φ : LInfinityMorphismPathData L M)
    (α : MaurerCartanElement L) :
    RwEq
      (Path.trans (Path.symm (mapMaurerCartan φ α).equation) (mapMaurerCartan φ α).equation)
      (Path.refl M.zero) :=
  rweq_cmpA_inv_left (mapMaurerCartan φ α).equation

namespace LInfinityMorphismPathData

variable {A : Type u} (L : LInfinityPathData A)

/-- Identity path-preserving L-infinity morphism. -/
def id : LInfinityMorphismPathData L L where
  f1 := _root_.id
  mapPath := fun p => p
  preservesAdd := fun _ _ => Path.refl _
  preservesL1 := fun _ => Path.refl _
  preservesL2 := fun _ _ => Path.refl _
  preservesZero := Path.refl _

end LInfinityMorphismPathData

end LInfinityPaths
end Deformation
end ComputationalPaths
