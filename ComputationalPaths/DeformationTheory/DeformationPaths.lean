import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.CriticalPairs
namespace ComputationalPaths
namespace DeformationTheory

open ComputationalPaths
open ComputationalPaths.Path
open ComputationalPaths.Path.Rewriting

universe u

/-!
# Deformations as computational-path rewrite chains

A deformation of a path is encoded as a finite sequence of intermediate paths
whose consecutive entries are linked by `RwEq`.
-/

/-- A finite family `p₀, p₁, ..., pₙ` with `RwEq pᵢ pᵢ₊₁` witnesses. -/
inductive RwEqSequence {A : Type u} {a b : A} :
    Path a b → Path a b → Type u where
  | nil (p : Path a b) : RwEqSequence p p
  | cons {p q r : Path a b} :
      RwEq p q → RwEqSequence q r → RwEqSequence p r

namespace RwEqSequence

noncomputable def compose {A : Type u} {a b : A} {p q : Path a b}
    (σ : RwEqSequence p q) : RwEq p q := by
  induction σ with
  | nil p =>
      exact rweq_trans (rweq_symm (rweq_cmpA_refl_right p)) (rweq_cmpA_refl_right p)
  | cons h tail ih =>
      exact rweq_trans h ih

noncomputable def append {A : Type u} {a b : A}
    {p q r : Path a b} (σ : RwEqSequence p q) (h : RwEq q r) :
    RwEqSequence p r :=
  match σ with
  | .nil _ => .cons h (.nil r)
  | .cons h₁ tail => .cons h₁ (append tail h)

end RwEqSequence

/-- A deformation starting at `p₀` and ending at `terminal`. -/
structure PathDeformation {A : Type u} {a b : A} (p₀ : Path a b) where
  terminal : Path a b
  sequence : RwEqSequence p₀ terminal

namespace PathDeformation

noncomputable def consistency {A : Type u} {a b : A} {p₀ : Path a b}
    (D : PathDeformation p₀) : RwEq p₀ D.terminal :=
  RwEqSequence.compose D.sequence

noncomputable def extend {A : Type u} {a b : A} {p₀ : Path a b}
    (D : PathDeformation p₀) {q : Path a b} (h : RwEq D.terminal q) :
    PathDeformation p₀ where
  terminal := q
  sequence := RwEqSequence.append D.sequence h

noncomputable def refl {A : Type u} {a b : A} (p₀ : Path a b) :
    PathDeformation p₀ where
  terminal := p₀
  sequence := .nil p₀

end PathDeformation

/-- Infinitesimal deformation: one rewrite step viewed as tangent data. -/
structure InfinitesimalDeformation {A : Type u} {a b : A} (p : Path a b) where
  next : Path a b
  tangent : Path.Step p next

namespace InfinitesimalDeformation

noncomputable def tangent_rweq {A : Type u} {a b : A} {p : Path a b}
    (δ : InfinitesimalDeformation p) : RwEq p δ.next :=
  rweq_of_step δ.tangent

noncomputable def toSequence {A : Type u} {a b : A} {p : Path a b}
    (δ : InfinitesimalDeformation p) : RwEqSequence p δ.next :=
  .cons (δ.tangent_rweq) (.nil δ.next)

noncomputable def toDeformation {A : Type u} {a b : A} {p : Path a b}
    (δ : InfinitesimalDeformation p) : PathDeformation p where
  terminal := δ.next
  sequence := δ.toSequence

end InfinitesimalDeformation

/-- A sequence of primitive `Step`s along a deformation trajectory. -/
inductive StepSequence {A : Type u} {a b : A} :
    Path a b → Path a b → Type u where
  | nil (p : Path a b) : StepSequence p p
  | cons {p q r : Path a b} :
      Path.Step p q → StepSequence q r → StepSequence p r

namespace StepSequence

noncomputable def toRwEq {A : Type u} {a b : A} {p q : Path a b}
    (σ : StepSequence p q) : RwEq p q := by
  induction σ with
  | nil p =>
      exact rweq_trans (rweq_symm (rweq_cmpA_refl_right p)) (rweq_cmpA_refl_right p)
  | cons hs tail ih =>
      exact rweq_trans (rweq_of_step hs) ih

noncomputable def toRwEqSequence {A : Type u} {a b : A} {p q : Path a b}
    (σ : StepSequence p q) : RwEqSequence p q := by
  induction σ with
  | nil p =>
      exact .nil p
  | cons hs tail ih =>
      exact .cons (rweq_of_step hs) ih

noncomputable def toDeformation {A : Type u} {a b : A} {p q : Path a b}
    (σ : StepSequence p q) : PathDeformation p where
  terminal := q
  sequence := σ.toRwEqSequence

end StepSequence

/-- Maurer-Cartan consistency: composed infinitesimal steps yield one `RwEq` chain. -/
structure MaurerCartanEquation {A : Type u} {a b : A} (p : Path a b) where
  terminal : Path a b
  steps : StepSequence p terminal

namespace MaurerCartanEquation

noncomputable def consistency {A : Type u} {a b : A} {p : Path a b}
    (mc : MaurerCartanEquation p) : RwEq p mc.terminal :=
  StepSequence.toRwEq mc.steps

noncomputable def toDeformation {A : Type u} {a b : A} {p : Path a b}
    (mc : MaurerCartanEquation p) : PathDeformation p :=
  StepSequence.toDeformation mc.steps

end MaurerCartanEquation

/-- A critical-pair branch at the tip of a partial deformation. -/
structure CriticalPairAt {A : Type u} {a b : A} (p : Path a b) where
  caseTag : CriticalPairCase
  left : Path a b
  right : Path a b
  leftStep : Path.Step p left
  rightStep : Path.Step p right

namespace CriticalPairAt

noncomputable def Joinable {A : Type u} {a b : A} {p : Path a b}
    (cp : CriticalPairAt p) : Type u :=
  Σ r : Path a b, RwEq cp.left r × RwEq cp.right r

noncomputable def left_rweq {A : Type u} {a b : A} {p : Path a b}
    (cp : CriticalPairAt p) : RwEq p cp.left :=
  rweq_of_step cp.leftStep

noncomputable def right_rweq {A : Type u} {a b : A} {p : Path a b}
    (cp : CriticalPairAt p) : RwEq p cp.right :=
  rweq_of_step cp.rightStep

end CriticalPairAt

noncomputable def PathDeformation.ExtendableAlong
    {A : Type u} {a b : A} {p₀ : Path a b}
    (D : PathDeformation p₀) (cp : CriticalPairAt D.terminal) : Type u :=
  cp.Joinable

noncomputable def PathDeformation.extend_of_joinable
    {A : Type u} {a b : A} {p₀ : Path a b}
    (D : PathDeformation p₀) (cp : CriticalPairAt D.terminal)
    (h : D.ExtendableAlong cp) :
    Σ r : Path a b, PathDeformation p₀ :=
  ⟨h.1,
   D.extend (rweq_trans cp.left_rweq h.2.1)⟩

/-- Obstruction: a non-joinable critical pair blocks extension. -/
structure ExtensionObstruction {A : Type u} {a b : A} {p₀ : Path a b}
    (D : PathDeformation p₀) where
  critical : CriticalPairAt D.terminal
  nonjoinable : D.ExtendableAlong critical → False

namespace ExtensionObstruction

theorem blocks_extension
    {A : Type u} {a b : A} {p₀ : Path a b}
    {D : PathDeformation p₀} (obs : ExtensionObstruction D) :
    D.ExtendableAlong obs.critical → False :=
  obs.nonjoinable

end ExtensionObstruction

/-- Gauge equivalence between deformations via a higher `RwEq` witness. -/
structure GaugeEquivalence {A : Type u} {a b : A} {p₀ : Path a b}
    (D₁ D₂ : PathDeformation p₀) where
  higher : RwEq D₁.terminal D₂.terminal

namespace GaugeEquivalence

noncomputable def refl {A : Type u} {a b : A} {p₀ : Path a b}
    (D : PathDeformation p₀) : GaugeEquivalence D D where
  higher := rweq_trans (rweq_symm (rweq_cmpA_refl_right D.terminal)) (rweq_cmpA_refl_right D.terminal)

noncomputable def symm {A : Type u} {a b : A} {p₀ : Path a b}
    {D₁ D₂ : PathDeformation p₀} (g : GaugeEquivalence D₁ D₂) :
    GaugeEquivalence D₂ D₁ where
  higher := rweq_symm g.higher

noncomputable def trans {A : Type u} {a b : A} {p₀ : Path a b}
    {D₁ D₂ D₃ : PathDeformation p₀}
    (g₁ : GaugeEquivalence D₁ D₂) (g₂ : GaugeEquivalence D₂ D₃) :
    GaugeEquivalence D₁ D₃ where
  higher := rweq_trans g₁.higher g₂.higher

end GaugeEquivalence

end DeformationTheory
end ComputationalPaths
