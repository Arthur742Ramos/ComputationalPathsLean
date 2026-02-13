import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Kac-Moody Lie algebra path infrastructure

This module packages infinite-dimensional Kac-Moody style Lie data with explicit
computational-path witnesses for simple-root reflections and Serre relations.
-/

namespace ComputationalPaths
namespace KacMoody

open Path

universe u v

/-- Domain-specific rewrite tags for Kac-Moody path normalizations. -/
inductive KacMoodyStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  | contract_right {A : Type u} {a b : A} (p : Path a b) :
      KacMoodyStep (Path.trans p (Path.refl b)) p
  | contract_left {A : Type u} {a b : A} (p : Path a b) :
      KacMoodyStep (Path.trans (Path.refl a) p) p

/-- Kac-Moody rewrite tags induce rewrite equivalence. -/
theorem KacMoodyStep.to_rweq {A : Type u} {a b : A} {p q : Path a b}
    (h : KacMoodyStep p q) : RwEq p q := by
  cases h with
  | contract_right =>
      exact rweq_of_step (Path.Step.trans_refl_right _)
  | contract_left =>
      exact rweq_of_step (Path.Step.trans_refl_left _)

/-- Infinite-dimensional Lie-style data with path-preserving operations. -/
structure KacMoodyAlgebraPathData (L : Type u) (I : Type v) where
  zero : L
  add : L → L → L
  bracket : L → L → L
  simpleRoot : I → L
  coroot : I → L
  adPower : Nat → L → L → L
  addPath :
    {x₁ x₂ y₁ y₂ : L} →
      Path x₁ x₂ → Path y₁ y₂ →
      Path (add x₁ y₁) (add x₂ y₂)
  bracketPath :
    {x₁ x₂ y₁ y₂ : L} →
      Path x₁ x₂ → Path y₁ y₂ →
      Path (bracket x₁ y₁) (bracket x₂ y₂)
  adPath :
    {n : Nat} → {x₁ x₂ y₁ y₂ : L} →
      Path x₁ x₂ → Path y₁ y₂ →
      Path (adPower n x₁ y₁) (adPower n x₂ y₂)
  /-- Reflection witness exchanging simple root and coroot bracket order. -/
  simpleReflectionPath :
    ∀ i : I,
      Path (bracket (simpleRoot i) (coroot i)) (bracket (coroot i) (simpleRoot i))
  /-- Primitive right-unit normalization witness for simple reflections. -/
  simpleReflectionStep :
    ∀ i : I,
      Path.Step
        (Path.trans (simpleReflectionPath i) (Path.refl (bracket (coroot i) (simpleRoot i))))
        (simpleReflectionPath i)
  /-- Serre-relation witness on simple roots. -/
  serrePath :
    ∀ i j : I, Path (adPower 2 (simpleRoot i) (simpleRoot j)) zero
  /-- Primitive left-unit normalization witness for Serre relations. -/
  serreStep :
    ∀ i j : I,
      Path.Step
        (Path.trans (Path.refl (adPower 2 (simpleRoot i) (simpleRoot j))) (serrePath i j))
        (serrePath i j)

namespace KacMoodyAlgebraPathData

variable {L : Type u} {I : Type v} (K : KacMoodyAlgebraPathData L I)

@[simp] theorem simpleReflection_rweq (i : I) :
    RwEq
      (Path.trans (K.simpleReflectionPath i) (Path.refl (K.bracket (K.coroot i) (K.simpleRoot i))))
      (K.simpleReflectionPath i) :=
  rweq_of_step (K.simpleReflectionStep i)

@[simp] theorem serre_rweq (i j : I) :
    RwEq
      (Path.trans
        (Path.refl (K.adPower 2 (K.simpleRoot i) (K.simpleRoot j)))
        (K.serrePath i j))
      (K.serrePath i j) :=
  rweq_of_step (K.serreStep i j)

@[simp] theorem simpleReflection_cancel_rweq (i : I) :
    RwEq
      (Path.trans (Path.symm (K.simpleReflectionPath i)) (K.simpleReflectionPath i))
      (Path.refl (K.bracket (K.coroot i) (K.simpleRoot i))) :=
  rweq_cmpA_inv_left (K.simpleReflectionPath i)

@[simp] theorem serre_cancel_rweq (i j : I) :
    RwEq
      (Path.trans (K.serrePath i j) (Path.symm (K.serrePath i j)))
      (Path.refl (K.adPower 2 (K.simpleRoot i) (K.simpleRoot j))) :=
  rweq_cmpA_inv_right (K.serrePath i j)

end KacMoodyAlgebraPathData
end KacMoody
end ComputationalPaths
