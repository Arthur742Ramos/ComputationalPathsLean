import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Weyl-group path infrastructure

This module packages simple-reflection and braid data for Weyl groups with
explicit computational-step witnesses and derived rewrite equivalences.
-/

namespace ComputationalPaths
namespace KacMoody

open Path

universe u v

/-- Domain-specific rewrite tags for Weyl-group path normalizations. -/
inductive WeylStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  | contract_right {A : Type u} {a b : A} (p : Path a b) :
      WeylStep (Path.trans p (Path.refl b)) p
  | contract_left {A : Type u} {a b : A} (p : Path a b) :
      WeylStep (Path.trans (Path.refl a) p) p

/-- Weyl rewrite tags induce rewrite equivalence. -/
theorem WeylStep.to_rweq {A : Type u} {a b : A} {p q : Path a b}
    (h : WeylStep p q) : RwEq p q := by
  cases h with
  | contract_right =>
      exact rweq_of_step (Path.Step.trans_refl_right _)
  | contract_left =>
      exact rweq_of_step (Path.Step.trans_refl_left _)

/-- Weyl-group data with path-preserving multiplication and Coxeter witnesses. -/
structure WeylGroupPathData (W : Type u) (I : Type v) where
  one : W
  mul : W → W → W
  simpleRef : I → W
  actionOnIndex : W → I → I
  mulPath :
    {w₁ w₂ v₁ v₂ : W} →
      Path w₁ w₂ → Path v₁ v₂ →
      Path (mul w₁ v₁) (mul w₂ v₂)
  /-- The simple reflection fixes its own index at the path level. -/
  reflectionActionPath : ∀ i : I, Path (actionOnIndex (simpleRef i) i) i
  /-- Primitive right-unit normalization witness for reflection action. -/
  reflectionActionStep :
    ∀ i : I,
      Path.Step
        (Path.trans (reflectionActionPath i) (Path.refl i))
        (reflectionActionPath i)
  /-- Involutivity witness `sᵢ * sᵢ = 1`. -/
  involutivePath : ∀ i : I, Path (mul (simpleRef i) (simpleRef i)) one
  /-- Primitive right-unit normalization witness for involutivity. -/
  involutiveStep :
    ∀ i : I,
      Path.Step
        (Path.trans (involutivePath i) (Path.refl one))
        (involutivePath i)
  /-- Three-term braid relation witness. -/
  braidPath :
    ∀ i j : I,
      Path
        (mul (mul (simpleRef i) (simpleRef j)) (simpleRef i))
        (mul (mul (simpleRef j) (simpleRef i)) (simpleRef j))
  /-- Primitive left-unit normalization witness for braid relations. -/
  braidStep :
    ∀ i j : I,
      Path.Step
        (Path.trans
          (Path.refl (mul (mul (simpleRef i) (simpleRef j)) (simpleRef i)))
          (braidPath i j))
        (braidPath i j)

namespace WeylGroupPathData

variable {W : Type u} {I : Type v} (Weyl : WeylGroupPathData W I)

@[simp] theorem reflectionAction_rweq (i : I) :
    RwEq
      (Path.trans (Weyl.reflectionActionPath i) (Path.refl i))
      (Weyl.reflectionActionPath i) :=
  rweq_of_step (Weyl.reflectionActionStep i)

@[simp] theorem involutive_rweq (i : I) :
    RwEq
      (Path.trans (Weyl.involutivePath i) (Path.refl Weyl.one))
      (Weyl.involutivePath i) :=
  rweq_of_step (Weyl.involutiveStep i)

@[simp] theorem braid_rweq (i j : I) :
    RwEq
      (Path.trans
        (Path.refl (Weyl.mul (Weyl.mul (Weyl.simpleRef i) (Weyl.simpleRef j)) (Weyl.simpleRef i)))
        (Weyl.braidPath i j))
      (Weyl.braidPath i j) :=
  rweq_of_step (Weyl.braidStep i j)

@[simp] theorem involutive_cancel_rweq (i : I) :
    RwEq
      (Path.trans (Path.symm (Weyl.involutivePath i)) (Weyl.involutivePath i))
      (Path.refl Weyl.one) :=
  rweq_cmpA_inv_left (Weyl.involutivePath i)

@[simp] theorem braid_cancel_rweq (i j : I) :
    RwEq
      (Path.trans (Weyl.braidPath i j) (Path.symm (Weyl.braidPath i j)))
      (Path.refl (Weyl.mul (Weyl.mul (Weyl.simpleRef i) (Weyl.simpleRef j)) (Weyl.simpleRef i))) :=
  rweq_cmpA_inv_right (Weyl.braidPath i j)

end WeylGroupPathData
end KacMoody
end ComputationalPaths
