/- 
# Factorization-system path infrastructure

This module packages weak factorization systems and model structures in the
computational-path setting. Factorizations carry explicit `Path.Step` witnesses
so unit-normalization is available as `RwEq`.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Factorization

open Path

universe u

/-- A chosen factorization `f = right ∘ left` with explicit step witnesses. -/
structure FactorizationWitness (A : Type u)
    (L R : {a b : A} → Path a b → Prop) {a b : A} (f : Path a b) where
  mid : A
  left : Path a mid
  right : Path mid b
  left_mem : L left
  right_mem : R right
  composePath : Path (Path.trans left right) f
  rightUnitStep :
    Path.Step (Path.trans (Path.trans left right) (Path.refl b)) (Path.trans left right)
  leftUnitStep :
    Path.Step (Path.trans (Path.refl a) (Path.trans left right)) (Path.trans left right)

namespace FactorizationWitness

variable {A : Type u}
variable {L R : {a b : A} → Path a b → Prop}
variable {a b : A} {f : Path a b}

/-- The composite map produced by the factorization witness. -/
def composite (F : FactorizationWitness A L R f) : Path a b :=
  Path.trans F.left F.right

noncomputable def right_unit_rweq (F : FactorizationWitness A L R f) :
    RwEq (Path.trans F.composite (Path.refl b)) F.composite :=
  rweq_of_step F.rightUnitStep

noncomputable def left_unit_rweq (F : FactorizationWitness A L R f) :
    RwEq (Path.trans (Path.refl a) F.composite) F.composite :=
  rweq_of_step F.leftUnitStep

end FactorizationWitness

/-- Weak factorization systems packaged with path-level factor data. -/
structure WeakFactorizationSystemPaths (A : Type u) where
  leftClass : {a b : A} → Path a b → Prop
  rightClass : {a b : A} → Path a b → Prop
  factor : ∀ {a b : A} (f : Path a b),
    FactorizationWitness A leftClass rightClass f
  left_closed_trans :
    ∀ {a b c : A} (f : Path a b) (g : Path b c),
      leftClass f → leftClass g → leftClass (Path.trans f g)
  right_closed_trans :
    ∀ {a b c : A} (f : Path a b) (g : Path b c),
      rightClass f → rightClass g → rightClass (Path.trans f g)

namespace WeakFactorizationSystemPaths

variable {A : Type u} (W : WeakFactorizationSystemPaths A)

/-- Composite associated to the chosen factorization of `f`. -/
def factorComposite {a b : A} (f : Path a b) : Path a b :=
  (W.factor f).composite

theorem factor_right_unit_step {a b : A} (f : Path a b) :
    Path.Step (Path.trans (W.factorComposite f) (Path.refl b)) (W.factorComposite f) :=
  (W.factor f).rightUnitStep

theorem factor_left_unit_step {a b : A} (f : Path a b) :
    Path.Step (Path.trans (Path.refl a) (W.factorComposite f)) (W.factorComposite f) :=
  (W.factor f).leftUnitStep

noncomputable def factor_right_unit_rweq {a b : A} (f : Path a b) :
    RwEq (Path.trans (W.factorComposite f) (Path.refl b)) (W.factorComposite f) :=
  rweq_of_step (W.factor_right_unit_step f)

noncomputable def factor_left_unit_rweq {a b : A} (f : Path a b) :
    RwEq (Path.trans (Path.refl a) (W.factorComposite f)) (W.factorComposite f) :=
  rweq_of_step (W.factor_left_unit_step f)

end WeakFactorizationSystemPaths

/-- The trivial weak factorization system where every path lies in both classes. -/
def trivialWeakFactorizationSystem (A : Type u) : WeakFactorizationSystemPaths A where
  leftClass := fun _ => True
  rightClass := fun _ => True
  factor := by
    intro a b f
    refine
      { mid := b
        left := f
        right := Path.refl b
        left_mem := trivial
        right_mem := trivial
        composePath := ?_
        rightUnitStep := ?_
        leftUnitStep := ?_ }
    · exact Path.stepChain (Path.trans_refl_right f)
    · exact Path.Step.trans_refl_right (Path.trans f (Path.refl b))
    · exact Path.Step.trans_refl_left (Path.trans f (Path.refl b))
  left_closed_trans := fun _ _ _ _ => trivial
  right_closed_trans := fun _ _ _ _ => trivial

/-- Model-structure data with factorization axioms tracked by explicit steps. -/
structure ModelStructurePaths (A : Type u) where
  weakEquivalence : {a b : A} → Path a b → Prop
  cofibration : {a b : A} → Path a b → Prop
  fibration : {a b : A} → Path a b → Prop
  cofTrivFib : WeakFactorizationSystemPaths A
  trivCofFib : WeakFactorizationSystemPaths A
  weq_refl : ∀ (a : A), weakEquivalence (Path.refl a)
  weq_trans :
    ∀ {a b c : A} (f : Path a b) (g : Path b c),
      weakEquivalence f → weakEquivalence g → weakEquivalence (Path.trans f g)
  cof_factor_step :
    ∀ {a b : A} (f : Path a b),
      Path.Step
        (Path.trans (cofTrivFib.factorComposite f) (Path.refl b))
        (cofTrivFib.factorComposite f)
  fib_factor_step :
    ∀ {a b : A} (f : Path a b),
      Path.Step
        (Path.trans (Path.refl a) (trivCofFib.factorComposite f))
        (trivCofFib.factorComposite f)

namespace ModelStructurePaths

variable {A : Type u} (M : ModelStructurePaths A)

noncomputable def cof_factor_rweq {a b : A} (f : Path a b) :
    RwEq
      (Path.trans (M.cofTrivFib.factorComposite f) (Path.refl b))
      (M.cofTrivFib.factorComposite f) :=
  rweq_of_step (M.cof_factor_step f)

noncomputable def fib_factor_rweq {a b : A} (f : Path a b) :
    RwEq
      (Path.trans (Path.refl a) (M.trivCofFib.factorComposite f))
      (M.trivCofFib.factorComposite f) :=
  rweq_of_step (M.fib_factor_step f)

end ModelStructurePaths

/-- The trivial model structure induced by the trivial weak factorization system. -/
def trivialModelStructurePaths (A : Type u) : ModelStructurePaths A where
  weakEquivalence := fun _ => True
  cofibration := fun _ => True
  fibration := fun _ => True
  cofTrivFib := trivialWeakFactorizationSystem A
  trivCofFib := trivialWeakFactorizationSystem A
  weq_refl := fun _ => trivial
  weq_trans := fun _ _ _ _ => trivial
  cof_factor_step := by
    intro a b f
    exact (trivialWeakFactorizationSystem A).factor_right_unit_step f
  fib_factor_step := by
    intro a b f
    exact (trivialWeakFactorizationSystem A).factor_left_unit_step f

end Factorization
end ComputationalPaths
