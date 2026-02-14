import ComputationalPaths.OperadicAlgebra.AlgebrasOverOperadsPaths
import ComputationalPaths.OperadicAlgebra.KoszulDualityPaths
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Operadic algebra path infrastructure

Shared Step-level infrastructure for operadic algebra and Koszul duality
path constructions.
-/

namespace ComputationalPaths
namespace OperadicAlgebra

open Path

universe u

/-- Shared domain-specific rewrite steps for operadic algebra path modules. -/
inductive OperadicPathStep {A : Type u} :
    {a b : A} → Path a b → Path a b → Prop where
  | right_unit {a b : A} (p : Path a b) :
      OperadicPathStep (Path.trans p (Path.refl b)) p
  | left_unit {a b : A} (p : Path a b) :
      OperadicPathStep (Path.trans (Path.refl a) p) p
  | inverse_cancel {a b : A} (p : Path a b) :
      OperadicPathStep (Path.trans p (Path.symm p)) (Path.refl a)

/-- Interpret an operadic infrastructure step as a primitive `Path.Step`. -/
def OperadicPathStep.toStep {A : Type u} {a b : A} {p q : Path a b}
    (s : OperadicPathStep p q) : Path.Step p q :=
  match s with
  | .right_unit p => Path.Step.trans_refl_right p
  | .left_unit p => Path.Step.trans_refl_left p
  | .inverse_cancel p => Path.Step.trans_symm p

/-- Lift a shared operadic infrastructure step to rewrite equivalence. -/
theorem rweq_of_operadic_step {A : Type u} {a b : A}
    {p q : Path a b} (s : OperadicPathStep p q) : RwEq p q :=
  rweq_of_step (OperadicPathStep.toStep s)

/-- Translate legacy operad-algebra steps to shared operadic infrastructure. -/
def OperadicPathStep.ofOperadAlgebraStep {A : Type u} {a b : A} {p q : Path a b}
    (s : OperadAlgebraStep p q) : OperadicPathStep p q :=
  match s with
  | .right_unit p => OperadicPathStep.right_unit p
  | .left_unit p => OperadicPathStep.left_unit p
  | .inverse_cancel p => OperadicPathStep.inverse_cancel p

/-- Translate legacy Koszul steps to shared operadic infrastructure. -/
def OperadicPathStep.ofKoszulStep {A : Type u} {a b : A} {p q : Path a b}
    (s : KoszulStep p q) : OperadicPathStep p q :=
  match s with
  | .right_unit p => OperadicPathStep.right_unit p
  | .left_unit p => OperadicPathStep.left_unit p
  | .inverse_cancel p => OperadicPathStep.inverse_cancel p

/-- Shared infrastructure recovers rewrite equivalence for legacy operad-algebra steps. -/
theorem rweq_of_operad_algebra_step_infra {A : Type u} {a b : A}
    {p q : Path a b} (s : OperadAlgebraStep p q) : RwEq p q :=
  rweq_of_operadic_step (OperadicPathStep.ofOperadAlgebraStep s)

/-- Shared infrastructure recovers rewrite equivalence for legacy Koszul steps. -/
theorem rweq_of_koszul_step_infra {A : Type u} {a b : A}
    {p q : Path a b} (s : KoszulStep p q) : RwEq p q :=
  rweq_of_operadic_step (OperadicPathStep.ofKoszulStep s)

end OperadicAlgebra
end ComputationalPaths
