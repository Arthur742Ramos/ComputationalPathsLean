import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import Prismatic.PrismPaths

/-!
# Prismatic cohomology paths: Breuil-Kisin modules

This module formalizes Breuil-Kisin style module data over prisms using explicit
computational paths and rewrite-equivalence normalization.
-/

namespace ComputationalPaths
namespace Prismatic

open Path

universe u v

/-- Domain-specific rewrite steps for Breuil-Kisin computations. -/
inductive BreuilKisinStep {M : Type v} :
    {x y : M} → Path x y → Path x y → Prop where
  | linearity_right_unit {x y : M} (p : Path x y) :
      BreuilKisinStep (Path.trans p (Path.refl y)) p
  | twist_left_unit {x y : M} (p : Path x y) :
      BreuilKisinStep (Path.trans (Path.refl x) p) p
  | frobenius_cancel {x y : M} (p : Path x y) :
      BreuilKisinStep (Path.trans p (Path.symm p)) (Path.refl x)

/-- Interpret a Breuil-Kisin step as a primitive `Path.Step`. -/
def BreuilKisinStep.toStep {M : Type v} {x y : M} {p q : Path x y}
    (s : BreuilKisinStep p q) : Path.Step p q :=
  match s with
  | .linearity_right_unit p => Path.Step.trans_refl_right p
  | .twist_left_unit p => Path.Step.trans_refl_left p
  | .frobenius_cancel p => Path.Step.trans_symm p

/-- Lift a Breuil-Kisin step to rewrite equivalence. -/
theorem rweq_of_breuil_kisin_step {M : Type v} {x y : M}
    {p q : Path x y} (s : BreuilKisinStep p q) : RwEq p q :=
  rweq_of_step (BreuilKisinStep.toStep s)

/-- Breuil-Kisin module data over a prism with explicit path witnesses. -/
structure BreuilKisinModulePathData
    (A : Type u) (M : Type v) (P : PrismPathData A) where
  scalar : A → M → M
  phiModule : M → M
  twist : M → M
  linearityPath :
    ∀ a : A, ∀ m : M,
      Path (phiModule (scalar a m)) (scalar (P.frobenius a) (phiModule m))
  twistPath :
    ∀ m : M,
      Path (twist (phiModule m)) (phiModule (twist m))
  generatorActionPath :
    ∀ m : M,
      Path (scalar P.idealGenerator m) (twist m)
  linearityStep :
    ∀ a : A, ∀ m : M,
      BreuilKisinStep
        (Path.trans (linearityPath a m)
          (Path.refl (scalar (P.frobenius a) (phiModule m))))
        (linearityPath a m)
  twistStep :
    ∀ m : M,
      BreuilKisinStep
        (Path.trans (Path.refl (twist (phiModule m))) (twistPath m))
        (twistPath m)
  generatorActionStep :
    ∀ m : M,
      BreuilKisinStep
        (Path.trans (generatorActionPath m) (Path.refl (twist m)))
        (generatorActionPath m)

namespace BreuilKisinModulePathData

variable {A : Type u} {M : Type v} {P : PrismPathData A}
variable (B : BreuilKisinModulePathData A M P)

@[simp] theorem linearity_rweq (a : A) (m : M) :
    RwEq
      (Path.trans (B.linearityPath a m)
        (Path.refl (B.scalar (P.frobenius a) (B.phiModule m))))
      (B.linearityPath a m) :=
  rweq_of_breuil_kisin_step (B.linearityStep a m)

@[simp] theorem twist_rweq (m : M) :
    RwEq
      (Path.trans (Path.refl (B.twist (B.phiModule m))) (B.twistPath m))
      (B.twistPath m) :=
  rweq_of_breuil_kisin_step (B.twistStep m)

@[simp] theorem generator_action_rweq (m : M) :
    RwEq
      (Path.trans (B.generatorActionPath m) (Path.refl (B.twist m)))
      (B.generatorActionPath m) :=
  rweq_of_breuil_kisin_step (B.generatorActionStep m)

/-- Base-change of the prism generator along Frobenius in module action. -/
def generatorBaseChange (m : M) :
    Path
      (B.scalar (P.frobenius P.idealGenerator) (B.phiModule m))
      (B.scalar P.idealGenerator (B.phiModule m)) :=
  Path.congrArg (fun a => B.scalar a (B.phiModule m)) P.prismConditionPath

/-- Generator action after Frobenius base-change. -/
def frobeniusGeneratorAction (m : M) :
    Path
      (B.scalar (P.frobenius P.idealGenerator) (B.phiModule m))
      (B.twist (B.phiModule m)) :=
  Path.trans (B.generatorBaseChange m) (B.generatorActionPath (B.phiModule m))

/-- Prismatic/Breuil-Kisin compatibility path through Frobenius and twist. -/
def breuilKisinPrismaticPath (m : M) :
    Path
      (B.scalar (P.frobenius P.idealGenerator) (B.phiModule m))
      (B.phiModule (B.twist m)) :=
  Path.trans (B.frobeniusGeneratorAction m) (B.twistPath m)

/-- Round-trip path on the twisted Frobenius side. -/
def twistRoundTrip (m : M) :
    Path (B.twist (B.phiModule m)) (B.twist (B.phiModule m)) :=
  Path.trans (B.twistPath m) (Path.symm (B.twistPath m))

@[simp] theorem twist_roundtrip_rweq (m : M) :
    RwEq (B.twistRoundTrip m) (Path.refl (B.twist (B.phiModule m))) :=
  rweq_of_breuil_kisin_step (BreuilKisinStep.frobenius_cancel (B.twistPath m))

end BreuilKisinModulePathData

/-- Trivial Breuil-Kisin module package over the trivial prism. -/
def trivialBreuilKisinModulePathData :
    BreuilKisinModulePathData PUnit PUnit trivialPrismPathData where
  scalar := fun _ _ => PUnit.unit
  phiModule := fun _ => PUnit.unit
  twist := fun _ => PUnit.unit
  linearityPath := fun _ _ => Path.refl PUnit.unit
  twistPath := fun _ => Path.refl PUnit.unit
  generatorActionPath := fun _ => Path.refl PUnit.unit
  linearityStep := fun _ _ => BreuilKisinStep.linearity_right_unit (Path.refl PUnit.unit)
  twistStep := fun _ => BreuilKisinStep.twist_left_unit (Path.refl PUnit.unit)
  generatorActionStep := fun _ => BreuilKisinStep.linearity_right_unit (Path.refl PUnit.unit)

end Prismatic
end ComputationalPaths
