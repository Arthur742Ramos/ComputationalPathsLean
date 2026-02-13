import OperadicAlgebra.AlgebrasOverOperadsPaths
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Koszul duality as computational paths

This module packages bar/cobar duality and operadic compatibility as
path-preserving constructions.
-/

namespace ComputationalPaths
namespace OperadicAlgebra

open Path

universe u v w

/-- Domain-specific rewrite steps for Koszul duality path witnesses. -/
inductive KoszulStep {A : Type u} :
    {a b : A} → Path a b → Path a b → Prop where
  | right_unit {a b : A} (p : Path a b) :
      KoszulStep (Path.trans p (Path.refl b)) p
  | left_unit {a b : A} (p : Path a b) :
      KoszulStep (Path.trans (Path.refl a) p) p
  | inverse_cancel {a b : A} (p : Path a b) :
      KoszulStep (Path.trans p (Path.symm p)) (Path.refl a)

/-- Interpret a Koszul-domain step as a primitive `Path.Step`. -/
def KoszulStep.toStep {A : Type u} {a b : A} {p q : Path a b}
    (s : KoszulStep p q) : Path.Step p q :=
  match s with
  | .right_unit p => Path.Step.trans_refl_right p
  | .left_unit p => Path.Step.trans_refl_left p
  | .inverse_cancel p => Path.Step.trans_symm p

/-- Lift Koszul-domain steps to rewrite equivalence. -/
theorem rweq_of_koszul_step {A : Type u} {a b : A}
    {p q : Path a b} (s : KoszulStep p q) : RwEq p q :=
  rweq_of_step (KoszulStep.toStep s)

/-- Bar/cobar duality package with path-preserving unit/counit witnesses. -/
structure BarCobarDualityPathData (A : Type u) (C : Type v) where
  /-- Bar map from algebra-side data to coalgebra-side data. -/
  bar : A → C
  /-- Cobar map back to the algebra side. -/
  cobar : C → A
  /-- Unit of the duality as a computational path. -/
  unitPath : ∀ a : A, Path (cobar (bar a)) a
  /-- Counit of the duality as a computational path. -/
  counitPath : ∀ c : C, Path (bar (cobar c)) c
  /-- Right-unit normalization on unit paths. -/
  unitStep :
    ∀ a : A,
      KoszulStep (Path.trans (unitPath a) (Path.refl a)) (unitPath a)
  /-- Left-unit normalization on counit paths. -/
  counitStep :
    ∀ c : C,
      KoszulStep
        (Path.trans (Path.refl (bar (cobar c))) (counitPath c))
        (counitPath c)

namespace BarCobarDualityPathData

variable {A : Type u} {C : Type v}
variable (D : BarCobarDualityPathData A C)

@[simp] theorem unit_rweq (a : A) :
    RwEq (Path.trans (D.unitPath a) (Path.refl a)) (D.unitPath a) :=
  rweq_of_koszul_step (D.unitStep a)

@[simp] theorem counit_rweq (c : C) :
    RwEq
      (Path.trans (Path.refl (D.bar (D.cobar c))) (D.counitPath c))
      (D.counitPath c) :=
  rweq_of_koszul_step (D.counitStep c)

/-- Round-trip path at the algebra side. -/
def algebraRoundTrip (a : A) : Path (D.cobar (D.bar a)) (D.cobar (D.bar a)) :=
  Path.trans (D.unitPath a) (Path.symm (D.unitPath a))

@[simp] theorem algebra_roundtrip_rweq (a : A) :
    RwEq (D.algebraRoundTrip a) (Path.refl (D.cobar (D.bar a))) := by
  unfold algebraRoundTrip
  exact rweq_cmpA_inv_right (D.unitPath a)

/-- Transport a path through the bar map. -/
def mapBar {x y : A} (p : Path x y) : Path (D.bar x) (D.bar y) :=
  Path.congrArg D.bar p

end BarCobarDualityPathData

/-- Operadic algebra equipped with Koszul duality data and bar compatibility. -/
structure KoszulOperadicAlgebraPathData
    (O : Path.Algebra.OperadTheory.CleanOperad) where
  /-- Algebra carrier. -/
  carrier : Type v
  /-- Dual coalgebra carrier. -/
  dualCarrier : Type w
  /-- Path-preserving operad action on the algebra side. -/
  algebra : AlgebraOverOperadPathData O carrier
  /-- Path-preserving bar/cobar duality package. -/
  duality : BarCobarDualityPathData carrier dualCarrier
  /-- Action on the dual side induced by Koszul transfer data. -/
  dualAct : {n : Nat} → O.ops n → (Fin n → dualCarrier) → dualCarrier
  /-- Bar map preserves operadic action. -/
  barActionPath :
    {n : Nat} → ∀ (θ : O.ops n) (xs : Fin n → carrier),
      Path (duality.bar (algebra.act θ xs))
           (dualAct θ (fun i => duality.bar (xs i)))
  /-- Right-unit normalization of bar-action compatibility paths. -/
  barActionStep :
    {n : Nat} → ∀ (θ : O.ops n) (xs : Fin n → carrier),
      KoszulStep
        (Path.trans (barActionPath θ xs)
          (Path.refl (dualAct θ (fun i => duality.bar (xs i)))))
        (barActionPath θ xs)

namespace KoszulOperadicAlgebraPathData

variable {O : Path.Algebra.OperadTheory.CleanOperad}
variable (K : KoszulOperadicAlgebraPathData O)

@[simp] theorem bar_action_rweq
    {n : Nat} (θ : O.ops n) (xs : Fin n → K.carrier) :
    RwEq
      (Path.trans (K.barActionPath θ xs)
        (Path.refl (K.dualAct θ (fun i => K.duality.bar (xs i)))))
      (K.barActionPath θ xs) :=
  rweq_of_koszul_step (K.barActionStep θ xs)

/-- Unit action on a bar-cobar image in the underlying operadic algebra. -/
def unitOnDualized (x : K.carrier) :
    Path
      (K.algebra.act O.unit (fun _ => K.duality.cobar (K.duality.bar x)))
      (K.duality.cobar (K.duality.bar x)) :=
  K.algebra.unitActionPath (K.duality.cobar (K.duality.bar x))

end KoszulOperadicAlgebraPathData

/-- Trivial bar/cobar duality package on `Unit`. -/
def BarCobarDualityPathData.trivial : BarCobarDualityPathData Unit Unit where
  bar := _root_.id
  cobar := _root_.id
  unitPath := fun _ => Path.refl ()
  counitPath := fun _ => Path.refl ()
  unitStep := fun _ => KoszulStep.right_unit (Path.refl ())
  counitStep := fun _ => KoszulStep.left_unit (Path.refl ())

/-- Trivial Koszul-operadic algebra path data over any operad. -/
def KoszulOperadicAlgebraPathData.trivial
    (O : Path.Algebra.OperadTheory.CleanOperad) :
    KoszulOperadicAlgebraPathData O where
  carrier := Unit
  dualCarrier := Unit
  algebra := AlgebraOverOperadPathData.trivial O
  duality := BarCobarDualityPathData.trivial
  dualAct := fun _ _ => ()
  barActionPath := fun _ _ => Path.refl ()
  barActionStep := fun _ _ => KoszulStep.right_unit (Path.refl ())

end OperadicAlgebra
end ComputationalPaths
