import OperadicAlgebra.EnOperads

/-!
# Koszul duality for operadic algebra paths

Path-level Koszul duality data for `E_n`-operad algebras, using the shared
operadic Step infrastructure.
-/

namespace ComputationalPaths
namespace OperadicAlgebra

open Path
open Path.Algebra.LittleCubesOperad

universe u v

/-- Koszul duality package for path-level `E_n`-operad algebras. -/
structure EnKoszulDualityPathData (n : Nat) (A : Type u) (C : Type v) where
  /-- Source `E_n`-algebra path data. -/
  enAlgebra : EnOperadAlgebraPathData n A
  /-- Bar/cobar path data between algebra and dual carrier. -/
  duality : BarCobarDualityPathData A C
  /-- Transferred little-cubes action on the dual side. -/
  dualAct : {k : Nat} → EnSpace n k → (Fin k → C) → C
  /-- Bar map preserves the little-cubes operadic action. -/
  barActionPath :
    {k : Nat} → ∀ (c : EnSpace n k) (xs : Fin k → A),
      Path (duality.bar (enAlgebra.base.act c xs))
           (dualAct c (fun i => duality.bar (xs i)))
  /-- Step-level normalization of bar-action compatibility. -/
  barActionStep :
    {k : Nat} → ∀ (c : EnSpace n k) (xs : Fin k → A),
      OperadicPathStep
        (Path.trans (barActionPath c xs)
          (Path.refl (dualAct c (fun i => duality.bar (xs i)))))
        (barActionPath c xs)

namespace EnKoszulDualityPathData

variable {n : Nat} {A : Type u} {C : Type v}
variable (K : EnKoszulDualityPathData n A C)

@[simp] theorem bar_action_rweq
    {k : Nat} (c : EnSpace n k) (xs : Fin k → A) :
    RwEq
      (Path.trans (K.barActionPath c xs)
        (Path.refl (K.dualAct c (fun i => K.duality.bar (xs i)))))
      (K.barActionPath c xs) :=
  rweq_of_operadic_step (K.barActionStep c xs)

/-- Round-trip loop from bar/cobar unit on the algebra side. -/
def dualRoundTrip (x : A) :
    Path (K.duality.cobar (K.duality.bar x)) (K.duality.cobar (K.duality.bar x)) :=
  Path.trans (K.duality.unitPath x) (Path.symm (K.duality.unitPath x))

@[simp] theorem dual_roundtrip_rweq (x : A) :
    RwEq (K.dualRoundTrip x) (Path.refl (K.duality.cobar (K.duality.bar x))) := by
  unfold dualRoundTrip
  exact rweq_cmpA_inv_right (K.duality.unitPath x)

/-- Unit action path on a bar-cobar image inside the source `E_n`-algebra. -/
def enUnitOnDualized (x : A) :
    Path
      (K.enAlgebra.base.act (identityCube n)
        (fun _ => K.duality.cobar (K.duality.bar x)))
      (K.duality.cobar (K.duality.bar x)) :=
  K.enAlgebra.base.unitActionPath (K.duality.cobar (K.duality.bar x))

end EnKoszulDualityPathData

/-- Build `E_n`-Koszul duality path data from legacy operadic Koszul data. -/
def EnKoszulDualityPathData.ofLegacy
    (n : Nat)
    (K : KoszulOperadicAlgebraPathData (enOperad n)) :
    EnKoszulDualityPathData n K.carrier K.dualCarrier where
  enAlgebra := EnOperadAlgebraPathData.ofBase n K.algebra
  duality := K.duality
  dualAct := K.dualAct
  barActionPath := K.barActionPath
  barActionStep := fun c xs => OperadicPathStep.ofKoszulStep (K.barActionStep c xs)

/-- Trivial `E_n`-Koszul duality path data on `Unit`. -/
def EnKoszulDualityPathData.trivial (n : Nat) :
    EnKoszulDualityPathData n Unit Unit where
  enAlgebra := EnOperadAlgebraPathData.trivial n
  duality := BarCobarDualityPathData.trivial
  dualAct := fun _ _ => ()
  barActionPath := fun _ _ => Path.refl ()
  barActionStep := fun _ _ => OperadicPathStep.right_unit (Path.refl ())

end OperadicAlgebra
end ComputationalPaths
