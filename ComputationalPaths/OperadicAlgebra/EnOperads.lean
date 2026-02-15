import ComputationalPaths.OperadicAlgebra.PathInfrastructure
import ComputationalPaths.Path.Algebra.LittleCubesOperad

/-!
# E_n-operad algebra paths

Path-level infrastructure for algebras over little-cubes operads, reusing the
shared operadic Step layer.
-/

namespace ComputationalPaths
namespace OperadicAlgebra

open Path
open Path.Algebra
open Path.Algebra.LittleCubesOperad

universe u

/-- `E_n`-operad algebras with explicit computational-path coherences. -/
structure EnOperadAlgebraPathData (n : Nat) (A : Type u) where
  /-- Underlying operad-algebra path data for the little-cubes operad. -/
  base : AlgebraOverOperadPathData (LittleCubesOperad.enOperad n) A
  /-- Iterated unit coherence path for little-cubes action. -/
  iteratedUnitPath :
    ∀ x : A,
      Path
        (base.act (LittleCubesOperad.identityCube n) (fun _ =>
          base.act (LittleCubesOperad.identityCube n) (fun _ => x)))
        x
  /-- Normalization of iterated unit coherence via shared operadic steps. -/
  iteratedUnitStep :
    ∀ x : A,
      OperadicPathStep
        (Path.trans (iteratedUnitPath x) (Path.refl x))
        (iteratedUnitPath x)

namespace EnOperadAlgebraPathData

variable {n : Nat} {A : Type u}
variable (E : EnOperadAlgebraPathData n A)

@[simp] theorem iterated_unit_rweq (x : A) :
    RwEq
      (Path.trans (E.iteratedUnitPath x) (Path.refl x))
      (E.iteratedUnitPath x) :=
  rweq_of_operadic_step (E.iteratedUnitStep x)

/-- Unit action path on an `E_n`-algebra output. -/
def unitOnAction {k : Nat} (c : EnSpace n k) (xs : Fin k → A) :
    Path
      (E.base.act (LittleCubesOperad.identityCube n) (fun _ => E.base.act c xs))
      (E.base.act c xs) :=
  E.base.unitActionPath (E.base.act c xs)

@[simp] theorem unitOnAction_eq_unitActionPath
    {k : Nat} (c : EnSpace n k) (xs : Fin k → A) :
    E.unitOnAction c xs = E.base.unitActionPath (E.base.act c xs) := by
  sorry

/-- Round-trip loop formed from the unit-action witness on an output. -/
def actionUnitRoundTrip {k : Nat} (c : EnSpace n k) (xs : Fin k → A) :
    Path
      (E.base.act (LittleCubesOperad.identityCube n) (fun _ => E.base.act c xs))
      (E.base.act (LittleCubesOperad.identityCube n) (fun _ => E.base.act c xs)) :=
  Path.trans (E.unitOnAction c xs) (Path.symm (E.unitOnAction c xs))

@[simp] theorem actionUnitRoundTrip_eq
    {k : Nat} (c : EnSpace n k) (xs : Fin k → A) :
    E.actionUnitRoundTrip c xs =
      Path.trans (E.unitOnAction c xs) (Path.symm (E.unitOnAction c xs)) := by
  sorry

@[simp] theorem action_unit_roundtrip_rweq
    {k : Nat} (c : EnSpace n k) (xs : Fin k → A) :
    RwEq
      (E.actionUnitRoundTrip c xs)
      (Path.refl
        (E.base.act (LittleCubesOperad.identityCube n) (fun _ => E.base.act c xs))) := by
  unfold actionUnitRoundTrip unitOnAction
  exact rweq_cmpA_inv_right (E.base.unitActionPath (E.base.act c xs))

theorem action_unit_roundtrip_left_refl_rweq
    {k : Nat} (c : EnSpace n k) (xs : Fin k → A) :
    RwEq
      (Path.trans
        (Path.refl
          (E.base.act (LittleCubesOperad.identityCube n) (fun _ => E.base.act c xs)))
        (E.actionUnitRoundTrip c xs))
      (E.actionUnitRoundTrip c xs) := by
  sorry

theorem action_unit_roundtrip_right_refl_rweq
    {k : Nat} (c : EnSpace n k) (xs : Fin k → A) :
    RwEq
      (Path.trans
        (E.actionUnitRoundTrip c xs)
        (Path.refl
          (E.base.act (LittleCubesOperad.identityCube n) (fun _ => E.base.act c xs))))
      (E.actionUnitRoundTrip c xs) := by
  sorry

theorem unit_on_action_assoc_with_refl
    {k : Nat} (c : EnSpace n k) (xs : Fin k → A) :
    RwEq
      (Path.trans
        (Path.trans (E.unitOnAction c xs) (Path.refl (E.base.act c xs)))
        (Path.symm (E.unitOnAction c xs)))
      (Path.trans
        (E.unitOnAction c xs)
        (Path.trans (Path.refl (E.base.act c xs)) (Path.symm (E.unitOnAction c xs)))) := by
  sorry

theorem unit_on_action_inverse_right_rweq
    {k : Nat} (c : EnSpace n k) (xs : Fin k → A) :
    RwEq
      (Path.trans (E.unitOnAction c xs) (Path.symm (E.unitOnAction c xs)))
      (Path.refl
        (E.base.act (LittleCubesOperad.identityCube n) (fun _ => E.base.act c xs))) := by
  sorry

theorem unit_on_action_inverse_left_rweq
    {k : Nat} (c : EnSpace n k) (xs : Fin k → A) :
    RwEq
      (Path.trans (Path.symm (E.unitOnAction c xs)) (E.unitOnAction c xs))
      (Path.refl (E.base.act c xs)) := by
  sorry

theorem iterated_unit_left_refl_rweq (x : A) :
    RwEq
      (Path.trans
        (Path.refl
          (E.base.act (LittleCubesOperad.identityCube n) (fun _ =>
            E.base.act (LittleCubesOperad.identityCube n) (fun _ => x))))
        (E.iteratedUnitPath x))
      (E.iteratedUnitPath x) := by
  sorry

end EnOperadAlgebraPathData

/-- Build `E_n`-operad algebra path data from an operad-algebra path package. -/
def EnOperadAlgebraPathData.ofBase
    (n : Nat)
    {A : Type u}
    (base : AlgebraOverOperadPathData (LittleCubesOperad.enOperad n) A) :
    EnOperadAlgebraPathData n A where
  base := base
  iteratedUnitPath := fun x =>
    Path.trans
      (base.unitActionPath (base.act (LittleCubesOperad.identityCube n) (fun _ => x)))
      (base.unitActionPath x)
  iteratedUnitStep := fun x =>
    OperadicPathStep.right_unit
      (Path.trans
        (base.unitActionPath (base.act (LittleCubesOperad.identityCube n) (fun _ => x)))
        (base.unitActionPath x))

/-- Upgrade a plain `E_n`-algebra to path-preserving `E_n`-algebra data. -/
def EnOperadAlgebraPathData.ofEnAlgebra
    (n : Nat)
    (A : LittleCubesOperad.EnAlgebra n) :
    EnOperadAlgebraPathData n A.carrier :=
  EnOperadAlgebraPathData.ofBase n
    { act := A.act
      unitActionPath := fun x => LittleCubesOperad.EnAlgebra.unit_act_path A x
      equivariantPath := fun σ θ xs => Path.stepChain (A.equivariant σ θ xs)
      unitActionStep := fun x =>
        OperadAlgebraStep.right_unit (LittleCubesOperad.EnAlgebra.unit_act_path A x)
      equivariantStep := fun σ θ xs =>
        OperadAlgebraStep.left_unit (Path.stepChain (A.equivariant σ θ xs)) }

/-- Trivial `E_n`-operad algebra path data on `Unit`. -/
def EnOperadAlgebraPathData.trivial (n : Nat) : EnOperadAlgebraPathData n Unit :=
  EnOperadAlgebraPathData.ofBase n
    (AlgebraOverOperadPathData.trivial (LittleCubesOperad.enOperad n))

@[simp] theorem EnOperadAlgebraPathData.ofBase_base
    (n : Nat) {A : Type u}
    (base : AlgebraOverOperadPathData (LittleCubesOperad.enOperad n) A) :
    (EnOperadAlgebraPathData.ofBase n base).base = base := by
  sorry

@[simp] theorem EnOperadAlgebraPathData.ofBase_iteratedUnitPath
    (n : Nat) {A : Type u}
    (base : AlgebraOverOperadPathData (LittleCubesOperad.enOperad n) A)
    (x : A) :
    (EnOperadAlgebraPathData.ofBase n base).iteratedUnitPath x =
      Path.trans
        (base.unitActionPath (base.act (LittleCubesOperad.identityCube n) (fun _ => x)))
        (base.unitActionPath x) := by
  sorry

@[simp] theorem EnOperadAlgebraPathData.ofEnAlgebra_base_act
    (n : Nat)
    (A : LittleCubesOperad.EnAlgebra n)
    {k : Nat} (c : EnSpace n k) (xs : Fin k → A.carrier) :
    (EnOperadAlgebraPathData.ofEnAlgebra n A).base.act c xs = A.act c xs := by
  sorry

@[simp] theorem EnOperadAlgebraPathData.trivial_base_act
    (n : Nat) {k : Nat} (c : EnSpace n k) (xs : Fin k → Unit) :
    (EnOperadAlgebraPathData.trivial n).base.act c xs = () := by
  sorry

end OperadicAlgebra
end ComputationalPaths
