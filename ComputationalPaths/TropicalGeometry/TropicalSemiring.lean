import Mathlib.Algebra.Tropical.Basic
import Mathlib.Data.Real.Basic

namespace ComputationalPathsLean
namespace TropicalGeometry

open Tropical

noncomputable section

/-- The min-plus tropical semiring on `ℝ ∪ {∞}`. -/
abbrev TropicalSemiring : Type := Tropical (WithTop ℝ)

/-- Tropical addition (`⊕`) is minimum on the underlying values. -/
def tAdd : TropicalSemiring → TropicalSemiring → TropicalSemiring := (· + ·)

/-- Tropical multiplication (`⊗`) is ordinary addition on the underlying values. -/
def tMul : TropicalSemiring → TropicalSemiring → TropicalSemiring := (· * ·)

/-- Tropical additive identity (`∞`). -/
def tZero : TropicalSemiring := 0

/-- Tropical multiplicative identity (`0`). -/
def tOne : TropicalSemiring := 1

/-- `TropicalSemiring` is a commutative semiring. -/
def tropicalCommSemiring : CommSemiring TropicalSemiring := inferInstance

@[simp] theorem untrop_tAdd (a b : TropicalSemiring) :
    Tropical.untrop (tAdd a b) = min (Tropical.untrop a) (Tropical.untrop b) := rfl

@[simp] theorem untrop_tMul (a b : TropicalSemiring) :
    Tropical.untrop (tMul a b) = Tropical.untrop a + Tropical.untrop b := rfl

@[simp] theorem untrop_tZero : Tropical.untrop tZero = (⊤ : WithTop ℝ) := rfl

@[simp] theorem untrop_tOne : Tropical.untrop tOne = (0 : WithTop ℝ) := rfl

theorem tAdd_assoc (a b c : TropicalSemiring) :
    tAdd (tAdd a b) c = tAdd a (tAdd b c) := by
  simpa [tAdd] using add_assoc a b c

theorem tAdd_comm (a b : TropicalSemiring) :
    tAdd a b = tAdd b a := by
  simpa [tAdd] using add_comm a b

theorem tMul_assoc (a b c : TropicalSemiring) :
    tMul (tMul a b) c = tMul a (tMul b c) := by
  simpa [tMul] using mul_assoc a b c

theorem tMul_comm (a b : TropicalSemiring) :
    tMul a b = tMul b a := by
  simpa [tMul] using mul_comm a b

theorem tZero_tAdd (a : TropicalSemiring) :
    tAdd tZero a = a := by
  simp [tAdd, tZero]

theorem tAdd_tZero (a : TropicalSemiring) :
    tAdd a tZero = a := by
  simp [tAdd, tZero]

theorem tOne_tMul (a : TropicalSemiring) :
    tMul tOne a = a := by
  simp [tMul, tOne]

theorem tMul_tOne (a : TropicalSemiring) :
    tMul a tOne = a := by
  simp [tMul, tOne]

theorem tMul_tAdd_left_distrib (a b c : TropicalSemiring) :
    tMul a (tAdd b c) = tAdd (tMul a b) (tMul a c) := by
  simpa [tAdd, tMul] using (left_distrib a b c)

theorem tMul_tAdd_right_distrib (a b c : TropicalSemiring) :
    tMul (tAdd a b) c = tAdd (tMul a c) (tMul b c) := by
  simpa [tAdd, tMul] using (right_distrib a b c)

theorem tZero_tMul (a : TropicalSemiring) :
    tMul tZero a = tZero := by
  simp [tMul, tZero]

theorem tMul_tZero (a : TropicalSemiring) :
    tMul a tZero = tZero := by
  simp [tMul, tZero]

theorem tAdd_eq_min (a b : TropicalSemiring) :
    tAdd a b = Tropical.trop (min (Tropical.untrop a) (Tropical.untrop b)) := rfl

theorem tMul_eq_add (a b : TropicalSemiring) :
    tMul a b = Tropical.trop (Tropical.untrop a + Tropical.untrop b) := rfl

end

end TropicalGeometry
end ComputationalPathsLean
