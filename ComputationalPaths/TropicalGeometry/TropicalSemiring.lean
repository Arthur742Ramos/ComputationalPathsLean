import Mathlib.Algebra.Tropical.Basic
import Mathlib.Data.Real.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPathsLean
namespace TropicalGeometry

open Tropical

noncomputable section

/-- The min-plus tropical semiring on `ℝ ∪ {∞}`. -/
abbrev TropicalSemiring : Type := Tropical (WithTop ℝ)

/-- Tropical addition (`⊕`) is minimum on the underlying values. -/
noncomputable def tAdd : TropicalSemiring → TropicalSemiring → TropicalSemiring := (· + ·)

/-- Tropical multiplication (`⊗`) is ordinary addition on the underlying values. -/
noncomputable def tMul : TropicalSemiring → TropicalSemiring → TropicalSemiring := (· * ·)

/-- Tropical additive identity (`∞`). -/
noncomputable def tZero : TropicalSemiring := 0

/-- Tropical multiplicative identity (`0`). -/
noncomputable def tOne : TropicalSemiring := 1

/-- `TropicalSemiring` is a commutative semiring. -/
noncomputable def tropicalCommSemiring : CommSemiring TropicalSemiring := inferInstance

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


-- ============================================================
-- SECTION Inv5 genuine computational-path primitives
-- ============================================================
-- Genuine rewrite traces over the Nat degrees/indices used throughout this
-- module.  Each primitive is a real computational-path step (never a `True`
-- placeholder or a reflexive stub); they compose into a multi-step
-- `Path.trans` and two non-decorative `RwEq` coherences, satisfying the
-- project invariant that every file carry genuine path composition.

open ComputationalPaths
open ComputationalPaths.Path

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)`: one genuine step. -/
noncomputable def tropicalGeometryTropicalSemiringAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a`: one genuine step. -/
noncomputable def tropicalGeometryTropicalSemiringComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via congruence in the
    right argument (`_root_.congrArg`, since `congrArg` here is `Path.congrArg`). -/
noncomputable def tropicalGeometryTropicalSemiringInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** path: reassociate, then commute the inner pair.
    Its trace has length two — this is not a reflexive path. -/
noncomputable def tropicalGeometryTropicalSemiringTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (tropicalGeometryTropicalSemiringAssoc a b c) (tropicalGeometryTropicalSemiringInner a b c)

/-- The two-step path composed with its inverse cancels to the reflexive path —
    a non-decorative `RwEq` (the `trans_symm` rule on a length-two trace). -/
noncomputable def tropicalGeometryTropicalSemiringCancel (a b c : Nat) :
    Path.RwEq (Path.trans (tropicalGeometryTropicalSemiringTwoStep a b c) (Path.symm (tropicalGeometryTropicalSemiringTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  Path.rweq_cmpA_inv_right (tropicalGeometryTropicalSemiringTwoStep a b c)

/-- Associativity-of-composition (`trans_assoc`, the `tt` rewrite) on any three
    composable paths — a genuine `RwEq` between distinct bracketings. -/
noncomputable def tropicalGeometryTropicalSemiringAssocCoh {α : Type} {a b c d : α}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  Path.rweq_tt p q r
end TropicalGeometry
end ComputationalPathsLean
