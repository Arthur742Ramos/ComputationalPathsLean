/-
# Covering and Fibration Algebra

This module develops algebraic lemmas for covering spaces and fibrations in the
computational paths setting.  We package the fundamental-group action on fibers
as a strict group action, derive inverse and power laws, and connect these
identities with the connecting map from fibration theory.

## Key Results

- `fiberActionGroupAction`: π₁-action on fibers as a strict group action
- `fiberAction_inv`, `fiberAction_pow`, `fiberAction_zpow`
- `connectingMapPi1_comp`: connecting map respects loop composition
- Compatibility between connecting maps and fiber actions

## References

- HoTT Book, Chapter 8
- Brown, "Topology and Groupoids"
-/

import ComputationalPaths.Path.Homotopy.CoveringSpace
import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.LoopIteration
import ComputationalPaths.Path.Homotopy.IntArith
import ComputationalPaths.Path.Homotopy.LoopGroupAlgebra
import ComputationalPaths.Path.Algebra.GroupStructures

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace CoveringFibrationAlgebra

open CoveringSpace Fibration
open Algebra

universe u

variable {A : Type u}

/-! ## Fiber Actions as Group Actions -/

/-- The strict group structure on `LoopQuot` used for fiber actions. -/
@[simp] def loopGroupStructure (A : Type u) (a : A) : StrictGroup (LoopQuot A a) :=
  LoopGroupAlgebra.loopGroupStructure A a

/-- The π₁-action on fibers packaged as a strict group action. -/
noncomputable def fiberActionGroupAction {P : A → Type u} (a : A) :
    GroupAction (LoopQuot A a) (loopGroupStructure A a) (P a) where
  act := fiberAction (P := P) (a := a)
  act_one := by
    intro x
    simpa [LoopQuot.id] using (fiberAction_id (P := P) (a := a) x)
  act_mul := by
    intro g h x
    simpa [LoopQuot.comp] using (fiberAction_comp (P := P) (a := a) g h x).symm

/-- Fiber action respects identity (restated). -/
@[simp] theorem fiberAction_one {P : A → Type u} {a : A} (x : P a) :
    fiberAction (P := P) (a := a) (LoopQuot.id (A := A) (a := a)) x = x := by
  simpa [LoopQuot.id] using (fiberAction_id (P := P) (a := a) x)

/-- Fiber action respects composition (restated). -/
@[simp] theorem fiberAction_mul {P : A → Type u} {a : A}
    (g h : LoopQuot A a) (x : P a) :
    fiberAction (P := P) (a := a) g (fiberAction (P := P) (a := a) h x) =
      fiberAction (P := P) (a := a) (LoopQuot.comp g h) x := by
  simpa [LoopQuot.comp] using (fiberAction_comp (P := P) (a := a) g h x)

/-! ## Inverse and Cancellation Laws -/

/-- Action of an inverse loop cancels the action. -/
theorem fiberAction_inv_left {P : A → Type u} {a : A}
    (g : LoopQuot A a) (x : P a) :
    fiberAction (P := P) (a := a) (LoopQuot.inv g)
      (fiberAction (P := P) (a := a) g x) = x := by
  have h := fiberAction_mul (P := P) (a := a) (LoopQuot.inv g) g x
  calc
    fiberAction (P := P) (a := a) (LoopQuot.inv g)
        (fiberAction (P := P) (a := a) g x)
        = fiberAction (P := P) (a := a)
            (LoopQuot.comp (LoopQuot.inv g) g) x := h
    _ = fiberAction (P := P) (a := a) (LoopQuot.id (A := A) (a := a)) x := by
          simpa [LoopQuot.inv_comp]
    _ = x := fiberAction_one (P := P) (a := a) (x := x)

/-- Action of a loop cancels the action of its inverse. -/
theorem fiberAction_inv_right {P : A → Type u} {a : A}
    (g : LoopQuot A a) (x : P a) :
    fiberAction (P := P) (a := a) g
      (fiberAction (P := P) (a := a) (LoopQuot.inv g) x) = x := by
  have h := fiberAction_mul (P := P) (a := a) g (LoopQuot.inv g) x
  calc
    fiberAction (P := P) (a := a) g
        (fiberAction (P := P) (a := a) (LoopQuot.inv g) x)
        = fiberAction (P := P) (a := a)
            (LoopQuot.comp g (LoopQuot.inv g)) x := h
    _ = fiberAction (P := P) (a := a) (LoopQuot.id (A := A) (a := a)) x := by
          simpa [LoopQuot.comp_inv]
    _ = x := fiberAction_one (P := P) (a := a) (x := x)

/-- Left cancellation for the fiber action. -/
theorem fiberAction_left_cancel {P : A → Type u} {a : A}
    {g h : LoopQuot A a} {x y : P a}
    (hxy : fiberAction (P := P) (a := a) g x = fiberAction (P := P) (a := a) g y) :
    x = y := by
  have h' :=
    _root_.congrArg (fun z => fiberAction (P := P) (a := a) (LoopQuot.inv g) z) hxy
  have hx : fiberAction (P := P) (a := a) (LoopQuot.inv g)
      (fiberAction (P := P) (a := a) g x) = x :=
    fiberAction_inv_left (P := P) (a := a) (g := g) x
  have hy : fiberAction (P := P) (a := a) (LoopQuot.inv g)
      (fiberAction (P := P) (a := a) g y) = y :=
    fiberAction_inv_left (P := P) (a := a) (g := g) y
  exact hx.symm.trans (h'.trans hy)

/-! ## Iterated Actions -/

/-- Iterated action of a loop on the fiber. -/
noncomputable def actionIter {P : A → Type u} {a : A} (g : LoopQuot A a) (n : Nat) (x : P a) : P a :=
  fiberAction (P := P) (a := a) (LoopQuot.pow g n) x

@[simp] theorem actionIter_zero {P : A → Type u} {a : A} (g : LoopQuot A a) (x : P a) :
    actionIter (P := P) (a := a) g 0 x = x := by
  simpa [actionIter, LoopQuot.pow] using
    (fiberAction_one (P := P) (a := a) (x := x))

@[simp] theorem actionIter_succ {P : A → Type u} {a : A} (g : LoopQuot A a) (n : Nat) (x : P a) :
    actionIter (P := P) (a := a) g (Nat.succ n) x =
      actionIter (P := P) (a := a) g n (fiberAction (P := P) (a := a) g x) := by
  have h := fiberAction_mul (P := P) (a := a) (LoopQuot.pow g n) g x
  simpa [actionIter, LoopQuot.pow] using h

/-- Iterated action respects addition. -/
@[simp] theorem actionIter_add {P : A → Type u} {a : A}
    (g : LoopQuot A a) (m n : Nat) (x : P a) :
    actionIter (P := P) (a := a) g (m + n) x =
      actionIter (P := P) (a := a) g m (actionIter (P := P) (a := a) g n x) := by
  have h := fiberAction_mul (P := P) (a := a) (LoopQuot.pow g m) (LoopQuot.pow g n) x
  calc
    actionIter (P := P) (a := a) g (m + n) x
        = fiberAction (P := P) (a := a) (LoopQuot.pow g (m + n)) x := rfl
    _ = fiberAction (P := P) (a := a)
          (LoopQuot.comp (LoopQuot.pow g m) (LoopQuot.pow g n)) x := by
          simpa [LoopQuot.pow_add]
    _ = actionIter (P := P) (a := a) g m (actionIter (P := P) (a := a) g n x) := by
          simpa [actionIter] using h

/-- Fiber action of powers equals iterated action. -/
theorem fiberAction_pow {P : A → Type u} {a : A}
    (g : LoopQuot A a) (n : Nat) (x : P a) :
    fiberAction (P := P) (a := a) (LoopQuot.pow g n) x =
      actionIter (P := P) (a := a) g n x := rfl

/-- Power action at zero. -/
@[simp] theorem fiberAction_pow_zero {P : A → Type u} {a : A}
    (g : LoopQuot A a) (x : P a) :
    fiberAction (P := P) (a := a) (LoopQuot.pow g 0) x = x := by
  simpa [LoopQuot.pow] using (fiberAction_one (P := P) (a := a) (x := x))

/-- Power action at successor. -/
@[simp] theorem fiberAction_pow_succ {P : A → Type u} {a : A}
    (g : LoopQuot A a) (n : Nat) (x : P a) :
    fiberAction (P := P) (a := a) (LoopQuot.pow g (Nat.succ n)) x =
      fiberAction (P := P) (a := a) (LoopQuot.pow g n) (fiberAction (P := P) (a := a) g x) := by
  have h := fiberAction_mul (P := P) (a := a) (LoopQuot.pow g n) g x
  simpa [LoopQuot.pow] using h

/-- Power action respects addition. -/
theorem fiberAction_pow_add {P : A → Type u} {a : A}
    (g : LoopQuot A a) (m n : Nat) (x : P a) :
    fiberAction (P := P) (a := a) (LoopQuot.pow g (m + n)) x =
      fiberAction (P := P) (a := a) (LoopQuot.pow g m)
        (fiberAction (P := P) (a := a) (LoopQuot.pow g n) x) := by
  have h := fiberAction_mul (P := P) (a := a) (LoopQuot.pow g m) (LoopQuot.pow g n) x
  calc
    fiberAction (P := P) (a := a) (LoopQuot.pow g (m + n)) x
        = fiberAction (P := P) (a := a)
            (LoopQuot.comp (LoopQuot.pow g m) (LoopQuot.pow g n)) x := by
            simpa [LoopQuot.pow_add]
    _ = fiberAction (P := P) (a := a) (LoopQuot.pow g m)
          (fiberAction (P := P) (a := a) (LoopQuot.pow g n) x) := by
          simpa using h

/-! ## Integer Powers -/

/-- Iterated action for integer powers. -/
noncomputable def actionIterZ {P : A → Type u} {a : A} (g : LoopQuot A a) (n : Int) (x : P a) : P a :=
  fiberAction (P := P) (a := a) (LoopQuot.zpow g n) x

@[simp] theorem actionIterZ_ofNat {P : A → Type u} {a : A} (g : LoopQuot A a) (n : Nat) (x : P a) :
    actionIterZ (P := P) (a := a) g (Int.ofNat n) x = actionIter (P := P) (a := a) g n x := by
  rfl

theorem actionIterZ_negSucc {P : A → Type u} {a : A} (g : LoopQuot A a) (n : Nat) (x : P a) :
    actionIterZ (P := P) (a := a) g (Int.negSucc n) x =
      actionIter (P := P) (a := a) (LoopQuot.inv g) (Nat.succ n) x := by
  have hpow :
      LoopQuot.inv (LoopQuot.pow g (Nat.succ n)) =
        LoopQuot.pow (LoopQuot.inv g) (Nat.succ n) := by
    induction n with
    | zero =>
        simp [LoopQuot.pow]
    | succ n ih =>
        calc
          LoopQuot.inv (LoopQuot.pow g (Nat.succ (Nat.succ n)))
              = LoopQuot.inv (LoopQuot.comp (LoopQuot.pow g (Nat.succ n)) g) := rfl
          _ = LoopQuot.comp (LoopQuot.inv g) (LoopQuot.inv (LoopQuot.pow g (Nat.succ n))) := by
                simpa using (LoopQuot.inv_comp_eq (A := A) (a := a)
                  (x := LoopQuot.pow g (Nat.succ n)) (y := g))
          _ = LoopQuot.comp (LoopQuot.inv g) (LoopQuot.pow (LoopQuot.inv g) (Nat.succ n)) := by
                exact _root_.congrArg (fun z => LoopQuot.comp (LoopQuot.inv g) z) ih
          _ = LoopQuot.pow (LoopQuot.inv g) (Nat.succ (Nat.succ n)) := by
                exact (LoopQuot.pow_succ' (A := A) (a := a)
                  (x := LoopQuot.inv g) (n := Nat.succ n)).symm
  calc
    actionIterZ (P := P) (a := a) g (Int.negSucc n) x
        = fiberAction (P := P) (a := a) (LoopQuot.inv (LoopQuot.pow g (Nat.succ n))) x := rfl
    _ = fiberAction (P := P) (a := a) (LoopQuot.pow (LoopQuot.inv g) (Nat.succ n)) x := by
          exact _root_.congrArg (fun z => fiberAction (P := P) (a := a) z x) hpow
    _ = actionIter (P := P) (a := a) (LoopQuot.inv g) (Nat.succ n) x := rfl

/-- Fiber action of integer powers equals iterated action. -/
theorem fiberAction_zpow {P : A → Type u} {a : A}
    (g : LoopQuot A a) (n : Int) (x : P a) :
    fiberAction (P := P) (a := a) (LoopQuot.zpow g n) x =
      actionIterZ (P := P) (a := a) g n x := rfl

/-! ## Conjugation Action -/

-- Conjugation and commutator action lemmas are available via LoopGroupAlgebra.

/-! ## Connecting Maps and Fiber Actions -/

/-- Connecting map agrees with the loop action on fibers. -/
@[simp] theorem connectingMap₁_eq_loopAction {P : A → Type u} (a : A) (x₀ : P a)
    (l : LoopSpace A a) :
    connectingMap₁ (P := P) a x₀ l = loopAction (P := P) l x₀ := rfl

/-- Connecting map agrees with the fiber action on π₁. -/
theorem connectingMapPi1_eq_fiberAction {P : A → Type u} (a : A) (x₀ : P a) :
    connectingMapPi1 (P := P) a x₀ = fun g => fiberAction (P := P) (a := a) g x₀ := by
  funext g
  induction g using Quot.ind with
  | _ l => rfl

/-- Connecting map respects identity. -/
@[simp] theorem connectingMapPi1_id {P : A → Type u} (a : A) (x₀ : P a) :
    connectingMapPi1 (P := P) a x₀ (LoopQuot.id (A := A) (a := a)) = x₀ := by
  simpa [LoopQuot.id] using (connectingMap₁_refl (P := P) a x₀)

/-- Connecting map respects loop composition. -/
@[simp] theorem connectingMapPi1_comp {P : A → Type u} (a : A) (x₀ : P a)
    (α β : LoopQuot A a) :
    connectingMapPi1 (P := P) a x₀ (LoopQuot.comp α β) =
      connectingMapPi1 (P := P) a (connectingMapPi1 (P := P) a x₀ α) β := by
  induction α using Quot.ind with
  | _ p =>
      induction β using Quot.ind with
      | _ q =>
          simpa [connectingMapPi1, LoopQuot.comp] using
            (connectingMap₁_trans (P := P) a x₀ p q)

end CoveringFibrationAlgebra
end Homotopy
end Path
end ComputationalPaths
