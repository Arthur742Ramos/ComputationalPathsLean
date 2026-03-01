/-
# Higher Homotopy Groups (computational paths)

This module exposes the computational-path definition of higher homotopy groups
`πₙ` and records the abelian-range group laws as `Path` witnesses.

## Key Results

- `PiN`: the n-th homotopy group from `HigherHomotopy`
- `piN_mul`, `piN_one`, `piN_inv`: operations on πₙ used for `n ≥ 2`
- basic group laws as `Path`s (`piN_mul_assoc`, `piN_one_mul`, `piN_mul_one`,
  `piN_inv_mul_self`, `piN_mul_inv_self`, `piN_mul_comm`)

## References

- `Path.Homotopy.HigherHomotopy`
-/

import Mathlib.Data.Nat.Init
import ComputationalPaths.Path.Homotopy.HigherHomotopy

namespace ComputationalPaths
namespace Path
namespace HigherHomotopyGroups

universe u

variable {X : Type u}

private lemma atLeastTwo_false_zero [Nat.AtLeastTwo 0] : False :=
  (Nat.not_succ_le_zero 1 (Nat.AtLeastTwo.prop (n := 0)))

private lemma atLeastTwo_false_one [Nat.AtLeastTwo 1] : False :=
  (Nat.not_succ_le_self 1 (Nat.AtLeastTwo.prop (n := 1)))

/-- The n-th homotopy group `πₙ(X, x)` from `HigherHomotopy`. -/
abbrev PiN (n : Nat) (X : Type u) (x : X) : Type (u + 2) :=
  HigherHomotopy.PiN n X x

/-- Multiplication on πₙ in the computational-path model. -/
noncomputable def piN_mul (n : Nat) (x : X) : PiN n X x → PiN n X x → PiN n X x :=
  match n with
  | 0 => fun _ _ => PUnit.unit
  | 1 => PiOne.mul (A := X) (a := x)
  | 2 => HigherHomotopy.PiTwo.mul (A := X) (a := x)
  | _ + 3 => fun _ _ => PUnit.unit

/-- Identity in πₙ in the computational-path model. -/
noncomputable def piN_one (n : Nat) (x : X) : PiN n X x :=
  match n with
  | 0 => PUnit.unit
  | 1 => PiOne.id (A := X) (a := x)
  | 2 => HigherHomotopy.PiTwo.id (A := X) (a := x)
  | _ + 3 => PUnit.unit

/-- Inverse in πₙ in the computational-path model. -/
noncomputable def piN_inv (n : Nat) (x : X) : PiN n X x → PiN n X x :=
  match n with
  | 0 => fun _ => PUnit.unit
  | 1 => PiOne.inv (A := X) (a := x)
  | 2 => HigherHomotopy.PiTwo.inv (A := X) (a := x)
  | _ + 3 => fun _ => PUnit.unit

noncomputable def piN_mul_assoc (n : Nat) [Nat.AtLeastTwo n] {x : X}
    (a b c : PiN n X x) :
    Path
      (piN_mul n x (piN_mul n x a b) c)
      (piN_mul n x a (piN_mul n x b c)) := by
  cases n with
  | zero =>
      cases atLeastTwo_false_zero
  | succ n =>
      cases n with
      | zero =>
          cases atLeastTwo_false_one
      | succ n =>
          cases n with
          | zero =>
              exact Path.stepChain
                (HigherHomotopy.PiTwo.mul_assoc (A := X) (a := x) a b c)
          | succ _ =>
              cases a
              cases b
              cases c
              exact Path.refl _

noncomputable def piN_one_mul (n : Nat) [Nat.AtLeastTwo n] {x : X}
    (a : PiN n X x) :
    Path (piN_mul n x (piN_one n x) a) a := by
  cases n with
  | zero =>
      cases atLeastTwo_false_zero
  | succ n =>
      cases n with
      | zero =>
          cases atLeastTwo_false_one
      | succ n =>
          cases n with
          | zero =>
              exact Path.stepChain
                (HigherHomotopy.PiTwo.id_mul (A := X) (a := x) a)
          | succ _ =>
              cases a
              exact Path.refl _

noncomputable def piN_mul_one (n : Nat) [Nat.AtLeastTwo n] {x : X}
    (a : PiN n X x) :
    Path (piN_mul n x a (piN_one n x)) a := by
  cases n with
  | zero =>
      cases atLeastTwo_false_zero
  | succ n =>
      cases n with
      | zero =>
          cases atLeastTwo_false_one
      | succ n =>
          cases n with
          | zero =>
              exact Path.stepChain
                (HigherHomotopy.PiTwo.mul_id (A := X) (a := x) a)
          | succ _ =>
              cases a
              exact Path.refl _

noncomputable def piN_inv_mul_self (n : Nat) [Nat.AtLeastTwo n] {x : X}
    (a : PiN n X x) :
    Path (piN_mul n x (piN_inv n x a) a) (piN_one n x) := by
  cases n with
  | zero =>
      cases atLeastTwo_false_zero
  | succ n =>
      cases n with
      | zero =>
          cases atLeastTwo_false_one
      | succ n =>
          cases n with
          | zero =>
              exact Path.stepChain
                (HigherHomotopy.PiTwo.mul_left_inv (A := X) (a := x) a)
          | succ _ =>
              cases a
              exact Path.refl _

noncomputable def piN_mul_inv_self (n : Nat) [Nat.AtLeastTwo n] {x : X}
    (a : PiN n X x) :
    Path (piN_mul n x a (piN_inv n x a)) (piN_one n x) := by
  cases n with
  | zero =>
      cases atLeastTwo_false_zero
  | succ n =>
      cases n with
      | zero =>
          cases atLeastTwo_false_one
      | succ n =>
          cases n with
          | zero =>
              exact Path.stepChain
                (HigherHomotopy.PiTwo.mul_right_inv (A := X) (a := x) a)
          | succ _ =>
              cases a
              exact Path.refl _

noncomputable def piN_mul_comm (n : Nat) [Nat.AtLeastTwo n] {x : X}
    (a b : PiN n X x) :
    Path (piN_mul n x a b) (piN_mul n x b a) := by
  cases n with
  | zero =>
      cases atLeastTwo_false_zero
  | succ n =>
      cases n with
      | zero =>
          cases atLeastTwo_false_one
      | succ n =>
          cases n with
          | zero =>
              exact Path.stepChain
                (HigherHomotopy.piTwo_comm (A := X) (a := x) a b)
          | succ _ =>
              cases a
              cases b
              exact Path.refl _

end HigherHomotopyGroups
end Path
end ComputationalPaths
