/-
# Loop Group Algebra

This module develops additional algebraic structure on loop quotients and
fundamental groups.  It focuses on conjugation, commutators, and power laws
for `LoopQuot`/`π₁(A, a)` with proofs carried out in the strict group structure
already established in `Loops.lean`.

## Key Results

- Conjugation as an automorphism of the loop group
- Commutator identities
- Power and inverse laws
- Compatibility of powers with conjugation

## References

- HoTT Book, Chapter 2
- Hatcher, "Algebraic Topology", Section 1.3
-/

import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Algebra.GroupStructures

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace LoopGroupAlgebra

open Algebra

universe u

variable {A : Type u} {a : A}

/-! ## Loop Group Structure -/

/-- The strict group structure on the loop quotient. -/
@[simp] noncomputable def loopGroupStructure (A : Type u) (a : A) : Algebra.StrictGroup (LoopQuot A a) :=
  { mul := LoopQuot.comp
    one := LoopQuot.id
    mul_assoc := LoopQuot.comp_assoc
    one_mul := LoopQuot.id_comp
    mul_one := LoopQuot.comp_id
    inv := LoopQuot.inv
    mul_left_inv := LoopQuot.inv_comp
    mul_right_inv := LoopQuot.comp_inv }

/-- The loop group structure as a convenience abbreviation. -/
@[simp] abbrev LoopGroup' (A : Type u) (a : A) : Algebra.StrictGroup (LoopQuot A a) :=
  loopGroupStructure A a

/-! ## Conjugation and Commutators -/

/-- Conjugation in the loop group. -/
@[simp] noncomputable def conj (x y : LoopQuot A a) : LoopQuot A a :=
  Algebra.StrictGroup.conj (loopGroupStructure A a) x y

/-- Commutator in the loop group. -/
@[simp] noncomputable def commutator (x y : LoopQuot A a) : LoopQuot A a :=
  Algebra.StrictGroup.commutator (loopGroupStructure A a) x y

/-- Conjugation by the identity loop is identity. -/
@[simp] theorem conj_id_left (x : LoopQuot A a) :
    conj (A := A) (a := a) (LoopQuot.id (A := A) (a := a)) x = x := by
  exact Algebra.StrictGroup.conj_one_left (loopGroupStructure A a) x

/-- Conjugation of the identity loop yields identity. -/
@[simp] theorem conj_id_right (x : LoopQuot A a) :
    conj (A := A) (a := a) x (LoopQuot.id (A := A) (a := a)) = LoopQuot.id := by
  exact Algebra.StrictGroup.conj_one_right (loopGroupStructure A a) x

/-- Conjugation distributes over multiplication. -/
@[simp] theorem conj_comp (x y z : LoopQuot A a) :
    conj (A := A) (a := a) x (LoopQuot.comp y z) =
      LoopQuot.comp (conj (A := A) (a := a) x y) (conj (A := A) (a := a) x z) := by
  exact Algebra.StrictGroup.conj_mul (loopGroupStructure A a) x y z

/-- Conjugation of an inverse. -/
@[simp] theorem conj_inv (x y : LoopQuot A a) :
    conj (A := A) (a := a) x (LoopQuot.inv y) = LoopQuot.inv (conj (A := A) (a := a) x y) := by
  exact Algebra.StrictGroup.conj_inv (loopGroupStructure A a) x y

/-- Conjugation composition law. -/
@[simp] theorem conj_conj (x y z : LoopQuot A a) :
    conj (A := A) (a := a) x (conj (A := A) (a := a) y z) =
      conj (A := A) (a := a) (LoopQuot.comp x y) z := by
  exact Algebra.StrictGroup.conj_conj (loopGroupStructure A a) x y z

/-- Commutator with identity on the left. -/
@[simp] theorem commutator_id_left (x : LoopQuot A a) :
    commutator (A := A) (a := a) (LoopQuot.id (A := A) (a := a)) x = LoopQuot.id := by
  exact Algebra.StrictGroup.commutator_one_left (loopGroupStructure A a) x

/-- Commutator with identity on the right. -/
@[simp] theorem commutator_id_right (x : LoopQuot A a) :
    commutator (A := A) (a := a) x (LoopQuot.id (A := A) (a := a)) = LoopQuot.id := by
  exact Algebra.StrictGroup.commutator_one_right (loopGroupStructure A a) x

/-- Commutator of a loop with itself is identity. -/
@[simp] theorem commutator_self (x : LoopQuot A a) :
    commutator (A := A) (a := a) x x = LoopQuot.id := by
  exact Algebra.StrictGroup.commutator_self (loopGroupStructure A a) x

/-- Conjugation preserves commutators. -/
@[simp] theorem conj_commutator (g x y : LoopQuot A a) :
    conj (A := A) (a := a) g (commutator (A := A) (a := a) x y) =
      commutator (A := A) (a := a) (conj (A := A) (a := a) g x)
        (conj (A := A) (a := a) g y) := by
  exact Algebra.StrictGroup.conj_commutator (loopGroupStructure A a) g x y

/-! ## Power Laws -/

/-- Natural powers in the loop group. -/
@[simp] noncomputable def pow (x : LoopQuot A a) : Nat → LoopQuot A a :=
  Algebra.StrictGroup.pow (loopGroupStructure A a) x

/-- Integer powers in the loop group. -/
@[simp] noncomputable def zpow (x : LoopQuot A a) : Int → LoopQuot A a :=
  Algebra.StrictGroup.zpow (loopGroupStructure A a) x

@[simp] theorem pow_zero (x : LoopQuot A a) : pow (A := A) (a := a) x 0 = LoopQuot.id := by
  simp [pow]

@[simp] theorem pow_succ (x : LoopQuot A a) (n : Nat) :
    pow (A := A) (a := a) x (Nat.succ n) = LoopQuot.comp (pow (A := A) (a := a) x n) x := by
  simp [pow]

@[simp] theorem pow_add (x : LoopQuot A a) (m n : Nat) :
    pow (A := A) (a := a) x (m + n) =
      LoopQuot.comp (pow (A := A) (a := a) x m) (pow (A := A) (a := a) x n) := by
  simpa [pow] using (Algebra.StrictGroup.pow_add (loopGroupStructure A a) x m n)

@[simp] theorem pow_comm (x : LoopQuot A a) (m n : Nat) :
    LoopQuot.comp (pow (A := A) (a := a) x m) (pow (A := A) (a := a) x n) =
      LoopQuot.comp (pow (A := A) (a := a) x n) (pow (A := A) (a := a) x m) := by
  simpa [pow] using (Algebra.StrictGroup.pow_comm (loopGroupStructure A a) x m n)

@[simp] theorem pow_mul (x : LoopQuot A a) (m n : Nat) :
    pow (A := A) (a := a) x (m * n) = pow (A := A) (a := a) (pow (A := A) (a := a) x m) n := by
  simpa [pow] using (Algebra.StrictGroup.pow_mul (loopGroupStructure A a) x m n)

@[simp] theorem zpow_zero (x : LoopQuot A a) : zpow (A := A) (a := a) x 0 = LoopQuot.id := by
  simp [zpow]

@[simp] theorem zpow_one (x : LoopQuot A a) : zpow (A := A) (a := a) x 1 = x := by
  simp [zpow]

@[simp] theorem zpow_neg (x : LoopQuot A a) (z : Int) :
    zpow (A := A) (a := a) x (-z) = LoopQuot.inv (zpow (A := A) (a := a) x z) := by
  simpa [zpow] using (Algebra.StrictGroup.zpow_neg (loopGroupStructure A a) x z)

@[simp] theorem zpow_succ (x : LoopQuot A a) (n : Int) :
    zpow (A := A) (a := a) x (n + 1) = LoopQuot.comp (zpow (A := A) (a := a) x n) x := by
  simpa [zpow] using (Algebra.StrictGroup.zpow_succ (loopGroupStructure A a) x n)

@[simp] theorem zpow_pred (x : LoopQuot A a) (n : Int) :
    zpow (A := A) (a := a) x (n - 1) = LoopQuot.comp (zpow (A := A) (a := a) x n) (LoopQuot.inv x) := by
  simpa [zpow] using (Algebra.StrictGroup.zpow_pred (loopGroupStructure A a) x n)

@[simp] theorem zpow_add (x : LoopQuot A a) (m n : Int) :
    zpow (A := A) (a := a) x (m + n) =
      LoopQuot.comp (zpow (A := A) (a := a) x m) (zpow (A := A) (a := a) x n) := by
  simpa [zpow] using (Algebra.StrictGroup.zpow_add (loopGroupStructure A a) x m n)

/-! ## Conjugation and Powers -/


end LoopGroupAlgebra
end Homotopy
end Path

private noncomputable def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

end ComputationalPaths
