/- 
# Cohomology Rings and Cup Products for Computational Paths

This module packages graded cohomology groups, the cup product, and
cohomology ring axioms in a lightweight form.  All equalities are provided
as definitional equations, with `Path` witnesses derived from them.
-/

import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u

/-! ## Graded cohomology groups -/

/-- Graded cohomology groups with abelian-group structure at each degree. -/
structure CohomologyGroups where
  /-- The carrier at each degree. -/
  carrier : Nat → Type u
  /-- Zero at each degree. -/
  zero : ∀ n, carrier n
  /-- Addition at each degree. -/
  add : ∀ n, carrier n → carrier n → carrier n
  /-- Negation at each degree. -/
  neg : ∀ n, carrier n → carrier n
  /-- Addition is commutative. -/
  add_comm : ∀ n (x y : carrier n), add n x y = add n y x
  /-- Addition is associative. -/
  add_assoc : ∀ n (x y z : carrier n), add n (add n x y) z = add n x (add n y z)
  /-- Zero is a left identity. -/
  zero_add : ∀ n (x : carrier n), add n (zero n) x = x
  /-- Left inverse. -/
  add_left_neg : ∀ n (x : carrier n), add n (neg n x) x = zero n

namespace CohomologyGroups

variable (H : CohomologyGroups)

/-- Right identity for addition. -/
theorem add_zero (n : Nat) (x : H.carrier n) : H.add n x (H.zero n) = x := by
  have h := H.add_comm n x (H.zero n)
  rw [h]
  exact H.zero_add n x

/-- Right inverse for addition. -/
theorem add_right_neg (n : Nat) (x : H.carrier n) :
    H.add n x (H.neg n x) = H.zero n := by
  have h := H.add_comm n x (H.neg n x)
  rw [h]
  exact H.add_left_neg n x

/-- `Path` witness of x + 0 = x. -/
def add_zero_path (n : Nat) (x : H.carrier n) :
    Path (H.add n x (H.zero n)) x :=
  Path.stepChain (H.add_zero n x)

/-- `Path` witness of x + (-x) = 0. -/
def add_right_neg_path (n : Nat) (x : H.carrier n) :
    Path (H.add n x (H.neg n x)) (H.zero n) :=
  Path.stepChain (H.add_right_neg n x)

end CohomologyGroups

/-! ## Cup products -/

/-- Cup product data on graded cohomology groups. -/
structure CupProduct (H : CohomologyGroups) where
  /-- Cup product: H^p x H^q -> H^{p+q}. -/
  cup : ∀ p q, H.carrier p → H.carrier q → H.carrier (p + q)
  /-- Cup product with zero on the left. -/
  cup_zero_left : ∀ p q (y : H.carrier q), cup p q (H.zero p) y = H.zero (p + q)
  /-- Cup product with zero on the right. -/
  cup_zero_right : ∀ p q (x : H.carrier p), cup p q x (H.zero q) = H.zero (p + q)
  /-- Left distributivity. -/
  cup_add_left : ∀ p q (x x' : H.carrier p) (y : H.carrier q),
    cup p q (H.add p x x') y =
      H.add (p + q) (cup p q x y) (cup p q x' y)
  /-- Right distributivity. -/
  cup_add_right : ∀ p q (x : H.carrier p) (y y' : H.carrier q),
    cup p q x (H.add q y y') =
      H.add (p + q) (cup p q x y) (cup p q x y')
  /-- Associativity (up to transport along `Nat.add_assoc`). -/
  cup_assoc : ∀ p q r (x : H.carrier p) (y : H.carrier q) (z : H.carrier r),
    cup (p + q) r (cup p q x y) z =
      _root_.cast (_root_.congrArg H.carrier (Nat.add_assoc p q r).symm)
        (cup p (q + r) x (cup q r y z))
  /-- Graded commutativity (up to transport along `Nat.add_comm`). -/
  cup_comm : ∀ p q (x : H.carrier p) (y : H.carrier q),
    cup p q x y =
      _root_.cast (_root_.congrArg H.carrier (Nat.add_comm q p)) (cup q p y x)

namespace CupProductLemmas

variable {H : CohomologyGroups} (C : CupProduct H)

/-- Path witness for associativity. -/
def cup_assoc_path (p q r : Nat) (x : H.carrier p) (y : H.carrier q) (z : H.carrier r) :
    Path (C.cup (p + q) r (C.cup p q x y) z)
      (_root_.cast (_root_.congrArg H.carrier (Nat.add_assoc p q r).symm)
        (C.cup p (q + r) x (C.cup q r y z))) :=
  Path.stepChain (C.cup_assoc p q r x y z)

/-- Path witness for graded commutativity. -/
def cup_comm_path (p q : Nat) (x : H.carrier p) (y : H.carrier q) :
    Path (C.cup p q x y)
      (_root_.cast (_root_.congrArg H.carrier (Nat.add_comm q p)) (C.cup q p y x)) :=
  Path.stepChain (C.cup_comm p q x y)

/-- Path witness for left distributivity. -/
def cup_add_left_path (p q : Nat) (x x' : H.carrier p) (y : H.carrier q) :
    Path (C.cup p q (H.add p x x') y)
      (H.add (p + q) (C.cup p q x y) (C.cup p q x' y)) :=
  Path.stepChain (C.cup_add_left p q x x' y)

/-- Path witness for right distributivity. -/
def cup_add_right_path (p q : Nat) (x : H.carrier p) (y y' : H.carrier q) :
    Path (C.cup p q x (H.add q y y'))
      (H.add (p + q) (C.cup p q x y) (C.cup p q x y')) :=
  Path.stepChain (C.cup_add_right p q x y y')

/-- Path witness for cup product with zero on the left. -/
def cup_zero_left_path (p q : Nat) (y : H.carrier q) :
    Path (C.cup p q (H.zero p) y) (H.zero (p + q)) :=
  Path.stepChain (C.cup_zero_left p q y)

/-- Path witness for cup product with zero on the right. -/
def cup_zero_right_path (p q : Nat) (x : H.carrier p) :
    Path (C.cup p q x (H.zero q)) (H.zero (p + q)) :=
  Path.stepChain (C.cup_zero_right p q x)

end CupProductLemmas

/-! ## Cohomology rings -/

/-- Cohomology rings: graded groups with a unital, graded-commutative cup product. -/
structure CohomologyRing extends CohomologyGroups where
  /-- The unit element in degree 0. -/
  one : carrier 0
  /-- Cup product: H^p x H^q -> H^{p+q}. -/
  cup : ∀ p q, carrier p → carrier q → carrier (p + q)
  /-- Cup product with zero on the left. -/
  cup_zero_left : ∀ p q (y : carrier q), cup p q (zero p) y = zero (p + q)
  /-- Cup product with zero on the right. -/
  cup_zero_right : ∀ p q (x : carrier p), cup p q x (zero q) = zero (p + q)
  /-- Left distributivity. -/
  cup_add_left : ∀ p q (x x' : carrier p) (y : carrier q),
    cup p q (add p x x') y =
      add (p + q) (cup p q x y) (cup p q x' y)
  /-- Right distributivity. -/
  cup_add_right : ∀ p q (x : carrier p) (y y' : carrier q),
    cup p q x (add q y y') =
      add (p + q) (cup p q x y) (cup p q x y')
  /-- Associativity (up to transport along `Nat.add_assoc`). -/
  cup_assoc : ∀ p q r (x : carrier p) (y : carrier q) (z : carrier r),
    cup (p + q) r (cup p q x y) z =
      _root_.cast (_root_.congrArg carrier (Nat.add_assoc p q r).symm)
        (cup p (q + r) x (cup q r y z))
  /-- Graded commutativity (up to transport along `Nat.add_comm`). -/
  cup_comm : ∀ p q (x : carrier p) (y : carrier q),
    cup p q x y =
      _root_.cast (_root_.congrArg carrier (Nat.add_comm q p)) (cup q p y x)
  /-- Left unit for the cup product. -/
  cup_one_left : ∀ n (x : carrier n),
    cup 0 n one x =
      _root_.cast (_root_.congrArg carrier (Nat.zero_add n).symm) x
  /-- Right unit for the cup product. -/
  cup_one_right : ∀ n (x : carrier n),
    cup n 0 x one =
      _root_.cast (_root_.congrArg carrier (Nat.add_zero n).symm) x

namespace CohomologyRing

variable (R : CohomologyRing)

/-- Cup product data obtained from a cohomology ring. -/
def cupProduct : CupProduct R.toCohomologyGroups where
  cup := R.cup
  cup_zero_left := R.cup_zero_left
  cup_zero_right := R.cup_zero_right
  cup_add_left := R.cup_add_left
  cup_add_right := R.cup_add_right
  cup_assoc := R.cup_assoc
  cup_comm := R.cup_comm

/-- Path witness for associativity. -/
def cup_assoc_path (p q r : Nat) (x : R.carrier p) (y : R.carrier q) (z : R.carrier r) :
    Path (R.cup (p + q) r (R.cup p q x y) z)
      (_root_.cast (_root_.congrArg R.carrier (Nat.add_assoc p q r).symm)
        (R.cup p (q + r) x (R.cup q r y z))) :=
  Path.stepChain (R.cup_assoc p q r x y z)

/-- Path witness for graded commutativity. -/
def cup_comm_path (p q : Nat) (x : R.carrier p) (y : R.carrier q) :
    Path (R.cup p q x y)
      (_root_.cast (_root_.congrArg R.carrier (Nat.add_comm q p)) (R.cup q p y x)) :=
  Path.stepChain (R.cup_comm p q x y)

/-- Path witness for left distributivity. -/
def cup_add_left_path (p q : Nat) (x x' : R.carrier p) (y : R.carrier q) :
    Path (R.cup p q (R.add p x x') y)
      (R.add (p + q) (R.cup p q x y) (R.cup p q x' y)) :=
  Path.stepChain (R.cup_add_left p q x x' y)

/-- Path witness for right distributivity. -/
def cup_add_right_path (p q : Nat) (x : R.carrier p) (y y' : R.carrier q) :
    Path (R.cup p q x (R.add q y y'))
      (R.add (p + q) (R.cup p q x y) (R.cup p q x y')) :=
  Path.stepChain (R.cup_add_right p q x y y')

/-- Path witness for cup product with zero on the left. -/
def cup_zero_left_path (p q : Nat) (y : R.carrier q) :
    Path (R.cup p q (R.zero p) y) (R.zero (p + q)) :=
  Path.stepChain (R.cup_zero_left p q y)

/-- Path witness for cup product with zero on the right. -/
def cup_zero_right_path (p q : Nat) (x : R.carrier p) :
    Path (R.cup p q x (R.zero q)) (R.zero (p + q)) :=
  Path.stepChain (R.cup_zero_right p q x)

/-- Path witness for the left unit. -/
def cup_one_left_path (n : Nat) (x : R.carrier n) :
    Path (R.cup 0 n R.one x)
      (_root_.cast (_root_.congrArg R.carrier (Nat.zero_add n).symm) x) :=
  Path.stepChain (R.cup_one_left n x)

/-- Path witness for the right unit. -/
def cup_one_right_path (n : Nat) (x : R.carrier n) :
    Path (R.cup n 0 x R.one)
      (_root_.cast (_root_.congrArg R.carrier (Nat.add_zero n).symm) x) :=
  Path.stepChain (R.cup_one_right n x)

end CohomologyRing

/-! ## Examples -/

/-- The trivial cohomology ring with one element in every degree. -/
def CohomologyRing.trivial : CohomologyRing.{u} where
  carrier := fun _ => PUnit
  zero := fun _ => PUnit.unit
  add := fun _ _ _ => PUnit.unit
  neg := fun _ _ => PUnit.unit
  add_comm := by intro _ _ _; rfl
  add_assoc := by intro _ _ _ _; rfl
  zero_add := by intro _ _; rfl
  add_left_neg := by intro _ _; rfl
  one := PUnit.unit
  cup := fun _ _ _ _ => PUnit.unit
  cup_zero_left := by intro _ _ _; rfl
  cup_zero_right := by intro _ _ _; rfl
  cup_add_left := by intro _ _ _ _ _; rfl
  cup_add_right := by intro _ _ _ _ _; rfl
  cup_assoc := by intro _ _ _ _ _ _; rfl
  cup_comm := by intro _ _ _ _; rfl
  cup_one_left := by intro _ _; rfl
  cup_one_right := by intro _ _; rfl

end Algebra
end Path
end ComputationalPaths
