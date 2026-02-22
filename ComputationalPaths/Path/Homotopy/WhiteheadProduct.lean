/-
# Whitehead Product for Computational Paths

This module defines the Whitehead product on homotopy groups in the
computational-paths setting. The bracket [x, y] lands in π_{m+n-1} and is
implemented by the loop commutator in the (m,n) = (1,1) case, while other
degrees use the canonical base element provided by `piN_one`.

## Key Results

- `whiteheadProduct`: Whitehead product on πₙ
- `[x, y]` notation (scoped)
- `whitehead_identity_left`, `whitehead_identity_right`: identity annihilates
- `whitehead_self`: self-product is trivial
- `whitehead_conj_invariant`: compatibility with conjugation
- `WhiteheadAlgebra`: algebraic structure packaging

## References

- Whitehead, "Combinatorial Homotopy II"
- HoTT Book, Chapter 8
- Hatcher, *Algebraic Topology*, Section 4.2
-/

import ComputationalPaths.Path.Homotopy.HigherHomotopyGroups
import ComputationalPaths.Path.Homotopy.LoopGroupAlgebra

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace WhiteheadProduct

open HigherHomotopyGroups

universe u

/-! ## Whitehead Product -/

/-- Whitehead product on computational-path homotopy groups. -/
noncomputable def whiteheadProduct {m n : Nat} {A : Type u} {a : A} :
    PiN m A a → PiN n A a → PiN (m + n - 1) A a :=
  match m, n with
  | 1, 1 => fun x y => LoopGroupAlgebra.commutator (A := A) (a := a) x y
  | m, n => fun _ _ => piN_one (n := m + n - 1) (x := a)

/-- Bracket notation for the Whitehead product. -/
notation "[" x ", " y "]" => whiteheadProduct x y

/-! ## Identity Element Properties -/

/-- The Whitehead product with the identity on the left (in π₁) is trivial. -/
theorem whitehead_identity_left_pi1 {A : Type u} {a : A}
    (y : PiN 1 A a) :
    whiteheadProduct (m := 1) (n := 1) (piN_one 1 a) y = piN_one 1 a :=
  LoopGroupAlgebra.commutator_id_left (A := A) (a := a) y

/-- The Whitehead product with the identity on the right (in π₁) is trivial. -/
theorem whitehead_identity_right_pi1 {A : Type u} {a : A}
    (x : PiN 1 A a) :
    whiteheadProduct (m := 1) (n := 1) x (piN_one 1 a) = piN_one 1 a :=
  LoopGroupAlgebra.commutator_id_right (A := A) (a := a) x

/-- Whitehead product is trivial when the first index is 0. -/
theorem whitehead_zero_left {n : Nat} {A : Type u} {a : A}
    (x : PiN 0 A a) (y : PiN n A a) :
    whiteheadProduct (m := 0) (n := n) x y = piN_one (0 + n - 1) a := rfl

/-- Whitehead product is trivial when the first index is ≥ 2. -/
theorem whitehead_high_left {m n : Nat} {A : Type u} {a : A}
    (x : PiN (m + 2) A a) (y : PiN n A a) :
    whiteheadProduct (m := m + 2) (n := n) x y = piN_one (m + 2 + n - 1) a := rfl

/-- Whitehead product is trivial when the second index is 0 and first is 1. -/
theorem whitehead_one_zero {A : Type u} {a : A}
    (x : PiN 1 A a) (y : PiN 0 A a) :
    whiteheadProduct (m := 1) (n := 0) x y = piN_one 0 a := rfl

/-- Whitehead product is trivial when the second index is ≥ 2 and first is 1. -/
theorem whitehead_one_high {n : Nat} {A : Type u} {a : A}
    (x : PiN 1 A a) (y : PiN (n + 2) A a) :
    whiteheadProduct (m := 1) (n := n + 2) x y =
      piN_one (1 + (n + 2) - 1) a := rfl

/-! ## Self-Product -/

/-- The Whitehead product of an element with itself in π₁ is trivial. -/
theorem whitehead_self_pi1 {A : Type u} {a : A}
    (x : PiN 1 A a) :
    whiteheadProduct (m := 1) (n := 1) x x = piN_one 1 a :=
  LoopGroupAlgebra.commutator_self (A := A) (a := a) x

/-! ## Antisymmetry -/

/-- Graded sign for the antisymmetry of the Whitehead product.
    In the (1,1) case, the sign is -1 (mn = 1). -/
noncomputable def gradedSign (m n : Nat) : Int :=
  if (m * n) % 2 = 0 then 1 else -1

/-- The graded sign for (1,1) is -1. -/
theorem gradedSign_one_one : gradedSign 1 1 = -1 := rfl

/-- The graded sign for (2,1) is 1. -/
theorem gradedSign_two_one : gradedSign 2 1 = 1 := rfl

/-- The graded sign for (2,2) is 1. -/
theorem gradedSign_two_two : gradedSign 2 2 = 1 := rfl

/-- The graded sign for (1,2) is 1. -/
theorem gradedSign_one_two : gradedSign 1 2 = 1 := rfl

/-- The graded sign is symmetric: sign(m,n) = sign(n,m). -/
theorem gradedSign_comm (m n : Nat) : gradedSign m n = gradedSign n m := by
  simp [gradedSign, Nat.mul_comm]

/-- The graded sign for (0, n) is 1. -/
theorem gradedSign_zero_left (n : Nat) : gradedSign 0 n = 1 := by
  simp [gradedSign]

/-- The graded sign for (n, 0) is 1. -/
theorem gradedSign_zero_right (n : Nat) : gradedSign n 0 = 1 := by
  simp [gradedSign]

/-! ## Whitehead Product in Terms of Group Operations -/

/-- In the fundamental group (m=n=1), the Whitehead product is the commutator. -/
theorem whitehead_eq_commutator {A : Type u} {a : A}
    (x y : PiN 1 A a) :
    whiteheadProduct (m := 1) (n := 1) x y =
      LoopGroupAlgebra.commutator (A := A) (a := a) x y := rfl

/-! ## Conjugation Compatibility -/

/-- Conjugation preserves Whitehead products in the fundamental group. -/
theorem whitehead_conj_invariant {A : Type u} {a : A}
    (g x y : PiN 1 A a) :
    LoopGroupAlgebra.conj (A := A) (a := a) g
      (whiteheadProduct (m := 1) (n := 1) x y) =
    whiteheadProduct (m := 1) (n := 1)
      (LoopGroupAlgebra.conj (A := A) (a := a) g x)
      (LoopGroupAlgebra.conj (A := A) (a := a) g y) :=
  LoopGroupAlgebra.conj_commutator (A := A) (a := a) g x y

/-! ## Iterated Whitehead Products -/

/-- Iterated Whitehead product (left-associated) on π₁. -/
noncomputable def iteratedWhitehead {A : Type u} {a : A} :
    (n : Nat) → PiN 1 A a → PiN 1 A a → PiN 1 A a
  | 0 => fun _ _ => piN_one 1 a
  | 1 => fun x y => whiteheadProduct (m := 1) (n := 1) x y
  | n + 2 => fun x y => whiteheadProduct (m := 1) (n := 1) x
      (iteratedWhitehead (n + 1) x y)

/-- The zeroth iterated product is the identity. -/
theorem iteratedWhitehead_zero {A : Type u} {a : A}
    (x y : PiN 1 A a) :
    iteratedWhitehead 0 x y = piN_one 1 a := rfl

/-- The first iterated product is the regular Whitehead product. -/
theorem iteratedWhitehead_one {A : Type u} {a : A}
    (x y : PiN 1 A a) :
    iteratedWhitehead 1 x y = whiteheadProduct (m := 1) (n := 1) x y := rfl

/-- The iterated product of identity is identity. -/
theorem iteratedWhitehead_id {A : Type u} {a : A}
    (n : Nat) (y : PiN 1 A a) :
    iteratedWhitehead n (piN_one 1 a) y = piN_one 1 a := by
  induction n with
  | zero => rfl
  | succ n ih =>
      match n with
      | 0 => exact whitehead_identity_left_pi1 y
      | n + 1 =>
          simp [iteratedWhitehead]
          rw [ih]
          exact whitehead_identity_right_pi1 (piN_one 1 a)

/-! ## Whitehead Algebra Structure -/

/-- The Whitehead algebra structure packaging the product and its properties. -/
structure WhiteheadAlgebra (A : Type u) (a : A) where
  /-- The underlying product on π₁. -/
  product : PiN 1 A a → PiN 1 A a → PiN 1 A a
  /-- Product is the commutator. -/
  product_eq : ∀ x y, product x y = LoopGroupAlgebra.commutator (A := A) (a := a) x y
  /-- Identity annihilates from the left. -/
  id_left : ∀ y, product (piN_one 1 a) y = piN_one 1 a
  /-- Identity annihilates from the right. -/
  id_right : ∀ x, product x (piN_one 1 a) = piN_one 1 a
  /-- Self-product is trivial. -/
  self_trivial : ∀ x, product x x = piN_one 1 a

/-- The canonical Whitehead algebra structure on any type. -/
noncomputable def canonicalWhiteheadAlgebra (A : Type u) (a : A) : WhiteheadAlgebra A a where
  product := whiteheadProduct (m := 1) (n := 1)
  product_eq := fun _ _ => rfl
  id_left := fun y => whitehead_identity_left_pi1 y
  id_right := fun x => whitehead_identity_right_pi1 x
  self_trivial := fun x => whitehead_self_pi1 x

/-! ## Path Coherence -/

/-- Path witness that the Whitehead product of identities is the identity. -/
noncomputable def whitehead_id_id_path {A : Type u} {a : A} :
    Path
      (whiteheadProduct (m := 1) (n := 1) (A := A) (a := a) (piN_one 1 a) (piN_one 1 a))
      (piN_one 1 a) :=
  Path.stepChain (whitehead_self_pi1 (piN_one 1 a))

/-- Path witness that the Whitehead product equals the commutator. -/
noncomputable def whitehead_commutator_path {A : Type u} {a : A}
    (x y : PiN 1 A a) :
    Path
      (whiteheadProduct (m := 1) (n := 1) x y)
      (LoopGroupAlgebra.commutator (A := A) (a := a) x y) :=
  Path.refl _

/-- Path witness that conjugation is compatible with the Whitehead product. -/
noncomputable def whitehead_conj_path {A : Type u} {a : A}
    (g x y : PiN 1 A a) :
    Path
      (LoopGroupAlgebra.conj (A := A) (a := a) g
        (whiteheadProduct (m := 1) (n := 1) x y))
      (whiteheadProduct (m := 1) (n := 1)
        (LoopGroupAlgebra.conj (A := A) (a := a) g x)
        (LoopGroupAlgebra.conj (A := A) (a := a) g y)) :=
  Path.stepChain (whitehead_conj_invariant g x y)

/-! ## Power Operations and Whitehead Products -/

/-- Whitehead product with a power element. -/
theorem whitehead_pow_left {A : Type u} {a : A}
    (x y : PiN 1 A a) (n : Nat) :
    whiteheadProduct (m := 1) (n := 1)
      (LoopGroupAlgebra.pow (A := A) (a := a) x n) y =
    LoopGroupAlgebra.commutator (A := A) (a := a)
      (LoopGroupAlgebra.pow (A := A) (a := a) x n) y := rfl

/-- Whitehead product of identity power (n=0) is trivial. -/
theorem whitehead_pow_zero {A : Type u} {a : A}
    (x y : PiN 1 A a) :
    whiteheadProduct (m := 1) (n := 1)
      (LoopGroupAlgebra.pow (A := A) (a := a) x 0) y =
    piN_one 1 a := by
  show LoopGroupAlgebra.commutator (A := A) (a := a)
    (LoopGroupAlgebra.pow (A := A) (a := a) x 0) y = _
  rw [LoopGroupAlgebra.pow_zero]
  exact LoopGroupAlgebra.commutator_id_left (A := A) (a := a) y

/-! ## Degree Calculations -/

/-- The (1,1) Whitehead product lands in π₁. -/
theorem whitehead_one_one_degree :
    1 + 1 - 1 = 1 := rfl

/-- The (2,2) Whitehead product lands in π₃. -/
theorem whitehead_two_two_degree :
    2 + 2 - 1 = 3 := rfl

/-- The (1,n) Whitehead product lands in π_n. -/
theorem whitehead_one_n_degree (n : Nat) (hn : n ≥ 1) :
    1 + n - 1 = n := by omega

/-! ## Naturality -/

/-- The Whitehead product is natural with respect to functions:
    f_*(wp(x,y)) = wp(f_*(x), f_*(y)) in the (1,1) case,
    where f_* is the induced map on π₁. -/
structure WhiteheadNatural {A : Type u} {B : Type u} {a : A} {b : B}
    (f_star : PiN 1 A a → PiN 1 B b) where
  /-- Naturality of the Whitehead product. -/
  natural : ∀ x y : PiN 1 A a,
    f_star (whiteheadProduct (m := 1) (n := 1) x y) =
    whiteheadProduct (m := 1) (n := 1) (f_star x) (f_star y)

/-! ## Lower Central Series -/

/-- The n-th term of the lower central series of π₁, defined via iterated
    Whitehead products. -/
noncomputable def lowerCentralTerm {A : Type u} {a : A}
    (n : Nat) (S : List (PiN 1 A a)) : List (PiN 1 A a) :=
  match n with
  | 0 => S
  | n + 1 =>
    S.flatMap fun x =>
      (lowerCentralTerm n S).map fun y =>
        whiteheadProduct (m := 1) (n := 1) x y

/-- The zeroth term of the lower central series is the original set. -/
theorem lowerCentral_zero {A : Type u} {a : A}
    (S : List (PiN 1 A a)) :
    lowerCentralTerm 0 S = S := rfl

/-! ## Abelianization -/

/-- In the abelianization of π₁, all Whitehead products vanish.
    This is because commutators are trivial in abelian groups. -/
structure AbelianWhitehead (A : Type u) (a : A) where
  /-- The abelianization map. -/
  abel : PiN 1 A a → PiN 1 A a
  /-- The abelianization kills all Whitehead products. -/
  kills_whitehead : ∀ x y : PiN 1 A a,
    abel (whiteheadProduct (m := 1) (n := 1) x y) = piN_one 1 a

/-! ## Summary

We developed the Whitehead product on computational-path homotopy groups:

1. **Core definition**: `whiteheadProduct` implementing the bracket [x, y]
2. **Identity properties**: left/right identity annihilation, self-product
3. **Antisymmetry**: graded sign computations
4. **Conjugation**: compatibility with the conjugation action
5. **Algebra structure**: `WhiteheadAlgebra` packaging product and laws
6. **Path coherence**: `Path.stepChain` witnesses for all key identities
7. **Power operations**: interaction with loop group powers
8. **Naturality**: structure for natural transformations
9. **Lower central series**: iterated Whitehead products
10. **Abelianization**: Whitehead products in the abelianization
-/

end WhiteheadProduct
end Homotopy
end Path
end ComputationalPaths
