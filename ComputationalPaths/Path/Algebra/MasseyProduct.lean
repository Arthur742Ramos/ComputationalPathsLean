/-
# Massey Products

This module formalizes Massey products in the computational paths framework.
We define triple Massey products, higher Massey products, and indeterminacy.

## Key Results

- `TripleMasseyInput`: input data for a triple Massey product ⟨a, b, c⟩
- `TripleMasseyDefSys`: a defining system for the triple product
- `tripleMasseyValue`: the value of the Massey product
- `MasseyIndeterminacy`: indeterminacy predicate
- `HigherMasseyInput`: higher Massey product input

## References

- Massey, "Some higher order cohomology operations"
- May, "Matric Massey products"
- McCleary, "A User's Guide to Spectral Sequences"
-/

import ComputationalPaths.Path.Algebra.CohomologyRing

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace MasseyProduct

universe u

/-! ## Graded multiplication -/

/-- A graded abelian group with multiplication. -/
structure GradedRing where
  /-- Carrier at each degree. -/
  carrier : Nat → Type u
  /-- Zero at each degree. -/
  zero : ∀ n, carrier n
  /-- Addition at each degree. -/
  add : ∀ n, carrier n → carrier n → carrier n
  /-- Negation at each degree. -/
  neg : ∀ n, carrier n → carrier n
  /-- Left identity. -/
  zero_add : ∀ n (x : carrier n), add n (zero n) x = x
  /-- Left inverse. -/
  add_left_neg : ∀ n (x : carrier n), add n (neg n x) x = zero n
  /-- Multiplication p + q → p+q. -/
  mul : ∀ p q, carrier p → carrier q → carrier (p + q)
  /-- Multiplication by zero on the left. -/
  mul_zero_left : ∀ p q (y : carrier q), mul p q (zero p) y = zero (p + q)
  /-- Multiplication by zero on the right. -/
  mul_zero_right : ∀ p q (x : carrier p), mul p q x (zero q) = zero (p + q)

/-! ## Triple Massey products -/

/-- Input data for a triple Massey product ⟨a, b, c⟩.
    We need a ∈ H^p, b ∈ H^q, c ∈ H^r with a·b = 0 and b·c = 0. -/
structure TripleMasseyInput (R : GradedRing) where
  /-- Degree of a. -/
  p : Nat
  /-- Degree of b. -/
  q : Nat
  /-- Degree of c. -/
  r : Nat
  /-- The element a ∈ H^p. -/
  a : R.carrier p
  /-- The element b ∈ H^q. -/
  b : R.carrier q
  /-- The element c ∈ H^r. -/
  c : R.carrier r
  /-- a · b = 0 in H^{p+q}. -/
  ab_zero : R.mul p q a b = R.zero (p + q)
  /-- b · c = 0 in H^{q+r}. -/
  bc_zero : R.mul q r b c = R.zero (q + r)

/-- A defining system for a triple Massey product. -/
structure TripleMasseyDefSys (R : GradedRing) (inp : TripleMasseyInput R) where
  /-- Witness s ∈ H^{p+q}. -/
  s : R.carrier (inp.p + inp.q)
  /-- Witness t ∈ H^{q+r}. -/
  t : R.carrier (inp.q + inp.r)

/-- The value of a triple Massey product given a defining system.
    The value lives in H^{(p+q)+r}. -/
noncomputable def tripleMasseyValue {R : GradedRing}
    {inp : TripleMasseyInput R}
    (sys : TripleMasseyDefSys R inp) :
    R.carrier ((inp.p + inp.q) + inp.r) :=
  -- s·c lives in H^{(p+q)+r}
  -- a·t lives in H^{p+(q+r)}, need to cast to H^{(p+q)+r}
  -- Since (p+q)+r = p+(q+r) by Nat.add_assoc, we use cast
  let sc := R.mul (inp.p + inp.q) inp.r sys.s inp.c
  let at' := R.mul inp.p (inp.q + inp.r) inp.a sys.t
  let h : inp.p + (inp.q + inp.r) = (inp.p + inp.q) + inp.r := by omega
  R.add ((inp.p + inp.q) + inp.r) sc (h ▸ at')

/-- The triple Massey product ⟨a, b, c⟩ as a predicate on elements:
    x is in the Massey product if it arises from some defining system. -/
def isTripleMasseyValue {R : GradedRing}
    (inp : TripleMasseyInput R)
    (x : R.carrier ((inp.p + inp.q) + inp.r)) : Prop :=
  ∃ sys : TripleMasseyDefSys R inp,
    x = tripleMasseyValue sys

/-! ## Indeterminacy -/

/-- The indeterminacy predicate: x is in the indeterminacy if
    x = a · u or x = v · c for some u, v. -/
def MasseyIndeterminacy {R : GradedRing}
    (inp : TripleMasseyInput R)
    (x : R.carrier ((inp.p + inp.q) + inp.r)) : Prop :=
  (∃ u : R.carrier (inp.q + inp.r),
    let h : inp.p + (inp.q + inp.r) = (inp.p + inp.q) + inp.r := by omega
    x = h ▸ R.mul inp.p (inp.q + inp.r) inp.a u) ∨
  (∃ v : R.carrier (inp.p + inp.q),
    x = R.mul (inp.p + inp.q) inp.r v inp.c)

/-- Zero is in the indeterminacy. -/
theorem zero_mem_indeterminacy {R : GradedRing}
    (inp : TripleMasseyInput R) :
    MasseyIndeterminacy inp (R.zero ((inp.p + inp.q) + inp.r)) := by
  right
  exact ⟨R.zero (inp.p + inp.q), by rw [R.mul_zero_left]⟩

/-- The Massey product is a coset of the indeterminacy. -/
structure MasseyCosetProperty {R : GradedRing}
    (inp : TripleMasseyInput R) where
  /-- Any two values differ by an indeterminacy element. -/
  coset :
    ∀ (sys1 sys2 : TripleMasseyDefSys R inp),
      MasseyIndeterminacy inp
        (R.add ((inp.p + inp.q) + inp.r)
          (tripleMasseyValue sys1)
          (R.neg ((inp.p + inp.q) + inp.r) (tripleMasseyValue sys2)))

/-! ## Higher Massey products -/

/-- Input data for a higher Massey product ⟨a₁, ..., aₙ⟩. -/
structure HigherMasseyInput (R : GradedRing) (n : Nat) where
  /-- The degrees. -/
  degree : Fin n → Nat
  /-- The elements. -/
  element : (i : Fin n) → R.carrier (degree i)
  /-- All consecutive sub-products vanish. -/
  consecutive_zero :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      R.mul (degree i) (degree ⟨i.val + 1, hi⟩)
        (element i)
        (element ⟨i.val + 1, hi⟩) =
      R.zero (degree i + degree ⟨i.val + 1, hi⟩)

/-! ## Nontrivial Massey products -/

/-- A nontrivial triple Massey product detects secondary structure. -/
structure NontrivialMassey (R : GradedRing) where
  /-- The input data. -/
  input : TripleMasseyInput R
  /-- A representative value. -/
  representative : R.carrier ((input.p + input.q) + input.r)
  /-- The representative is a Massey product value. -/
  is_massey : isTripleMasseyValue input representative
  /-- The representative is nontrivial. -/
  nontrivial : representative ≠ R.zero ((input.p + input.q) + input.r)

/-- Path-valued zero membership. -/
def zero_mem_indeterminacy_path {R : GradedRing}
    (inp : TripleMasseyInput R) :
    Path (R.mul (inp.p + inp.q) inp.r (R.zero (inp.p + inp.q)) inp.c)
      (R.zero ((inp.p + inp.q) + inp.r)) :=
  Path.stepChain (R.mul_zero_left (inp.p + inp.q) inp.r inp.c)

/-! ## Summary -/

end MasseyProduct
end Algebra
end Path
end ComputationalPaths
