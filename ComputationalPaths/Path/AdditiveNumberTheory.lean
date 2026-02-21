/-
# Additive number theory via computational paths

This module provides a lightweight, axioms-free formalization of additive number
theory in the computational paths setting. We model Waring's problem, Goldbach
representations, Vinogradov's theorem, and the circle method as formal data
equipped with Path witnesses for additive decompositions.

## Key Results

- `AdditiveStructure` and `AdditiveDecomposition`
- `AdditiveFunction` and `AdditiveStep`
- `WaringProblem`, `GoldbachProblem`, `VinogradovProblem`
- `CircleMethodData`

## References

- Hardy and Littlewood, "Some Problems of Partitio Numerorum"
- Vinogradov, "The Method of Trigonometric Sums in the Theory of Numbers"
- Vaughan, "The Hardy-Littlewood Method"
- Nathanson, "Additive Number Theory: The Classical Bases"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path

universe u v w

/-! ## Additive structures -/

/-- An additive structure with Path witnesses for the basic laws. -/
structure AdditiveStructure where
  /-- Carrier type. -/
  carrier : Type u
  /-- Additive zero. -/
  zero : carrier
  /-- Addition. -/
  add : carrier -> carrier -> carrier
  /-- Associativity. -/
  add_assoc : forall a b c, Path (add (add a b) c) (add a (add b c))
  /-- Commutativity. -/
  add_comm : forall a b, Path (add a b) (add b a)
  /-- Left identity. -/
  zero_add : forall a, Path (add zero a) a
  /-- Right identity. -/
  add_zero : forall a, Path (add a zero) a

namespace AdditiveStructure

/-- Sum of the first `n` terms of a sequence. -/
def sum (A : AdditiveStructure) (f : Nat -> A.carrier) : Nat -> A.carrier
  | 0 => A.zero
  | n + 1 => A.add (sum A f n) (f n)

/-- Congruence on the left input of addition. -/
def add_path_left (A : AdditiveStructure) {a b : A.carrier} (p : Path a b)
    (c : A.carrier) : Path (A.add a c) (A.add b c) :=
  Path.congrArg (fun x => A.add x c) p

/-- Two-term sum path used in Goldbach-style decompositions. -/
def sum_two_path (A : AdditiveStructure) (p q : A.carrier) :
    Path (sum A (fun i => match i with | 0 => p | _ => q) 2)
      (A.add p q) :=
  add_path_left A (A.zero_add p) q

/-- Three-term sum path used in Vinogradov-style decompositions. -/
def sum_three_path (A : AdditiveStructure) (p q r : A.carrier) :
    Path (sum A (fun i => match i with | 0 => p | 1 => q | _ => r) 3)
      (A.add p (A.add q r)) :=
  Path.trans
    (add_path_left A (sum_two_path A p q) r)
    (A.add_assoc p q r)

end AdditiveStructure

/-! ## Additive decompositions -/

/-- An additive decomposition of a target value. -/
structure AdditiveDecomposition (A : AdditiveStructure) (target : A.carrier) where
  /-- Number of summands. -/
  length : Nat
  /-- Summand sequence. -/
  terms : Nat -> A.carrier
  /-- Path witness for the additive decomposition. -/
  sumPath : Path (AdditiveStructure.sum A terms length) target

/-! ## Additive functions and steps -/

/-- An additive counting or representation function. -/
structure AdditiveFunction (S : Type u) (V : Type v) where
  /-- Evaluation. -/
  eval : S -> V

namespace AdditiveFunction

/-- Pointwise Path equality between additive functions. -/
def PointwisePath {S : Type u} {V : Type v} (F G : AdditiveFunction S V) :
    Type (max u v) :=
  forall s : S, Path (F.eval s) (G.eval s)

end AdditiveFunction

/-- Rewrite steps between additive presentations. -/
inductive AdditiveStep {S : Type u} {V : Type v} :
    AdditiveFunction S V -> AdditiveFunction S V -> Type (max u v) where
  /-- Step justified by an explicit decomposition. -/
  | byDecomposition (F G : AdditiveFunction S V)
      (h : AdditiveFunction.PointwisePath F G) : AdditiveStep F G
  /-- Step justified by Waring's problem. -/
  | byWaring (F G : AdditiveFunction S V)
      (h : AdditiveFunction.PointwisePath F G) : AdditiveStep F G
  /-- Step justified by Goldbach representations. -/
  | byGoldbach (F G : AdditiveFunction S V)
      (h : AdditiveFunction.PointwisePath F G) : AdditiveStep F G
  /-- Step justified by Vinogradov's theorem. -/
  | byVinogradov (F G : AdditiveFunction S V)
      (h : AdditiveFunction.PointwisePath F G) : AdditiveStep F G
  /-- Step justified by the circle method. -/
  | byCircleMethod (F G : AdditiveFunction S V)
      (h : AdditiveFunction.PointwisePath F G) : AdditiveStep F G

namespace AdditiveStep

/-- Build a decomposition step from a pointwise Path. -/
def ofPointwisePath {S : Type u} {V : Type v} {F G : AdditiveFunction S V}
    (h : AdditiveFunction.PointwisePath F G) : AdditiveStep F G :=
  AdditiveStep.byDecomposition F G h

end AdditiveStep

/-! ## Waring's problem -/

/-- Waring representation: a sum of k-th powers. -/
structure WaringRepresentation (A : AdditiveStructure)
    (power : Nat -> A.carrier -> A.carrier) (k : Nat) (n : A.carrier) where
  /-- Number of summands. -/
  length : Nat
  /-- Underlying terms. -/
  terms : Nat -> A.carrier
  /-- Path witness for the k-th power sum. -/
  sumPath : Path
    (AdditiveStructure.sum A (fun i => power k (terms i)) length) n

/-- Waring problem data with uniform length control. -/
structure WaringProblem (A : AdditiveStructure) where
  /-- Power operation. -/
  power : Nat -> A.carrier -> A.carrier
  /-- Number of summands g(k). -/
  g : Nat -> Nat
  /-- Waring representations. -/
  representation : forall k n, WaringRepresentation A power k n
  /-- Path witness that the representation length equals g(k). -/
  lengthPath : forall k n, Path (representation k n).length (g k)

/-! ## Prime predicates and Goldbach representations -/

/-- A prime predicate as a Type-valued predicate. -/
structure PrimePredicate (N : Type u) where
  /-- Predicate for primality. -/
  isPrime : N -> Type u

/-- A Goldbach representation of a number as a sum of two primes. -/
structure GoldbachRepresentation (A : AdditiveStructure)
    (prime : PrimePredicate A.carrier) (n : A.carrier) where
  /-- First prime. -/
  p : A.carrier
  /-- Second prime. -/
  q : A.carrier
  /-- Primality of p. -/
  pPrime : prime.isPrime p
  /-- Primality of q. -/
  qPrime : prime.isPrime q
  /-- Path witness for p + q = n. -/
  sumPath : Path (A.add p q) n

/-- Goldbach problem data: even numbers admit Goldbach representations. -/
structure GoldbachProblem (A : AdditiveStructure) (prime : PrimePredicate A.carrier) where
  /-- Even predicate. -/
  even : A.carrier -> Type u
  /-- Goldbach representation for even numbers. -/
  representation : forall n, even n -> GoldbachRepresentation A prime n

/-! ## Vinogradov's theorem framework -/

/-- A Vinogradov representation as a sum of three primes. -/
structure VinogradovRepresentation (A : AdditiveStructure)
    (prime : PrimePredicate A.carrier) (n : A.carrier) where
  /-- Prime summands. -/
  p : A.carrier
  q : A.carrier
  r : A.carrier
  /-- Primality witnesses. -/
  pPrime : prime.isPrime p
  qPrime : prime.isPrime q
  rPrime : prime.isPrime r
  /-- Path witness for p + q + r = n. -/
  sumPath : Path (A.add p (A.add q r)) n

/-- Vinogradov problem data: large odd numbers are sums of three primes. -/
structure VinogradovProblem (A : AdditiveStructure)
    (prime : PrimePredicate A.carrier) where
  /-- Odd predicate. -/
  odd : A.carrier -> Type u
  /-- Largeness predicate. -/
  large : A.carrier -> Type u
  /-- Vinogradov representation for odd large numbers. -/
  representation :
    forall n, odd n -> large n -> VinogradovRepresentation A prime n

/-! ## Circle method data -/

/-- Data for the circle method decomposition. -/
structure CircleMethodData (S : Type u) (A : AdditiveStructure) where
  /-- Total contribution. -/
  total : AdditiveFunction S A.carrier
  /-- Major arc contribution. -/
  major : AdditiveFunction S A.carrier
  /-- Minor arc contribution. -/
  minor : AdditiveFunction S A.carrier
  /-- Path witness for total = major + minor. -/
  split : forall s, Path (total.eval s) (A.add (major.eval s) (minor.eval s))

/-! ## Summary -/

/-!
We introduced additive structures and decomposition witnesses, then packaged
classical additive number theory statements (Waring, Goldbach, Vinogradov) and
the circle method as Path-based data. The `AdditiveStep` relation records the
rewrite steps between additive presentations.
-/

end Path
end ComputationalPaths
