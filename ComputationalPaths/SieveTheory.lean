/-
# Sieve theory via computational paths

This module records a lightweight formalization of classical sieve ideas using
computational paths as explicit witnesses of equalities between sieve weights.
We focus on the structure needed for Eratosthenes and Selberg-style sieves, and
we package inclusion-exclusion as `Path` witnesses over formal weight data.

## Key Results

- `SieveStep`: syntax of sieve constructions.
- `eratosthenesSieve`: Eratosthenes-style iteration of removal steps.
- `CombinatorialSieve`: combinatorial sieve data with weights.
- `SelbergSieve`: Selberg sieve data with lambda weights.
- `inclusion_exclusion_path`: Path witness for inclusion-exclusion.

## References

- Iwaniec-Kowalski, *Analytic Number Theory*, Chapter 6.
- Halberstam-Richert, *Sieve Methods*.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace SieveTheory

/-! ## Basic sieves -/

/-- A sieve set on natural numbers. -/
abbrev SieveSet := Nat → Prop

/-- A sieve on `Nat`, represented by a membership predicate. -/
structure Sieve where
  /-- Membership predicate. -/
  carrier : SieveSet

namespace Sieve

/-- Coe a sieve to its membership predicate. -/
instance : CoeFun Sieve (fun _ => Nat → Prop) where
  coe := Sieve.carrier

/-- The full sieve (all natural numbers). -/
def univ : Sieve := ⟨fun _ => True⟩

/-- The empty sieve. -/
def empty : Sieve := ⟨fun _ => False⟩

/-- Singleton sieve at a fixed natural number. -/
def singleton (n : Nat) : Sieve := ⟨fun m => m = n⟩

/-- Union of two sieves. -/
def union (S T : Sieve) : Sieve := ⟨fun n => S n ∨ T n⟩

/-- Intersection of two sieves. -/
def inter (S T : Sieve) : Sieve := ⟨fun n => S n ∧ T n⟩

/-- Complement of a sieve. -/
def compl (S : Sieve) : Sieve := ⟨fun n => ¬ S n⟩

/-- Predicate for multiples of a modulus. -/
def isMultiple (p n : Nat) : Prop := ∃ k, n = p * k

/-- Remove multiples of `p` from a sieve. -/
def removeMultiples (p : Nat) (S : Sieve) : Sieve :=
  ⟨fun n => S n ∧ ¬ isMultiple p n⟩

/-- Membership characterization for `removeMultiples`. -/
theorem mem_removeMultiples (p : Nat) (S : Sieve) (n : Nat) :
    removeMultiples p S n ↔ S n ∧ ¬ isMultiple p n :=
  Iff.rfl

end Sieve

/-! ## Sieve steps -/

/-- Syntax of sieve constructions. -/
inductive SieveStep : Type
  | base : Sieve → SieveStep
  | removeMultiples : Nat → SieveStep → SieveStep
  | inter : SieveStep → SieveStep → SieveStep
  | union : SieveStep → SieveStep → SieveStep
  | compl : SieveStep → SieveStep

namespace SieveStep

/-- Evaluate a sieve step to a concrete sieve. -/
def eval : SieveStep → Sieve
  | base S => S
  | removeMultiples p s => Sieve.removeMultiples p (eval s)
  | inter s t => Sieve.inter (eval s) (eval t)
  | union s t => Sieve.union (eval s) (eval t)
  | compl s => Sieve.compl (eval s)

end SieveStep

/-! ## Eratosthenes sieve -/

/-- Eratosthenes-style iteration of removing prime multiples. -/
def eratosthenesSteps (primes : List Nat) (base : Sieve) : SieveStep :=
  primes.foldl (fun step p => SieveStep.removeMultiples p step) (SieveStep.base base)

/-- Evaluate the Eratosthenes sieve on a base sieve. -/
def eratosthenesSieve (primes : List Nat) (base : Sieve) : Sieve :=
  (eratosthenesSteps primes base).eval

/-! ## Sieve weights -/

/-- Weight data for sieve estimates. -/
structure SieveWeight where
  /-- Pointwise weight on naturals. -/
  pointWeight : Nat → Int
  /-- Finite support list for explicit sums. -/
  support : List Nat
  /-- Abstract total weight of a sieve. -/
  weight : Sieve → Int

namespace SieveWeight

/-- Sum of the point weights on the support list. -/
def supportSum (w : SieveWeight) : Int :=
  w.support.foldl (fun acc n => acc + w.pointWeight n) 0

end SieveWeight

/-- Formal weight assigned to sieve steps via inclusion-exclusion. -/
def stepWeight (w : SieveWeight) : SieveStep → Int
  | SieveStep.base S => w.weight S
  | SieveStep.removeMultiples _ s => stepWeight w s
  | SieveStep.inter s t => w.weight (SieveStep.eval (SieveStep.inter s t))
  | SieveStep.union s t =>
      stepWeight w s + stepWeight w t - w.weight (SieveStep.eval (SieveStep.inter s t))
  | SieveStep.compl s => -stepWeight w s

/-! ## Combinatorial sieve structure -/

/-- Data for a combinatorial sieve. -/
structure CombinatorialSieve where
  /-- Universe being sifted. -/
  universeSieve : Sieve
  /-- Predicate describing the admissible moduli. -/
  prime : Nat → Prop
  /-- Level of distribution parameter. -/
  level : Nat
  /-- Sieve weights attached to the data. -/
  weights : SieveWeight

namespace CombinatorialSieve

/-- Evaluate a sieve step in the given universe. -/
def sift (S : CombinatorialSieve) (step : SieveStep) : Sieve :=
  Sieve.inter S.universeSieve (SieveStep.eval step)

/-- Formal weight of a sieve step using the attached weights. -/
def weightOf (S : CombinatorialSieve) (step : SieveStep) : Int :=
  stepWeight S.weights step

end CombinatorialSieve

/-! ## Selberg sieve -/

/-- Selberg sieve data with lambda weights. -/
structure SelbergSieve extends CombinatorialSieve where
  /-- Selberg lambda weights indexed by divisors. -/
  lambda : Nat → Int
  /-- Normalization at 1, recorded as a computational path. -/
  lambda_one : Path (lambda 1) 1

namespace SelbergSieve

/-- Selberg lambda weight summed over a list of divisors. -/
def lambdaSum (S : SelbergSieve) (divisors : List Nat) : Int :=
  divisors.foldl (fun acc d => acc + S.lambda d) 0

end SelbergSieve

/-! ## Inclusion-exclusion as paths -/

/-- Inclusion-exclusion witness for the formal weight of a union. -/
def inclusion_exclusion_path (w : SieveWeight) (s t : SieveStep) :
    Path (stepWeight w (SieveStep.union s t))
      (stepWeight w s + stepWeight w t - stepWeight w (SieveStep.inter s t)) := by
  exact Path.refl _

/-- Symmetric inclusion-exclusion witness. -/
def inclusion_exclusion_path_symm (w : SieveWeight) (s t : SieveStep) :
    Path (stepWeight w s + stepWeight w t - stepWeight w (SieveStep.inter s t))
      (stepWeight w (SieveStep.union s t)) := by
  exact Path.symm (inclusion_exclusion_path w s t)

/-- Removing multiples preserves the formal weight. -/
def removeMultiples_weight_path (w : SieveWeight) (p : Nat) (s : SieveStep) :
    Path (stepWeight w (SieveStep.removeMultiples p s)) (stepWeight w s) := by
  exact Path.refl _

/-- Complement weights are the formal negation. -/
def complement_weight_path (w : SieveWeight) (s : SieveStep) :
    Path (stepWeight w (SieveStep.compl s)) (-stepWeight w s) := by
  exact Path.refl _

/-! ## Summary -/

/-- The Eratosthenes sieve step evaluates to the expected sieve. -/
theorem eratosthenesSieve_def (primes : List Nat) (base : Sieve) :
    eratosthenesSieve primes base = (eratosthenesSteps primes base).eval := rfl

end SieveTheory
end ComputationalPaths
