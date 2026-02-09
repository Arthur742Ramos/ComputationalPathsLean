/-
# Model category structure on computational paths

This module introduces a minimal model category interface for the weak category
of computational paths. We define weak equivalences, fibrations, and
cofibrations, and record the two factorization axioms up to `Rw`-rewrite.

## Key Results

- `ModelCategory`: a weak category equipped with weak equivalences, fibrations,
  cofibrations, and factorization axioms.
- `pathModelCategory`: the trivial model structure on computational paths.

## References

- Quillen, *Homotopical Algebra*
- Hovey, *Model Categories*
-/

import ComputationalPaths.Path.Groupoid

namespace ComputationalPaths
namespace Path

universe u

/-! ## Model category interface -/

/-- A model category structure on the weak category of computational paths. -/
structure ModelCategory (A : Type u) extends WeakCategory A where
  /-- Weak equivalences. -/
  weq : {a b : A} → Path a b → Prop
  /-- Fibrations. -/
  fib : {a b : A} → Path a b → Prop
  /-- Cofibrations. -/
  cof : {a b : A} → Path a b → Prop
  /-- Factorization as a cofibration followed by a trivial fibration. -/
  factorization_cof_triv_fib :
    {a b : A} → (p : Path a b) →
      ∃ (c : A) (i : Path a c) (q : Path c b),
        cof i ∧ fib q ∧ weq q ∧ Rw (comp i q) p
  /-- Factorization as a trivial cofibration followed by a fibration. -/
  factorization_triv_cof_fib :
    {a b : A} → (p : Path a b) →
      ∃ (c : A) (i : Path a c) (q : Path c b),
        cof i ∧ weq i ∧ fib q ∧ Rw (comp i q) p

namespace ModelCategory

variable {A : Type u}

/-- A trivial cofibration is both a cofibration and a weak equivalence. -/
def trivialCofibration (M : ModelCategory A) {a b : A} (p : Path a b) : Prop :=
  M.cof p ∧ M.weq p

/-- A trivial fibration is both a fibration and a weak equivalence. -/
def trivialFibration (M : ModelCategory A) {a b : A} (p : Path a b) : Prop :=
  M.fib p ∧ M.weq p

end ModelCategory

/-! ## Path model structure -/

section PathModel

variable (A : Type u)

/-- Weak equivalences in the path model structure: paths with rewrite inverses. -/
def pathWeakEquivalence {a b : A} (p : Path a b) : Prop :=
  Nonempty (WeakCategory.IsIso (A := A) (WeakCategory.identity A) p)

/-- Fibrations in the path model structure (all paths). -/
def pathFibration {a b : A} (_p : Path a b) : Prop :=
  True

/-- Cofibrations in the path model structure (all paths). -/
def pathCofibration {a b : A} (_p : Path a b) : Prop :=
  True

/-- Every computational path is a weak equivalence. -/
theorem path_is_weak_equivalence {a b : A} (p : Path a b) :
    pathWeakEquivalence (A := A) p := by
  exact ⟨WeakGroupoid.isIso (A := A) (G := WeakGroupoid.identity A) p⟩

/-- The trivial model category structure on computational paths. -/
def pathModelCategory (A : Type u) : ModelCategory A where
  toWeakCategory := WeakCategory.identity A
  weq := fun {a b} p => pathWeakEquivalence (A := A) p
  fib := fun {a b} p => pathFibration (A := A) p
  cof := fun {a b} p => pathCofibration (A := A) p
  factorization_cof_triv_fib := by
    intro a b p
    refine ⟨b, p, Path.refl b, ?_, ?_, ?_, ?_⟩
    · exact True.intro
    · exact True.intro
    · exact path_is_weak_equivalence (A := A) (p := Path.refl b)
    · exact rw_of_step (Step.trans_refl_right p)
  factorization_triv_cof_fib := by
    intro a b p
    refine ⟨a, Path.refl a, p, ?_, ?_, ?_, ?_⟩
    · exact True.intro
    · exact path_is_weak_equivalence (A := A) (p := Path.refl a)
    · exact True.intro
    · exact rw_of_step (Step.trans_refl_left p)

end PathModel

/-! ## Summary -/

/-!
We introduced a minimal model category interface for computational paths and
constructed the trivial model structure where every path is a fibration,
cofibration, and weak equivalence, with factorization via reflexive paths.
-/

end Path
end ComputationalPaths
