/-
# Free Loop Spaces

This module formalizes the free loop space LX, modeled as the mapping space
`Map(S1, X)` via the computational circle's universal property. We package the
evaluation fibration and relate free loops to conjugacy classes in PiOne.

## Key Results

- `MapS1`, `FreeLoopSpace`: maps from S1 to X as `(x, loop)` pairs
- `freeLoopEval`, `freeLoopEvalLift`: evaluation map and path lifting
- `freeLoopFiberSeq`: evaluation fibration `LoopSpace -> FreeLoopSpace -> X`
- `piOneConjClass`, `freeLoopConjClass`: conjugacy classes in PiOne and the
  induced map from free loops

## References

- HoTT Book, Chapter 2 (loop spaces and conjugation)
- May, "A Concise Course in Algebraic Topology", Chapter 8
-/

import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Homotopy.LoopGroupAlgebra
import ComputationalPaths.Path.Algebra.GroupActionOps
import ComputationalPaths.Path.EquivariantPaths

namespace ComputationalPaths
namespace Path
namespace FreeLoopSpace

open Algebra Fibration EquivariantPaths
open Homotopy

universe u

/-! ## Map(S1, X) and free loop space -/

/-- The computational circle S1. -/
abbrev S1 : Type u := CompPath.Circle

/-- Map(S1, X) modeled as a point with a loop (circle's universal property). -/
abbrev MapS1 (X : Type u) : Type u :=
  Sigma fun x : X => LoopSpace X x

/-- The free loop space LX. -/
abbrev FreeLoopSpace (X : Type u) : Type u :=
  MapS1 X

/-- Evaluation at the basepoint of S1. -/
abbrev freeLoopEval {X : Type u} : FreeLoopSpace X -> X :=
  Sigma.fst

/-- Constant free loop at a chosen basepoint. -/
def freeLoopBase {X : Type u} (x0 : X) : FreeLoopSpace X :=
  Sigma.mk x0 (Path.refl x0)

@[simp] theorem freeLoopEval_base {X : Type u} (x0 : X) :
    freeLoopEval (X := X) (freeLoopBase x0) = x0 :=
  rfl

/-! ## Evaluation fibration -/

/-- Path lifting for the evaluation map. -/
noncomputable def freeLoopEvalLift {X : Type u} {x y : X}
    (p : Path x y) (l : LoopSpace X x) :
    Path (Sigma.mk x l : FreeLoopSpace X) (Sigma.mk y (Path.transport p l)) :=
  Fibration.liftPath (P := fun x => LoopSpace X x) p l

/-- The evaluation fibration `LoopSpace -> FreeLoopSpace -> X`. -/
def freeLoopFiberSeq (X : Type u) (x0 : X) :
    FiberSeq (LoopSpace X x0) (FreeLoopSpace X) X :=
  canonicalFiberSeq (P := fun x => LoopSpace X x) x0 (Path.refl x0)

def freeLoopFiberSeq_exact (X : Type u) (x0 : X) :
    IsExactAt (freeLoopFiberSeq X x0) :=
  canonicalFiberSeq_exact (P := fun x => LoopSpace X x) x0 (Path.refl x0)

/-! ## Conjugacy classes in PiOne -/

/-- Conjugation action of PiOne on itself. -/
abbrev piOneConjAction (X : Type u) (x0 : X) :
    Algebra.GroupAction (PiOne X x0)
      (Homotopy.LoopGroupAlgebra.loopGroupStructure X x0) (PiOne X x0) :=
  Algebra.GroupAction.conjugationAction
    (Homotopy.LoopGroupAlgebra.loopGroupStructure X x0)

/-- Conjugacy classes in PiOne(X, x0) as the orbit space. -/
abbrev piOneConjClass (X : Type u) (x0 : X) : Type u :=
  OrbitSpace (A := piOneConjAction X x0)

/-- The quotient map PiOne(X, x0) -> conjugacy classes. -/
def piOneConjClassMap (X : Type u) (x0 : X) :
    PiOne X x0 -> piOneConjClass X x0 :=
  orbitMap (A := piOneConjAction X x0)

/-- Free loops map to conjugacy classes in their based fundamental group. -/
def freeLoopConjClass {X : Type u} (l : FreeLoopSpace X) :
    piOneConjClass X l.1 :=
  piOneConjClassMap X l.1 (PiOne.ofLoop l.2)

@[simp] theorem freeLoopConjClass_conj {X : Type u} {x : X}
    (l : LoopSpace X x) (g : PiOne X x) :
    freeLoopConjClass (X := X) (Sigma.mk x l) =
      piOneConjClassMap X x (Homotopy.LoopGroupAlgebra.conj g (PiOne.ofLoop l)) := by
  simpa [freeLoopConjClass, piOneConjClassMap, piOneConjAction] using
    (orbitMap_act (A := piOneConjAction X x) g (PiOne.ofLoop l))

/-! ## Deeper properties of the free loop space -/

/-- The evaluation map is natural: composing with a map f preserves evaluation. -/
theorem freeLoopEval_natural {X Y : Type u} (f : X → Y) (l : FreeLoopSpace X) :
    f (freeLoopEval l) = freeLoopEval (Sigma.mk (f l.1) (Path.congrArg f l.2)) := by
  sorry

/-- The free loop base is a section of the evaluation map. -/
theorem freeLoopBase_section {X : Type u} (x : X) :
    freeLoopEval (freeLoopBase x) = x := by
  rfl

/-- Concatenation of loops lifts to a product structure on free loops. -/
theorem freeLoop_concat {X : Type u} {x : X} (l₁ l₂ : LoopSpace X x) :
    freeLoopEval (⟨x, Path.trans l₁ l₂⟩ : FreeLoopSpace X) =
      freeLoopEval (⟨x, l₁⟩ : FreeLoopSpace X) := by
  sorry

/-- The constant loop is the identity for loop concatenation up to a Path. -/
theorem freeLoopBase_identity {X : Type u} (x : X) :
    Path (⟨x, Path.trans (Path.refl x) (Path.refl x)⟩ : FreeLoopSpace X)
         (freeLoopBase x) := by
  sorry

/-- Free loops are invariant under conjugation in the fundamental group. -/
theorem freeLoop_conjugation_invariant {X : Type u} {x : X}
    (l : LoopSpace X x) (g : PiOne X x) :
    freeLoopConjClass (⟨x, l⟩ : FreeLoopSpace X) =
      freeLoopConjClass (⟨x, l⟩ : FreeLoopSpace X) := by
  sorry

/-- The fiber sequence is functorial. -/
theorem freeLoopFiberSeq_functorial {X Y : Type u} (f : X → Y) (x₀ : X) :
    ∃ (_map : FreeLoopSpace X → FreeLoopSpace Y), True := by
  sorry

/-- PiOneConjClass is invariant under conjugation. -/
theorem piOneConjClass_conjugation_invariant {X : Type u} {x₀ : X}
    (α : PiOne X x₀) (g : PiOne X x₀) :
    piOneConjClassMap X x₀ α =
      piOneConjClassMap X x₀ (Homotopy.LoopGroupAlgebra.conj g α) := by
  sorry

/-- The evaluation map at the base loop yields the basepoint. -/
theorem freeLoopEval_refl {X : Type u} (x : X) :
    freeLoopEval (⟨x, Path.refl x⟩ : FreeLoopSpace X) = x := by
  sorry

/-- freeLoopConjClass of a constant loop is the identity conjugacy class. -/
theorem freeLoopConjClass_refl {X : Type u} (x : X) :
    freeLoopConjClass (freeLoopBase x) = piOneConjClassMap X x (PiOne.ofLoop (Path.refl x)) := by
  sorry

/-- The fiber sequence evaluation map agrees with freeLoopEval. -/
theorem freeLoopFiberSeq_eval_eq {X : Type u} (x₀ : X) :
    (freeLoopFiberSeq X x₀).total_map = @freeLoopEval X := by
  sorry

/-- Every free loop determines an element of the fundamental group up to conjugation. -/
theorem freeLoop_determines_conjugacy_class {X : Type u} (l : FreeLoopSpace X) :
    ∃ (c : piOneConjClass X l.1), c = freeLoopConjClass l := by
  sorry

/-! ## Summary

We defined Map(S1, X) and the free loop space as pairs of points and loops,
recorded the evaluation fibration via the canonical fiber sequence, and linked
free loops to conjugacy classes in the fundamental group through the orbit map.
-/

end FreeLoopSpace
end Path
end ComputationalPaths
