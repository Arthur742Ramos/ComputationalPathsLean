/-
# Brouwer degree and fixed point consequences

This module provides a lightweight Mathlib-friendly interface for Brouwer
degree on continuous self-maps. We package the degree as data together with
homotopy invariance and a "no fixed point implies null-homotopic" hypothesis.
From this data we derive fixed point consequences.

## Key Results

- `BrouwerDegreeData`: degree assignment for continuous self-maps.
- `degree_of_no_fixed_point`: maps without fixed points have degree 0.
- `fixed_point_of_degree_ne_zero`: nonzero degree forces a fixed point.
- `brouwer_fixed_point`: homotopy-to-identity implies a fixed point.

## References

- Hatcher, *Algebraic Topology*, Section 2.2.
- HoTT Book, Section 8.7.
-/

import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.ContinuousMap.Basic

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace BrouwerDegree

open scoped Topology

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Data for a Brouwer degree on continuous self-maps of `X`. -/
structure BrouwerDegreeData (X : Type u) [TopologicalSpace X] where
  /-- The degree of a continuous self-map. -/
  degree : C(X, X) → Int
  /-- Homotopy invariance of the degree. -/
  homotopy_invariant :
      ∀ {f g : C(X, X)}, ContinuousMap.Homotopic f g → degree f = degree g
  /-- Degree of the identity map. -/
  degree_id : degree (ContinuousMap.id X) = 1
  /-- Degree of a constant map. -/
  degree_const : ∀ x : X, degree (ContinuousMap.const X x) = 0
  /-- Maps without fixed points are homotopic to a constant map. -/
  homotopy_const_of_no_fixed_point :
      ∀ f : C(X, X), (∀ x, f x ≠ x) →
        ∃ x : X, ContinuousMap.Homotopic f (ContinuousMap.const X x)

attribute [simp] BrouwerDegreeData.degree_id BrouwerDegreeData.degree_const

namespace BrouwerDegreeData

/-- Maps without fixed points have degree zero. -/
theorem degree_of_no_fixed_point (D : BrouwerDegreeData X) (f : C(X, X))
    (h : ∀ x, f x ≠ x) : D.degree f = 0 := by
  rcases D.homotopy_const_of_no_fixed_point f h with ⟨x, hx⟩
  calc
    D.degree f = D.degree (ContinuousMap.const X x) :=
      D.homotopy_invariant hx
    _ = 0 := D.degree_const x

/-- A nonzero degree forces a fixed point. -/
theorem fixed_point_of_degree_ne_zero (D : BrouwerDegreeData X) (f : C(X, X))
    (hdeg : D.degree f ≠ 0) : ∃ x, f x = x := by
  by_contra h
  have h' : ∀ x, f x ≠ x := by
    intro x hx
    exact h ⟨x, hx⟩
  exact hdeg (degree_of_no_fixed_point D f h')

/-- A map homotopic to the identity has a fixed point. -/
theorem fixed_point_of_homotopic_id (D : BrouwerDegreeData X) (f : C(X, X))
    (h : ContinuousMap.Homotopic f (ContinuousMap.id X)) : ∃ x, f x = x := by
  have hdeg : D.degree f = 1 := by
    calc
      D.degree f = D.degree (ContinuousMap.id X) := D.homotopy_invariant h
      _ = 1 := D.degree_id
  have hdeg_ne : D.degree f ≠ 0 := by
    have : (1 : Int) ≠ 0 := by decide
    simpa [hdeg] using this
  exact fixed_point_of_degree_ne_zero D f hdeg_ne

/-- Brouwer fixed point theorem in the presence of degree data. -/
theorem brouwer_fixed_point (D : BrouwerDegreeData X) (f : C(X, X))
    (h : ContinuousMap.Homotopic f (ContinuousMap.id X)) : ∃ x, f x = x :=
  fixed_point_of_homotopic_id D f h

end BrouwerDegreeData

/-! ## Summary

We packaged Brouwer degree as data on continuous self-maps, proved that
absence of fixed points forces degree zero, and derived fixed-point results
for maps homotopic to the identity.
-/

end BrouwerDegree
end Homotopy
end Path
end ComputationalPaths
