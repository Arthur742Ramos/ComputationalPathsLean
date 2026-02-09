/-
# Homotopy Properties of Pullback Squares

This module records basic homotopy-invariance properties for pullback squares in `TopCat`.

## Key Results

- `HomotopyPullbackSquare`: squares commuting up to homotopy.
- `HomotopyPullbackSquare.of_eq`: strict commutation gives a homotopy square.
- `pullback_square_commutes`: the canonical pullback square in `TopCat` strictly commutes.

## References

- HoTT Book, Chapter 2 (pullbacks and homotopies).
-/

import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

open CategoryTheory
open CategoryTheory.Limits

/-! ## Definition -/

/-- A pullback square that commutes up to homotopy.
    For continuous maps f : X → Z and g : Y → Z with projections p1 : P → X and p2 : P → Y,
    the square commutes up to homotopy if f ∘ p1 is homotopic to g ∘ p2. -/
structure HomotopyPullbackSquare {X Y Z P : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace P] (f : C(X, Z)) (g : C(Y, Z))
    (p1 : C(P, X)) (p2 : C(P, Y)) : Prop where
  homotopic : ContinuousMap.Homotopic (f.comp p1) (g.comp p2)

namespace HomotopyPullbackSquare

/-! ## Basic properties -/

/-- A strictly commuting square yields a homotopy pullback square. -/
theorem of_eq {X Y Z P : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace P] {f : C(X, Z)} {g : C(Y, Z)}
    {p1 : C(P, X)} {p2 : C(P, Y)} (h : f.comp p1 = g.comp p2) :
    HomotopyPullbackSquare f g p1 p2 where
  homotopic := h ▸ ContinuousMap.Homotopic.refl _

/-- Homotopy pullback squares are symmetric in composition order. -/
theorem symm {X Y Z P : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace P] {f : C(X, Z)} {g : C(Y, Z)}
    {p1 : C(P, X)} {p2 : C(P, Y)} (h : HomotopyPullbackSquare f g p1 p2) :
    ContinuousMap.Homotopic (g.comp p2) (f.comp p1) :=
  h.homotopic.symm

end HomotopyPullbackSquare

/-! ## Pullback square in TopCat -/

/-- The canonical pullback square in `TopCat` strictly commutes. -/
theorem pullback_square_commutes {X Y Z : TopCat} (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback.fst f g ≫ f = pullback.snd f g ≫ g :=
  pullback.condition

/-! ## Summary

We defined homotopy pullback squares using continuous maps and the Mathlib homotopy API,
showed that strict commutation implies homotopy commutation, and recorded that the
canonical pullback square in `TopCat` strictly commutes.
-/
