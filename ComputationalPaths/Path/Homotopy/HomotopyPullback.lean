/-
# Homotopy Properties of Pullback Squares

This module records basic homotopy-invariance properties for pullback squares in
the computational paths setting.

## Key Results

- `HomotopyPullbackSquare`: squares commuting up to Path-valued homotopy.
- `HomotopyPullbackSquare.of_eq`: strict commutation gives a homotopy square.
- `pullback_square_commutes`: the canonical computational pullback square commutes.

## References

- HoTT Book, Chapter 2 (pullbacks and homotopies).
-/

import ComputationalPaths.Path.CompPath.PullbackPaths
import ComputationalPaths.Path.Homotopy.HoTT

namespace ComputationalPaths
namespace Path
namespace HomotopyPullback

open HoTT
open CompPath

universe u

/-! ## Definition -/

/-- A pullback square that commutes up to homotopy.
    For maps f : X → Z and g : Y → Z with projections p1 : P → X and p2 : P → Y,
    the square commutes up to homotopy if f ∘ p1 is homotopic to g ∘ p2. -/
structure HomotopyPullbackSquare {X Y Z P : Type u}
    (f : X → Z) (g : Y → Z) (p1 : P → X) (p2 : P → Y) : Type u where
  /-- Pointwise homotopy witnessing the commutative square. -/
  comm : FunHomotopy (fun p => f (p1 p)) (fun p => g (p2 p))

namespace HomotopyPullbackSquare

/-! ## Basic properties -/

/-- A strictly commuting square yields a homotopy pullback square. -/
noncomputable def of_eq {X Y Z P : Type u} {f : X → Z} {g : Y → Z}
    {p1 : P → X} {p2 : P → Y}
    (h : (fun p => f (p1 p)) = (fun p => g (p2 p))) :
    HomotopyPullbackSquare f g p1 p2 where
  comm := fun p =>
    Path.stepChain (_root_.congrArg (fun k => k p) h)

/-- Homotopy pullback squares are symmetric in composition order. -/
noncomputable def symm {X Y Z P : Type u} {f : X → Z} {g : Y → Z}
    {p1 : P → X} {p2 : P → Y} (h : HomotopyPullbackSquare f g p1 p2) :
    FunHomotopy (fun p => g (p2 p)) (fun p => f (p1 p)) :=
  fun p => Path.symm (h.comm p)

end HomotopyPullbackSquare

/-! ## Pullback square in the path setting -/

/-- The canonical pullback square in the computational pullback type commutes. -/
noncomputable def pullback_square_commutes {A B C : Type u} (f : A → C) (g : B → C) :
    HomotopyPullbackSquare f g
      (CompPath.Pullback.fst (f := f) (g := g))
      (CompPath.Pullback.snd (f := f) (g := g)) where
  comm := fun x => CompPath.Pullback.comm (f := f) (g := g) x

/-! ## Summary

We defined homotopy pullback squares using computational paths, showed that
strict commutation yields a Path-valued homotopy, and recorded the canonical
pullback square for the computational pullback type.
-/

end HomotopyPullback
end Path
end ComputationalPaths
