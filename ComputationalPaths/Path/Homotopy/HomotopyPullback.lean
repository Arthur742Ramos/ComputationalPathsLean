/- 
# Homotopy Pullbacks

This module defines homotopy pullbacks (homotopy fiber products) using
computational paths. We record the universal property via cones and connect
the construction to fibrations by identifying it with the total space of a
pullback family over the right leg.

## Key Results

- `HomotopyPullback`: homotopy pullback of a span.
- `HomotopyPullback.coneEquiv`: universal property equivalence.
- `HomotopyPullback.family`: pullback family over the right leg.
- `HomotopyPullback.totalEquiv`: equivalence with the total space of the family.
- `HomotopyPullback.total_proj`: projection compatibility.

## References

- HoTT Book, Chapter 2 (pullbacks).
-/

import ComputationalPaths.Path.CompPath.PullbackPaths
import ComputationalPaths.Path.Homotopy.Fibration

namespace ComputationalPaths
namespace Path

open Fibration

universe u x

variable {A : Type u} {B : Type u} {C : Type u}

/-! ## Definition -/

/-- The homotopy pullback of a span `A -> C <- B`. -/
abbrev HomotopyPullback (f : A → C) (g : B → C) : Type u :=
  CompPath.Pullback A B C f g

namespace HomotopyPullback

variable {f : A → C} {g : B → C}

/-! ## Universal property -/

/-- A cone over the span `A -> C <- B` with vertex `X`. -/
abbrev Cone (X : Type x) : Type (max u x) :=
  CompPath.Pullback.Cone (A := A) (B := B) (C := C) (f := f) (g := g) X

/-- The canonical lift into the homotopy pullback. -/
abbrev lift {X : Type x} (p : X → A) (q : X → B)
    (h : ∀ x : X, Path (f (p x)) (g (q x))) :
    X → HomotopyPullback (f := f) (g := g) :=
  CompPath.Pullback.lift (A := A) (B := B) (C := C) (f := f) (g := g) p q h

/-- Universal property: maps into the homotopy pullback are equivalent to cones. -/
abbrev coneEquiv (X : Type x) :
    SimpleEquiv (X → HomotopyPullback (f := f) (g := g))
      (Cone (A := A) (B := B) (C := C) (f := f) (g := g) X) :=
  CompPath.Pullback.coneEquiv (A := A) (B := B) (C := C) (f := f) (g := g) X

/-! ## Connection to fibrations -/

/-- The pullback family over `B`, with fiber the homotopy fiber of `f` over `g b`. -/
abbrev family (f : A → C) (g : B → C) : B → Type u :=
  fun b => Sigma fun a : A => Path (f a) (g b)

/-- The homotopy pullback is equivalent to the total space of the pullback family. -/
def totalEquiv (f : A → C) (g : B → C) :
    SimpleEquiv (HomotopyPullback (f := f) (g := g))
      (Total (P := family (f := f) (g := g))) where
  toFun := fun x =>
    match x with
    | ⟨(a, b), h⟩ => ⟨b, ⟨a, h⟩⟩
  invFun := fun x =>
    match x with
    | ⟨b, ⟨a, h⟩⟩ => ⟨(a, b), h⟩
  left_inv := by
    intro x
    cases x with
    | mk ab h =>
        cases ab with
        | mk a b => rfl
  right_inv := by
    intro x
    cases x with
    | mk b rest =>
        cases rest with
        | mk a h => rfl

/-- The projection to `B` agrees with the total-space projection of the family. -/
theorem total_proj (f : A → C) (g : B → C) :
    Total.proj (P := family (f := f) (g := g)) ∘
        (totalEquiv (f := f) (g := g)).toFun =
      CompPath.Pullback.snd (A := A) (B := B) (C := C) (f := f) (g := g) := by
  rfl

/-! ## Summary

We defined homotopy pullbacks using computational paths, recorded the universal
property via cones, and identified the homotopy pullback with the total space
of a pullback family over the right leg.
-/

end HomotopyPullback
end Path
end ComputationalPaths
