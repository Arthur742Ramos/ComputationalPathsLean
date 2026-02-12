/-
# Grothendieck Construction for the Fundamental Groupoid

This module packages the Grothendieck construction for the fundamental groupoid.
Type-valued functors on Π₁(A) correspond to fibrations over A, and their
category of elements is the total space with its induced fundamental groupoid.

## Key Results

- `GrothendieckTotal`: the type of elements (total space) of a functor
- `grothendieckProjection`: the projection functor to the base groupoid
- `functorFibrationEquiv`: equivalence between type-valued functors and fibrations

## References

- HoTT Book, Chapter 2 (groupoids of paths)
- Brown, "Topology and Groupoids"
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroupoid
import ComputationalPaths.Path.Homotopy.FundamentalGroupoidFunctor
import ComputationalPaths.Path.Homotopy.Fibration

namespace ComputationalPaths
namespace Path

universe u v

/-! ## Functors to types -/

/-- Type-valued functors out of the fundamental groupoid. -/
abbrev FundamentalGroupoidTypeFunctor (A : Type u) : Type (u + 1) :=
  EqFunctor (A := A) (B := Type u)

/-- A fibration over A is a type family in the same universe. -/
abbrev FibrationFamily (A : Type u) : Type (u + 1) :=
  A → Type u

/-! ## Fiber transport -/

/-- Transport along base paths in a fibration family. -/
def transportFiber {A : Type u} (P : FibrationFamily A) {a b : A}
    (p : Path a b) (x : P a) : P b :=
  Path.transport p x

/-- Transport along reflexive paths is the identity. -/
@[simp] theorem transportFiber_refl {A : Type u} (P : FibrationFamily A)
    (a : A) (x : P a) :
    transportFiber P (Path.refl a) x = x := by
  rfl

/-- Transport is functorial with respect to path composition. -/
@[simp] theorem transportFiber_trans {A : Type u} (P : FibrationFamily A)
    {a b c : A} (p : Path a b) (q : Path b c) (x : P a) :
    transportFiber P (Path.trans p q) x =
      transportFiber P q (transportFiber P p x) := by
  unfold transportFiber
  simpa using (Path.transport_trans (D := P) p q x)

/-! ## Category of elements -/

/-- The total space (category of elements) of a type-valued functor. -/
abbrev GrothendieckTotal {A : Type u} (F : FundamentalGroupoidTypeFunctor A) : Type u :=
  Fibration.Total (P := F.obj)

/-- The Grothendieck construction as the fundamental groupoid of the total space. -/
abbrev GrothendieckConstruction {A : Type u} (F : FundamentalGroupoidTypeFunctor A) :
    StrictGroupoid (GrothendieckTotal F) :=
  FundamentalGroupoid (GrothendieckTotal F)

/-- Projection functor from the Grothendieck construction to the base groupoid. -/
def grothendieckProjection {A : Type u} (F : FundamentalGroupoidTypeFunctor A) :
    FundamentalGroupoidFunctor (GrothendieckTotal F) A :=
  fundamentalGroupoidFunctor (A := GrothendieckTotal F) (B := A)
    (Fibration.Total.proj (P := F.obj))

/-- The projection functor acts on objects by the first projection. -/
@[simp] theorem grothendieckProjection_obj {A : Type u}
    (F : FundamentalGroupoidTypeFunctor A) (x : GrothendieckTotal F) :
    (grothendieckProjection F).obj x = x.1 := rfl

/-! ## Functor–fibration equivalence -/

namespace EqFunctor

/-- Extensionality for equality-valued functors. -/
@[ext] theorem ext {A : Type u} {B : Type v} {F G : EqFunctor A B}
    (h_obj : ∀ a, F.obj a = G.obj a) : F = G := by
  cases F with
  | mk objF mapF map_reflF map_transF map_symmF =>
    cases G with
    | mk objG mapG map_reflG map_transG map_symmG =>
      have h_obj' : objF = objG := funext h_obj
      subst h_obj'
      have h_map' : @mapF = @mapG := by
        funext a b p
        apply Subsingleton.elim
      cases h_map'
      have h_refl : @map_reflF = @map_reflG := by
        funext a
        apply Subsingleton.elim
      have h_trans : @map_transF = @map_transG := by
        funext a b c p q
        apply Subsingleton.elim
      have h_symm : @map_symmF = @map_symmG := by
        funext a b p
        apply Subsingleton.elim
      cases h_refl
      cases h_trans
      cases h_symm
      rfl

end EqFunctor

/-- Forgetful map from type-valued functors to fibrations. -/
def functorToFibration {A : Type u} (F : FundamentalGroupoidTypeFunctor A) :
    FibrationFamily A :=
  F.obj

/-- The canonical functor associated to a fibration. -/
def fibrationToFunctor {A : Type u} (P : FibrationFamily A) :
    FundamentalGroupoidTypeFunctor A :=
  EqFunctor.ofFunction (A := A) (B := Type u) P

/-- Functor-to-fibration round-trip is the identity. -/
theorem functorToFibration_left_inv {A : Type u} (F : FundamentalGroupoidTypeFunctor A) :
    fibrationToFunctor (functorToFibration F) = F := by
  apply EqFunctor.ext
  · intro a
    rfl

/-- Fibration-to-functor round-trip is the identity. -/
theorem functorToFibration_right_inv {A : Type u} (P : FibrationFamily A) :
    functorToFibration (fibrationToFunctor P) = P := rfl

/-- Type-valued functors on Π₁(A) are equivalent to fibrations over A. -/
def functorFibrationEquiv (A : Type u) :
    SimpleEquiv (FundamentalGroupoidTypeFunctor A) (FibrationFamily A) where
  toFun := functorToFibration
  invFun := fibrationToFunctor
  left_inv := functorToFibration_left_inv
  right_inv := functorToFibration_right_inv

/-! ## Summary

1. The Grothendieck construction is the fundamental groupoid of the total space.
2. The projection to the base is a fundamental groupoid functor.
3. Type-valued functors on Π₁(A) are equivalent to fibrations over A.
-/

end Path
end ComputationalPaths
