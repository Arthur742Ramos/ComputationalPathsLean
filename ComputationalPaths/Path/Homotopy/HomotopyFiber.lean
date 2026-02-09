/-
# Homotopy Fibers of Maps

This module defines the homotopy fiber of a map and packages the resulting
fiber sequence and long exact sequence properties at the π₁ level. It also
records that the homotopy fiber of a type-family fibration agrees with the
actual fiber.

## Key Results

- `HomotopyFiber`: homotopy fiber of a map
- `HomotopyFiber.fiberSeq`: homotopy fiber sequence
- `HomotopyFiber.fiberSeq_exact`: exactness at the total space
- `HomotopyFiber.longExactSequence`: π₁ long exact sequence for the homotopy fiber
- `HomotopyFiber.fibrationEquiv`: homotopy fiber of a fibration is the actual fiber

## References

- HoTT Book, Chapter 4 (homotopy fibers)
- May, "A Concise Course in Algebraic Topology"
-/

import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Homotopy.LongExactSequence

namespace ComputationalPaths
namespace Path

open Fibration

universe u

variable {A : Type u} {B : Type u}

/-! ## Definition -/

/-- The homotopy fiber of a map `f` at `b`. -/
abbrev HomotopyFiber (f : A → B) (b : B) : Type u :=
  Fiber f b

namespace HomotopyFiber

/-! ## Fiber sequence -/

/-- The homotopy fiber family associated to `f`. -/
abbrev family (f : A → B) : B → Type u :=
  fun b => HomotopyFiber f b

/-- The homotopy fiber sequence `hofiber f b → A → B` at a chosen basepoint. -/
def fiberSeq {f : A → B} {b : B} (x0 : HomotopyFiber f b) :
    FiberSeq (HomotopyFiber f b) A B where
  proj := f
  baseB := b
  baseE := x0.point
  base_proj := x0.prop
  toFiber := fun x => x
  fromFiber := fun x => x
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- The homotopy fiber sequence is exact at the total space. -/
theorem fiberSeq_exact {f : A → B} {b : B} (x0 : HomotopyFiber f b) :
    IsExactAt (fiberSeq (f := f) (b := b) x0) := by
  refine
    { incl_to_base := ?_, base_from_fiber := ?_ }
  · intro x
    exact x.prop
  · intro e h
    exact ⟨⟨e, h⟩, rfl⟩

/-! ## Total space equivalence -/

/-- The total space of the homotopy fiber family is equivalent to `A`. -/
def totalEquiv (f : A → B) :
    SimpleEquiv (Total (P := family f)) A where
  toFun := fun x => x.2.point
  invFun := fun a => ⟨f a, ⟨a, rfl⟩⟩
  left_inv := by
    intro x
    cases x with
    | mk b fib =>
        cases fib with
        | mk a h =>
            cases h
            rfl
  right_inv := by
    intro a
    rfl

/-- The projection of the homotopy fiber total space corresponds to `f`. -/
theorem total_proj (f : A → B) :
    Total.proj (P := family f) ∘ (totalEquiv (f := f)).invFun = f := by
  funext a
  rfl

/-! ## Long exact sequence properties -/

/-- The π₁ long exact sequence attached to the homotopy fiber family of `f`. -/
noncomputable def longExactSequence {f : A → B} (b : B) (x0 : HomotopyFiber f b) :
    Fibration.LongExactSequencePi1 (P := family f) b x0 :=
  Fibration.longExactSequence (P := family f) b x0

/-- Exactness at the total space term for the homotopy fiber sequence. -/
theorem exact_at_totalSpace {f : A → B} (b : B) (x0 : HomotopyFiber f b) :
    ∀ α : π₁(HomotopyFiber f b, x0),
      inducedPi1Map Total.proj ⟨b, x0⟩
          (inducedPi1Map (fun x => (⟨b, x⟩ : Total (P := family f))) x0 α) =
        Quot.mk _ (Path.refl b) :=
  LongExactSequence.exact_at_totalSpace (P := family f) b x0

/-- Exactness at the base term for the homotopy fiber sequence. -/
theorem exact_at_base {f : A → B} (b : B) (x0 : HomotopyFiber f b) :
    ∀ β : π₁(Total (P := family f), ⟨b, x0⟩),
      connectingMapPi1 b x0 (inducedPi1Map Total.proj ⟨b, x0⟩ β) = x0 :=
  LongExactSequence.exact_at_base (P := family f) b x0

/-! ## Fibration case -/

/-- For a type family fibration, the homotopy fiber agrees with the actual fiber. -/
def fibrationEquiv {P : B → Type u} (b : B) :
    SimpleEquiv (HomotopyFiber (@Total.proj B P) b) (P b) :=
  fiberEquivFamily (P := P) b

/-! ## Summary

We defined homotopy fibers as fibers of maps, packaged the associated fiber
sequence and π₁ long exact sequence properties, and showed that for type
families the homotopy fiber recovers the actual fiber.
-/

end HomotopyFiber
end Path
end ComputationalPaths
