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
noncomputable def fiberSeq {f : A → B} {b : B} (x0 : HomotopyFiber f b) :
    FiberSeq (HomotopyFiber f b) A B where
  proj := f
  baseB := b
  baseE := x0.point
  base_proj := x0.prop
  toFiber := fun x => x
  fromFiber := fun x => x
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- `Path` witness for the basepoint projection in the homotopy fiber sequence. -/
noncomputable def fiberSeq_base_proj_path {f : A → B} {b : B} (x0 : HomotopyFiber f b) :
    Path ((fiberSeq (f := f) (b := b) x0).proj (fiberSeq (f := f) (b := b) x0).baseE)
      (fiberSeq (f := f) (b := b) x0).baseB :=
  (fiberSeq (f := f) (b := b) x0).base_proj

/-- `Path` witness for the left inverse of the homotopy fiber sequence identification. -/
noncomputable def fiberSeq_left_inv_path {f : A → B} {b : B} (x0 : HomotopyFiber f b)
    (x : HomotopyFiber f b) :
    Path ((fiberSeq (f := f) (b := b) x0).fromFiber ((fiberSeq (f := f) (b := b) x0).toFiber x)) x :=
  Path.stepChain ((fiberSeq (f := f) (b := b) x0).left_inv x)

/-- `Path` witness for the right inverse of the homotopy fiber sequence identification. -/
noncomputable def fiberSeq_right_inv_path {f : A → B} {b : B} (x0 : HomotopyFiber f b)
    (x : Fiber (fiberSeq (f := f) (b := b) x0).proj (fiberSeq (f := f) (b := b) x0).baseB) :
    Path ((fiberSeq (f := f) (b := b) x0).toFiber ((fiberSeq (f := f) (b := b) x0).fromFiber x)) x :=
  Path.stepChain ((fiberSeq (f := f) (b := b) x0).right_inv x)

/-- The homotopy fiber sequence is exact at the total space. -/
noncomputable def fiberSeq_exact {f : A → B} {b : B} (x0 : HomotopyFiber f b) :
    IsExactAt (fiberSeq (f := f) (b := b) x0) := by
  refine
    { incl_to_base := ?_, base_from_fiber := ?_ }
  · intro x
    exact x.prop
  · intro e h
    exact ⟨⟨e, h.toEq⟩, Path.refl e⟩

/-! ## Total space equivalence -/

/-- The total space of the homotopy fiber family is equivalent to `A`. -/
noncomputable def totalEquiv (f : A → B) :
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

/-- `Path` witness for the left round-trip of `totalEquiv`. -/
noncomputable def totalEquiv_left_inv_path (f : A → B)
    (x : Total (P := family f)) :
    Path ((totalEquiv (f := f)).invFun ((totalEquiv (f := f)).toFun x)) x :=
  Path.stepChain ((totalEquiv (f := f)).left_inv x)

/-- `Path` witness for the right round-trip of `totalEquiv`. -/
noncomputable def totalEquiv_right_inv_path (f : A → B) (a : A) :
    Path ((totalEquiv (f := f)).toFun ((totalEquiv (f := f)).invFun a)) a :=
  Path.stepChain ((totalEquiv (f := f)).right_inv a)

/-- The projection of the homotopy fiber total space corresponds to `f`. -/
theorem total_proj (f : A → B) :
    Total.proj (P := family f) ∘ (totalEquiv (f := f)).invFun = f := by
  funext a
  rfl

/-- `Path` witness for the total-space projection correspondence, pointwise. -/
noncomputable def total_proj_apply_path (f : A → B) (a : A) :
    Path (Total.proj ((totalEquiv (f := f)).invFun a)) (f a) :=
  Path.stepChain rfl

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

/-- `Path` witness for exactness at the total-space term. -/
noncomputable def exact_at_totalSpace_path {f : A → B} (b : B) (x0 : HomotopyFiber f b)
    (α : π₁(HomotopyFiber f b, x0)) :
    Path
      (inducedPi1Map Total.proj ⟨b, x0⟩
        (inducedPi1Map (fun x => (⟨b, x⟩ : Total (P := family f))) x0 α))
      (Quot.mk _ (Path.refl b)) :=
  Path.stepChain (exact_at_totalSpace (f := f) b x0 α)

/-- Exactness at the base term for the homotopy fiber sequence. -/
theorem exact_at_base {f : A → B} (b : B) (x0 : HomotopyFiber f b) :
    ∀ β : π₁(Total (P := family f), ⟨b, x0⟩),
      connectingMapPi1 b x0 (inducedPi1Map Total.proj ⟨b, x0⟩ β) = x0 :=
  LongExactSequence.exact_at_base (P := family f) b x0

/-- `Path` witness for exactness at the base term. -/
noncomputable def exact_at_base_path {f : A → B} (b : B) (x0 : HomotopyFiber f b)
    (β : π₁(Total (P := family f), ⟨b, x0⟩)) :
    Path (connectingMapPi1 b x0 (inducedPi1Map Total.proj ⟨b, x0⟩ β)) x0 :=
  Path.stepChain (exact_at_base (f := f) b x0 β)

/-! ## Fibration case -/

/-- For a type family fibration, the homotopy fiber agrees with the actual fiber. -/
noncomputable def fibrationEquiv {P : B → Type u} (b : B) :
    SimpleEquiv (HomotopyFiber (@Total.proj B P) b) (P b) :=
  fiberEquivFamily (P := P) b

/-- `Path` witness for the left round-trip of `fibrationEquiv`. -/
noncomputable def fibrationEquiv_left_inv_path {P : B → Type u} (b : B)
    (x : HomotopyFiber (@Total.proj B P) b) :
    Path ((fibrationEquiv (P := P) b).invFun ((fibrationEquiv (P := P) b).toFun x)) x :=
  fiberEquivFamily_left_inv_path (P := P) b x

/-- `Path` witness for the right round-trip of `fibrationEquiv`. -/
noncomputable def fibrationEquiv_right_inv_path {P : B → Type u} (b : B)
    (x : P b) :
    Path ((fibrationEquiv (P := P) b).toFun ((fibrationEquiv (P := P) b).invFun x)) x :=
  fiberEquivFamily_right_inv_path (P := P) b x


private noncomputable def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

/-! ## Summary

We defined homotopy fibers as fibers of maps, packaged the associated fiber
sequence and π₁ long exact sequence properties, and showed that for type
families the homotopy fiber recovers the actual fiber.
-/

end HomotopyFiber
end Path
end ComputationalPaths
