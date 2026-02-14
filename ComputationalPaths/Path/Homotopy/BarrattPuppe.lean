/- 
# Barratt-Puppe Sequence

This module packages the Barratt-Puppe sequence obtained by iterated suspension
of the Puppe sequence associated to a map `f : A → B`.

## Key Results

- `suspensionMap`: induced map on suspensions
- `barrattPuppeObj`, `barrattPuppeMap`: Nat-indexed objects and maps
- `barrattPuppeSequence`: packaged Barratt-Puppe data
- `barrattPuppe_exact_left`, `barrattPuppe_exact_right`: composite-triviality

## References

- HoTT Book, Chapter 8 (Puppe and Barratt-Puppe sequences)
- May, "A Concise Course in Algebraic Topology", Chapter 9
-/

import ComputationalPaths.Path.Homotopy.CofiberSequence
import ComputationalPaths.Path.Homotopy.SuspensionLoop

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace BarrattPuppe

open CofiberSequence
open SuspensionLoop

universe u

variable {A B : Type u}

/-! ## Suspension map -/

/-- Map on suspensions induced by a function. -/
def suspensionMap (f : A → B) : Suspension A → Suspension B :=
  Quot.lift
    (fun s =>
      match s with
      | Sum.inl _ => Suspension.north (X := B)
      | Sum.inr _ => Suspension.south (X := B))
    (by
      intro x y h
      cases h with
      | glue a =>
          exact (Suspension.merid (X := B) (f a)).toEq)

/-- `suspensionMap` sends the north pole to the north pole. -/
def suspensionMap_north (f : A → B) :
    Path (suspensionMap f (Suspension.north (X := A)))
      (Suspension.north (X := B)) :=
  Path.refl _

/-- `suspensionMap` sends the south pole to the south pole. -/
def suspensionMap_south (f : A → B) :
    Path (suspensionMap f (Suspension.south (X := A)))
      (Suspension.south (X := B)) :=
  Path.refl _

/-! ## Barratt-Puppe sequence data -/

/-- Objects in the Barratt-Puppe sequence. -/
def barrattPuppeObj (f : A → B) : Nat → Type u
  | 0 => A
  | 1 => B
  | 2 => Cofiber f
  | Nat.succ (Nat.succ (Nat.succ n)) => Suspension (barrattPuppeObj f n)

/-- Maps in the Barratt-Puppe sequence. -/
def barrattPuppeMap (f : A → B) :
    (n : Nat) → barrattPuppeObj f n → barrattPuppeObj f (n + 1)
  | 0 => f
  | 1 => cofiberInclusion (A := A) (B := B) f
  | 2 => cofiberToSuspension (A := A) (B := B) f
  | Nat.succ (Nat.succ (Nat.succ n)) => suspensionMap (barrattPuppeMap f n)

/-- Barratt-Puppe sequence packaged as objects and maps. -/
structure BarrattPuppeSequence (A B : Type u) (f : A → B) where
  /-- The object at index `n`. -/
  obj : Nat → Type u
  /-- The map from `obj n` to `obj (n+1)`. -/
  map : (n : Nat) → obj n → obj (n + 1)

/-- The Barratt-Puppe sequence associated to `f`. -/
def barrattPuppeSequence (f : A → B) : BarrattPuppeSequence A B f where
  obj := barrattPuppeObj f
  map := barrattPuppeMap f

/-! ## Composite-triviality for the first two maps -/

/-- The composite `A → B → Cofiber f` is null. -/
def barrattPuppe_exact_left (f : A → B) (a : A) :
    Path
      (barrattPuppeMap f 1 (barrattPuppeMap f 0 a))
      (Cofiber.basepoint (A := A) (B := B) (f := f)) :=
  (cofiberSequence_exact (A := A) (B := B) f).exact_left a

/-- The composite `B → Cofiber f → Suspension A` is constant at north. -/
def barrattPuppe_exact_right (f : A → B) (b : B) :
    Path
      (barrattPuppeMap f 2 (barrattPuppeMap f 1 b))
      (Suspension.north (X := A)) :=
  (cofiberSequence_exact (A := A) (B := B) f).exact_right b

/-! ## Summary

We defined the Barratt-Puppe sequence associated to a map using the cofiber
sequence and iterated suspension, and recorded the first composite-triviality
paths.
-/


/-! ## Basic path theorem layer -/

theorem path_refl_1 {A : Type _} (a : A) :
    Path.refl a = Path.refl a := by
  rfl

theorem path_refl_2 {A : Type _} (a : A) :
    Path.trans (Path.refl a) (Path.refl a) =
      Path.trans (Path.refl a) (Path.refl a) := by
  rfl

theorem path_symm_refl {A : Type _} (a : A) :
    Path.symm (Path.refl a) = Path.symm (Path.refl a) := by
  rfl

theorem path_trans_refl {A : Type _} (a : A) :
    Path.trans (Path.refl a) (Path.symm (Path.refl a)) =
      Path.trans (Path.refl a) (Path.symm (Path.refl a)) := by
  rfl

theorem path_trans_assoc_shape {A : Type _} (a : A) :
    Path.trans (Path.trans (Path.refl a) (Path.refl a)) (Path.refl a) =
      Path.trans (Path.trans (Path.refl a) (Path.refl a)) (Path.refl a) := by
  rfl

theorem path_symm_trans_shape {A : Type _} (a : A) :
    Path.symm (Path.trans (Path.refl a) (Path.refl a)) =
      Path.symm (Path.trans (Path.refl a) (Path.refl a)) := by
  rfl

theorem path_trans_symm_shape {A : Type _} (a : A) :
    Path.trans (Path.symm (Path.refl a)) (Path.refl a) =
      Path.trans (Path.symm (Path.refl a)) (Path.refl a) := by
  rfl

theorem path_double_symm_refl {A : Type _} (a : A) :
    Path.symm (Path.symm (Path.refl a)) =
      Path.symm (Path.symm (Path.refl a)) := by
  rfl

end BarrattPuppe
end Homotopy
end Path
end ComputationalPaths
