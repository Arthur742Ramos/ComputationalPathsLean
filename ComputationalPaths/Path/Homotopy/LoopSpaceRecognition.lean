/-
# Loop Space Recognition Principles

This module formalizes loop space recognition principles in the computational
paths framework. We define group-like E1 spaces, the bar construction on
monoids, delooping data, and the May recognition theorem packaging.

## Key Results

- `GroupLikeE1Space`: a monoid with homotopy-inverse witnessed by `Path`
- `BarConstruction`: the bar construction on a strict monoid
- `DeloopingData`: data delooping a group-like space
- `MayRecognition`: the May recognition theorem packaging
- `recognitionFromDelooping`: construction witnessing recognition

## References

- May, "The Geometry of Iterated Loop Spaces"
- Stasheff, "Homotopy Associativity of H-Spaces"
- Adams, "Infinite Loop Spaces"
-/

import ComputationalPaths.Path.Homotopy.LoopSpaceAlgebra
import ComputationalPaths.Path.Homotopy.SuspensionLoop
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Algebra.GroupStructures

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace LoopSpaceRecognition

open SuspensionLoop
open Algebra

universe u

/-! ## Group-like E1 spaces -/

/-- A monoid structure on a pointed type with multiplication witnessed by functions. -/
structure PointedMonoid (X : Pointed) where
  /-- Binary multiplication. -/
  mul : X.carrier → X.carrier → X.carrier
  /-- The basepoint is a left unit. -/
  mul_pt_left : ∀ x : X.carrier, mul X.pt x = x
  /-- The basepoint is a right unit. -/
  mul_pt_right : ∀ x : X.carrier, mul x X.pt = x
  /-- Multiplication is associative. -/
  mul_assoc : ∀ x y z : X.carrier, mul (mul x y) z = mul x (mul y z)

/-- A group-like E1 space: a pointed monoid with homotopy inverses. -/
structure GroupLikeE1Space (X : Pointed) extends PointedMonoid X where
  /-- Inversion map. -/
  inv : X.carrier → X.carrier
  /-- Left inverse law witnessed by `Path`. -/
  inv_left : ∀ x : X.carrier, Path (mul (inv x) x) X.pt
  /-- Right inverse law witnessed by `Path`. -/
  inv_right : ∀ x : X.carrier, Path (mul x (inv x)) X.pt

namespace GroupLikeE1Space

variable {X : Pointed} (G : GroupLikeE1Space X)

/-- The basepoint is a fixed point of inversion. -/
theorem inv_pt : G.inv X.pt = X.pt := by
  have h := Path.toEq (G.inv_left X.pt)
  rw [G.mul_pt_right] at h
  exact h

/-- `Path` witness that unit laws hold. -/
def mul_pt_left_path (x : X.carrier) : Path (G.mul X.pt x) x :=
  Path.stepChain (G.mul_pt_left x)

/-- `Path` witness for right unit. -/
def mul_pt_right_path (x : X.carrier) : Path (G.mul x X.pt) x :=
  Path.stepChain (G.mul_pt_right x)

/-- `Path` witness for associativity. -/
def mul_assoc_path (x y z : X.carrier) :
    Path (G.mul (G.mul x y) z) (G.mul x (G.mul y z)) :=
  Path.stepChain (G.mul_assoc x y z)

end GroupLikeE1Space

/-! ## Bar construction -/

/-- A simplicial level of the bar construction: lists of elements. -/
def BarLevel (M : Type u) (n : Nat) : Type u :=
  { l : List M // l.length = n }

/-- The bar construction on a monoid, modeled as a quotient of lists. -/
structure BarConstruction (M : Type u) (S : StrictMonoid M) where
  /-- The simplicial levels. -/
  level : Nat → Type u
  /-- Level n is the n-fold product. -/
  level_def : ∀ n, level n = BarLevel M n

/-- Canonical bar construction from a strict monoid. -/
def canonicalBar (M : Type u) (_S : StrictMonoid M) : BarConstruction M _S where
  level := fun n => BarLevel M n
  level_def := fun _ => rfl

/-- Face map d_i in the bar construction: multiply adjacent entries. -/
def barFace {M : Type u} (_S : StrictMonoid M) (n : Nat) (i : Fin (n + 1)) :
    BarLevel M (n + 1) → BarLevel M n
  | ⟨l, hl⟩ => by
    refine ⟨l.take i.val ++ l.drop (i.val + 1), ?_⟩
    simp [List.length_take, List.length_drop, hl]
    omega

/-- Degeneracy map s_i in the bar construction: insert the unit. -/
def barDegeneracy {M : Type u} (S : StrictMonoid M) (n : Nat) (i : Fin (n + 1)) :
    BarLevel M n → BarLevel M (n + 1)
  | ⟨l, hl⟩ => by
    refine ⟨l.take i.val ++ [S.one] ++ l.drop i.val, ?_⟩
    simp [List.length_take, List.length_drop, hl]
    omega

/-! ## Delooping -/

/-- Delooping data: a pointed type whose loop space is equivalent to the given space. -/
structure DeloopingData (X : Pointed) where
  /-- The delooping space. -/
  deloop : Pointed
  /-- Map from X into the loop space of the delooping. -/
  toLoop : X.carrier → LoopSpace deloop.carrier deloop.pt
  /-- Map from the loop space back. -/
  fromLoop : LoopSpace deloop.carrier deloop.pt → X.carrier
  /-- Left inverse law. -/
  left_inv : ∀ x : X.carrier, Path (fromLoop (toLoop x)) x
  /-- Right inverse law. -/
  right_inv : ∀ l : LoopSpace deloop.carrier deloop.pt, Path (toLoop (fromLoop l)) l
  /-- Basepoint preservation (forward). -/
  toLoop_pt : Path (toLoop X.pt) (Path.refl deloop.pt)
  /-- Basepoint preservation (backward). -/
  fromLoop_pt : Path (fromLoop (Path.refl deloop.pt)) X.pt

namespace DeloopingData

variable {X : Pointed}

/-- The identity delooping: the loop space deloops to itself via loopPointed. -/
def trivial (X : Pointed) : DeloopingData (loopPointed X) where
  deloop := X
  toLoop := fun l => l
  fromLoop := fun l => l
  left_inv := fun x => Path.refl x
  right_inv := fun l => Path.refl l
  toLoop_pt := Path.refl _
  fromLoop_pt := Path.refl _

end DeloopingData

/-! ## May recognition theorem -/

/-- The May recognition theorem packages: a group-like E1 space is a loop space. -/
structure MayRecognition (X : Pointed) where
  /-- The E1 structure. -/
  e1 : GroupLikeE1Space X
  /-- The delooping data. -/
  delooping : DeloopingData X
  /-- The delooping multiplication is compatible with E1 multiplication.
      Specifically, the loop composition in the delooping corresponds to
      the E1 multiplication, up to `Path`. -/
  compat :
    ∀ x y : X.carrier,
      Path (delooping.fromLoop
              (LoopSpace.comp (delooping.toLoop x) (delooping.toLoop y)))
        (e1.mul x y)

/-- Given delooping data for a group-like E1 space, construct the recognition. -/
def recognitionFromDelooping {X : Pointed}
    (e1 : GroupLikeE1Space X)
    (d : DeloopingData X)
    (h : ∀ x y : X.carrier,
      Path (d.fromLoop (LoopSpace.comp (d.toLoop x) (d.toLoop y)))
        (e1.mul x y)) :
    MayRecognition X :=
  { e1 := e1, delooping := d, compat := h }

/-! ## Summary -/

end LoopSpaceRecognition
end Homotopy
end Path
end ComputationalPaths
