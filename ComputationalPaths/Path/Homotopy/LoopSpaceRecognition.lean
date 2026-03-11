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

/-- `Path` witness that inversion fixes the basepoint. -/
noncomputable def inv_pt_path : Path (G.inv X.pt) X.pt :=
  Path.stepChain (G.inv_pt)

/-- `Path` witness that unit laws hold. -/
noncomputable def mul_pt_left_path (x : X.carrier) : Path (G.mul X.pt x) x :=
  Path.stepChain (G.mul_pt_left x)

/-- `Path` witness for right unit. -/
noncomputable def mul_pt_right_path (x : X.carrier) : Path (G.mul x X.pt) x :=
  Path.stepChain (G.mul_pt_right x)

/-- `Path` witness for associativity. -/
noncomputable def mul_assoc_path (x y z : X.carrier) :
    Path (G.mul (G.mul x y) z) (G.mul x (G.mul y z)) :=
  Path.stepChain (G.mul_assoc x y z)

end GroupLikeE1Space

/-! ## Bar construction -/

/-- A simplicial level of the bar construction: lists of elements. -/
noncomputable def BarLevel (M : Type u) (n : Nat) : Type u :=
  { l : List M // l.length = n }

/-- The bar construction on a monoid, modeled as a quotient of lists. -/
structure BarConstruction (M : Type u) (S : StrictMonoid M) where
  /-- The simplicial levels. -/
  level : Nat → Type u
  /-- Level n is the n-fold product. -/
  level_def : ∀ n, level n = BarLevel M n

/-- Canonical bar construction from a strict monoid. -/
noncomputable def canonicalBar (M : Type u) (_S : StrictMonoid M) : BarConstruction M _S where
  level := fun n => BarLevel M n
  level_def := fun _ => rfl

/-- Face map d_i in the bar construction: multiply adjacent entries. -/
noncomputable def barFace {M : Type u} (_S : StrictMonoid M) (n : Nat) (i : Fin (n + 1)) :
    BarLevel M (n + 1) → BarLevel M n
  | ⟨l, hl⟩ => by
    refine ⟨l.take i.val ++ l.drop (i.val + 1), ?_⟩
    simp [List.length_take, List.length_drop, hl]
    omega

/-- Degeneracy map s_i in the bar construction: insert the unit. -/
noncomputable def barDegeneracy {M : Type u} (S : StrictMonoid M) (n : Nat) (i : Fin (n + 1)) :
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
noncomputable def trivial (X : Pointed) : DeloopingData (loopPointed X) where
  deloop := X
  toLoop := fun l => l
  fromLoop := fun l => l
  left_inv := fun x => Path.refl x
  right_inv := fun l => Path.refl l
  toLoop_pt := Path.refl _
  fromLoop_pt := Path.refl _

/-- Public left-inverse witness for the trivial delooping. -/
noncomputable def trivial_left_inv_path (X : Pointed) (l : LoopSpace X.carrier X.pt) :
    Path ((trivial X).fromLoop ((trivial X).toLoop l)) l :=
  (trivial X).left_inv l

/-- Public right-inverse witness for the trivial delooping. -/
noncomputable def trivial_right_inv_path (X : Pointed) (l : LoopSpace X.carrier X.pt) :
    Path ((trivial X).toLoop ((trivial X).fromLoop l)) l :=
  (trivial X).right_inv l

/-- Public basepoint-preservation witness for the forward map of the trivial delooping. -/
noncomputable def trivial_toLoop_pt_path (X : Pointed) :
    Path ((trivial X).toLoop (loopPointed X).pt) (Path.refl X.pt) :=
  (trivial X).toLoop_pt

/-- Public basepoint-preservation witness for the backward map of the trivial delooping. -/
noncomputable def trivial_fromLoop_pt_path (X : Pointed) :
    Path ((trivial X).fromLoop (Path.refl X.pt)) (loopPointed X).pt :=
  (trivial X).fromLoop_pt

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
noncomputable def recognitionFromDelooping {X : Pointed}
    (e1 : GroupLikeE1Space X)
    (d : DeloopingData X)
    (h : ∀ x y : X.carrier,
      Path (d.fromLoop (LoopSpace.comp (d.toLoop x) (d.toLoop y)))
        (e1.mul x y)) :
    MayRecognition X :=
  { e1 := e1, delooping := d, compat := h }

/-- The `e1` field of `recognitionFromDelooping` is judgmentally the supplied one. -/
theorem recognitionFromDelooping_e1_eq {X : Pointed}
    (e1 : GroupLikeE1Space X) (d : DeloopingData X)
    (h : ∀ x y : X.carrier,
      Path (d.fromLoop (LoopSpace.comp (d.toLoop x) (d.toLoop y)))
        (e1.mul x y)) :
    (recognitionFromDelooping e1 d h).e1 = e1 := rfl

/-- `Path` witness exposing the `e1` field of `recognitionFromDelooping`. -/
noncomputable def recognitionFromDelooping_e1_path {X : Pointed}
    (e1 : GroupLikeE1Space X) (d : DeloopingData X)
    (h : ∀ x y : X.carrier,
      Path (d.fromLoop (LoopSpace.comp (d.toLoop x) (d.toLoop y)))
        (e1.mul x y)) :
    Path (recognitionFromDelooping e1 d h).e1 e1 :=
  Path.stepChain (recognitionFromDelooping_e1_eq e1 d h)

/-- The `delooping` field of `recognitionFromDelooping` is judgmentally the supplied one. -/
theorem recognitionFromDelooping_delooping_eq {X : Pointed}
    (e1 : GroupLikeE1Space X) (d : DeloopingData X)
    (h : ∀ x y : X.carrier,
      Path (d.fromLoop (LoopSpace.comp (d.toLoop x) (d.toLoop y)))
        (e1.mul x y)) :
    (recognitionFromDelooping e1 d h).delooping = d := rfl

/-- `Path` witness exposing the `delooping` field of `recognitionFromDelooping`. -/
noncomputable def recognitionFromDelooping_delooping_path {X : Pointed}
    (e1 : GroupLikeE1Space X) (d : DeloopingData X)
    (h : ∀ x y : X.carrier,
      Path (d.fromLoop (LoopSpace.comp (d.toLoop x) (d.toLoop y)))
        (e1.mul x y)) :
    Path (recognitionFromDelooping e1 d h).delooping d :=
  Path.stepChain (recognitionFromDelooping_delooping_eq e1 d h)

namespace MayRecognition

variable {X : Pointed} (R : MayRecognition X)

/-- Public left-inverse witness from the delooping packaged by May recognition. -/
noncomputable def left_inv_path (x : X.carrier) :
    Path (R.delooping.fromLoop (R.delooping.toLoop x)) x :=
  R.delooping.left_inv x

/-- Public right-inverse witness from the delooping packaged by May recognition. -/
noncomputable def right_inv_path (l : LoopSpace R.delooping.deloop.carrier R.delooping.deloop.pt) :
    Path (R.delooping.toLoop (R.delooping.fromLoop l)) l :=
  R.delooping.right_inv l

/-- Public forward basepoint-preservation witness from the packaged delooping. -/
noncomputable def toLoop_pt_path :
    Path (R.delooping.toLoop X.pt) (Path.refl R.delooping.deloop.pt) :=
  R.delooping.toLoop_pt

/-- Public backward basepoint-preservation witness from the packaged delooping. -/
noncomputable def fromLoop_pt_path :
    Path (R.delooping.fromLoop (Path.refl R.delooping.deloop.pt)) X.pt :=
  R.delooping.fromLoop_pt

/-- Public compatibility witness between loop composition and E1 multiplication. -/
noncomputable def compat_path (x y : X.carrier) :
    Path (R.delooping.fromLoop (LoopSpace.comp (R.delooping.toLoop x) (R.delooping.toLoop y)))
      (R.e1.mul x y) :=
  R.compat x y

end MayRecognition

/-! ## Summary -/

end LoopSpaceRecognition
end Homotopy
end Path
end ComputationalPaths
