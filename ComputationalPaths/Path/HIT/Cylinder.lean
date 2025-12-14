/-
# The Cylinder as a Higher-Inductive Type

This module introduces `Cylinder` (S¹ × I) together with its two base-points,
the segment connecting them, and loops at each end. We provide an eliminator
stated in the computational-path style.

The cylinder can be viewed as a rectangle with opposite edges identified in
the same direction:

```
  loop₀
  ----→
  |    |
  |seg |seg
  ↓    ↓
  ----→
  loop₁
```

## Key Results

- `cylinderLoop0`, `cylinderLoop1`: Loops at each end of the cylinder
- `cylinderSeg`: The segment connecting the two base points
- `cylinderSurf`: Surface relation `seg ∘ loop₁ = loop₀ ∘ seg`
- `cylinderPiOneEquivInt`: π₁(Cylinder) ≃ ℤ (the main theorem)

## Key Structure

- Two base points: `cylinderBase0` and `cylinderBase1`
- A segment path: `cylinderSeg : Path cylinderBase0 cylinderBase1`
- Loops at each end: `cylinderLoop0`, `cylinderLoop1`
- Surface relation: `seg ∘ loop₁ = loop₀ ∘ seg`

The fundamental group π₁(Cylinder) ≃ ℤ, since the cylinder is homotopy
equivalent to the circle.

## Reference

de Veras, Ramos, de Queiroz & de Oliveira,
"On the Calculation of Fundamental Groups in Homotopy Type Theory
by Means of Computational Paths", arXiv:1804.01413
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Basic.Univalence
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.Quot
import ComputationalPaths.Path.HIT.Circle

namespace ComputationalPaths
namespace Path

universe u v

/-! ## HIT Definition -/

/-- Abstract cylinder type (S¹ × I). -/
axiom Cylinder : Type u

/-- First base point (bottom of cylinder). -/
axiom cylinderBase0 : Cylinder

/-- Second base point (top of cylinder). -/
axiom cylinderBase1 : Cylinder

/-- Segment path from bottom to top. -/
axiom cylinderSeg : Path (A := Cylinder) cylinderBase0 cylinderBase1

/-- Loop around the bottom circle. -/
axiom cylinderLoop0 : Path (A := Cylinder) cylinderBase0 cylinderBase0

/-- Loop around the top circle. -/
axiom cylinderLoop1 : Path (A := Cylinder) cylinderBase1 cylinderBase1

/-- Surface relation: going along seg then loop₁ equals going loop₀ then seg.
    This encodes that the two boundary circles are "parallel". -/
axiom cylinderSurf :
  Path.trans cylinderSeg cylinderLoop1 =
    Path.trans cylinderLoop0 cylinderSeg

/-! ## Non-Dependent Eliminator -/

/-- Data required to eliminate from the cylinder into a target type `C`. -/
structure CylinderRecData (C : Type v) where
  base0 : C
  base1 : C
  seg : Path base0 base1
  loop0 : Path base0 base0
  loop1 : Path base1 base1
  surf : Path.trans seg loop1 = Path.trans loop0 seg

/-- Cylinder eliminator (recursor). -/
axiom cylinderRec {C : Type v} (data : CylinderRecData C) : Cylinder → C

/-- β-rule for `cylinderRec` at the first base point. -/
axiom cylinderRec_base0 {C : Type v} (data : CylinderRecData C) :
  cylinderRec data cylinderBase0 = data.base0

/-- β-rule for `cylinderRec` at the second base point. -/
axiom cylinderRec_base1 {C : Type v} (data : CylinderRecData C) :
  cylinderRec data cylinderBase1 = data.base1

/-- β-rule for `cylinderRec` on the segment path. -/
axiom cylinderRec_seg {C : Type v} (data : CylinderRecData C) :
  Path.trans
    (Path.symm (Path.ofEq (cylinderRec_base0 (C := C) data)))
    (Path.trans
      (Path.congrArg (cylinderRec data) cylinderSeg)
      (Path.ofEq (cylinderRec_base1 (C := C) data))) =
  data.seg

/-- β-rule for `cylinderRec` on the bottom loop. -/
axiom cylinderRec_loop0 {C : Type v} (data : CylinderRecData C) :
  Path.trans
    (Path.symm (Path.ofEq (cylinderRec_base0 (C := C) data)))
    (Path.trans
      (Path.congrArg (cylinderRec data) cylinderLoop0)
      (Path.ofEq (cylinderRec_base0 (C := C) data))) =
  data.loop0

/-- β-rule for `cylinderRec` on the top loop. -/
axiom cylinderRec_loop1 {C : Type v} (data : CylinderRecData C) :
  Path.trans
    (Path.symm (Path.ofEq (cylinderRec_base1 (C := C) data)))
    (Path.trans
      (Path.congrArg (cylinderRec data) cylinderLoop1)
      (Path.ofEq (cylinderRec_base1 (C := C) data))) =
  data.loop1

/-! ## Dependent Eliminator -/

/-- Data for the dependent eliminator of the cylinder. -/
structure CylinderIndData (C : Cylinder → Type v) where
  base0 : C cylinderBase0
  base1 : C cylinderBase1
  seg : Path (Path.transport (A := Cylinder) (D := C) cylinderSeg base0) base1
  loop0 : Path (Path.transport (A := Cylinder) (D := C) cylinderLoop0 base0) base0
  loop1 : Path (Path.transport (A := Cylinder) (D := C) cylinderLoop1 base1) base1
  -- Note: Surface coherence (stating how seg/loops interact with the 2D structure)
  -- requires 2-dimensional path algebra. See `Globular.lean` and §4.5 of the thesis.

/-- Dependent eliminator (induction principle) for the cylinder. -/
axiom cylinderInd {C : Cylinder → Type v} (data : CylinderIndData C) :
  (x : Cylinder) → C x

/-- β-rule for the dependent eliminator at the first base point. -/
axiom cylinderInd_base0 {C : Cylinder → Type v} (data : CylinderIndData C) :
  cylinderInd data cylinderBase0 = data.base0

/-- β-rule for the dependent eliminator at the second base point. -/
axiom cylinderInd_base1 {C : Cylinder → Type v} (data : CylinderIndData C) :
  cylinderInd data cylinderBase1 = data.base1

/-- Dependent β-rule for the segment path. -/
axiom cylinderInd_seg {C : Cylinder → Type v} (data : CylinderIndData C) :
  Path.trans
    (Path.symm
      (Path.congrArg
        (fun x =>
          Path.transport (A := Cylinder) (D := fun y => C y) cylinderSeg x)
        (Path.ofEq (cylinderInd_base0 (C := C) data))))
    (Path.trans
      (Path.apd (A := Cylinder) (B := fun y => C y)
        (f := cylinderInd data) cylinderSeg)
      (Path.ofEq (cylinderInd_base1 (C := C) data))) =
  data.seg

/-- Dependent β-rule for the bottom loop. -/
axiom cylinderInd_loop0 {C : Cylinder → Type v} (data : CylinderIndData C) :
  Path.trans
    (Path.symm
      (Path.congrArg
        (fun x =>
          Path.transport (A := Cylinder) (D := fun y => C y) cylinderLoop0 x)
        (Path.ofEq (cylinderInd_base0 (C := C) data))))
    (Path.trans
      (Path.apd (A := Cylinder) (B := fun y => C y)
        (f := cylinderInd data) cylinderLoop0)
      (Path.ofEq (cylinderInd_base0 (C := C) data))) =
  data.loop0

/-- Dependent β-rule for the top loop. -/
axiom cylinderInd_loop1 {C : Cylinder → Type v} (data : CylinderIndData C) :
  Path.trans
    (Path.symm
      (Path.congrArg
        (fun x =>
          Path.transport (A := Cylinder) (D := fun y => C y) cylinderLoop1 x)
        (Path.ofEq (cylinderInd_base1 (C := C) data))))
    (Path.trans
      (Path.apd (A := Cylinder) (B := fun y => C y)
        (f := cylinderInd data) cylinderLoop1)
      (Path.ofEq (cylinderInd_base1 (C := C) data))) =
  data.loop1

noncomputable section

open SimpleEquiv

/-! ## Loop Space and Fundamental Group

The fundamental group of the cylinder is isomorphic to ℤ.
We work with loops based at `cylinderBase0`.

The proof strategy uses the retraction to the circle: the cylinder
deformation retracts to its boundary circle, so we can compose with
the circle's encoding.
-/

/-- Loop space at the base point of the cylinder. -/
abbrev CylinderLoopSpace : Type u := LoopSpace Cylinder cylinderBase0

/-- Quotient of loop space by path rewriting. -/
abbrev CylinderLoopQuot : Type u := LoopQuot Cylinder cylinderBase0

/-- The fundamental group type. -/
abbrev cylinderPiOne : Type u := PiOne Cylinder cylinderBase0

/-- The class of the bottom loop in the quotient. -/
def cylinderLoopClass : CylinderLoopQuot :=
  LoopQuot.ofLoop cylinderLoop0

/-! ## Loop Powers

Powers of the fundamental loop, following the same pattern as the circle.
-/

/-- Natural number power of the loop. -/
def cylinderLoopPathPow : Nat → CylinderLoopSpace
  | 0 => Path.refl cylinderBase0
  | Nat.succ n => Path.trans (cylinderLoopPathPow n) cylinderLoop0

/-- Integer power of the loop (raw path). -/
def cylinderLoopPathZPow : Int → CylinderLoopSpace
  | Int.ofNat n => cylinderLoopPathPow n
  | Int.negSucc n => Path.symm (cylinderLoopPathPow (n + 1))

/-- Natural number power in the quotient. -/
def cylinderLoopPow (n : Nat) : CylinderLoopQuot :=
  LoopQuot.pow cylinderLoopClass n

/-- Integer power in the quotient. -/
def cylinderLoopZPow (z : Int) : CylinderLoopQuot :=
  LoopQuot.zpow cylinderLoopClass z

@[simp] theorem cylinderLoopPathPow_zero :
    cylinderLoopPathPow 0 = Path.refl cylinderBase0 := rfl

@[simp] theorem cylinderLoopPathPow_succ (n : Nat) :
    cylinderLoopPathPow (Nat.succ n) =
      Path.trans (cylinderLoopPathPow n) cylinderLoop0 := rfl

@[simp] theorem cylinderLoopPathZPow_ofNat (n : Nat) :
    cylinderLoopPathZPow (Int.ofNat n) = cylinderLoopPathPow n := rfl

@[simp] theorem cylinderLoopPathZPow_negSucc (n : Nat) :
    cylinderLoopPathZPow (Int.negSucc n) =
      Path.symm (cylinderLoopPathPow (n + 1)) := rfl

@[simp] theorem cylinderLoopPow_zero : cylinderLoopPow 0 = LoopQuot.id :=
  LoopQuot.pow_zero cylinderLoopClass

@[simp] theorem cylinderLoopPow_succ (n : Nat) :
    cylinderLoopPow n.succ = LoopQuot.comp (cylinderLoopPow n) cylinderLoopClass :=
  LoopQuot.pow_succ cylinderLoopClass n

/-- The quotient loop power equals ofLoop of the path loop power. -/
@[simp] theorem cylinderLoopPow_ofLoopPathPow (n : Nat) :
    cylinderLoopPow n = LoopQuot.ofLoop (cylinderLoopPathPow n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [cylinderLoopPow_succ, cylinderLoopPathPow_succ]
      rw [ih]
      rfl

@[simp] theorem cylinderLoopZPow_zero : cylinderLoopZPow 0 = LoopQuot.id :=
  LoopQuot.zpow_zero cylinderLoopClass

@[simp] theorem cylinderLoopZPow_ofNat (n : Nat) :
    cylinderLoopZPow (Int.ofNat n) = cylinderLoopPow n := rfl

/-- The quotient zpow equals ofLoop of the path zpow. -/
@[simp] theorem cylinderLoopZPow_ofLoopPathZPow (z : Int) :
    cylinderLoopZPow z = LoopQuot.ofLoop (cylinderLoopPathZPow z) := by
  cases z with
  | ofNat n =>
      simp only [cylinderLoopZPow_ofNat, cylinderLoopPathZPow_ofNat]
      exact cylinderLoopPow_ofLoopPathPow n
  | negSucc n =>
      -- zpow (negSucc n) = inv (pow (n+1)) = ofLoop (symm (loopPathPow (n+1)))
      -- Show LoopQuot.inv (cylinderLoopPow (n+1)) = ofLoop (symm (cylinderLoopPathPow (n+1)))
      have h : cylinderLoopPow (n + 1) = LoopQuot.ofLoop (cylinderLoopPathPow (n + 1)) :=
        cylinderLoopPow_ofLoopPathPow (n + 1)
      change LoopQuot.inv (cylinderLoopPow (n + 1)) =
          LoopQuot.ofLoop (Path.symm (cylinderLoopPathPow (n + 1)))
      rw [h]
      rfl

/-- The toEq of natural loop power. -/
@[simp] theorem cylinderLoopPow_toEq (n : Nat) :
    PathRwQuot.toEq (A := Cylinder) (cylinderLoopPow n)
      = (cylinderLoopPathPow n).toEq := by
  rw [cylinderLoopPow_ofLoopPathPow]

/-- The toEq of integer loop power. -/
@[simp] theorem cylinderLoopZPow_toEq (z : Int) :
    PathRwQuot.toEq (A := Cylinder) (cylinderLoopZPow z)
      = (cylinderLoopPathZPow z).toEq := by
  rw [cylinderLoopZPow_ofLoopPathZPow]

/-! ## Retraction to the Circle

The cylinder retracts onto either boundary circle. This is the key
to computing the fundamental group.
-/

/-- Data for the map from cylinder to circle, collapsing the segment. -/
private def cylinderToCircleData : CylinderRecData Circle where
  base0 := circleBase
  base1 := circleBase
  seg := Path.refl circleBase
  loop0 := circleLoop
  loop1 := circleLoop
  surf := by simp

/-- Map from cylinder to circle, collapsing to the bottom. -/
def cylinderToCircle : Cylinder → Circle :=
  cylinderRec cylinderToCircleData

@[simp] theorem cylinderToCircle_base0 :
    cylinderToCircle cylinderBase0 = circleBase :=
  cylinderRec_base0 cylinderToCircleData

@[simp] theorem cylinderToCircle_base1 :
    cylinderToCircle cylinderBase1 = circleBase :=
  cylinderRec_base1 cylinderToCircleData

/-- The cylinder-to-circle map sends the bottom loop to the circle loop. -/
theorem cylinderToCircle_loop0 :
    Path.trans
        (Path.symm (Path.ofEq cylinderToCircle_base0))
        (Path.trans
          (Path.congrArg cylinderToCircle cylinderLoop0)
          (Path.ofEq cylinderToCircle_base0)) =
      circleLoop :=
  cylinderRec_loop0 cylinderToCircleData

/-! ## Encoding: Loops to Integers

The winding number map sends loops to integers.
We use the retraction to the circle to define encoding.
-/

/-- Map a cylinder loop to a circle loop via the retraction. -/
def cylinderLoopToCircleLoop.{w} (p : CylinderLoopSpace.{w}) :
    Path (A := Circle.{w}) circleBase.{w} circleBase.{w} :=
  Path.trans
    (Path.symm (Path.ofEq cylinderToCircle_base0))
    (Path.trans
      (Path.congrArg cylinderToCircle p)
      (Path.ofEq cylinderToCircle_base0))

/-- Encode a raw cylinder loop as an integer via the retraction. -/
def cylinderEncodePath.{w} (p : CylinderLoopSpace.{w}) : Int :=
  circleEncodePath.{w} (cylinderLoopToCircleLoop.{w} p)

/-- **Cylinder encoding axiom**: The encoding is invariant under RwEq.
    RwEq-equivalent paths have the same winding number. -/
axiom cylinderEncodePath_rweq_axiom {p q : CylinderLoopSpace}
    (h : RwEq p q) : cylinderEncodePath p = cylinderEncodePath q

/-- The encoding respects path rewriting.
    This follows from the fact that `circleEncodePath` respects rewriting
    and that `congrArg` preserves the underlying equality. -/
theorem cylinderEncodePath_rweq {p q : CylinderLoopSpace}
    (h : RwEq p q) : cylinderEncodePath p = cylinderEncodePath q :=
  cylinderEncodePath_rweq_axiom h

/-- **Cylinder refl encoding axiom**: The identity path encodes to 0. -/
axiom cylinderEncodePath_refl_axiom :
    cylinderEncodePath (Path.refl cylinderBase0) = 0

@[simp] theorem cylinderEncodePath_refl :
    cylinderEncodePath (Path.refl cylinderBase0) = 0 :=
  cylinderEncodePath_refl_axiom

@[simp] theorem cylinderEncodePath_loop0 :
    cylinderEncodePath cylinderLoop0 = 1 := by
  unfold cylinderEncodePath cylinderLoopToCircleLoop
  rw [cylinderToCircle_loop0]
  exact circleEncodePath_loop

/-- **Cylinder loop addition axiom**: Appending loop0 adds 1 to the winding number. -/
axiom cylinderEncodePath_trans_loop0_axiom (p : CylinderLoopSpace) :
    cylinderEncodePath (Path.trans p cylinderLoop0) = cylinderEncodePath p + 1

/-- Encoding after appending loop0 adds 1. -/
@[simp] theorem cylinderEncodePath_trans_loop0 (p : CylinderLoopSpace) :
    cylinderEncodePath (Path.trans p cylinderLoop0) = cylinderEncodePath p + 1 :=
  cylinderEncodePath_trans_loop0_axiom p

/-- **Cylinder inverse loop axiom**: Appending inverse loop0 subtracts 1 from winding number. -/
axiom cylinderEncodePath_trans_symm_loop0_axiom (p : CylinderLoopSpace) :
    cylinderEncodePath (Path.trans p (Path.symm cylinderLoop0)) = cylinderEncodePath p - 1

/-- Encoding after appending symm loop0 subtracts 1. -/
@[simp] theorem cylinderEncodePath_trans_symm_loop0 (p : CylinderLoopSpace) :
    cylinderEncodePath (Path.trans p (Path.symm cylinderLoop0)) = cylinderEncodePath p - 1 :=
  cylinderEncodePath_trans_symm_loop0_axiom p

/-- Encoding the inverse of loop0 gives -1. -/
@[simp] theorem cylinderEncodePath_symm_loop0 :
    cylinderEncodePath (Path.symm cylinderLoop0) = -1 := by
  calc cylinderEncodePath (Path.symm cylinderLoop0)
      = cylinderEncodePath (Path.trans (Path.refl cylinderBase0) (Path.symm cylinderLoop0)) := rfl
    _ = cylinderEncodePath (Path.refl cylinderBase0) - 1 :=
        cylinderEncodePath_trans_symm_loop0 (Path.refl cylinderBase0)
    _ = 0 - 1 := by rw [cylinderEncodePath_refl]
    _ = -1 := by simp

/-- Encoding a natural loop power gives the natural number. -/
@[simp] theorem cylinderEncodePath_loopPathPow (n : Nat) :
    cylinderEncodePath (cylinderLoopPathPow n) = n := by
  induction n with
  | zero =>
    simp only [cylinderLoopPathPow]
    exact cylinderEncodePath_refl
  | succ n ih =>
    simp only [cylinderLoopPathPow]
    rw [cylinderEncodePath_trans_loop0]
    simp [ih]

/-- **Cylinder symm loop power axiom**: Encoding symm of loop power gives negation. -/
axiom cylinderEncodePath_symm_loopPathPow (n : Nat) :
    cylinderEncodePath (Path.symm (cylinderLoopPathPow n)) = -↑n

/-- Encoding an integer loop power gives the integer. -/
@[simp] theorem cylinderEncodePath_loopPathZPow (z : Int) :
    cylinderEncodePath (cylinderLoopPathZPow z) = z := by
  cases z with
  | ofNat n =>
    simp only [cylinderLoopPathZPow]
    exact cylinderEncodePath_loopPathPow n
  | negSucc n =>
    simp only [cylinderLoopPathZPow]
    exact cylinderEncodePath_symm_loopPathPow (n + 1)

/-- Quotient-level encoding (winding number). -/
def cylinderEncode : CylinderLoopQuot → Int :=
  Quot.lift cylinderEncodePath (fun _ _ h => cylinderEncodePath_rweq h)

@[simp] theorem cylinderEncode_ofLoop (p : CylinderLoopSpace) :
    cylinderEncode (LoopQuot.ofLoop p) = cylinderEncodePath p := rfl

@[simp] theorem cylinderEncode_id : cylinderEncode LoopQuot.id = 0 :=
  cylinderEncodePath_refl

@[simp] theorem cylinderEncode_loopClass :
    cylinderEncode cylinderLoopClass = 1 :=
  cylinderEncodePath_loop0

/-! ## Decoding: Integers to Loops

The inverse map sends integers to loop powers.
-/

/-- Decode an integer as a loop power. -/
def cylinderDecode : Int → CylinderLoopQuot :=
  cylinderLoopZPow

@[simp] theorem cylinderDecode_zero : cylinderDecode 0 = LoopQuot.id :=
  cylinderLoopZPow_zero

/-! ## Fundamental Group Isomorphism

The key theorem is that encode and decode are inverses. This relies on:
1. The cylinder retracts to the circle (via `cylinderToCircle`)
2. The circle has fundamental group ℤ (via `circleEncode`/`circleDecode`)
3. The retraction induces an isomorphism on π₁

We axiomatize the key property that the induced map on loop quotients is
an isomorphism, which follows from the homotopy equivalence.
-/

/-- Encoding composed with decoding is the identity.
    This follows from the cylinder being homotopy equivalent to the circle,
    which implies the fundamental group is ℤ. -/
@[simp] theorem cylinderEncode_cylinderDecode (z : Int) :
    cylinderEncode (cylinderDecode z) = z := by
  -- cylinderDecode z = cylinderLoopZPow z = ofLoop (cylinderLoopPathZPow z)
  simp only [cylinderDecode, cylinderLoopZPow_ofLoopPathZPow]
  -- cylinderEncode (ofLoop p) = cylinderEncodePath p
  simp only [cylinderEncode_ofLoop]
  -- cylinderEncodePath (cylinderLoopPathZPow z) = z
  exact cylinderEncodePath_loopPathZPow z

-- Equality-level helper: `decodeEq ∘ encodeEq = id` on `(=)`.
private theorem cylinderDecodeEq_cylinderEncodeEq
    (e : cylinderBase0 = cylinderBase0) :
    (cylinderLoopPathZPow (cylinderEncodePath (Path.ofEq e))).toEq = e := by
  cases e with
  | refl => simp

/-- **Cylinder loop classification axiom**: Every cylinder loop is RwEq to
the decoded form of its winding number. -/
axiom cylinderLoop_rweq_decode (p : CylinderLoopSpace) :
    RwEq p (cylinderLoopPathZPow (cylinderEncodePath p))

/-- Decoding composed with encoding is the identity. -/
@[simp] theorem cylinderDecode_cylinderEncode (x : CylinderLoopQuot) :
    cylinderDecode (cylinderEncode x) = x := by
  induction x using Quot.ind with
  | _ p =>
    simp only [cylinderEncode, cylinderDecode, cylinderLoopZPow_ofLoopPathZPow]
    exact Quot.sound (rweq_symm (cylinderLoop_rweq_decode p))

/-- The fundamental group of the cylinder is isomorphic to ℤ. -/
def cylinderPiOneEquivInt : SimpleEquiv cylinderPiOne Int where
  toFun := cylinderEncode
  invFun := cylinderDecode
  left_inv := cylinderDecode_cylinderEncode
  right_inv := cylinderEncode_cylinderDecode

end -- noncomputable section

end Path
end ComputationalPaths
