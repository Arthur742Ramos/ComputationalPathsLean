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
  -- Surface coherence is complex and omitted for now.

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

/-- The encoding respects path rewriting.
    This follows from the fact that `circleEncodePath` respects rewriting
    and that `congrArg` preserves the underlying equality. -/
theorem cylinderEncodePath_rweq {p q : CylinderLoopSpace}
    (h : RwEq p q) : cylinderEncodePath p = cylinderEncodePath q := by
  unfold cylinderEncodePath cylinderLoopToCircleLoop
  apply circleEncodePath_rweq
  apply rweq_trans_congr_right
  apply rweq_trans_congr_left
  have htoEq := rweq_toEq h
  -- (congrArg f p).toEq = congrArg f p.toEq by definition
  apply rweq_of_toEq_eq
  exact _root_.congrArg (_root_.congrArg cylinderToCircle) htoEq

@[simp] theorem cylinderEncodePath_refl :
    cylinderEncodePath (Path.refl cylinderBase0) = 0 := by
  unfold cylinderEncodePath cylinderLoopToCircleLoop
  -- The conjugated path has the same toEq as Path.refl circleBase
  have hrweq : RwEq
      (Path.trans (Path.symm (Path.ofEq cylinderToCircle_base0))
        (Path.trans (Path.congrArg cylinderToCircle (Path.refl cylinderBase0))
          (Path.ofEq cylinderToCircle_base0)))
      (Path.refl circleBase) := by
    apply rweq_of_toEq_eq
    simp
  rw [circleEncodePath_rweq hrweq]
  exact circleEncodePath_refl

@[simp] theorem cylinderEncodePath_loop0 :
    cylinderEncodePath cylinderLoop0 = 1 := by
  unfold cylinderEncodePath cylinderLoopToCircleLoop
  rw [cylinderToCircle_loop0]
  exact circleEncodePath_loop

/-- Encoding after appending loop0 adds 1. -/
@[simp] theorem cylinderEncodePath_trans_loop0 (p : CylinderLoopSpace) :
    cylinderEncodePath (Path.trans p cylinderLoop0) = cylinderEncodePath p + 1 := by
  unfold cylinderEncodePath cylinderLoopToCircleLoop
  -- Show the conjugated form of (trans p loop0) is RwEq to (trans (conjugated p) circleLoop)
  have hrweq : RwEq
      (Path.trans (Path.symm (Path.ofEq cylinderToCircle_base0))
        (Path.trans (Path.congrArg cylinderToCircle (Path.trans p cylinderLoop0))
          (Path.ofEq cylinderToCircle_base0)))
      (Path.trans
        (Path.trans (Path.symm (Path.ofEq cylinderToCircle_base0))
          (Path.trans (Path.congrArg cylinderToCircle p)
            (Path.ofEq cylinderToCircle_base0)))
        circleLoop) := by
    apply rweq_of_toEq_eq
    simp
  rw [circleEncodePath_rweq hrweq]
  rw [circleEncodePath_trans_loop]

/-- Encoding after appending symm loop0 subtracts 1. -/
@[simp] theorem cylinderEncodePath_trans_symm_loop0 (p : CylinderLoopSpace) :
    cylinderEncodePath (Path.trans p (Path.symm cylinderLoop0)) = cylinderEncodePath p - 1 := by
  unfold cylinderEncodePath cylinderLoopToCircleLoop
  have hrweq : RwEq
      (Path.trans (Path.symm (Path.ofEq cylinderToCircle_base0))
        (Path.trans (Path.congrArg cylinderToCircle (Path.trans p (Path.symm cylinderLoop0)))
          (Path.ofEq cylinderToCircle_base0)))
      (Path.trans
        (Path.trans (Path.symm (Path.ofEq cylinderToCircle_base0))
          (Path.trans (Path.congrArg cylinderToCircle p)
            (Path.ofEq cylinderToCircle_base0)))
        (Path.symm circleLoop)) := by
    apply rweq_of_toEq_eq
    simp
  rw [circleEncodePath_rweq hrweq]
  rw [circleEncodePath_trans_symm_loop]

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

/-- Encoding an integer loop power gives the integer. -/
@[simp] theorem cylinderEncodePath_loopPathZPow (z : Int) :
    cylinderEncodePath (cylinderLoopPathZPow z) = z := by
  cases z with
  | ofNat n =>
    simp only [cylinderLoopPathZPow]
    exact cylinderEncodePath_loopPathPow n
  | negSucc n =>
    simp only [cylinderLoopPathZPow]
    -- Path.symm (cylinderLoopPathPow (n + 1))
    -- Use induction on n, decrementing by 1 each time
    induction n with
    | zero =>
      simp only [cylinderLoopPathPow]
      exact cylinderEncodePath_symm_loop0
    | succ k ih =>
      -- symm (loop^(k+2)) = symm (loop^(k+1) ∘ loop) = symm loop ∘ symm (loop^(k+1))
      -- First, unfold cylinderLoopPathPow one step:
      -- cylinderLoopPathPow (k + 1 + 1) = trans (cylinderLoopPathPow (k + 1)) cylinderLoop0
      have hunfold : cylinderLoopPathPow (k + 1 + 1) =
          Path.trans (cylinderLoopPathPow (k + 1)) cylinderLoop0 := rfl
      rw [hunfold]
      have hstep : Path.symm (Path.trans (cylinderLoopPathPow (k + 1)) cylinderLoop0) =
                   Path.trans (Path.symm cylinderLoop0) (Path.symm (cylinderLoopPathPow (k + 1))) :=
        Path.symm_trans _ _
      rw [hstep]
      -- Now: encode (symm loop ∘ symm (loop^(k+1)))
      -- Reorder using commutativity up to RwEq, then use trans_symm_loop0
      have ih' : cylinderEncodePath (Path.symm (cylinderLoopPathPow (k + 1))) = Int.negSucc k := ih
      calc cylinderEncodePath (Path.trans (Path.symm cylinderLoop0) (Path.symm (cylinderLoopPathPow (k + 1))))
          = cylinderEncodePath (Path.trans (Path.symm (cylinderLoopPathPow (k + 1))) (Path.symm cylinderLoop0)) := by
            apply cylinderEncodePath_rweq
            apply rweq_of_toEq_eq
            simp
        _ = cylinderEncodePath (Path.symm (cylinderLoopPathPow (k + 1))) - 1 :=
            cylinderEncodePath_trans_symm_loop0 _
        _ = Int.negSucc k - 1 := by rw [ih']
        _ = Int.negSucc (k + 1) := by simp [Int.negSucc_sub_one]

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

/-- Decoding composed with encoding is the identity. -/
@[simp] theorem cylinderDecode_cylinderEncode (x : CylinderLoopQuot) :
    cylinderDecode (cylinderEncode x) = x := by
  -- Compare via propositional equality using `toEq`.
  apply PathRwQuot.eq_of_toEq_eq (A := Cylinder) (a := cylinderBase0) (b := cylinderBase0)
  -- Work with a path representative of `x`.
  refine Quot.inductionOn x (fun p => ?_)
  -- Reduce `decode (encode (ofLoop p))` to an equality on raw z-powers.
  have hDec :
      PathRwQuot.toEq (A := Cylinder)
        (cylinderDecode (cylinderEncode
          (LoopQuot.ofLoop (A := Cylinder) (a := cylinderBase0) p)))
        = (cylinderLoopPathZPow (cylinderEncodePath p)).toEq := by
    change PathRwQuot.toEq (A := Cylinder)
        (cylinderLoopZPow (cylinderEncodePath p))
        = (cylinderLoopPathZPow (cylinderEncodePath p)).toEq
    exact cylinderLoopZPow_toEq (z := cylinderEncodePath p)
  -- Replace the integer by the canonicalised version built from `p.toEq`.
  have hcanon :
      cylinderEncodePath (Path.ofEq p.toEq) = cylinderEncodePath p := by
    have hcanonRw : RwEq p (Path.ofEq p.toEq) := rweq_canon (p := p)
    exact (cylinderEncodePath_rweq (h := hcanonRw)).symm
  -- Finish by equality induction on `e := p.toEq`.
  have hEq := cylinderDecodeEq_cylinderEncodeEq (e := p.toEq)
  -- Rewrite the integer using `hcanon` and conclude.
  calc PathRwQuot.toEq (A := Cylinder)
        (cylinderDecode (cylinderEncode
          (LoopQuot.ofLoop (A := Cylinder) (a := cylinderBase0) p)))
      = (cylinderLoopPathZPow (cylinderEncodePath p)).toEq := hDec
    _ = (cylinderLoopPathZPow (cylinderEncodePath (Path.ofEq p.toEq))).toEq := by rw [hcanon]
    _ = p.toEq := hEq
    _ = PathRwQuot.toEq (A := Cylinder)
          (LoopQuot.ofLoop (A := Cylinder) (a := cylinderBase0) p) := by simp

/-- The fundamental group of the cylinder is isomorphic to ℤ. -/
def cylinderPiOneEquivInt : SimpleEquiv cylinderPiOne Int where
  toFun := cylinderEncode
  invFun := cylinderDecode
  left_inv := cylinderDecode_cylinderEncode
  right_inv := cylinderEncode_cylinderDecode

end -- noncomputable section

end Path
end ComputationalPaths
