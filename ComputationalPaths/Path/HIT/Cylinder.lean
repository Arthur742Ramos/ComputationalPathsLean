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
def cylinderEncodePath.{w} [HasCircleLoopDecode.{w}] (p : CylinderLoopSpace.{w}) : Int :=
  circleEncodePath.{w} (cylinderLoopToCircleLoop.{w} p)

/-- The encoding respects path rewriting.

This is inherited from `circleEncodePath_rweq` because `cylinderEncodePath` is defined
via the retraction `cylinderLoopToCircleLoop`. -/
theorem cylinderEncodePath_rweq [HasCircleLoopDecode.{u}] {p q : CylinderLoopSpace}
    (h : RwEq p q) : cylinderEncodePath.{u} p = cylinderEncodePath.{u} q := by
  unfold cylinderEncodePath
  -- Reduce to rewrite-invariance of the circle encoding.
  apply circleEncodePath_rweq
  unfold cylinderLoopToCircleLoop
  -- `congrArg` preserves `RwEq`, and `trans` is congruent in both arguments.
  have hCongr :
      RwEq (Path.congrArg cylinderToCircle p) (Path.congrArg cylinderToCircle q) :=
    rweq_congrArg_of_rweq cylinderToCircle h
  have hInner :
      RwEq
        (Path.trans (Path.congrArg cylinderToCircle p) (Path.ofEq cylinderToCircle_base0))
        (Path.trans (Path.congrArg cylinderToCircle q) (Path.ofEq cylinderToCircle_base0)) :=
    rweq_trans_congr_left (Path.ofEq cylinderToCircle_base0) hCongr
  exact
    rweq_trans_congr_right (Path.symm (Path.ofEq cylinderToCircle_base0)) hInner

@[simp] theorem cylinderEncodePath_refl [HasCircleLoopDecode.{u}] :
    cylinderEncodePath.{u} (Path.refl cylinderBase0) = 0 := by
  unfold cylinderEncodePath cylinderLoopToCircleLoop
  -- Fix the universe instantiation of the basepoint equation so no metavariables
  -- remain in the compiled proof term.
  let baseEq := cylinderToCircle_base0.{u, u}
  -- The conjugation path `symm(ofEq e) · ofEq e` rewrites to `refl`.
  have hCancel :
      RwEq
        (Path.trans (Path.symm (Path.ofEq baseEq)) (Path.ofEq baseEq))
        (Path.refl (circleBase.{u})) := by
    simpa using rweq_cmpA_inv_left (p := Path.ofEq baseEq)
  calc
    circleEncodePath
        (Path.trans (Path.symm (Path.ofEq baseEq)) (Path.ofEq baseEq))
        = circleEncodePath (Path.refl (circleBase.{u})) := circleEncodePath_rweq hCancel
    _ = 0 := circleEncodePath_refl

@[simp] theorem cylinderEncodePath_loop0 [HasCircleLoopDecode.{u}] :
    cylinderEncodePath.{u} cylinderLoop0 = 1 := by
  unfold cylinderEncodePath cylinderLoopToCircleLoop
  rw [cylinderToCircle_loop0]
  exact circleEncodePath_loop

/-! ### Algebraic laws for `cylinderLoopToCircleLoop` and `cylinderEncodePath` -/

/-- `cylinderLoopToCircleLoop` preserves concatenation up to `RwEq`.

This is the standard “conjugation is a homomorphism” calculation:
the middle factor `ofEq e · symm(ofEq e)` cancels by `rweq_cmpA_inv_right`. -/
private theorem cylinderLoopToCircleLoop_trans_rweq (p q : CylinderLoopSpace) :
    RwEq (cylinderLoopToCircleLoop (Path.trans p q))
      (Path.trans (cylinderLoopToCircleLoop p) (cylinderLoopToCircleLoop q)) := by
  unfold cylinderLoopToCircleLoop
  -- Push `congrArg` through concatenation in the middle.
  rw [Path.congrArg_trans (f := cylinderToCircle) (p := p) (q := q)]
  -- Now it is a pure `trans`/associativity/cancellation argument.
  have h1 :=
    rweq_tt (Path.symm (Path.ofEq cylinderToCircle_base0))
      (Path.trans (Path.congrArg cylinderToCircle p) (Path.ofEq cylinderToCircle_base0))
      (Path.trans (Path.symm (Path.ofEq cylinderToCircle_base0))
        (Path.trans (Path.congrArg cylinderToCircle q) (Path.ofEq cylinderToCircle_base0)))
  have h2 :=
    rweq_trans_congr_right (Path.symm (Path.ofEq cylinderToCircle_base0)) <|
      rweq_tt (Path.congrArg cylinderToCircle p) (Path.ofEq cylinderToCircle_base0)
        (Path.trans (Path.symm (Path.ofEq cylinderToCircle_base0))
          (Path.trans (Path.congrArg cylinderToCircle q) (Path.ofEq cylinderToCircle_base0)))
  have h3 :=
    rweq_trans_congr_right (Path.symm (Path.ofEq cylinderToCircle_base0)) <|
      rweq_trans_congr_right (Path.congrArg cylinderToCircle p) <|
        (rweq_tt (Path.ofEq cylinderToCircle_base0)
          (Path.symm (Path.ofEq cylinderToCircle_base0))
          (Path.trans (Path.congrArg cylinderToCircle q) (Path.ofEq cylinderToCircle_base0))).symm
  have hCancel :=
    rweq_cmpA_inv_right (p := Path.ofEq cylinderToCircle_base0)
  have h4 :=
    rweq_trans_congr_right (Path.symm (Path.ofEq cylinderToCircle_base0)) <|
      rweq_trans_congr_right (Path.congrArg cylinderToCircle p) <|
        RwEq.trans
          (rweq_trans_congr_left
            (Path.trans (Path.congrArg cylinderToCircle q) (Path.ofEq cylinderToCircle_base0))
            hCancel)
          (rweq_cmpA_refl_left
            (Path.trans (Path.congrArg cylinderToCircle q) (Path.ofEq cylinderToCircle_base0)))
  have h5 :=
    rweq_trans_congr_right (Path.symm (Path.ofEq cylinderToCircle_base0)) <|
      (rweq_tt (Path.congrArg cylinderToCircle p)
        (Path.congrArg cylinderToCircle q)
        (Path.ofEq cylinderToCircle_base0)).symm
  -- The chain as written produces `RwEq` in the reverse direction; flip it at the end.
  exact rweq_symm (RwEq.trans (RwEq.trans (RwEq.trans (RwEq.trans h1 h2) h3) h4) h5)

section

variable [HasCircleLoopDecode.{u}]

/-- `cylinderEncodePath` is additive over concatenation (raw loop level). -/
theorem cylinderEncodePath_trans (p q : CylinderLoopSpace) :
    cylinderEncodePath.{u} (Path.trans p q) = cylinderEncodePath.{u} p + cylinderEncodePath.{u} q := by
  unfold cylinderEncodePath
  have hMul := cylinderLoopToCircleLoop_trans_rweq (p := p) (q := q)
  calc
    circleEncodePath (cylinderLoopToCircleLoop (Path.trans p q))
        = circleEncodePath (Path.trans (cylinderLoopToCircleLoop p) (cylinderLoopToCircleLoop q)) :=
      circleEncodePath_rweq hMul
    _ = circleEncodePath (cylinderLoopToCircleLoop p) + circleEncodePath (cylinderLoopToCircleLoop q) := by
      simpa using
        circleEncodePath_trans
          (p := cylinderLoopToCircleLoop p)
          (q := cylinderLoopToCircleLoop q)

/-- Encoding respects inversion: `encode (p⁻¹) = - encode p`. -/
theorem cylinderEncodePath_symm (p : CylinderLoopSpace) :
    cylinderEncodePath.{u} (Path.symm p) = - cylinderEncodePath.{u} p := by
  -- `p · p⁻¹ ≈ refl` in `RwEq`, hence encodes to 0.
  have hCancel : RwEq (Path.trans p (Path.symm p)) (Path.refl cylinderBase0) :=
    rweq_cmpA_inv_right (p := p)
  have h0 :
      cylinderEncodePath.{u} (Path.trans p (Path.symm p)) = 0 := by
    have hEq := cylinderEncodePath_rweq (h := hCancel)
    exact hEq.trans cylinderEncodePath_refl
  have hTrans := cylinderEncodePath_trans (p := p) (q := Path.symm p)
  have hSum : cylinderEncodePath.{u} p + cylinderEncodePath.{u} (Path.symm p) = 0 :=
    (Eq.symm hTrans).trans h0
  -- Solve the resulting linear integer equation.
  omega

/-- Encoding after appending loop0 adds 1. -/
@[simp] theorem cylinderEncodePath_trans_loop0 (p : CylinderLoopSpace) :
    cylinderEncodePath.{u} (Path.trans p cylinderLoop0) = cylinderEncodePath.{u} p + 1 := by
  simpa [cylinderEncodePath_loop0] using cylinderEncodePath_trans (p := p) (q := cylinderLoop0)

/-- Encoding after appending symm loop0 subtracts 1. -/
@[simp] theorem cylinderEncodePath_trans_symm_loop0 (p : CylinderLoopSpace) :
    cylinderEncodePath.{u} (Path.trans p (Path.symm cylinderLoop0)) = cylinderEncodePath.{u} p - 1 := by
  have hLoopInv : cylinderEncodePath.{u} (Path.symm cylinderLoop0) = -1 := by
    simpa [cylinderEncodePath_loop0] using cylinderEncodePath_symm (p := cylinderLoop0)
  -- `encode (p · loop⁻¹) = encode p + encode(loop⁻¹) = encode p - 1`.
  rw [Int.sub_eq_add_neg]
  refine (cylinderEncodePath_trans (p := p) (q := Path.symm cylinderLoop0)).trans ?_
  rw [hLoopInv]

/-- Encoding the inverse of loop0 gives -1. -/
@[simp] theorem cylinderEncodePath_symm_loop0 :
    cylinderEncodePath.{u} (Path.symm cylinderLoop0) = -1 := by
  simpa [cylinderEncodePath_loop0] using cylinderEncodePath_symm (p := cylinderLoop0)

/-- Encoding a natural loop power gives the natural number. -/
@[simp] theorem cylinderEncodePath_loopPathPow (n : Nat) :
    cylinderEncodePath.{u} (cylinderLoopPathPow n) = n := by
  induction n with
  | zero =>
    simp only [cylinderLoopPathPow]
    exact cylinderEncodePath_refl
  | succ n ih =>
    simp only [cylinderLoopPathPow]
    rw [cylinderEncodePath_trans_loop0]
    simp [ih]

/-- Encoding of symm (loop^n) gives -n. -/
theorem cylinderEncodePath_symm_loopPathPow (n : Nat) :
    cylinderEncodePath.{u} (Path.symm (cylinderLoopPathPow n)) = -↑n := by
  simpa [cylinderEncodePath_loopPathPow] using
    cylinderEncodePath_symm (p := cylinderLoopPathPow n)

/-- Encoding an integer loop power gives the integer. -/
@[simp] theorem cylinderEncodePath_loopPathZPow (z : Int) :
    cylinderEncodePath.{u} (cylinderLoopPathZPow z) = z := by
  cases z with
  | ofNat n =>
    simp only [cylinderLoopPathZPow]
    exact cylinderEncodePath_loopPathPow n
  | negSucc n =>
    simp only [cylinderLoopPathZPow]
    exact cylinderEncodePath_symm_loopPathPow (n + 1)

end

/-- Quotient-level encoding (winding number). -/
def cylinderEncode [HasCircleLoopDecode.{u}] : CylinderLoopQuot → Int :=
  Quot.lift cylinderEncodePath (fun _ _ h => cylinderEncodePath_rweq h)

@[simp] theorem cylinderEncode_ofLoop [HasCircleLoopDecode.{u}] (p : CylinderLoopSpace) :
    cylinderEncode (LoopQuot.ofLoop p) = cylinderEncodePath p := rfl

@[simp] theorem cylinderEncode_id [HasCircleLoopDecode.{u}] : cylinderEncode LoopQuot.id = 0 :=
  cylinderEncodePath_refl

@[simp] theorem cylinderEncode_loopClass [HasCircleLoopDecode.{u}] :
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
@[simp] theorem cylinderEncode_cylinderDecode [HasCircleLoopDecode.{u}] (z : Int) :
    cylinderEncode.{u} (cylinderDecode.{u} z) = z := by
  -- cylinderDecode z = cylinderLoopZPow z = ofLoop (cylinderLoopPathZPow z)
  simp only [cylinderDecode, cylinderLoopZPow_ofLoopPathZPow]
  -- cylinderEncode (ofLoop p) = cylinderEncodePath p
  simp only [cylinderEncode_ofLoop]
  -- cylinderEncodePath (cylinderLoopPathZPow z) = z
  exact cylinderEncodePath_loopPathZPow z

-- Equality-level helper: `decodeEq ∘ encodeEq = id` on `(=)`.
private theorem cylinderDecodeEq_cylinderEncodeEq [HasCircleLoopDecode.{u}]
    (e : cylinderBase0 = cylinderBase0) :
    (cylinderLoopPathZPow (cylinderEncodePath (Path.ofEq e))).toEq = e := by
  cases e with
  | refl => simp

/-- **Cylinder loop classification axiom**: Every cylinder loop is RwEq to
the decoded form of its winding number. -/
class HasCylinderLoopDecode [HasCircleLoopDecode.{u}] : Prop where
  cylinderLoop_rweq_decode (p : CylinderLoopSpace.{u}) :
    RwEq.{u} p (cylinderLoopPathZPow (cylinderEncodePath p))

/-- Every loop is RwEq to the decoded form of its winding number. -/
theorem cylinderLoop_rweq_decode [HasCircleLoopDecode.{u}] [h : HasCylinderLoopDecode.{u}] (p : CylinderLoopSpace.{u}) :
    RwEq.{u} p (cylinderLoopPathZPow (cylinderEncodePath p)) :=
  h.cylinderLoop_rweq_decode p

/-- Decoding composed with encoding is the identity. -/
@[simp] theorem cylinderDecode_cylinderEncode [HasCircleLoopDecode.{u}] [h : HasCylinderLoopDecode.{u}] (x : CylinderLoopQuot.{u}) :
    cylinderDecode (cylinderEncode x) = x := by
  induction x using Quot.ind with
  | _ p =>
    simp only [cylinderEncode, cylinderDecode, cylinderLoopZPow_ofLoopPathZPow]
    exact Quot.sound (rweq_symm (cylinderLoop_rweq_decode (h := h) p))

/-- The fundamental group of the cylinder is isomorphic to ℤ. -/
def cylinderPiOneEquivInt [HasCircleLoopDecode.{u}] [HasCylinderLoopDecode.{u}] :
    SimpleEquiv cylinderPiOne Int where
  toFun := cylinderEncode
  invFun := cylinderDecode
  left_inv := cylinderDecode_cylinderEncode
  right_inv := cylinderEncode_cylinderDecode

end -- noncomputable section

end Path
end ComputationalPaths
