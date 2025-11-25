/-
# The Möbius Band as a Higher-Inductive Type

This module introduces `MobiusBand` together with its base-point, the
central loop, and the characteristic twist. We provide an eliminator
stated in the computational-path style.

The Möbius band can be viewed as a rectangle with opposite edges identified
in *opposite* directions (twisted):

```
  loop
  ----→
  |    |
  ↓    ↑   (note: opposite orientations on sides!)
  ←----
  loop⁻¹
```

Alternatively, it is obtained by taking I × I and identifying (0,t) with (1,1-t).

## Key Structure

- Base point: `mobiusBase`
- Central loop: `mobiusLoop : Path mobiusBase mobiusBase`
- The band is formed by the identification, but the fundamental group
  sees only the central circle.

The fundamental group π₁(Möbius) ≃ ℤ, since the Möbius band is homotopy
equivalent to the circle (it deformation retracts to its central circle).

## Note on Twisting

The "twist" in the Möbius band affects the fiber bundle structure (the band
is a non-orientable line bundle over S¹), but does not change the fundamental
group. The twist is visible in the universal cover and transport behavior.

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

/-! ## HIT Definition

The Möbius band is presented as a HIT with:
- A base point
- A loop (the central circle)
- A "twist" path that identifies fibers with a flip

For fundamental group purposes, the Möbius band is equivalent to the circle,
so we can use a simpler presentation focused on the central loop.
-/

/-- Abstract Möbius band type. -/
axiom MobiusBand : Type u

/-- Distinguished point on the Möbius band (on the central circle). -/
axiom mobiusBase : MobiusBand

/-- The central loop around the Möbius band.
    This generates the fundamental group. -/
axiom mobiusLoop : Path (A := MobiusBand) mobiusBase mobiusBase

/-! ## Alternative Presentation with Twist

A more detailed presentation includes the fiber structure.
The "twist" is encoded by how transport behaves along the loop.

In the I × I model:
- base corresponds to (0, 1/2) ∼ (1, 1/2)
- loop corresponds to the path from (0, 1/2) to (1, 1/2) along the middle
- The twist: going around once flips the fiber coordinate

For the fundamental group calculation, we don't need the full fiber structure.
-/

/-! ## Non-Dependent Eliminator -/

/-- Data required to eliminate from the Möbius band into a target type `C`. -/
structure MobiusBandRecData (C : Type v) where
  base : C
  loop : Path base base

/-- Möbius band eliminator (recursor). -/
axiom mobiusBandRec {C : Type v} (data : MobiusBandRecData C) : MobiusBand → C

/-- β-rule for `mobiusBandRec` at the base point. -/
axiom mobiusBandRec_base {C : Type v} (data : MobiusBandRecData C) :
  mobiusBandRec data mobiusBase = data.base

/-- β-rule for `mobiusBandRec` on the central loop. -/
axiom mobiusBandRec_loop {C : Type v} (data : MobiusBandRecData C) :
  Path.trans
    (Path.symm (Path.ofEq (mobiusBandRec_base (C := C) data)))
    (Path.trans
      (Path.congrArg (mobiusBandRec data) mobiusLoop)
      (Path.ofEq (mobiusBandRec_base (C := C) data))) =
  data.loop

/-! ## Dependent Eliminator -/

/-- Data for the dependent eliminator of the Möbius band.
    The key feature is that `loop` must respect the twist:
    transport along `mobiusLoop` should involve a "flip" in the fiber. -/
structure MobiusBandIndData (C : MobiusBand → Type v) where
  base : C mobiusBase
  loop : Path (Path.transport (A := MobiusBand) (D := C) mobiusLoop base) base
  -- For a genuine Möbius band, C should be a bundle where transport
  -- along the loop gives a non-trivial (orientation-reversing) map.

/-- Dependent eliminator (induction principle) for the Möbius band. -/
axiom mobiusBandInd {C : MobiusBand → Type v} (data : MobiusBandIndData C) :
  (x : MobiusBand) → C x

/-- β-rule for the dependent eliminator at the base point. -/
axiom mobiusBandInd_base {C : MobiusBand → Type v} (data : MobiusBandIndData C) :
  mobiusBandInd data mobiusBase = data.base

/-- Dependent β-rule for the central loop. -/
axiom mobiusBandInd_loop {C : MobiusBand → Type v} (data : MobiusBandIndData C) :
  Path.trans
    (Path.symm
      (Path.congrArg
        (fun x =>
          Path.transport (A := MobiusBand) (D := fun y => C y) mobiusLoop x)
        (Path.ofEq (mobiusBandInd_base (C := C) data))))
    (Path.trans
      (Path.apd (A := MobiusBand) (B := fun y => C y)
        (f := mobiusBandInd data) mobiusLoop)
      (Path.ofEq (mobiusBandInd_base (C := C) data))) =
  data.loop

noncomputable section

open SimpleEquiv

/-! ## Loop Space and Fundamental Group

The fundamental group of the Möbius band is isomorphic to ℤ.
The Möbius band deformation retracts to its central circle.
-/

/-- Loop space at the base point of the Möbius band. -/
abbrev MobiusLoopSpace : Type u := LoopSpace MobiusBand mobiusBase

/-- Quotient of loop space by path rewriting. -/
abbrev MobiusLoopQuot : Type u := LoopQuot MobiusBand mobiusBase

/-- The fundamental group type. -/
abbrev mobiusPiOne : Type u := PiOne MobiusBand mobiusBase

/-- The class of the central loop in the quotient. -/
def mobiusLoopClass : MobiusLoopQuot :=
  LoopQuot.ofLoop mobiusLoop

/-! ## Loop Powers

Powers of the fundamental loop, following the same pattern as the circle.
-/

/-- Natural number power of the loop. -/
def mobiusLoopPathPow : Nat → MobiusLoopSpace
  | 0 => Path.refl mobiusBase
  | Nat.succ n => Path.trans (mobiusLoopPathPow n) mobiusLoop

@[simp] theorem mobiusLoopPathPow_zero : mobiusLoopPathPow 0 = Path.refl mobiusBase := rfl

@[simp] theorem mobiusLoopPathPow_succ (n : Nat) :
    mobiusLoopPathPow n.succ = Path.trans (mobiusLoopPathPow n) mobiusLoop := rfl

/-- Integer power of the loop (raw path). -/
def mobiusLoopPathZPow : Int → MobiusLoopSpace
  | Int.ofNat n => mobiusLoopPathPow n
  | Int.negSucc n => Path.symm (mobiusLoopPathPow (n + 1))

/-- Natural number power in the quotient. -/
def mobiusLoopPow (n : Nat) : MobiusLoopQuot :=
  LoopQuot.pow mobiusLoopClass n

@[simp] theorem mobiusLoopPow_zero : mobiusLoopPow 0 = LoopQuot.id :=
  LoopQuot.pow_zero mobiusLoopClass

@[simp] theorem mobiusLoopPow_succ (n : Nat) :
    mobiusLoopPow n.succ = LoopQuot.comp (mobiusLoopPow n) mobiusLoopClass :=
  LoopQuot.pow_succ mobiusLoopClass n

/-- Integer power in the quotient. -/
def mobiusLoopZPow (z : Int) : MobiusLoopQuot :=
  LoopQuot.zpow mobiusLoopClass z

/-! ## Encoding: Loops to Integers

The winding number map sends loops to integers.
We use the retraction to the circle to define encoding.
-/

/-- Data for the map from Möbius band to circle. -/
private def mobiusToCircleData : MobiusBandRecData Circle where
  base := circleBase
  loop := circleLoop

/-- Map from Möbius band to circle (central circle inclusion). -/
def mobiusToCircle : MobiusBand → Circle :=
  mobiusBandRec mobiusToCircleData

@[simp] theorem mobiusToCircle_base :
    mobiusToCircle mobiusBase = circleBase :=
  mobiusBandRec_base mobiusToCircleData

/-- The Möbius-to-circle map sends the central loop to the circle loop. -/
theorem mobiusToCircle_loop :
    Path.trans
        (Path.symm (Path.ofEq mobiusToCircle_base))
        (Path.trans
          (Path.congrArg mobiusToCircle mobiusLoop)
          (Path.ofEq mobiusToCircle_base)) =
      circleLoop :=
  mobiusBandRec_loop mobiusToCircleData

/-- Map a Möbius band loop to a circle loop via the retraction. -/
def mobiusLoopToCircleLoop (p : MobiusLoopSpace) : Path circleBase circleBase :=
  Path.trans (Path.symm (Path.ofEq mobiusToCircle_base))
    (Path.trans (Path.congrArg mobiusToCircle p)
      (Path.ofEq mobiusToCircle_base))

/-- Encode a raw loop as an integer (winding number). -/
def mobiusEncodePath.{w} (p : MobiusLoopSpace.{w}) : Int :=
  circleEncodePath.{w} (mobiusLoopToCircleLoop.{w} p)

/-- The encoding respects path rewriting. -/
theorem mobiusEncodePath_rweq {p q : MobiusLoopSpace}
    (h : RwEq p q) : mobiusEncodePath p = mobiusEncodePath q := by
  unfold mobiusEncodePath mobiusLoopToCircleLoop
  apply circleEncodePath_rweq
  apply rweq_trans_congr_right
  apply rweq_trans_congr_left
  apply rweq_of_toEq_eq
  exact _root_.congrArg (_root_.congrArg mobiusToCircle) (rweq_toEq h)

@[simp] theorem mobiusEncodePath_refl :
    mobiusEncodePath (Path.refl mobiusBase) = 0 := by
  unfold mobiusEncodePath mobiusLoopToCircleLoop
  have hrweq : RwEq
      (Path.trans (Path.symm (Path.ofEq mobiusToCircle_base))
        (Path.trans (Path.congrArg mobiusToCircle (Path.refl mobiusBase))
          (Path.ofEq mobiusToCircle_base)))
      (Path.refl circleBase) := by
    apply rweq_of_toEq_eq
    simp
  rw [circleEncodePath_rweq hrweq]
  exact circleEncodePath_refl

@[simp] theorem mobiusEncodePath_loop :
    mobiusEncodePath mobiusLoop = 1 := by
  unfold mobiusEncodePath mobiusLoopToCircleLoop
  rw [mobiusToCircle_loop]
  exact circleEncodePath_loop

/-- Encoding after appending loop adds 1. -/
@[simp] theorem mobiusEncodePath_trans_loop (p : MobiusLoopSpace) :
    mobiusEncodePath (Path.trans p mobiusLoop) = mobiusEncodePath p + 1 := by
  unfold mobiusEncodePath mobiusLoopToCircleLoop
  have hrweq : RwEq
      (Path.trans (Path.symm (Path.ofEq mobiusToCircle_base))
        (Path.trans (Path.congrArg mobiusToCircle (Path.trans p mobiusLoop))
          (Path.ofEq mobiusToCircle_base)))
      (Path.trans
        (Path.trans (Path.symm (Path.ofEq mobiusToCircle_base))
          (Path.trans (Path.congrArg mobiusToCircle p)
            (Path.ofEq mobiusToCircle_base)))
        circleLoop) := by
    apply rweq_of_toEq_eq
    simp
  rw [circleEncodePath_rweq hrweq]
  rw [circleEncodePath_trans_loop]

/-- Encoding after appending symm loop subtracts 1. -/
@[simp] theorem mobiusEncodePath_trans_symm_loop (p : MobiusLoopSpace) :
    mobiusEncodePath (Path.trans p (Path.symm mobiusLoop)) = mobiusEncodePath p - 1 := by
  unfold mobiusEncodePath mobiusLoopToCircleLoop
  have hrweq : RwEq
      (Path.trans (Path.symm (Path.ofEq mobiusToCircle_base))
        (Path.trans (Path.congrArg mobiusToCircle (Path.trans p (Path.symm mobiusLoop)))
          (Path.ofEq mobiusToCircle_base)))
      (Path.trans
        (Path.trans (Path.symm (Path.ofEq mobiusToCircle_base))
          (Path.trans (Path.congrArg mobiusToCircle p)
            (Path.ofEq mobiusToCircle_base)))
        (Path.symm circleLoop)) := by
    apply rweq_of_toEq_eq
    simp
  rw [circleEncodePath_rweq hrweq]
  rw [circleEncodePath_trans_symm_loop]

/-- Encoding the inverse of loop gives -1. -/
@[simp] theorem mobiusEncodePath_symm_loop :
    mobiusEncodePath (Path.symm mobiusLoop) = -1 := by
  calc mobiusEncodePath (Path.symm mobiusLoop)
      = mobiusEncodePath (Path.trans (Path.refl mobiusBase) (Path.symm mobiusLoop)) := rfl
    _ = mobiusEncodePath (Path.refl mobiusBase) - 1 :=
        mobiusEncodePath_trans_symm_loop (Path.refl mobiusBase)
    _ = 0 - 1 := by rw [mobiusEncodePath_refl]
    _ = -1 := by simp

/-- Encoding a natural loop power gives the natural number. -/
@[simp] theorem mobiusEncodePath_loopPathPow (n : Nat) :
    mobiusEncodePath (mobiusLoopPathPow n) = n := by
  induction n with
  | zero =>
    simp only [mobiusLoopPathPow]
    exact mobiusEncodePath_refl
  | succ n ih =>
    simp only [mobiusLoopPathPow]
    rw [mobiusEncodePath_trans_loop]
    simp [ih]

/-- Encoding an integer loop power gives the integer. -/
@[simp] theorem mobiusEncodePath_loopPathZPow (z : Int) :
    mobiusEncodePath (mobiusLoopPathZPow z) = z := by
  cases z with
  | ofNat n =>
    simp only [mobiusLoopPathZPow]
    exact mobiusEncodePath_loopPathPow n
  | negSucc n =>
    simp only [mobiusLoopPathZPow]
    induction n with
    | zero =>
      simp only [mobiusLoopPathPow]
      exact mobiusEncodePath_symm_loop
    | succ k ih =>
      have hunfold : mobiusLoopPathPow (k + 1 + 1) =
          Path.trans (mobiusLoopPathPow (k + 1)) mobiusLoop := rfl
      rw [hunfold]
      have hstep : Path.symm (Path.trans (mobiusLoopPathPow (k + 1)) mobiusLoop) =
                   Path.trans (Path.symm mobiusLoop) (Path.symm (mobiusLoopPathPow (k + 1))) :=
        Path.symm_trans _ _
      rw [hstep]
      have ih' : mobiusEncodePath (Path.symm (mobiusLoopPathPow (k + 1))) = Int.negSucc k := ih
      calc mobiusEncodePath (Path.trans (Path.symm mobiusLoop) (Path.symm (mobiusLoopPathPow (k + 1))))
          = mobiusEncodePath (Path.trans (Path.symm (mobiusLoopPathPow (k + 1))) (Path.symm mobiusLoop)) := by
            apply mobiusEncodePath_rweq
            apply rweq_of_toEq_eq
            simp
        _ = mobiusEncodePath (Path.symm (mobiusLoopPathPow (k + 1))) - 1 :=
            mobiusEncodePath_trans_symm_loop _
        _ = Int.negSucc k - 1 := by rw [ih']
        _ = Int.negSucc (k + 1) := by simp [Int.negSucc_sub_one]

/-- Quotient-level encoding (winding number). -/
def mobiusEncode : MobiusLoopQuot → Int :=
  Quot.lift mobiusEncodePath (fun _ _ h => mobiusEncodePath_rweq (by exact h))

@[simp] theorem mobiusEncode_ofLoop (p : MobiusLoopSpace) :
    mobiusEncode (LoopQuot.ofLoop p) = mobiusEncodePath p := rfl

@[simp] theorem mobiusEncode_id : mobiusEncode LoopQuot.id = 0 :=
  mobiusEncodePath_refl

@[simp] theorem mobiusEncode_loopClass :
    mobiusEncode mobiusLoopClass = 1 :=
  mobiusEncodePath_loop

/-! ## Decoding: Integers to Loops

The inverse map sends integers to loop powers.
-/

/-- Decode an integer as a loop power. -/
def mobiusDecode : Int → MobiusLoopQuot :=
  mobiusLoopZPow

/-- The quotient loop power equals ofLoop of the path loop power. -/
@[simp] theorem mobiusLoopPow_ofLoopPathPow (n : Nat) :
    mobiusLoopPow n = LoopQuot.ofLoop (mobiusLoopPathPow n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [mobiusLoopPow_succ, mobiusLoopPathPow_succ]
      rw [ih]
      rfl

/-- The quotient zpow equals ofLoop of the path zpow. -/
@[simp] theorem mobiusLoopZPow_ofLoopPathZPow (z : Int) :
    mobiusLoopZPow z = LoopQuot.ofLoop (mobiusLoopPathZPow z) := by
  cases z with
  | ofNat n =>
      change LoopQuot.pow mobiusLoopClass n = LoopQuot.ofLoop (mobiusLoopPathPow n)
      exact mobiusLoopPow_ofLoopPathPow n
  | negSucc n =>
      have h : mobiusLoopPow (n + 1) = LoopQuot.ofLoop (mobiusLoopPathPow (n + 1)) :=
        mobiusLoopPow_ofLoopPathPow (n + 1)
      change LoopQuot.inv (mobiusLoopPow (n + 1)) =
          LoopQuot.ofLoop (Path.symm (mobiusLoopPathPow (n + 1)))
      rw [h]
      rfl

/-- The toEq of natural loop power. -/
@[simp] theorem mobiusLoopPow_toEq (n : Nat) :
    PathRwQuot.toEq (A := MobiusBand) (mobiusLoopPow n)
      = (mobiusLoopPathPow n).toEq := by
  rw [mobiusLoopPow_ofLoopPathPow]

/-- The toEq of integer loop power. -/
@[simp] theorem mobiusLoopZPow_toEq (z : Int) :
    PathRwQuot.toEq (A := MobiusBand) (mobiusLoopZPow z)
      = (mobiusLoopPathZPow z).toEq := by
  rw [mobiusLoopZPow_ofLoopPathZPow]

/-! ## Fundamental Group Isomorphism

The Möbius band has fundamental group isomorphic to ℤ.
-/

/-- Encoding composed with decoding is the identity. -/
@[simp] theorem mobiusEncode_mobiusDecode (z : Int) :
    mobiusEncode (mobiusDecode z) = z := by
  simp only [mobiusDecode, mobiusLoopZPow_ofLoopPathZPow]
  simp only [mobiusEncode_ofLoop]
  exact mobiusEncodePath_loopPathZPow z

-- Equality-level helper: `decodeEq ∘ encodeEq = id` on `(=)`.
private theorem mobiusDecodeEq_mobiusEncodeEq
    (e : mobiusBase = mobiusBase) :
    (mobiusLoopPathZPow (mobiusEncodePath (Path.ofEq e))).toEq = e := by
  cases e with
  | refl => simp

/-- Decoding composed with encoding is the identity. -/
@[simp] theorem mobiusDecode_mobiusEncode (x : MobiusLoopQuot) :
    mobiusDecode (mobiusEncode x) = x := by
  apply PathRwQuot.eq_of_toEq_eq (A := MobiusBand) (a := mobiusBase) (b := mobiusBase)
  refine Quot.inductionOn x (fun p => ?_)
  have hDec :
      PathRwQuot.toEq (A := MobiusBand)
        (mobiusDecode (mobiusEncode
          (LoopQuot.ofLoop (A := MobiusBand) (a := mobiusBase) p)))
        = (mobiusLoopPathZPow (mobiusEncodePath p)).toEq := by
    change PathRwQuot.toEq (A := MobiusBand)
        (mobiusLoopZPow (mobiusEncodePath p))
        = (mobiusLoopPathZPow (mobiusEncodePath p)).toEq
    exact mobiusLoopZPow_toEq (z := mobiusEncodePath p)
  have hcanon :
      mobiusEncodePath (Path.ofEq p.toEq) = mobiusEncodePath p := by
    have hcanonRw : RwEq p (Path.ofEq p.toEq) := rweq_canon (p := p)
    exact (mobiusEncodePath_rweq (h := hcanonRw)).symm
  have hEq := mobiusDecodeEq_mobiusEncodeEq (e := p.toEq)
  calc PathRwQuot.toEq (A := MobiusBand)
        (mobiusDecode (mobiusEncode
          (LoopQuot.ofLoop (A := MobiusBand) (a := mobiusBase) p)))
      = (mobiusLoopPathZPow (mobiusEncodePath p)).toEq := hDec
    _ = (mobiusLoopPathZPow (mobiusEncodePath (Path.ofEq p.toEq))).toEq := by rw [hcanon]
    _ = p.toEq := hEq
    _ = PathRwQuot.toEq (A := MobiusBand)
          (LoopQuot.ofLoop (A := MobiusBand) (a := mobiusBase) p) := by simp

/-- The fundamental group of the Möbius band is isomorphic to ℤ. -/
noncomputable def mobiusPiOneEquivInt : SimpleEquiv mobiusPiOne Int where
  toFun := mobiusEncode
  invFun := mobiusDecode
  left_inv := by
    intro x
    exact mobiusDecode_mobiusEncode x
  right_inv := by
    intro z
    exact mobiusEncode_mobiusDecode z

/-! ## Relationship to Other Spaces

The Möbius band is related to several other spaces:

1. **Circle**: The Möbius band deformation retracts to S¹
2. **Klein Bottle**: Gluing two Möbius bands along their boundary gives K
3. **RP²**: RP² can be obtained from a Möbius band by attaching a disk

These relationships are reflected in the fundamental groups:
- π₁(Möbius) ≃ ℤ
- π₁(Klein) ≃ ℤ ⋊ ℤ (with the Klein bottle relation)
- π₁(RP²) ≃ ℤ₂

Note: The distinctive "twist" property of the Möbius band (transport along
the loop gives a reflection in the fiber) is not formalized here, as it
requires additional structure beyond what's needed for the fundamental
group calculation. The paper arXiv:1804.01413 focuses on fundamental groups.
-/

end -- noncomputable section

end Path
end ComputationalPaths
