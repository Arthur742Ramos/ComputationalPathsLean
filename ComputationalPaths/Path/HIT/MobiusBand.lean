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

## Key Results

- `mobiusLoop`: The central loop around the Möbius band
- `mobiusPiOneEquivInt`: π₁(Möbius) ≃ ℤ (the main theorem)
- `MobiusLoopPower`: Loop power classification

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
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.Quot
import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.HIT.CircleStep

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
def mobiusEncodePath.{w} [HasCirclePiOneEncode.{w}] (p : MobiusLoopSpace.{w}) : Int :=
  circlePiOneEncode.{w} (Quot.mk _ (mobiusLoopToCircleLoop.{w} p))

/-- The encoding respects path rewriting. -/
theorem mobiusEncodePath_rweq [HasCirclePiOneEncode.{u}] {p q : MobiusLoopSpace}
    (h : RwEq p q) : mobiusEncodePath.{u} p = mobiusEncodePath.{u} q := by
  unfold mobiusEncodePath
  unfold mobiusLoopToCircleLoop
  have hCongr :
      RwEq (Path.congrArg mobiusToCircle p) (Path.congrArg mobiusToCircle q) :=
    rweq_congrArg_of_rweq mobiusToCircle h
  have hInner :
      RwEq
        (Path.trans (Path.congrArg mobiusToCircle p) (Path.ofEq mobiusToCircle_base))
        (Path.trans (Path.congrArg mobiusToCircle q) (Path.ofEq mobiusToCircle_base)) :=
    rweq_trans_congr_left (Path.ofEq mobiusToCircle_base) hCongr
  have hLoop :
      RwEq
        (Path.trans (Path.symm (Path.ofEq mobiusToCircle_base))
          (Path.trans (Path.congrArg mobiusToCircle p) (Path.ofEq mobiusToCircle_base)))
        (Path.trans (Path.symm (Path.ofEq mobiusToCircle_base))
          (Path.trans (Path.congrArg mobiusToCircle q) (Path.ofEq mobiusToCircle_base))) :=
    rweq_trans_congr_right (Path.symm (Path.ofEq mobiusToCircle_base)) hInner
  have hQuot :
      (Quot.mk _ (mobiusLoopToCircleLoop p) : circlePiOne.{u}) =
        Quot.mk _ (mobiusLoopToCircleLoop q) :=
    Quot.sound hLoop
  exact _root_.congrArg (circlePiOneEncode.{u}) hQuot

@[simp] theorem mobiusEncodePath_refl [HasCirclePiOneEncode.{u}] :
    mobiusEncodePath.{u} (Path.refl mobiusBase) = 0 := by
  unfold mobiusEncodePath mobiusLoopToCircleLoop
  let baseEq := mobiusToCircle_base.{u, u}
  have hCancel :
      RwEq
        (Path.trans (Path.symm (Path.ofEq baseEq)) (Path.ofEq baseEq))
        (Path.refl (circleBase.{u})) := by
    simpa using rweq_cmpA_inv_left (p := Path.ofEq baseEq)
  have hQuot :
      (Quot.mk _ (Path.trans (Path.symm (Path.ofEq baseEq)) (Path.ofEq baseEq)) : circlePiOne.{u}) =
        LoopQuot.id (A := Circle.{u}) (a := circleBase.{u}) := by
    simpa [LoopQuot.id] using (Quot.sound hCancel)
  have hEnc :
      circlePiOneEncode.{u}
          (Quot.mk _ (Path.trans (Path.symm (Path.ofEq baseEq)) (Path.ofEq baseEq)) : circlePiOne.{u}) =
        circlePiOneEncode.{u} (LoopQuot.id (A := Circle.{u}) (a := circleBase.{u})) :=
    _root_.congrArg (circlePiOneEncode.{u}) hQuot
  exact hEnc.trans (circlePiOneEncode_id.{u})

@[simp] theorem mobiusEncodePath_loop [HasCirclePiOneEncode.{u}] :
    mobiusEncodePath.{u} mobiusLoop = 1 := by
  unfold mobiusEncodePath mobiusLoopToCircleLoop
  rw [mobiusToCircle_loop]
  simpa using (circlePiOneEncode_loop.{u})

/-! ### Algebraic laws for Möbius encoding -/

/-- `mobiusLoopToCircleLoop` preserves concatenation up to `RwEq`. -/
private theorem mobiusLoopToCircleLoop_trans_rweq (p q : MobiusLoopSpace) :
    RwEq (mobiusLoopToCircleLoop (Path.trans p q))
      (Path.trans (mobiusLoopToCircleLoop p) (mobiusLoopToCircleLoop q)) := by
  unfold mobiusLoopToCircleLoop
  rw [Path.congrArg_trans (f := mobiusToCircle) (p := p) (q := q)]
  have h1 :=
    rweq_tt (Path.symm (Path.ofEq mobiusToCircle_base))
      (Path.trans (Path.congrArg mobiusToCircle p) (Path.ofEq mobiusToCircle_base))
      (Path.trans (Path.symm (Path.ofEq mobiusToCircle_base))
        (Path.trans (Path.congrArg mobiusToCircle q) (Path.ofEq mobiusToCircle_base)))
  have h2 :=
    rweq_trans_congr_right (Path.symm (Path.ofEq mobiusToCircle_base)) <|
      rweq_tt (Path.congrArg mobiusToCircle p) (Path.ofEq mobiusToCircle_base)
        (Path.trans (Path.symm (Path.ofEq mobiusToCircle_base))
          (Path.trans (Path.congrArg mobiusToCircle q) (Path.ofEq mobiusToCircle_base)))
  have h3 :=
    rweq_trans_congr_right (Path.symm (Path.ofEq mobiusToCircle_base)) <|
      rweq_trans_congr_right (Path.congrArg mobiusToCircle p) <|
        (rweq_tt (Path.ofEq mobiusToCircle_base)
          (Path.symm (Path.ofEq mobiusToCircle_base))
          (Path.trans (Path.congrArg mobiusToCircle q) (Path.ofEq mobiusToCircle_base))).symm
  have hCancel :=
    rweq_cmpA_inv_right (p := Path.ofEq mobiusToCircle_base)
  have h4 :=
    rweq_trans_congr_right (Path.symm (Path.ofEq mobiusToCircle_base)) <|
      rweq_trans_congr_right (Path.congrArg mobiusToCircle p) <|
        RwEq.trans
          (rweq_trans_congr_left
            (Path.trans (Path.congrArg mobiusToCircle q) (Path.ofEq mobiusToCircle_base))
            hCancel)
          (rweq_cmpA_refl_left
            (Path.trans (Path.congrArg mobiusToCircle q) (Path.ofEq mobiusToCircle_base)))
  have h5 :=
    rweq_trans_congr_right (Path.symm (Path.ofEq mobiusToCircle_base)) <|
      (rweq_tt (Path.congrArg mobiusToCircle p)
        (Path.congrArg mobiusToCircle q)
        (Path.ofEq mobiusToCircle_base)).symm
  exact rweq_symm (RwEq.trans (RwEq.trans (RwEq.trans (RwEq.trans h1 h2) h3) h4) h5)

section

variable [HasCirclePiOneEncode.{u}]

/-- `mobiusEncodePath` is additive over concatenation (raw loop level). -/
theorem mobiusEncodePath_trans (p q : MobiusLoopSpace) :
    mobiusEncodePath.{u} (Path.trans p q) = mobiusEncodePath.{u} p + mobiusEncodePath.{u} q := by
  unfold mobiusEncodePath
  have hMul := mobiusLoopToCircleLoop_trans_rweq (p := p) (q := q)
  have hQuot :
      (Quot.mk _ (mobiusLoopToCircleLoop (Path.trans p q)) : circlePiOne.{u}) =
        LoopQuot.comp (A := Circle.{u}) (a := circleBase.{u})
          (Quot.mk _ (mobiusLoopToCircleLoop p))
          (Quot.mk _ (mobiusLoopToCircleLoop q)) := by
    have h' :
        (Quot.mk _ (mobiusLoopToCircleLoop (Path.trans p q)) : circlePiOne.{u}) =
          (Quot.mk _ (Path.trans (mobiusLoopToCircleLoop p) (mobiusLoopToCircleLoop q)) : circlePiOne.{u}) :=
      Quot.sound hMul
    simpa [LoopQuot.comp] using h'
  calc
    circlePiOneEncode.{u} (Quot.mk _ (mobiusLoopToCircleLoop (Path.trans p q)))
        =
        circlePiOneEncode.{u}
          (LoopQuot.comp (A := Circle.{u}) (a := circleBase.{u})
            (Quot.mk _ (mobiusLoopToCircleLoop p))
            (Quot.mk _ (mobiusLoopToCircleLoop q))) := by
          simpa using _root_.congrArg (circlePiOneEncode.{u}) hQuot
    _ =
        circlePiOneEncode.{u} (Quot.mk _ (mobiusLoopToCircleLoop p)) +
          circlePiOneEncode.{u} (Quot.mk _ (mobiusLoopToCircleLoop q)) := by
          simpa using
            circlePiOneEncode_mul.{u}
              (α := (Quot.mk _ (mobiusLoopToCircleLoop p) : circlePiOne.{u}))
              (β := (Quot.mk _ (mobiusLoopToCircleLoop q) : circlePiOne.{u}))

/-- Encoding respects inversion: `encode (p⁻¹) = - encode p`. -/
theorem mobiusEncodePath_symm (p : MobiusLoopSpace) :
    mobiusEncodePath.{u} (Path.symm p) = - mobiusEncodePath.{u} p := by
  have hCancel : RwEq (Path.trans p (Path.symm p)) (Path.refl mobiusBase) :=
    rweq_cmpA_inv_right (p := p)
  have h0 : mobiusEncodePath.{u} (Path.trans p (Path.symm p)) = 0 := by
    have hEq := mobiusEncodePath_rweq (h := hCancel)
    exact hEq.trans mobiusEncodePath_refl
  have hTrans := mobiusEncodePath_trans (p := p) (q := Path.symm p)
  have hSum : mobiusEncodePath.{u} p + mobiusEncodePath.{u} (Path.symm p) = 0 :=
    (Eq.symm hTrans).trans h0
  omega

/-- Encoding after appending loop adds 1. -/
@[simp] theorem mobiusEncodePath_trans_loop (p : MobiusLoopSpace) :
    mobiusEncodePath.{u} (Path.trans p mobiusLoop) = mobiusEncodePath.{u} p + 1 := by
  simpa [mobiusEncodePath_loop] using mobiusEncodePath_trans (p := p) (q := mobiusLoop)

/-- Encoding after appending symm loop subtracts 1. -/
@[simp] theorem mobiusEncodePath_trans_symm_loop (p : MobiusLoopSpace) :
    mobiusEncodePath.{u} (Path.trans p (Path.symm mobiusLoop)) = mobiusEncodePath.{u} p - 1 := by
  have hLoopInv : mobiusEncodePath.{u} (Path.symm mobiusLoop) = -1 := by
    simpa [mobiusEncodePath_loop] using mobiusEncodePath_symm (p := mobiusLoop)
  rw [Int.sub_eq_add_neg]
  refine (mobiusEncodePath_trans (p := p) (q := Path.symm mobiusLoop)).trans ?_
  rw [hLoopInv]

/-- Encoding the inverse of loop gives -1. -/
@[simp] theorem mobiusEncodePath_symm_loop :
    mobiusEncodePath.{u} (Path.symm mobiusLoop) = -1 := by
  simpa [mobiusEncodePath_loop] using mobiusEncodePath_symm (p := mobiusLoop)

/-- Encoding a natural loop power gives the natural number. -/
@[simp] theorem mobiusEncodePath_loopPathPow (n : Nat) :
    mobiusEncodePath.{u} (mobiusLoopPathPow n) = n := by
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
    mobiusEncodePath.{u} (mobiusLoopPathZPow z) = z := by
  cases z with
  | ofNat n =>
    simp only [mobiusLoopPathZPow]
    exact mobiusEncodePath_loopPathPow n
  | negSucc n =>
    -- mobiusLoopPathZPow (Int.negSucc n) = Path.symm (mobiusLoopPathPow (n + 1))
    simp only [mobiusLoopPathZPow]
    -- Use the derived `encode(symm p) = - encode p` and compute the positive power.
    have h := mobiusEncodePath_symm (p := mobiusLoopPathPow (n + 1))
    rw [mobiusEncodePath_loopPathPow (n + 1)] at h
    simpa [Int.negSucc_eq] using h

end

/-- Quotient-level encoding (winding number). -/
def mobiusEncode [HasCirclePiOneEncode.{u}] : MobiusLoopQuot → Int :=
  Quot.lift mobiusEncodePath (fun _ _ h => mobiusEncodePath_rweq h)

@[simp] theorem mobiusEncode_ofLoop [HasCirclePiOneEncode.{u}] (p : MobiusLoopSpace) :
    mobiusEncode (LoopQuot.ofLoop p) = mobiusEncodePath p := rfl

@[simp] theorem mobiusEncode_id [HasCirclePiOneEncode.{u}] : mobiusEncode LoopQuot.id = 0 :=
  mobiusEncodePath_refl

@[simp] theorem mobiusEncode_loopClass [HasCirclePiOneEncode.{u}] :
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
@[simp] theorem mobiusEncode_mobiusDecode [HasCirclePiOneEncode.{u}] (z : Int) :
    mobiusEncode.{u} (mobiusDecode.{u} z) = z := by
  simp only [mobiusDecode, mobiusLoopZPow_ofLoopPathZPow]
  simp only [mobiusEncode_ofLoop]
  exact mobiusEncodePath_loopPathZPow z

-- Equality-level helper: `decodeEq ∘ encodeEq = id` on `(=)`.
private theorem mobiusDecodeEq_mobiusEncodeEq [HasCirclePiOneEncode.{u}]
    (e : mobiusBase = mobiusBase) :
    (mobiusLoopPathZPow (mobiusEncodePath (Path.ofEq e))).toEq = e := by
  cases e with
  | refl => simp

/-- **Möbius loop classification axiom**: Every Möbius loop is RwEq to
the decoded form of its winding number. -/
class HasMobiusLoopDecode [HasCirclePiOneEncode.{u}] : Prop where
  mobiusLoop_rweq_decode (p : MobiusLoopSpace.{u}) :
    RwEq.{u} p (mobiusLoopPathZPow (mobiusEncodePath p))

/-- Every loop is RwEq to the decoded form of its winding number. -/
theorem mobiusLoop_rweq_decode [HasCirclePiOneEncode.{u}] [h : HasMobiusLoopDecode.{u}] (p : MobiusLoopSpace.{u}) :
    RwEq.{u} p (mobiusLoopPathZPow (mobiusEncodePath p)) :=
  h.mobiusLoop_rweq_decode p

/-- Decoding composed with encoding is the identity. -/
@[simp] theorem mobiusDecode_mobiusEncode [HasCirclePiOneEncode.{u}] [h : HasMobiusLoopDecode.{u}] (x : MobiusLoopQuot.{u}) :
    mobiusDecode (mobiusEncode x) = x := by
  induction x using Quot.ind with
  | _ p =>
    simp only [mobiusEncode, mobiusDecode, mobiusLoopZPow_ofLoopPathZPow]
    exact Quot.sound (rweq_symm (mobiusLoop_rweq_decode (h := h) p))

/-- The fundamental group of the Möbius band is isomorphic to ℤ. -/
noncomputable def mobiusPiOneEquivInt [HasCirclePiOneEncode.{u}] [HasMobiusLoopDecode.{u}] :
    SimpleEquiv mobiusPiOne Int where
  toFun := mobiusEncode
  invFun := mobiusDecode
  left_inv := mobiusDecode_mobiusEncode
  right_inv := mobiusEncode_mobiusDecode

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
