/-
# The circle as a higher-inductive type (axiomatic skeleton)

This module introduces `Circle` together with its base-point, fundamental loop,
and an eliminator stated in the computational-path style.  At this stage we work
axiomatically: the constructors and recursor will later be justified by the
normalisation machinery developed for computational paths.  By providing these
interfaces now, downstream developments (loop spaces, fundamental groups, etc.)
can already depend on a stable API.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Basic.Univalence
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path

universe u v

/-- Abstract circle type used throughout the homotopy developments.  It will be
realised via computational paths once the rewrite system is extended to fully
support higher-inductive types. -/
axiom Circle : Type u

/-- Distinguished point on the circle. -/
axiom circleBase : Circle

/-- Fundamental loop around the circle, expressed as a computational path. -/
axiom circleLoop : Path (A := Circle) circleBase circleBase

/-- Data required to eliminate from the circle into a target type `C`.  One must
choose an image of the base point together with a computational path witnessing
how the chosen image behaves along the fundamental loop. -/
structure CircleRecData (C : Type v) where
  base : C
  loop : Path base base

/-- Circle eliminator (recursor).  Given a target type `C` together with images
for the base-point and loop, produce a map `Circle → C`.  The computation rules
below describe how this function acts on the constructors. -/
axiom circleRec {C : Type v} (data : CircleRecData C) : Circle → C

/-- β-rule for `circleRec` at the base point. -/
axiom circleRec_base {C : Type v} (data : CircleRecData C) :
  circleRec data circleBase = data.base

/-- β-rule for `circleRec` on the fundamental loop, expressed using
computational paths. -/
axiom circleRec_loop {C : Type v} (data : CircleRecData C) :
  Path.trans
    (Path.symm (Path.ofEq (circleRec_base (C := C) data)))
    (Path.trans
      (Path.congrArg (circleRec data) circleLoop)
      (Path.ofEq (circleRec_base (C := C) data))) =
  data.loop

/-- Data for the dependent eliminator of the circle.  Besides the fibre `C`
over `Circle`, we must specify the value on the base point together with a path
showing how the fibre transports along the fundamental loop. -/
structure CircleIndData (C : Circle → Type v) where
  base : C circleBase
  loop :
    Path
      (Path.transport (A := Circle) (D := fun x => C x) circleLoop base)
      base

/-- Dependent eliminator (induction principle) for the circle. -/
axiom circleInd {C : Circle → Type v} (data : CircleIndData C) :
  (x : Circle) → C x

/-- β-rule for the dependent eliminator at the base point. -/
axiom circleInd_base {C : Circle → Type v} (data : CircleIndData C) :
  circleInd data circleBase = data.base

/-- Dependent β-rule specialised to the fundamental loop.  The dependent
application of `circleInd` to `circleLoop` matches the prescribed path stored
in `CircleIndData`. -/
axiom circleInd_loop {C : Circle → Type v} (data : CircleIndData C) :
  Path.trans
    (Path.symm
      (Path.congrArg
        (fun x =>
          Path.transport (A := Circle) (D := fun y => C y) circleLoop x)
        (Path.ofEq (circleInd_base (C := C) data))))
    (Path.trans
      (Path.apd (A := Circle) (B := fun y => C y)
        (f := circleInd data) circleLoop)
      (Path.ofEq (circleInd_base (C := C) data))) =
  data.loop

noncomputable section

open SimpleEquiv

/-- Equivalence witnessing the successor/predecessor action on the integers. -/
def circleSuccEquiv : SimpleEquiv Int Int where
  toFun := fun z => z + 1
  invFun := fun z => z - 1
  left_inv := by
    intro z
    simpa using Int.add_sub_cancel z 1
  right_inv := by
    intro z
    simpa using Int.sub_add_cancel z 1

private def circleCodeData : CircleRecData (Type _) where
  base := Int
  loop := Path.ua circleSuccEquiv

/-- Universal-cover code family for the circle, landing in the integers. -/
noncomputable def circleCode : Circle → Type _ :=
  circleRec circleCodeData

@[simp] theorem circleCode_base :
    circleCode circleBase = Int :=
  circleRec_base circleCodeData

/-- View an element of `circleCode circleBase` as an integer using the base computation rule. -/
@[simp] def circleCodeToInt : circleCode circleBase → Int :=
  fun z => Eq.mp circleCode_base z

/-- Interpret an integer as an element of `circleCode circleBase`. -/
@[simp] def circleCodeOfInt : Int → circleCode circleBase :=
  fun z => Eq.mpr circleCode_base z

@[simp] theorem circleCodeToInt_ofInt (z : Int) :
    circleCodeToInt (circleCodeOfInt z) = z := by
  simp [circleCodeToInt, circleCodeOfInt]

@[simp] theorem circleCodeOfInt_toInt (z : circleCode circleBase) :
    circleCodeOfInt (circleCodeToInt z) = z := by
  simp [circleCodeToInt, circleCodeOfInt]

/-- Chosen basepoint in the code fibre at the circle base. -/
@[simp] def circleCodeZero : circleCode circleBase :=
  circleCodeOfInt 0

@[simp] theorem circleCodeToInt_zero :
    circleCodeToInt circleCodeZero = 0 := by
  simp [circleCodeZero]

/-- Transport the base code point along a loop to encode a path. -/
@[simp] def circleEncodeRaw (x : Circle) :
    Path circleBase x → circleCode x :=
  fun p => Path.transport (A := Circle) (D := circleCode) p circleCodeZero

/-- Circle computation rule transported to the `circleCode` family. -/
@[simp] theorem circleCode_loop_path :
    Path.trans (Path.symm (Path.ofEq circleCode_base))
        (Path.trans (Path.congrArg circleCode circleLoop)
          (Path.ofEq circleCode_base)) =
      Path.ua circleSuccEquiv :=
  circleRec_loop circleCodeData

/-- Iterate the fundamental loop `n` times at the raw path level (natural powers). -/
@[simp] def circleLoopPathPow : Nat → Path circleBase circleBase
  | 0 => Path.refl circleBase
  | Nat.succ n =>
      Path.trans (circleLoopPathPow n) circleLoop

/-- Integer iteration of the fundamental loop at the path level. -/
@[simp] def circleLoopPathZPow : Int → Path circleBase circleBase
  | Int.ofNat n => circleLoopPathPow n
  | Int.negSucc n =>
      Path.symm (circleLoopPathPow (Nat.succ n))

/-- Loop space of the circle, specialised from the generic `LoopSpace`. -/
abbrev CircleLoopSpace : Type u :=
  LoopSpace Circle circleBase

/-- Loop quotient of the circle, i.e. π₁(S¹) before imposing integer equivalence. -/
abbrev CircleLoopQuot : Type u :=
  LoopQuot Circle circleBase

/-- Strict loop group carried by the circle's rewrite quotient. -/
abbrev circleLoopGroup : LoopGroup Circle circleBase :=
  loopGroup Circle circleBase

/-- Fundamental group π₁(S¹, base) as rewrite classes of loops. -/
abbrev circlePiOne : Type u :=
  PiOne Circle circleBase

/-- Strict group structure on π₁(S¹, base). -/
abbrev circlePiOneGroup : LoopGroup Circle circleBase :=
  PiOneGroup Circle circleBase

/-- The distinguished fundamental loop as an inhabitant of the circle loop space. -/
@[simp] def circleLoopPath : CircleLoopSpace :=
  circleLoop

/-- Fundamental loop represented in the quotient. -/
@[simp] def circleLoopClass : CircleLoopQuot :=
  LoopQuot.ofLoop (A := Circle) (a := circleBase) circleLoop

/-- The fundamental loop seen as an element of π₁(S¹). -/
@[simp] def circlePiOneLoop : circlePiOne :=
  PiOne.ofLoop (A := Circle) (a := circleBase) circleLoop

/-- Iterate the fundamental loop `n` times in the quotient. -/
def circleLoopPow (n : Nat) : CircleLoopQuot :=
  LoopQuot.pow (A := Circle) (a := circleBase) circleLoopClass n

@[simp] theorem circleLoopPow_zero : circleLoopPow 0 = LoopQuot.id :=
  LoopQuot.pow_zero (A := Circle) (a := circleBase) circleLoopClass

@[simp] theorem circleLoopPow_succ (n : Nat) :
    circleLoopPow n.succ =
      LoopQuot.comp (circleLoopPow n) circleLoopClass :=
  LoopQuot.pow_succ (A := Circle) (a := circleBase)
    circleLoopClass n

@[simp] theorem circleLoopPow_one :
    circleLoopPow 1 = circleLoopClass := by
  unfold circleLoopPow
  exact
    LoopQuot.pow_one (A := Circle) (a := circleBase)
      (x := circleLoopClass)

theorem circleLoopPow_add (m n : Nat) :
    circleLoopPow (m + n) =
      LoopQuot.comp (circleLoopPow m) (circleLoopPow n) :=
  LoopQuot.pow_add (A := Circle) (a := circleBase)
    (x := circleLoopClass) m n

/-- Compatibility of `π₁` multiplication with `circleLoopPow`. -/
@[simp] theorem circlePiOne_mul_pow (m n : Nat) :
    PiOne.mul (A := Circle) (a := circleBase)
      (circleLoopPow m) (circleLoopPow n) =
      circleLoopPow (m + n) := by
  change LoopQuot.comp (circleLoopPow m) (circleLoopPow n) =
    circleLoopPow (m + n)
  exact (circleLoopPow_add (m := m) (n := n)).symm

/-- Iterate the fundamental loop an integer number of times. -/
def circleLoopZPow (z : Int) : CircleLoopQuot :=
  LoopQuot.zpow (A := Circle) (a := circleBase) circleLoopClass z

@[simp] theorem circleLoopZPow_ofNat (n : Nat) :
    circleLoopZPow n = circleLoopPow n := rfl

/-- Integer powers in π₁ agree with the explicit loop z-powers. -/
@[simp] theorem circlePiOne_zpow (z : Int) :
    PiOne.zpow (A := Circle) (a := circleBase)
      circleLoopClass z = circleLoopZPow z := rfl

@[simp] theorem circleLoopZPow_zero :
    circleLoopZPow 0 = LoopQuot.id := by
  unfold circleLoopZPow
  exact
    LoopQuot.zpow_zero (A := Circle) (a := circleBase) circleLoopClass

@[simp] theorem circleLoopZPow_one :
    circleLoopZPow 1 = circleLoopClass := by
  unfold circleLoopZPow
  exact
    LoopQuot.zpow_one (A := Circle) (a := circleBase) circleLoopClass

@[simp] theorem circleLoopZPow_negSucc (n : Nat) :
    circleLoopZPow (Int.negSucc n) =
      LoopQuot.inv (circleLoopPow (Nat.succ n)) := rfl

@[simp] theorem circleLoopZPow_neg_one :
    circleLoopZPow (-1) = LoopQuot.inv circleLoopClass := by
  unfold circleLoopZPow
  exact
    LoopQuot.zpow_neg_one (A := Circle) (a := circleBase) circleLoopClass

@[simp] theorem circleLoopZPow_neg (z : Int) :
    circleLoopZPow (-z) = LoopQuot.inv (circleLoopZPow z) := by
  unfold circleLoopZPow
  exact
    LoopQuot.zpow_neg (A := Circle) (a := circleBase)
      (x := circleLoopClass) z

@[simp] theorem circleLoopZPow_ofNat_add (m n : Nat) :
    circleLoopZPow (Int.ofNat m + Int.ofNat n) =
      LoopQuot.comp (circleLoopZPow (Int.ofNat m))
        (circleLoopZPow (Int.ofNat n)) := by
  exact
    LoopQuot.zpow_ofNat_add (A := Circle) (a := circleBase)
      (x := circleLoopClass) m n

/-- Integer addition rule for iterated circle loops. -/
@[simp] theorem circleLoopZPow_add (m n : Int) :
    circleLoopZPow (m + n) =
      LoopQuot.comp (circleLoopZPow m) (circleLoopZPow n) := by
  unfold circleLoopZPow
  exact
    LoopQuot.zpow_add (A := Circle) (a := circleBase)
      (x := circleLoopClass) m n

/-- Decode map ℤ → π₁(S¹), built by iterating the fundamental loop according
to the given integer.  The accompanying lemmas establish its homomorphic
behaviour. -/
def circleDecodeConcrete : Int → CircleLoopQuot :=
  circleLoopZPow

@[simp] theorem circleDecodeConcrete_ofNat (n : Nat) :
    circleDecodeConcrete (Int.ofNat n) = circleLoopPow n := rfl

@[simp] theorem circleDecodeConcrete_ofNat_succ (n : Nat) :
    circleDecodeConcrete (Int.ofNat n.succ) =
      LoopQuot.comp (circleLoopPow n) circleLoopClass := by
  calc
    circleDecodeConcrete (Int.ofNat (Nat.succ n))
        = circleLoopPow (Nat.succ n) :=
            circleDecodeConcrete_ofNat (Nat.succ n)
    _ = LoopQuot.comp (circleLoopPow n) circleLoopClass :=
            circleLoopPow_succ (n := n)

@[simp] theorem circleDecodeConcrete_negSucc (n : Nat) :
    circleDecodeConcrete (Int.negSucc n) =
      LoopQuot.inv (circleLoopPow (Nat.succ n)) := by
  unfold circleDecodeConcrete
  exact circleLoopZPow_negSucc (n := n)

@[simp] theorem circleDecodeConcrete_neg_one :
    circleDecodeConcrete (-1) = LoopQuot.inv circleLoopClass := by
  unfold circleDecodeConcrete
  exact circleLoopZPow_neg_one

@[simp] theorem circleDecodeConcrete_zero :
    circleDecodeConcrete 0 = LoopQuot.id :=
  circleLoopZPow_zero

@[simp] theorem circleDecodeConcrete_one :
    circleDecodeConcrete 1 = circleLoopClass :=
  circleLoopZPow_one

@[simp] theorem circleDecodeConcrete_neg (z : Int) :
    circleDecodeConcrete (-z) =
      LoopQuot.inv (circleDecodeConcrete z) :=
  circleLoopZPow_neg (z := z)

/-- Decoding respects integer addition. -/
@[simp] theorem circleDecodeConcrete_add (m n : Int) :
    circleDecodeConcrete (m + n) =
      LoopQuot.comp (circleDecodeConcrete m)
        (circleDecodeConcrete n) :=
  circleLoopZPow_add (m := m) (n := n)

/-- Subtraction law for the concrete decoder. -/
theorem circleDecodeConcrete_sub (m n : Int) :
    circleDecodeConcrete (m - n) =
      LoopQuot.comp (circleDecodeConcrete m)
        (LoopQuot.inv (circleDecodeConcrete n)) := by
  simpa only [Int.sub_eq_add_neg, circleDecodeConcrete_neg,
    Int.add_comm, Int.add_left_comm, Int.add_assoc]
    using circleDecodeConcrete_add (m := m) (n := -n)

@[simp] theorem circleLoopGroup_mul_decodeConcrete (m n : Int) :
    circleLoopGroup.mul (circleDecodeConcrete m)
        (circleDecodeConcrete n) =
      circleDecodeConcrete (m + n) := by
  change
    LoopQuot.comp (circleDecodeConcrete m)
      (circleDecodeConcrete n) =
        circleDecodeConcrete (m + n)
  exact
    (circleDecodeConcrete_add (m := m) (n := n)).symm

@[simp] theorem circlePiOneGroup_mul_decodeConcrete (m n : Int) :
    circlePiOneGroup.mul (circleDecodeConcrete m)
        (circleDecodeConcrete n) =
      circleDecodeConcrete (m + n) := by
  change
    circleLoopGroup.mul (circleDecodeConcrete m)
        (circleDecodeConcrete n) =
      circleDecodeConcrete (m + n)
  exact
    circleLoopGroup_mul_decodeConcrete (m := m) (n := n)

theorem circleLoopGroup_mul_decodeConcrete_sub (m n : Int) :
    circleLoopGroup.mul (circleDecodeConcrete m)
        (LoopQuot.inv (circleDecodeConcrete n)) =
      circleDecodeConcrete (m - n) := by
  change
    LoopQuot.comp (circleDecodeConcrete m)
        (LoopQuot.inv (circleDecodeConcrete n)) =
      circleDecodeConcrete (m - n)
  exact (circleDecodeConcrete_sub (m := m) (n := n)).symm

@[simp] theorem circleDecodeConcrete_ofNat_add (m n : Nat) :
    circleDecodeConcrete (Int.ofNat m + Int.ofNat n) =
      LoopQuot.comp (circleDecodeConcrete (Int.ofNat m))
        (circleDecodeConcrete (Int.ofNat n)) :=
  circleLoopZPow_ofNat_add (m := m) (n := n)

/-- Baseline data describing how π₁(S¹) will be related to ℤ.

These fields capture the encode/decode functions and the coherence facts we
plan to establish.  They are left as axioms for now so downstream developments
can proceed against a stable interface; future work will inhabit this record
with actual constructions derived from the higher-inductive semantics.
-/
structure CircleFundamentalGroupPlan where
  /-- Map loops on the circle to integers (winding number). -/
  encode : CircleLoopQuot → Int
  /-- Encoding respects loop multiplication. -/
  encode_mul : ∀ x y, encode (LoopQuot.comp x y) = encode x + encode y
  /-- Encoding sends the identity loop to zero. -/
  encode_one : encode LoopQuot.id = 0
  /-- Encoding sends inverses to negation. -/
  encode_inv : ∀ x, encode (LoopQuot.inv x) = - encode x
  /-- Map integers back to loops (iterated fundamental loop). -/
  decode : Int → CircleLoopQuot
  /-- The abstract decoder coincides with the concrete iteration of loops. -/
  decode_eq_concrete : ∀ n, decode n = circleDecodeConcrete n
  /-- Encode then decode yields the original integer. -/
  encode_decode : ∀ n, encode (decode n) = n
  /-- Decode then encode yields the original loop class. -/
  decode_encode : ∀ x, decode (encode x) = x

/-- Placeholder axiom instantiating the planned equivalence between π₁(S¹)
and ℤ.  The eventual formalisation will replace this axiom with an actual
construction built from the rewrite-normalised HIT semantics. -/
axiom circleFundamentalGroupPlan : CircleFundamentalGroupPlan

/-- Concrete interface for the planned equivalence between `CircleLoopQuot`
and `ℤ`.  All definitions and lemmas below are mere wrappers around the
fields of `circleFundamentalGroupPlan`, providing ergonomic names for
downstream developments. -/
@[simp] def circleEncode : CircleLoopQuot → Int :=
  circleFundamentalGroupPlan.encode

@[simp] def circleDecode : Int → CircleLoopQuot :=
  circleFundamentalGroupPlan.decode

@[simp] theorem circleDecode_eq_concrete (n : Int) :
    circleDecode n = circleDecodeConcrete n :=
  circleFundamentalGroupPlan.decode_eq_concrete n

@[simp] theorem circleEncode_mul (x y : CircleLoopQuot) :
    circleEncode (LoopQuot.comp x y) =
      circleEncode x + circleEncode y :=
  circleFundamentalGroupPlan.encode_mul x y

@[simp] theorem circleEncode_one : circleEncode LoopQuot.id = 0 :=
  circleFundamentalGroupPlan.encode_one

@[simp] theorem circleEncode_inv (x : CircleLoopQuot) :
    circleEncode (LoopQuot.inv x) = - circleEncode x :=
  circleFundamentalGroupPlan.encode_inv x

@[simp] theorem circleDecode_add (m n : Int) :
    circleDecode (m + n) =
      LoopQuot.comp (circleDecode m) (circleDecode n) :=
  by
    have hSum := circleDecode_eq_concrete (n := m + n)
    have hm := circleDecode_eq_concrete (n := m)
    have hn := circleDecode_eq_concrete (n := n)
    rw [hSum, circleDecodeConcrete_add (m := m) (n := n), hm, hn]

@[simp] theorem circleDecode_zero : circleDecode 0 = LoopQuot.id :=
  by
    have h := circleDecode_eq_concrete (n := 0)
    rw [h, circleDecodeConcrete_zero]

@[simp] theorem circleDecode_ofNat (n : Nat) :
    circleDecode (Int.ofNat n) = circleLoopPow n := by
  calc
    circleDecode (Int.ofNat n)
        = circleDecodeConcrete (Int.ofNat n) :=
            circleDecode_eq_concrete (n := Int.ofNat n)
    _ = circleLoopPow n := circleDecodeConcrete_ofNat n

@[simp] theorem circleDecode_ofNat_succ (n : Nat) :
    circleDecode (Int.ofNat n.succ) =
      LoopQuot.comp (circleLoopPow n) circleLoopClass := by
  calc
    circleDecode (Int.ofNat (Nat.succ n))
        = circleDecodeConcrete (Int.ofNat (Nat.succ n)) :=
            circleDecode_eq_concrete (n := Int.ofNat (Nat.succ n))
    _ = LoopQuot.comp (circleLoopPow n) circleLoopClass :=
            circleDecodeConcrete_ofNat_succ (n := n)

@[simp] theorem circleDecode_one : circleDecode 1 = circleLoopClass := by
  calc
    circleDecode 1
        = circleDecode (Int.ofNat 1) := rfl
    _ = circleLoopPow 1 := circleDecode_ofNat 1
    _ = circleLoopClass := circleLoopPow_one

@[simp] theorem circleDecode_neg (n : Int) :
    circleDecode (-n) = LoopQuot.inv (circleDecode n) :=
  by
    have hInv :=
      _root_.congrArg LoopQuot.inv
        (circleDecode_eq_concrete (n := n)).symm
    calc
      circleDecode (-n)
          = circleDecodeConcrete (-n) :=
              circleDecode_eq_concrete (n := -n)
      _ = LoopQuot.inv (circleDecodeConcrete n) :=
              circleDecodeConcrete_neg (z := n)
      _ = LoopQuot.inv (circleDecode n) := hInv

@[simp] theorem circleDecode_negSucc (n : Nat) :
    circleDecode (Int.negSucc n) =
      LoopQuot.inv (circleLoopPow (Nat.succ n)) := by
  calc
    circleDecode (Int.negSucc n)
        = circleDecodeConcrete (Int.negSucc n) :=
            circleDecode_eq_concrete (n := Int.negSucc n)
    _ = LoopQuot.inv (circleLoopPow (Nat.succ n)) :=
            circleDecodeConcrete_negSucc (n := n)

@[simp] theorem circleDecode_neg_one :
    circleDecode (-1) = LoopQuot.inv circleLoopClass := by
  calc
    circleDecode (-1)
        = circleDecodeConcrete (-1) :=
            circleDecode_eq_concrete (n := -1)
    _ = LoopQuot.inv circleLoopClass := circleDecodeConcrete_neg_one

theorem circleDecode_sub (m n : Int) :
    circleDecode (m - n) =
      LoopQuot.comp (circleDecode m) (LoopQuot.inv (circleDecode n)) := by
  simpa only [Int.sub_eq_add_neg, circleDecode_neg,
    Int.add_comm, Int.add_left_comm, Int.add_assoc]
    using circleDecode_add (m := m) (n := -n)

@[simp] theorem circleEncode_decode (n : Int) :
    circleEncode (circleDecode n) = n :=
  circleFundamentalGroupPlan.encode_decode n

@[simp] theorem circleDecode_encode (x : CircleLoopQuot) :
    circleDecode (circleEncode x) = x :=
  circleFundamentalGroupPlan.decode_encode x

/-- `circleLoopZPow` is left-inverse to `circleEncode`. -/
@[simp] theorem circleEncode_circleLoopZPow (z : Int) :
    circleEncode (circleLoopZPow z) = z := by
  have hz := circleDecode_eq_concrete (n := z)
  have h := (_root_.congrArg circleEncode hz) ▸ circleEncode_decode (n := z)
  dsimp [circleDecodeConcrete] at h
  exact h

/-- `circleLoopZPow` is right-inverse to `circleEncode`. -/
@[simp] theorem circleLoopZPow_encode (x : CircleLoopQuot) :
    circleLoopZPow (circleEncode x) = x := by
  have hx := circleDecode_eq_concrete (n := circleEncode x)
  have h := hx ▸ circleDecode_encode (x := x)
  dsimp [circleDecodeConcrete] at h
  exact h

theorem circleEncode_leftInverse :
    Function.LeftInverse circleEncode circleLoopZPow :=
  fun z => circleEncode_circleLoopZPow (z := z)

theorem circleEncode_rightInverse :
    Function.RightInverse circleEncode circleLoopZPow :=
  fun x => circleLoopZPow_encode (x := x)

theorem circleLoopZPow_injective :
    Function.Injective circleLoopZPow :=
  circleEncode_leftInverse.injective

theorem circleLoopZPow_surjective :
    Function.Surjective circleLoopZPow :=
  circleEncode_rightInverse.surjective

theorem circleLoopZPow_eq_iff (z₁ z₂ : Int) :
    circleLoopZPow z₁ = circleLoopZPow z₂ ↔ z₁ = z₂ :=
  circleLoopZPow_injective.eq_iff

theorem circleLoopZPow_exists (x : CircleLoopQuot) :
    ∃ z : Int, circleLoopZPow z = x :=
  circleLoopZPow_surjective x

theorem circleLoopZPow_exists_unique (x : CircleLoopQuot) :
    ∃ z : Int, circleLoopZPow z = x ∧
        ∀ z', circleLoopZPow z' = x → z' = z := by
  refine ⟨circleEncode x, circleLoopZPow_encode (x := x), ?_⟩
  intro z' hz'
  have hEncode := _root_.congrArg circleEncode hz'
  have hzPow := circleEncode_circleLoopZPow (z := z')
  calc
    z' = circleEncode (circleLoopZPow z') := hzPow.symm
    _ = circleEncode x := hEncode

theorem circleLoopZPow_exists_unique_left (x : CircleLoopQuot) :
    ∃ z : Int, x = circleLoopZPow z ∧
        ∀ z', x = circleLoopZPow z' → z' = z := by
  obtain ⟨z, hz, huniq⟩ := circleLoopZPow_exists_unique x
  refine ⟨z, hz.symm, ?_⟩
  intro z' hz'
  exact huniq z' hz'.symm

theorem circleEncode_injective : Function.Injective circleEncode := by
  intro x y h
  have hx := _root_.congrArg circleLoopZPow h
  have hxLeft := (circleLoopZPow_encode (x := x)).symm
  have hxRight := circleLoopZPow_encode (x := y)
  exact hxLeft.trans (hx.trans hxRight)

@[simp] theorem circleLoopQuot_eq_iff_encode_eq (x y : CircleLoopQuot) :
    x = y ↔ circleEncode x = circleEncode y := by
  constructor
  · intro h; cases h; rfl
  · intro h; exact circleEncode_injective h

@[simp] theorem circleLoopGroup_mul_comm (x y : CircleLoopQuot) :
    circleLoopGroup.mul x y = circleLoopGroup.mul y x := by
  apply circleEncode_injective
  have hx := circleEncode_mul x y
  have hy := circleEncode_mul y x
  calc
    circleEncode (circleLoopGroup.mul x y)
        = circleEncode x + circleEncode y := hx
    _ = circleEncode y + circleEncode x := by
          exact Int.add_comm _ _
    _ = circleEncode (circleLoopGroup.mul y x) := hy.symm

@[simp] theorem circlePiOne_eq_iff_encode_eq (x y : circlePiOne) :
    x = y ↔ circleEncode x = circleEncode y :=
  circleLoopQuot_eq_iff_encode_eq (x := x) (y := y)

@[simp] theorem circlePiOneGroup_mul_comm (x y : circlePiOne) :
    circlePiOneGroup.mul x y = circlePiOneGroup.mul y x := by
  apply circleEncode_injective
  have hx := circleEncode_mul x y
  have hy := circleEncode_mul y x
  calc
    circleEncode (circlePiOneGroup.mul x y)
        = circleEncode x + circleEncode y := hx
    _ = circleEncode y + circleEncode x := by
          exact Int.add_comm _ _
    _ = circleEncode (circlePiOneGroup.mul y x) := hy.symm

/-- Winding-number terminology for the map `π₁(S¹) → ℤ`. -/
@[simp] def circleWindingNumber : circlePiOne → Int :=
  circleEncode

/-- Iterate the fundamental loop according to an integer. -/
@[simp] def circleLoopFromInt : Int → circlePiOne :=
  circleLoopZPow

@[simp] theorem circleWindingNumber_mul (x y : circlePiOne) :
    circleWindingNumber (circlePiOneGroup.mul x y) =
      circleWindingNumber x + circleWindingNumber y :=
  circleEncode_mul x y

@[simp] theorem circleWindingNumber_one :
    circleWindingNumber circlePiOneGroup.one = 0 :=
  circleEncode_one

@[simp] theorem circleWindingNumber_inv (x : circlePiOne) :
    circleWindingNumber (circlePiOneGroup.inv x) =
      - circleWindingNumber x :=
  circleEncode_inv x

@[simp] theorem circleLoopFromInt_add (m n : Int) :
    circleLoopFromInt (m + n) =
      circlePiOneGroup.mul (circleLoopFromInt m) (circleLoopFromInt n) := by
  exact circleLoopZPow_add (m := m) (n := n)

@[simp] theorem circleLoopFromInt_zero :
    circleLoopFromInt 0 = circlePiOneGroup.one :=
  circleLoopZPow_zero

@[simp] theorem circleLoopFromInt_one :
    circleLoopFromInt 1 = circleLoopClass :=
  circleLoopZPow_one

@[simp] theorem circleLoopFromInt_neg (m : Int) :
    circleLoopFromInt (-m) =
      circlePiOneGroup.inv (circleLoopFromInt m) :=
  circleLoopZPow_neg (z := m)

theorem circleLoopFromInt_exists_unique (x : circlePiOne) :
    ∃ z : Int, x = circleLoopFromInt z ∧
        ∀ z', x = circleLoopFromInt z' → z' = z :=
  circleLoopZPow_exists_unique_left (x := x)

@[simp] theorem circleEncode_circleLoopClass :
    circleEncode circleLoopClass = 1 := by
  have h := circleEncode_circleLoopZPow (z := 1)
  have hz := circleLoopZPow_one
  exact hz ▸ h

@[simp] theorem circleEncode_circleLoopPow (n : Nat) :
    circleEncode (circleLoopPow n) = Int.ofNat n := by
  have h := circleEncode_circleLoopZPow (z := Int.ofNat n)
  have hz := circleLoopZPow_ofNat (n := n)
  exact hz ▸ h

/-- Lightweight equivalence witness specialised to the circle fundamental
group.  We record the forward and inverse maps together with their inverse
laws, packaged separately from Lean's absent `Equiv` infrastructure. -/
structure CircleLoopQuotEquivInt where
  toFun : CircleLoopQuot → Int
  invFun : Int → CircleLoopQuot
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ n, toFun (invFun n) = n

/-- The promised equivalence between `CircleLoopQuot` and `ℤ`. -/
def circleLoopQuotEquivInt : CircleLoopQuotEquivInt where
  toFun := circleEncode
  invFun := circleDecode
  left_inv := circleDecode_encode
  right_inv := circleEncode_decode

/-- Equivalence between the strict loop group on the circle and the additive
group of integers.  This repackages the encode/decode data so downstream
clients can refer directly to the `circleLoopGroup` operations without
unfolding the quotient-level definitions. -/
structure CircleLoopGroupEquivInt where
  toFun : CircleLoopQuot → Int
  invFun : Int → CircleLoopQuot
  map_mul : ∀ x y,
      toFun (circleLoopGroup.mul x y) = toFun x + toFun y
  map_one : toFun circleLoopGroup.one = 0
  map_inv : ∀ x,
      toFun (circleLoopGroup.inv x) = - toFun x
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ n, toFun (invFun n) = n

/-- The concrete strict loop-group equivalence between π₁(S¹) (with its
canonical group structure) and ℤ. -/
@[simp] def circleLoopGroupEquivInt : CircleLoopGroupEquivInt where
  toFun := circleEncode
  invFun := circleDecode
  map_mul := by
    intro x y
    exact circleEncode_mul x y
  map_one := circleEncode_one
  map_inv := by
    intro x
    exact circleEncode_inv x
  left_inv := circleDecode_encode
  right_inv := circleEncode_decode

@[simp] theorem circleLoopGroup_mul_decode (m n : Int) :
    circleLoopGroup.mul (circleDecode m) (circleDecode n) =
      circleDecode (m + n) := by
  exact (circleDecode_add m n).symm

@[simp] theorem circleLoopGroup_mul_decode_ofNat_succ (n : Nat) :
    circleLoopGroup.mul (circleDecode (Int.ofNat n)) circleLoopClass =
      circleDecode (Int.ofNat n.succ) := by
  have hMul :=
    circleLoopGroup_mul_decode (m := Int.ofNat n) (n := 1)
  have hBase :
      circleLoopGroup.mul (circleDecode (Int.ofNat n)) circleLoopClass =
        circleDecode (Int.ofNat n + 1) := by
    simpa only [circleLoopClass, circleDecode_one] using hMul
  have hAdd :=
    circleDecode_add (m := Int.ofNat n) (n := 1)
  have hAdd' :
      circleDecode (Int.ofNat n + 1) =
        LoopQuot.comp (circleLoopPow n) circleLoopClass := by
    simpa only [circleDecode_ofNat, circleLoopClass, circleDecode_one]
      using hAdd
  have hSucc :
      circleDecode (Int.ofNat n.succ) =
        LoopQuot.comp (circleLoopPow n) circleLoopClass :=
          circleDecode_ofNat_succ (n := n)
  have hEq :
      circleDecode (Int.ofNat n + 1) =
        circleDecode (Int.ofNat n.succ) :=
    hAdd'.trans hSucc.symm
  exact hBase.trans hEq

@[simp] theorem circleLoopGroup_inv_decode (n : Int) :
    circleLoopGroup.inv (circleDecode n) = circleDecode (-n) := by
  change LoopQuot.inv (circleDecode n) = circleDecode (-n)
  exact (circleDecode_neg (n := n)).symm

theorem circleLoopGroup_mul_decode_sub (m n : Int) :
    circleLoopGroup.mul (circleDecode m)
        (LoopQuot.inv (circleDecode n)) =
      circleDecode (m - n) := by
  change
    LoopQuot.comp (circleDecode m) (LoopQuot.inv (circleDecode n)) =
      circleDecode (m - n)
  exact (circleDecode_sub (m := m) (n := n)).symm

/-- Final statement: the strict loop group of the circle is isomorphic to the
additive group of integers. -/
@[simp] def fundamentalGroupCircle : CircleLoopGroupEquivInt :=
  circleLoopGroupEquivInt

/-- Equivalence between π₁(S¹, base) and ℤ. -/
structure CirclePiOneEquivInt where
  toFun : circlePiOne → Int
  invFun : Int → circlePiOne
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ n, toFun (invFun n) = n

/-- Concrete π₁-ℤ equivalence mirroring `circleLoopQuotEquivInt`. -/
def circlePiOneEquivInt : CirclePiOneEquivInt where
  toFun := circleEncode
  invFun := circleDecode
  left_inv := circleDecode_encode
  right_inv := circleEncode_decode

/-- Group-level equivalence phrased directly for π₁(S¹, base). -/
structure CirclePiOneGroupEquivInt where
  toFun : circlePiOne → Int
  invFun : Int → circlePiOne
  map_mul : ∀ x y,
      toFun (circlePiOneGroup.mul x y) = toFun x + toFun y
  map_one : toFun circlePiOneGroup.one = 0
  map_inv : ∀ x,
      toFun (circlePiOneGroup.inv x) = - toFun x
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ n, toFun (invFun n) = n

/-- Strict π₁ equivalence packaged at the group level. -/
@[simp] def circlePiOneGroupEquivInt : CirclePiOneGroupEquivInt where
  toFun := circleEncode
  invFun := circleDecode
  map_mul := by
    intro x y
    exact circleEncode_mul x y
  map_one := circleEncode_one
  map_inv := by
    intro x
    exact circleEncode_inv x
  left_inv := circleDecode_encode
  right_inv := circleEncode_decode

@[simp] theorem circlePiOneGroup_mul_decode (m n : Int) :
    circlePiOneGroup.mul (circleDecode m) (circleDecode n) =
      circleDecode (m + n) := by
  change circleLoopGroup.mul (circleDecode m) (circleDecode n) =
    circleDecode (m + n)
  exact circleLoopGroup_mul_decode m n

@[simp] theorem circlePiOneGroup_mul_decode_ofNat_succ (n : Nat) :
    circlePiOneGroup.mul (circleDecode (Int.ofNat n)) circleLoopClass =
      circleDecode (Int.ofNat n.succ) := by
  change
    circleLoopGroup.mul (circleDecode (Int.ofNat n)) circleLoopClass =
      circleDecode (Int.ofNat n.succ)
  exact circleLoopGroup_mul_decode_ofNat_succ (n := n)

@[simp] theorem circlePiOneGroup_inv_decode (n : Int) :
    circlePiOneGroup.inv (circleDecode n) = circleDecode (-n) := by
  change circleLoopGroup.inv (circleDecode n) = circleDecode (-n)
  exact circleLoopGroup_inv_decode (n := n)

theorem circlePiOneGroup_mul_decode_sub (m n : Int) :
    circlePiOneGroup.mul (circleDecode m)
        (LoopQuot.inv (circleDecode n)) =
      circleDecode (m - n) := by
  change
    circleLoopGroup.mul (circleDecode m)
        (LoopQuot.inv (circleDecode n)) =
      circleDecode (m - n)
  exact circleLoopGroup_mul_decode_sub (m := m) (n := n)

/-- Final statement: π₁(S¹, base) (with its strict group structure) is ℤ. -/
@[simp] def fundamentalGroupCirclePiOne :
    CirclePiOneGroupEquivInt :=
  circlePiOneGroupEquivInt

end

end Path
end ComputationalPaths
