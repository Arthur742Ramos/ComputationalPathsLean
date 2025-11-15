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
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup

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

noncomputable section

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

/-- Decode map ℤ → π₁(S¹), built by iterating the fundamental loop according
to the given integer.  The accompanying lemmas establish its homomorphic
behaviour. -/
def circleDecodeConcrete : Int → CircleLoopQuot :=
  circleLoopZPow

@[simp] theorem circleDecodeConcrete_ofNat (n : Nat) :
    circleDecodeConcrete (Int.ofNat n) = circleLoopPow n := rfl

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
  /-- Map integers back to loops (iterated fundamental loop). -/
  decode : Int → CircleLoopQuot
  /-- Encoding respects loop multiplication. -/
  encode_mul : ∀ x y, encode (LoopQuot.comp x y) = encode x + encode y
  /-- Encoding sends the identity loop to zero. -/
  encode_one : encode LoopQuot.id = 0
  /-- Encoding sends inverses to negation. -/
  encode_inv : ∀ x, encode (LoopQuot.inv x) = - encode x
  /-- Decoding respects integer addition. -/
  decode_add : ∀ m n, decode (m + n) = LoopQuot.comp (decode m) (decode n)
  /-- Decoding sends zero to the identity loop. -/
  decode_zero : decode 0 = LoopQuot.id
  /-- Decoding of negation yields inverse loops. -/
  decode_neg : ∀ n, decode (-n) = LoopQuot.inv (decode n)
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
  circleFundamentalGroupPlan.decode_add m n

@[simp] theorem circleDecode_zero : circleDecode 0 = LoopQuot.id :=
  circleFundamentalGroupPlan.decode_zero

@[simp] theorem circleDecode_neg (n : Int) :
    circleDecode (-n) = LoopQuot.inv (circleDecode n) :=
  circleFundamentalGroupPlan.decode_neg n

@[simp] theorem circleEncode_decode (n : Int) :
    circleEncode (circleDecode n) = n :=
  circleFundamentalGroupPlan.encode_decode n

@[simp] theorem circleDecode_encode (x : CircleLoopQuot) :
    circleDecode (circleEncode x) = x :=
  circleFundamentalGroupPlan.decode_encode x

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

/-- Final statement: the strict loop group of the circle is isomorphic to the
additive group of integers. -/
@[simp] def fundamentalGroupCircle : CircleLoopGroupEquivInt :=
  circleLoopGroupEquivInt

end

end Path
end ComputationalPaths
