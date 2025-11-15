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
open scoped Classical

/-- Loop space of the circle, specialised from the generic `LoopSpace`. -/
abbrev CircleLoopSpace : Type u :=
  LoopSpace Circle circleBase

/-- Loop quotient of the circle, i.e. π₁(S¹) before imposing integer equivalence. -/
abbrev CircleLoopQuot : Type u :=
  LoopQuot Circle circleBase

/-- Strict loop group carried by the circle's rewrite quotient. -/
abbrev circleLoopGroup : LoopGroup Circle circleBase :=
  loopGroup Circle circleBase

/-- The distinguished fundamental loop as an inhabitant of the circle loop space. -/
@[simp] def circleLoopPath : CircleLoopSpace :=
  circleLoop

/-- Fundamental loop represented in the quotient. -/
@[simp] def circleLoopClass : CircleLoopQuot :=
  LoopQuot.ofLoop (A := Circle) (a := circleBase) circleLoop

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

/-- Iterate the fundamental loop an integer number of times. -/
def circleLoopZPow (z : Int) : CircleLoopQuot :=
  LoopQuot.zpow (A := Circle) (a := circleBase) circleLoopClass z

@[simp] theorem circleLoopZPow_ofNat (n : Nat) :
    circleLoopZPow n = circleLoopPow n := rfl

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

/-- **(Thesis Ch. 5, Lemma 5.22)** Every loop class on the circle is uniquely
determined by an integer power of the fundamental loop.  This captures the
statement “all paths generated by `loop` are of the form `loop^{n}` with
`n ∈ ℤ`”. -/
axiom circleLoopQuot_cyclic :
  ∀ x : CircleLoopQuot, ∃ z : Int,
    x = circleLoopZPow z ∧
    ∀ z', x = circleLoopZPow z' → z' = z

/-- **(Thesis Ch. 5, Proposition “loopⁿ ∘ loopᵐ = loopⁿ⁺ᵐ”)** Composition in
the fundamental group corresponds to integer addition of iterated loops. -/
axiom circleLoopZPow_add (m n : Int) :
    circleLoopZPow (m + n) =
      LoopQuot.comp (circleLoopZPow m) (circleLoopZPow n)

/-- Concrete candidate for the decode map ℤ → π₁(S¹), built by
iterating the fundamental loop according to the given integer.  Later we
will show that this satisfies the planned decode axioms. -/
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

theorem circleDecodeConcrete_ofNat_add (m n : Nat) :
    circleDecodeConcrete (Int.ofNat m + Int.ofNat n) =
      LoopQuot.comp (circleDecodeConcrete (Int.ofNat m))
        (circleDecodeConcrete (Int.ofNat n)) :=
  circleLoopZPow_ofNat_add (m := m) (n := n)

@[simp] theorem circleDecodeConcrete_add (m n : Int) :
    circleDecodeConcrete (m + n) =
      LoopQuot.comp (circleDecodeConcrete m) (circleDecodeConcrete n) :=
  circleLoopZPow_add m n

/-- Concrete collection of facts about `circleDecodeConcrete`.  This record is
used as a stepping stone toward the full encode/decode equivalence, recording
the algebraic laws already verified in Lean (now including full integer
addition).  Additional fields can be appended later if more structure is
needed by downstream developments. -/
structure CircleDecodeConcreteData where
  /-- Decoder sending integers to loop classes. -/
  decode : Int → CircleLoopQuot
  /-- Decoder agrees with the explicit natural iteration of the loop. -/
  ofNat_eq : ∀ n : Nat, decode (Int.ofNat n) = circleLoopPow n
  /-- Decoder sends zero to the identity loop. -/
  zero_eq : decode 0 = LoopQuot.id
  /-- Decoder sends one to the fundamental loop class. -/
  one_eq : decode 1 = circleLoopClass
  /-- Decoder transports additive inverses to loop inverses. -/
  neg_eq : ∀ z, decode (-z) = LoopQuot.inv (decode z)
  /-- Decoder respects addition on naturals embedded in the integers. -/
  ofNat_add_eq : ∀ m n : Nat,
      decode (Int.ofNat m + Int.ofNat n) =
        LoopQuot.comp (decode (Int.ofNat m)) (decode (Int.ofNat n))
  /-- Decoder respects arbitrary integer addition (full axiom). -/
  add_eq : ∀ m n : Int,
      decode (m + n) =
        LoopQuot.comp (decode m) (decode n)

/-- Witness showing that `circleDecodeConcrete` satisfies the verified
decoder laws, including the full integer-addition axiom provided by
`circleLoopZPow_add`. -/
@[simp] def circleDecodeConcreteData : CircleDecodeConcreteData where
  decode := circleDecodeConcrete
  ofNat_eq := circleDecodeConcrete_ofNat
  zero_eq := circleDecodeConcrete_zero
  one_eq := circleDecodeConcrete_one
  neg_eq := circleDecodeConcrete_neg
  ofNat_add_eq := circleDecodeConcrete_ofNat_add
  add_eq := circleDecodeConcrete_add

/-- Concrete encoder turning any loop class into the corresponding integer
winding number (Thesis Ch. 5, “toInteger”).  It is defined via the uniqueness
witness supplied by `circleLoopQuot_cyclic`. -/
noncomputable def circleEncodeConcrete (x : CircleLoopQuot) : Int :=
  Classical.choose (circleLoopQuot_cyclic x)

@[simp] theorem circleEncodeConcrete_spec (x : CircleLoopQuot) :
    x = circleLoopZPow (circleEncodeConcrete x) := by
  classical
  exact (Classical.choose_spec (circleLoopQuot_cyclic x)).1

theorem circleEncodeConcrete_eq_of (x : CircleLoopQuot) {z : Int}
    (hx : x = circleLoopZPow z) :
    circleEncodeConcrete x = z := by
  classical
  have huniq := (Classical.choose_spec (circleLoopQuot_cyclic x)).2
  have hz : z = circleEncodeConcrete x := huniq z hx
  exact hz.symm

@[simp] theorem circleEncodeConcrete_zpow (z : Int) :
    circleEncodeConcrete (circleLoopZPow z) = z :=
  circleEncodeConcrete_eq_of (x := circleLoopZPow z) (z := z) rfl

@[simp] theorem circleLoopZPow_encode (x : CircleLoopQuot) :
    circleLoopZPow (circleEncodeConcrete x) = x := by
  classical
  exact (circleEncodeConcrete_spec x).symm

@[simp] theorem circleEncodeConcrete_mul (x y : CircleLoopQuot) :
    circleEncodeConcrete (LoopQuot.comp x y) =
      circleEncodeConcrete x + circleEncodeConcrete y := by
  classical
  have hx := circleLoopZPow_encode x
  have hy := circleLoopZPow_encode y
  have h₁ :=
    _root_.congrArg
      (fun t => circleEncodeConcrete (LoopQuot.comp t y)) hx.symm
  have h₂ :=
    _root_.congrArg
      (fun t => circleEncodeConcrete
        (LoopQuot.comp (circleLoopZPow (circleEncodeConcrete x)) t)) hy.symm
  have h₃ :=
    _root_.congrArg circleEncodeConcrete
      (circleLoopZPow_add (circleEncodeConcrete x)
        (circleEncodeConcrete y)).symm
  have h₄ :=
    circleEncodeConcrete_zpow
      (circleEncodeConcrete x + circleEncodeConcrete y)
  exact h₁.trans (h₂.trans (h₃.trans h₄))

@[simp] theorem circleEncodeConcrete_one :
    circleEncodeConcrete LoopQuot.id = 0 := by
  have h₁ :=
    _root_.congrArg circleEncodeConcrete circleLoopZPow_zero.symm
  have h₂ := circleEncodeConcrete_zpow 0
  exact h₁.trans h₂

@[simp] theorem circleEncodeConcrete_inv (x : CircleLoopQuot) :
    circleEncodeConcrete (LoopQuot.inv x) =
      - circleEncodeConcrete x := by
  classical
  have hx := circleLoopZPow_encode x
  have h₁ :=
    _root_.congrArg (fun t => circleEncodeConcrete (LoopQuot.inv t)) hx.symm
  have h₂ :=
    _root_.congrArg circleEncodeConcrete
      (circleLoopZPow_neg (circleEncodeConcrete x)).symm
  have h₃ := circleEncodeConcrete_zpow (- circleEncodeConcrete x)
  exact h₁.trans (h₂.trans h₃)

/-- Baseline data describing how π₁(S¹) relates to ℤ.

The fields capture the encode/decode functions together with the coherence
facts required for the fundamental-group computation.  In the following
definition we instantiate this record with the concrete encoder/decoder built
from `circleLoopQuot_cyclic` and `circleLoopZPow_add`. -/
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

/-- Noncomputable instantiation of the planned equivalence between π₁(S¹)
and ℤ, using the concrete encoder/decoder derived from the cyclicity axioms. -/
noncomputable def circleFundamentalGroupPlan : CircleFundamentalGroupPlan where
  encode := circleEncodeConcrete
  decode := circleDecodeConcrete
  encode_mul := circleEncodeConcrete_mul
  encode_one := circleEncodeConcrete_one
  encode_inv := circleEncodeConcrete_inv
  decode_add := circleDecodeConcrete_add
  decode_zero := circleDecodeConcrete_zero
  decode_neg := circleDecodeConcrete_neg
  encode_decode := circleEncodeConcrete_zpow
  decode_encode := circleLoopZPow_encode

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

end

end Path
end ComputationalPaths
