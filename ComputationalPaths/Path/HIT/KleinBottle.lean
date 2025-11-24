/-
# The Klein bottle as a higher-inductive type (axiomatic skeleton)

This module follows the same pattern as `Circle` and `Torus`: we introduce an
abstract type equipped with the fundamental loops and the characteristic
surface relation `aba⁻¹ = b⁻¹`.  Providing this HIT-like API now lets us stage
the forthcoming fundamental-group calculation without committing to a concrete
realisation yet.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Basic.Univalence
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path

universe u v

/-- Abstract Klein bottle type. -/
axiom KleinBottle : Type u

/-- Distinguished point on the Klein bottle. -/
axiom kleinBase : KleinBottle

/-- Horizontal generator (`a` in the usual presentation). -/
axiom kleinLoopA : Path (A := KleinBottle) kleinBase kleinBase

/-- Vertical generator (`b` in the usual presentation). -/
axiom kleinLoopB : Path (A := KleinBottle) kleinBase kleinBase

/-- Surface relation encoding `a ⬝ b ⬝ a⁻¹ = b⁻¹`. -/
axiom kleinSurf :
  Path.trans
      (Path.trans kleinLoopA kleinLoopB)
      (Path.symm kleinLoopA) =
    Path.symm kleinLoopB

/-- Data required to eliminate from the Klein bottle into a target type `C`. -/
structure KleinBottleRecData (C : Type v) where
  base : C
  loopA : Path base base
  loopB : Path base base
  surf :
    Path.trans
        (Path.trans loopA loopB)
        (Path.symm loopA) =
      Path.symm loopB

/-- Recursor for the Klein bottle HIT skeleton. -/
axiom kleinRec {C : Type v} (data : KleinBottleRecData C) :
  KleinBottle → C

/-- �-rule for `kleinRec` at the base point. -/
axiom kleinRec_base {C : Type v} (data : KleinBottleRecData C) :
  kleinRec data kleinBase = data.base

/-- �-rule for the horizontal generator. -/
axiom kleinRec_loopA {C : Type v} (data : KleinBottleRecData C) :
  Path.trans
    (Path.symm (Path.ofEq (kleinRec_base (C := C) data)))
    (Path.trans
      (Path.congrArg (kleinRec data) kleinLoopA)
      (Path.ofEq (kleinRec_base (C := C) data))) =
  data.loopA

/-- �-rule for the vertical generator. -/
axiom kleinRec_loopB {C : Type v} (data : KleinBottleRecData C) :
  Path.trans
    (Path.symm (Path.ofEq (kleinRec_base (C := C) data)))
    (Path.trans
      (Path.congrArg (kleinRec data) kleinLoopB)
      (Path.ofEq (kleinRec_base (C := C) data))) =
  data.loopB

-- The full computation rule for `kleinSurf` involves two-dimensional path
-- algebra and will be stated once the corresponding globular machinery is ready.

/-- Data for the dependent eliminator of the Klein bottle. -/
structure KleinBottleIndData (C : KleinBottle → Type v) where
  base : C kleinBase
  loopA : Path (Path.transport (A := KleinBottle) (D := C) kleinLoopA base) base
  loopB : Path (Path.transport (A := KleinBottle) (D := C) kleinLoopB base) base
  -- Surface coherence is postponed, mirroring the torus development.

/-- Dependent eliminator (induction principle) for the Klein bottle. -/
axiom kleinInd {C : KleinBottle → Type v} (data : KleinBottleIndData C) :
  (x : KleinBottle) → C x

/-- �-rule for the dependent eliminator at the base point. -/
axiom kleinInd_base {C : KleinBottle → Type v} (data : KleinBottleIndData C) :
  kleinInd data kleinBase = data.base

/-- Dependent �-rule for the horizontal generator. -/
axiom kleinInd_loopA {C : KleinBottle → Type v} (data : KleinBottleIndData C) :
  Path.trans
    (Path.symm
      (Path.congrArg
        (fun x =>
          Path.transport (A := KleinBottle) (D := fun y => C y) kleinLoopA x)
        (Path.ofEq (kleinInd_base (C := C) data))))
    (Path.trans
      (Path.apd (A := KleinBottle) (B := fun y => C y)
        (f := kleinInd data) kleinLoopA)
      (Path.ofEq (kleinInd_base (C := C) data))) =
  data.loopA

/-- Dependent �-rule for the vertical generator. -/
axiom kleinInd_loopB {C : KleinBottle → Type v} (data : KleinBottleIndData C) :
  Path.trans
    (Path.symm
      (Path.congrArg
        (fun x =>
          Path.transport (A := KleinBottle) (D := fun y => C y) kleinLoopB x)
        (Path.ofEq (kleinInd_base (C := C) data))))
    (Path.trans
      (Path.apd (A := KleinBottle) (B := fun y => C y)
        (f := kleinInd data) kleinLoopB)
      (Path.ofEq (kleinInd_base (C := C) data))) =
  data.loopB

noncomputable section

section LoopAlgebra

/-- Parity-based sign `(-1)^m` used to describe the Klein bottle multiplication law. -/
def kleinSign (m : Int) : Int :=
  if m.natAbs % 2 = 0 then
    1
  else
    -1

@[simp] theorem kleinSign_zero : kleinSign 0 = 1 := by
  classical
  simp [kleinSign]

@[simp] theorem kleinSign_neg (m : Int) : kleinSign (-m) = kleinSign m := by
  classical
  unfold kleinSign
  have : (-m).natAbs = m.natAbs := Int.natAbs_neg _
  simp [this]

theorem kleinSign_sq (m : Int) :
    kleinSign m * kleinSign m = (1 : Int) := by
  classical
  by_cases h : m.natAbs % 2 = 0
  · simp [kleinSign, h]
  · simp [kleinSign, h]

@[simp] theorem kleinSign_ofNat (n : Nat) :
    kleinSign (Int.ofNat n) =
      if n % 2 = 0 then 1 else -1 := by
  classical
  unfold kleinSign
  simp

@[simp] theorem kleinSign_negSucc (n : Nat) :
    kleinSign (Int.negSucc n) =
      if Nat.succ n % 2 = 0 then 1 else -1 := by
  classical
  unfold kleinSign
  simp

/-- Loop space on the Klein bottle at `kleinBase`. -/
abbrev KleinBottleLoopSpace : Type _ :=
  LoopSpace KleinBottle kleinBase

/-- Rewrite quotient of Klein bottle loops. -/
abbrev KleinBottleLoopQuot : Type _ :=
  LoopQuot KleinBottle kleinBase

/-- Fundamental group π₁(K, base) expressed via loop quotients. -/
abbrev kleinPiOne : Type _ :=
  PiOne KleinBottle kleinBase

/-- Induced strict group structure on π₁(K, base). -/
abbrev kleinPiOneGroup : LoopGroup KleinBottle kleinBase :=
  PiOneGroup KleinBottle kleinBase

/-- Loop class of the horizontal generator. -/
@[simp] def kleinLoopAClass : KleinBottleLoopQuot :=
  LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase) kleinLoopA

/-- Loop class of the vertical generator. -/
@[simp] def kleinLoopBClass : KleinBottleLoopQuot :=
  LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase) kleinLoopB

/-- Fundamental-group element corresponding to `kleinLoopA`. -/
@[simp] def kleinLoopAElement : kleinPiOne :=
  PiOne.ofLoop (A := KleinBottle) (a := kleinBase) kleinLoopA

/-- Fundamental-group element corresponding to `kleinLoopB`. -/
@[simp] def kleinLoopBElement : kleinPiOne :=
  PiOne.ofLoop (A := KleinBottle) (a := kleinBase) kleinLoopB

/-- Natural powers of the `a`-loop at the path level. -/
def kleinLoopAPathPow : Nat → Path kleinBase kleinBase
  | 0 => Path.refl _
  | Nat.succ n => Path.trans (kleinLoopAPathPow n) kleinLoopA

@[simp] theorem kleinLoopAPathPow_zero :
    kleinLoopAPathPow 0 = Path.refl _ := rfl

@[simp] theorem kleinLoopAPathPow_succ (n : Nat) :
    kleinLoopAPathPow (Nat.succ n) =
      Path.trans (kleinLoopAPathPow n) kleinLoopA := rfl

/-- Concatenating natural powers of `kleinLoopA` adds the exponents. -/
theorem kleinLoopAPathPow_add (m n : Nat) :
    kleinLoopAPathPow (m + n) =
      Path.trans (kleinLoopAPathPow m) (kleinLoopAPathPow n) := by
  induction n with
  | zero =>
      simp [kleinLoopAPathPow]
  | succ n ih =>
      calc
        kleinLoopAPathPow (m + Nat.succ n)
            = Path.trans (kleinLoopAPathPow (m + n)) kleinLoopA := by
                simp [kleinLoopAPathPow]
        _ = Path.trans
              (Path.trans (kleinLoopAPathPow m) (kleinLoopAPathPow n))
              kleinLoopA := by
                simp [ih]
        _ = Path.trans (kleinLoopAPathPow m)
              (Path.trans (kleinLoopAPathPow n) kleinLoopA) := by
                exact
                  Path.trans_assoc
                    (kleinLoopAPathPow m)
                    (kleinLoopAPathPow n)
                    kleinLoopA
        _ = Path.trans (kleinLoopAPathPow m)
              (kleinLoopAPathPow (Nat.succ n)) := by
                simp [kleinLoopAPathPow]

/-- Natural powers of the `b`-loop at the path level. -/
def kleinLoopBPathPow : Nat → Path kleinBase kleinBase
  | 0 => Path.refl _
  | Nat.succ n => Path.trans (kleinLoopBPathPow n) kleinLoopB

@[simp] theorem kleinLoopBPathPow_zero :
    kleinLoopBPathPow 0 = Path.refl _ := rfl

@[simp] theorem kleinLoopBPathPow_succ (n : Nat) :
    kleinLoopBPathPow (Nat.succ n) =
      Path.trans (kleinLoopBPathPow n) kleinLoopB := rfl

/-- Concatenating natural powers of `kleinLoopB` adds the exponents. -/
theorem kleinLoopBPathPow_add (m n : Nat) :
    kleinLoopBPathPow (m + n) =
      Path.trans (kleinLoopBPathPow m) (kleinLoopBPathPow n) := by
  induction n with
  | zero =>
      simp [kleinLoopBPathPow]
  | succ n ih =>
      calc
        kleinLoopBPathPow (m + Nat.succ n)
            = Path.trans (kleinLoopBPathPow (m + n)) kleinLoopB := by
                simp [kleinLoopBPathPow]
        _ = Path.trans
              (Path.trans (kleinLoopBPathPow m) (kleinLoopBPathPow n))
              kleinLoopB := by
                simp [ih]
        _ = Path.trans (kleinLoopBPathPow m)
              (Path.trans (kleinLoopBPathPow n) kleinLoopB) := by
                exact
                  Path.trans_assoc
                    (kleinLoopBPathPow m)
                    (kleinLoopBPathPow n)
                    kleinLoopB
        _ = Path.trans (kleinLoopBPathPow m)
              (kleinLoopBPathPow (Nat.succ n)) := by
                simp [kleinLoopBPathPow]

/-- Integer powers of the `a`-loop. -/
def kleinLoopAPathZPow : Int → Path kleinBase kleinBase
  | Int.ofNat n => kleinLoopAPathPow n
  | Int.negSucc n => Path.symm (kleinLoopAPathPow (Nat.succ n))

@[simp] theorem kleinLoopAPathZPow_ofNat (n : Nat) :
    kleinLoopAPathZPow (Int.ofNat n) = kleinLoopAPathPow n := rfl

@[simp] theorem kleinLoopAPathZPow_negSucc (n : Nat) :
    kleinLoopAPathZPow (Int.negSucc n) =
      Path.symm (kleinLoopAPathPow (Nat.succ n)) := rfl

@[simp] theorem kleinLoopAPathZPow_zero :
    kleinLoopAPathZPow 0 = Path.refl _ := by
  simp [kleinLoopAPathZPow, kleinLoopAPathPow_zero]

@[simp] theorem kleinLoopAPathZPow_one :
    kleinLoopAPathZPow 1 = kleinLoopA := by
  simp [kleinLoopAPathZPow, kleinLoopAPathPow]

/-- Integer powers of the `b`-loop. -/
def kleinLoopBPathZPow : Int → Path kleinBase kleinBase
  | Int.ofNat n => kleinLoopBPathPow n
  | Int.negSucc n => Path.symm (kleinLoopBPathPow (Nat.succ n))

@[simp] theorem kleinLoopBPathZPow_ofNat (n : Nat) :
    kleinLoopBPathZPow (Int.ofNat n) = kleinLoopBPathPow n := rfl

@[simp] theorem kleinLoopBPathZPow_negSucc (n : Nat) :
    kleinLoopBPathZPow (Int.negSucc n) =
      Path.symm (kleinLoopBPathPow (Nat.succ n)) := rfl

@[simp] theorem kleinLoopBPathZPow_zero :
    kleinLoopBPathZPow 0 = Path.refl _ := by
  simp [kleinLoopBPathZPow, kleinLoopBPathPow_zero]

@[simp] theorem kleinLoopBPathZPow_one :
    kleinLoopBPathZPow 1 = kleinLoopB := by
  simp [kleinLoopBPathZPow, kleinLoopBPathPow]

@[simp] theorem kleinLoopAClass_pow (n : Nat) :
    LoopQuot.pow (A := KleinBottle) (a := kleinBase) kleinLoopAClass n =
      LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
        (kleinLoopAPathPow n) := by
  induction n with
  | zero =>
      change
        LoopQuot.id =
          LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
            (Path.refl _)
      exact
        (LoopQuot.ofLoop_refl
          (A := KleinBottle) (a := kleinBase)).symm
  | succ n ih =>
      have hcomp :
          LoopQuot.comp
              (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                kleinLoopAClass n)
              kleinLoopAClass =
            LoopQuot.comp
              (LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
                (kleinLoopAPathPow n))
              kleinLoopAClass :=
        _root_.congrArg
          (fun x =>
            LoopQuot.comp (A := KleinBottle) (a := kleinBase) x
              kleinLoopAClass) ih
      calc
        LoopQuot.pow (A := KleinBottle) (a := kleinBase)
            kleinLoopAClass (Nat.succ n)
            =
              LoopQuot.comp
                (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                  kleinLoopAClass n)
                kleinLoopAClass := rfl
        _ =
              LoopQuot.comp
                (LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
                  (kleinLoopAPathPow n))
                kleinLoopAClass := hcomp
        _ =
              LoopQuot.comp
                (LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
                  (kleinLoopAPathPow n))
                (LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
                  kleinLoopA) := rfl
        _ =
              LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
                (Path.trans (kleinLoopAPathPow n) kleinLoopA) :=
                  (LoopQuot.ofLoop_trans
                    (A := KleinBottle) (a := kleinBase)
                    (p := kleinLoopAPathPow n)
                    (q := kleinLoopA)).symm
        _ =
              LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
                (kleinLoopAPathPow (Nat.succ n)) := rfl

@[simp] theorem kleinLoopBClass_pow (n : Nat) :
    LoopQuot.pow (A := KleinBottle) (a := kleinBase) kleinLoopBClass n =
      LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
        (kleinLoopBPathPow n) := by
  induction n with
  | zero =>
      change
        LoopQuot.id =
          LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
            (Path.refl _)
      exact
        (LoopQuot.ofLoop_refl
          (A := KleinBottle) (a := kleinBase)).symm
  | succ n ih =>
      have hcomp :
          LoopQuot.comp
              (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                kleinLoopBClass n)
              kleinLoopBClass =
            LoopQuot.comp
              (LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
                (kleinLoopBPathPow n))
              kleinLoopBClass :=
        _root_.congrArg
          (fun x =>
            LoopQuot.comp (A := KleinBottle) (a := kleinBase) x
              kleinLoopBClass) ih
      calc
        LoopQuot.pow (A := KleinBottle) (a := kleinBase)
            kleinLoopBClass (Nat.succ n)
            =
              LoopQuot.comp
                (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                  kleinLoopBClass n)
                kleinLoopBClass := rfl
        _ =
              LoopQuot.comp
                (LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
                  (kleinLoopBPathPow n))
                kleinLoopBClass := hcomp
        _ =
              LoopQuot.comp
                (LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
                  (kleinLoopBPathPow n))
                (LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
                  kleinLoopB) := rfl
        _ =
              LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
                (Path.trans (kleinLoopBPathPow n) kleinLoopB) :=
                  (LoopQuot.ofLoop_trans
                    (A := KleinBottle) (a := kleinBase)
                    (p := kleinLoopBPathPow n)
                    (q := kleinLoopB)).symm
        _ =
              LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
                (kleinLoopBPathPow (Nat.succ n)) := rfl

/-- Inverses of `b`-powers are the corresponding powers of `b⁻¹`. -/
theorem kleinLoopBClass_pow_inv (n : Nat) :
    LoopQuot.inv
        (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
          kleinLoopBClass n) =
      LoopQuot.pow (A := KleinBottle) (a := kleinBase)
        (LoopQuot.inv kleinLoopBClass) n := by
  classical
  induction n with
  | zero =>
      change
        LoopQuot.inv
            (LoopQuot.id (A := KleinBottle) (a := kleinBase)) =
          LoopQuot.id (A := KleinBottle) (a := kleinBase)
      exact LoopQuot.inv_id
        (A := KleinBottle) (a := kleinBase)
  | succ n ih =>
      -- Expand the recursive definitions on both sides.
      change
        LoopQuot.inv
            (LoopQuot.comp
              (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                kleinLoopBClass n)
              kleinLoopBClass)
          =
            LoopQuot.comp
              (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                (LoopQuot.inv kleinLoopBClass) n)
              (LoopQuot.inv kleinLoopBClass)
      -- Peel off the final `b` on the left and rewrite using the induction hypothesis.
      have hcomp :
          LoopQuot.inv
              (LoopQuot.comp
                (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                  kleinLoopBClass n)
                kleinLoopBClass) =
            LoopQuot.comp
              (LoopQuot.inv kleinLoopBClass)
              (LoopQuot.inv
                (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                  kleinLoopBClass n)) :=
        LoopQuot.inv_comp_rev
          (A := KleinBottle) (a := kleinBase)
          (x := LoopQuot.pow (A := KleinBottle) (a := kleinBase)
            kleinLoopBClass n)
          (y := kleinLoopBClass)
      have hone :
          LoopQuot.pow (A := KleinBottle) (a := kleinBase)
              (LoopQuot.inv kleinLoopBClass) 1 =
            LoopQuot.inv kleinLoopBClass :=
        LoopQuot.pow_one
          (A := KleinBottle) (a := kleinBase)
          (x := LoopQuot.inv kleinLoopBClass)
      have hswap :=
        LoopQuot.pow_comm
            (A := KleinBottle) (a := kleinBase)
            (x := LoopQuot.inv kleinLoopBClass) 1 n
      calc
        LoopQuot.inv
            (LoopQuot.comp
              (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                kleinLoopBClass n)
              kleinLoopBClass)
            =
              LoopQuot.comp
                (LoopQuot.inv kleinLoopBClass)
                (LoopQuot.inv
                  (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                    kleinLoopBClass n)) := hcomp
        _ =
              LoopQuot.comp
                (LoopQuot.inv kleinLoopBClass)
                (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                  (LoopQuot.inv kleinLoopBClass) n) := by
                    rw [ih]
        _ =
              LoopQuot.comp
                (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                  (LoopQuot.inv kleinLoopBClass) 1)
                (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                  (LoopQuot.inv kleinLoopBClass) n) := by
                    rw [hone]
        _ =
              LoopQuot.comp
                (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                  (LoopQuot.inv kleinLoopBClass) n)
                (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                  (LoopQuot.inv kleinLoopBClass) 1) :=
                    hswap
        _ =
              LoopQuot.comp
                (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                  (LoopQuot.inv kleinLoopBClass) n)
                (LoopQuot.inv kleinLoopBClass) := by
                    rw [hone]

@[simp] theorem kleinLoopBClass_inv_pow (n : Nat) :
    LoopQuot.pow (A := KleinBottle) (a := kleinBase)
        (LoopQuot.inv kleinLoopBClass) n =
      LoopQuot.inv
        (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
          kleinLoopBClass n) :=
  (kleinLoopBClass_pow_inv (n := n)).symm

@[simp] theorem kleinLoopAElement_pow (n : Nat) :
    PiOne.pow (A := KleinBottle) (a := kleinBase) kleinLoopAElement n =
      PiOne.ofLoop (A := KleinBottle) (a := kleinBase)
        (kleinLoopAPathPow n) := by
  change
    LoopQuot.pow (A := KleinBottle) (a := kleinBase)
        kleinLoopAClass n =
      LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
        (kleinLoopAPathPow n)
  exact kleinLoopAClass_pow (n := n)

@[simp] theorem kleinLoopBElement_pow (n : Nat) :
    PiOne.pow (A := KleinBottle) (a := kleinBase) kleinLoopBElement n =
      PiOne.ofLoop (A := KleinBottle) (a := kleinBase)
        (kleinLoopBPathPow n) := by
  change
    LoopQuot.pow (A := KleinBottle) (a := kleinBase)
        kleinLoopBClass n =
      LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
        (kleinLoopBPathPow n)
  exact kleinLoopBClass_pow (n := n)

/-- Integer iteration of the `kleinLoopA` class in the loop quotient. -/
@[simp] theorem kleinLoopAElement_zpow (z : Int) :
    PiOne.zpow (A := KleinBottle) (a := kleinBase)
        kleinLoopAElement z =
      PiOne.ofLoop (A := KleinBottle) (a := kleinBase)
        (kleinLoopAPathZPow z) := by
  change
    LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
        kleinLoopAClass z =
      LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
        (kleinLoopAPathZPow z)
  cases z using Int.rec with
  | ofNat n =>
      unfold LoopQuot.zpow
      change
        LoopQuot.pow (A := KleinBottle) (a := kleinBase)
            kleinLoopAClass n =
          LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
            (kleinLoopAPathPow n)
      exact kleinLoopAClass_pow (n := n)
  | negSucc n =>
      unfold LoopQuot.zpow
      change
        LoopQuot.inv
            (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
              kleinLoopAClass (Nat.succ n)) =
          LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
            (Path.symm (kleinLoopAPathPow (Nat.succ n)))
      have h := kleinLoopAClass_pow (n := Nat.succ n)
      have h' := _root_.congrArg LoopQuot.inv h
      have hsymm :=
        (LoopQuot.ofLoop_symm (A := KleinBottle) (a := kleinBase)
          (p := kleinLoopAPathPow (Nat.succ n))).symm
      exact h'.trans hsymm

@[simp] theorem kleinLoopBElement_zpow (z : Int) :
    PiOne.zpow (A := KleinBottle) (a := kleinBase)
        kleinLoopBElement z =
      PiOne.ofLoop (A := KleinBottle) (a := kleinBase)
        (kleinLoopBPathZPow z) := by
  change
    LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
        kleinLoopBClass z =
      LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
        (kleinLoopBPathZPow z)
  cases z using Int.rec with
  | ofNat n =>
      unfold LoopQuot.zpow
      change
        LoopQuot.pow (A := KleinBottle) (a := kleinBase)
            kleinLoopBClass n =
          LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
            (kleinLoopBPathPow n)
      exact kleinLoopBClass_pow (n := n)
  | negSucc n =>
      unfold LoopQuot.zpow
      change
        LoopQuot.inv
            (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
              kleinLoopBClass (Nat.succ n)) =
          LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
            (Path.symm (kleinLoopBPathPow (Nat.succ n)))
      have h := kleinLoopBClass_pow (n := Nat.succ n)
      have h' := _root_.congrArg LoopQuot.inv h
      have hsymm :=
        (LoopQuot.ofLoop_symm (A := KleinBottle) (a := kleinBase)
          (p := kleinLoopBPathPow (Nat.succ n))).symm
      exact h'.trans hsymm

/-- Words in the Klein-bottle presentation `a^m b^n`. -/
structure KleinBottleWord where
  a : Int
  b : Int
  deriving Repr, DecidableEq

namespace KleinBottleWord

@[ext] theorem ext {w₁ w₂ : KleinBottleWord}
    (ha : w₁.a = w₂.a) (hb : w₁.b = w₂.b) : w₁ = w₂ := by
  cases w₁
  cases w₂
  cases ha
  cases hb
  rfl

/-- Neutral Klein bottle word (`a^0 b^0`). -/
@[simp] def one : KleinBottleWord :=
  ⟨0, 0⟩

/-- Semidirect-style multiplication encoding the Klein bottle relation. -/
@[simp] def mul (w₁ w₂ : KleinBottleWord) : KleinBottleWord :=
  ⟨w₁.a + w₂.a, kleinSign w₂.a * w₁.b + w₂.b⟩

/-- Inversion in the Klein bottle normal form. -/
@[simp] def inv (w : KleinBottleWord) : KleinBottleWord :=
  ⟨-w.a, -kleinSign w.a * w.b⟩

@[simp] def toPair (w : KleinBottleWord) : Int × Int :=
  (w.a, w.b)

@[simp] def ofPair (p : Int × Int) : KleinBottleWord :=
  ⟨p.fst, p.snd⟩

@[simp] def pairOne : Int × Int :=
  (0, 0)

@[simp] def pairMul (p q : Int × Int) : Int × Int :=
  (p.fst + q.fst, kleinSign q.fst * p.snd + q.snd)

@[simp] def pairInv (p : Int × Int) : Int × Int :=
  (-p.fst, -kleinSign p.fst * p.snd)

@[simp] theorem toPair_ofPair (p : Int × Int) :
    toPair (ofPair p) = p := by
  cases p
  rfl

@[simp] theorem ofPair_toPair (w : KleinBottleWord) :
    ofPair (toPair w) = w := by
  cases w
  rfl

@[simp] theorem toPair_one :
    toPair one = pairOne := rfl

@[simp] theorem ofPair_pairOne :
    ofPair pairOne = one := rfl

@[simp] theorem toPair_mul (w₁ w₂ : KleinBottleWord) :
    toPair (mul w₁ w₂) =
      pairMul (toPair w₁) (toPair w₂) := by
  cases w₁
  cases w₂
  simp [toPair, pairMul, mul]

@[simp] theorem toPair_inv (w : KleinBottleWord) :
    toPair (inv w) = pairInv (toPair w) := by
  cases w
  simp [toPair, pairInv, inv]

@[simp] theorem ofPair_pairMul (p q : Int × Int) :
    ofPair (pairMul p q) =
      mul (ofPair p) (ofPair q) := by
  cases p
  cases q
  simp [ofPair, pairMul, mul]

@[simp] theorem ofPair_pairInv (p : Int × Int) :
    ofPair (pairInv p) = inv (ofPair p) := by
  cases p
  simp [ofPair, pairInv, inv]

@[simp] theorem mul_one (w : KleinBottleWord) :
    mul w one = w := by
  cases w
  simp [mul, one, kleinSign]

@[simp] theorem one_mul (w : KleinBottleWord) :
    mul one w = w := by
  cases w
  simp [mul, one, kleinSign]

/-- Evaluate a word as an explicit loop. -/
def toPath (w : KleinBottleWord) : Path kleinBase kleinBase :=
  Path.trans
    (kleinLoopAPathZPow w.a)
    (kleinLoopBPathZPow w.b)

/-- Rewrite-class of a normal-form word. -/
def toLoopQuot (w : KleinBottleWord) : KleinBottleLoopQuot :=
  LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase) (toPath w)

@[simp] theorem toPath_zero :
    toPath ⟨0, 0⟩ = Path.refl _ := by
  unfold toPath
  simp

@[simp] theorem toLoopQuot_zero :
    toLoopQuot ⟨0, 0⟩ = LoopQuot.id := by
  unfold toLoopQuot
  rw [toPath_zero]
  exact
    (LoopQuot.ofLoop_refl (A := KleinBottle) (a := kleinBase))

@[simp] theorem toLoopQuot_loopA :
    toLoopQuot ⟨1, 0⟩ = kleinLoopAClass := by
  unfold toLoopQuot toPath
  have h :
      Path.trans (kleinLoopAPathZPow 1) (kleinLoopBPathZPow 0) =
        kleinLoopA := by
    simp
  have hloop :
      LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
        (Path.trans (kleinLoopAPathZPow 1) (kleinLoopBPathZPow 0)) =
      LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase) kleinLoopA :=
    LoopQuot.ofLoop_eq (A := KleinBottle) (a := kleinBase)
      (p := Path.trans (kleinLoopAPathZPow 1) (kleinLoopBPathZPow 0))
      (q := kleinLoopA) h
  exact hloop.trans rfl

@[simp] theorem toLoopQuot_loopB :
    toLoopQuot ⟨0, 1⟩ = kleinLoopBClass := by
  unfold toLoopQuot toPath
  have h :
      Path.trans (kleinLoopAPathZPow 0) (kleinLoopBPathZPow 1) =
        kleinLoopB := by
    simp
  have hloop :
      LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
        (Path.trans (kleinLoopAPathZPow 0) (kleinLoopBPathZPow 1)) =
      LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase) kleinLoopB :=
    LoopQuot.ofLoop_eq (A := KleinBottle) (a := kleinBase)
      (p := Path.trans (kleinLoopAPathZPow 0) (kleinLoopBPathZPow 1))
      (q := kleinLoopB) h
  exact hloop.trans rfl

@[simp] theorem toLoopQuot_eq_zpow (w : KleinBottleWord) :
    toLoopQuot w =
      LoopQuot.comp
        (LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
          kleinLoopAClass w.a)
        (LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
          kleinLoopBClass w.b) := by
  unfold toLoopQuot toPath
  have hA :=
    kleinLoopAElement_zpow (z := w.a)
  change
    LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
        kleinLoopAClass w.a =
      LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
        (kleinLoopAPathZPow w.a) at hA
  have hB :=
    kleinLoopBElement_zpow (z := w.b)
  change
    LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
        kleinLoopBClass w.b =
      LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
        (kleinLoopBPathZPow w.b) at hB
  calc
    LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
        (Path.trans (kleinLoopAPathZPow w.a) (kleinLoopBPathZPow w.b))
        =
      LoopQuot.comp
        (LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
          (kleinLoopAPathZPow w.a))
        (LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
          (kleinLoopBPathZPow w.b)) :=
            (LoopQuot.ofLoop_trans
              (A := KleinBottle) (a := kleinBase)
              (p := kleinLoopAPathZPow w.a)
              (q := kleinLoopBPathZPow w.b))
    _ =
      LoopQuot.comp
        (LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
          kleinLoopAClass w.a)
        (LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
          kleinLoopBClass w.b) := by
            rw [hA, hB]

end KleinBottleWord

/-- Conjugation relation `a ⋅ b ⋅ a⁻¹ = b⁻¹` lifted to the loop quotient. -/
@[simp] theorem kleinLoop_relation_class :
    LoopQuot.comp
      (LoopQuot.comp kleinLoopAClass kleinLoopBClass)
      (LoopQuot.inv kleinLoopAClass) =
      LoopQuot.inv kleinLoopBClass := by
  have hinner :
      LoopQuot.comp kleinLoopAClass kleinLoopBClass =
        LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
          (Path.trans kleinLoopA kleinLoopB) := by
    unfold kleinLoopAClass kleinLoopBClass
    exact
      (LoopQuot.ofLoop_trans (A := KleinBottle) (a := kleinBase)
        (p := kleinLoopA) (q := kleinLoopB)).symm
  have hinv :
      LoopQuot.inv kleinLoopAClass =
        LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
          (Path.symm kleinLoopA) := by
    unfold kleinLoopAClass
    exact
      (LoopQuot.ofLoop_symm (A := KleinBottle) (a := kleinBase)
        (p := kleinLoopA)).symm
  have hcomp :
      LoopQuot.comp
          (LoopQuot.comp kleinLoopAClass kleinLoopBClass)
          (LoopQuot.inv kleinLoopAClass) =
        LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
          (Path.trans
            (Path.trans kleinLoopA kleinLoopB)
            (Path.symm kleinLoopA)) := by
    calc
      LoopQuot.comp
          (LoopQuot.comp kleinLoopAClass kleinLoopBClass)
          (LoopQuot.inv kleinLoopAClass)
          =
            LoopQuot.comp
              (LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
                (Path.trans kleinLoopA kleinLoopB))
              (LoopQuot.inv kleinLoopAClass) := by
                rw [hinner]
      _ =
            LoopQuot.comp
              (LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
                (Path.trans kleinLoopA kleinLoopB))
              (LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
                (Path.symm kleinLoopA)) := by
                rw [hinv]
      _ =
          LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
            (Path.trans
              (Path.trans kleinLoopA kleinLoopB)
              (Path.symm kleinLoopA)) := by
                exact
                  (LoopQuot.ofLoop_trans
                    (A := KleinBottle) (a := kleinBase)
                    (p := Path.trans kleinLoopA kleinLoopB)
                    (q := Path.symm kleinLoopA)).symm
  have hsurf :
      LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
          (Path.trans
            (Path.trans kleinLoopA kleinLoopB)
            (Path.symm kleinLoopA)) =
        LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
          (Path.symm kleinLoopB) :=
    LoopQuot.ofLoop_eq (A := KleinBottle) (a := kleinBase)
      (p := Path.trans (Path.trans kleinLoopA kleinLoopB) (Path.symm kleinLoopA))
      (q := Path.symm kleinLoopB) kleinSurf
  have hsymm :
      LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase)
          (Path.symm kleinLoopB) =
        LoopQuot.inv kleinLoopBClass := by
    unfold kleinLoopBClass
    exact
      LoopQuot.ofLoop_symm (A := KleinBottle) (a := kleinBase)
        (p := kleinLoopB)
  exact hcomp.trans (hsurf.trans hsymm)

/-- Equivalent commutation law `a b = b⁻¹ a` in the loop quotient. -/
@[simp] theorem kleinLoopAClass_mul_loopBClass :
    LoopQuot.comp kleinLoopAClass kleinLoopBClass =
      LoopQuot.comp (LoopQuot.inv kleinLoopBClass) kleinLoopAClass := by
  have h :=
    _root_.congrArg
      (fun x =>
        LoopQuot.comp x kleinLoopAClass)
      kleinLoop_relation_class
  have h₁ :=
    _root_.congrArg
      (fun x =>
        LoopQuot.comp
          (LoopQuot.comp kleinLoopAClass kleinLoopBClass) x)
      (LoopQuot.inv_comp
        (A := KleinBottle) (a := kleinBase)
        (x := kleinLoopAClass)).symm
  have h₂ :=
    (LoopQuot.comp_assoc
      (LoopQuot.comp kleinLoopAClass kleinLoopBClass)
      (LoopQuot.inv kleinLoopAClass)
      kleinLoopAClass).symm
  calc
    LoopQuot.comp kleinLoopAClass kleinLoopBClass
        =
          LoopQuot.comp
            (LoopQuot.comp kleinLoopAClass kleinLoopBClass)
            LoopQuot.id := (LoopQuot.comp_id _).symm
    _ =
          LoopQuot.comp
            (LoopQuot.comp kleinLoopAClass kleinLoopBClass)
            (LoopQuot.comp (LoopQuot.inv kleinLoopAClass) kleinLoopAClass) :=
              h₁
    _ =
          LoopQuot.comp
            (LoopQuot.comp
              (LoopQuot.comp kleinLoopAClass kleinLoopBClass)
              (LoopQuot.inv kleinLoopAClass))
            kleinLoopAClass := h₂
    _ =
        LoopQuot.comp (LoopQuot.inv kleinLoopBClass) kleinLoopAClass := h

/-- Conjugation relation expressed in π₁(K, base). -/
@[simp] theorem kleinPiOne_relation :
    PiOne.mul
        (PiOne.mul kleinLoopAElement kleinLoopBElement)
        (PiOne.inv kleinLoopAElement) =
      PiOne.inv kleinLoopBElement := by
  unfold PiOne.mul PiOne.inv kleinLoopAElement kleinLoopBElement
  exact kleinLoop_relation_class

/-- Conjugating the vertical generator by the horizontal loop reverses it. -/
@[simp] theorem kleinLoopA_conj_loopB :
    Path.trans kleinLoopA (Path.trans kleinLoopB (Path.symm kleinLoopA)) =
      Path.symm kleinLoopB := by
  have hassoc :=
    (Path.trans_assoc (kleinLoopA) (kleinLoopB) (Path.symm kleinLoopA)).symm
  exact hassoc.trans kleinSurf

end LoopAlgebra

/- Iterating the Klein relation across natural powers. -/
theorem kleinLoopAClass_mul_loopBClass_pow (n : Nat) :
    LoopQuot.comp kleinLoopAClass
        (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
          kleinLoopBClass n) =
      LoopQuot.comp
        (LoopQuot.inv
          (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
            kleinLoopBClass n))
        kleinLoopAClass := by
  classical
  induction n with
  | zero =>
      change
        LoopQuot.comp kleinLoopAClass
            (LoopQuot.id (A := KleinBottle) (a := kleinBase)) =
          LoopQuot.comp
            (LoopQuot.id (A := KleinBottle) (a := kleinBase))
            kleinLoopAClass
      have hL :
          LoopQuot.comp kleinLoopAClass
              (LoopQuot.id (A := KleinBottle) (a := kleinBase)) =
            kleinLoopAClass :=
        LoopQuot.comp_id
          (A := KleinBottle) (a := kleinBase)
          (x := kleinLoopAClass)
      have hR :
          LoopQuot.comp
              (LoopQuot.id (A := KleinBottle) (a := kleinBase))
              kleinLoopAClass =
            kleinLoopAClass :=
        LoopQuot.id_comp
          (A := KleinBottle) (a := kleinBase)
          (x := kleinLoopAClass)
      exact hL.trans hR.symm
  | succ n ih =>
      have hassoc :
          LoopQuot.comp
              (LoopQuot.comp
                kleinLoopAClass
                (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                  kleinLoopBClass n))
              kleinLoopBClass =
            LoopQuot.comp
              kleinLoopAClass
              (LoopQuot.comp
                (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                  kleinLoopBClass n)
                kleinLoopBClass) :=
        LoopQuot.comp_assoc
          (A := KleinBottle) (a := kleinBase)
          (x := kleinLoopAClass)
          (y := LoopQuot.pow (A := KleinBottle) (a := kleinBase)
            kleinLoopBClass n)
          (z := kleinLoopBClass)
      have hpow :
          LoopQuot.pow (A := KleinBottle) (a := kleinBase)
            kleinLoopBClass (Nat.succ n) =
            LoopQuot.comp
              (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                kleinLoopBClass n)
              kleinLoopBClass := rfl
      have hfront :
          LoopQuot.comp kleinLoopAClass
              (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                kleinLoopBClass (Nat.succ n)) =
            LoopQuot.comp
              (LoopQuot.comp
                kleinLoopAClass
                (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                  kleinLoopBClass n))
              kleinLoopBClass := by
                rw [hpow]
                exact hassoc.symm
      calc
        LoopQuot.comp kleinLoopAClass
            (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
              kleinLoopBClass (Nat.succ n))
            =
              LoopQuot.comp
                (LoopQuot.comp
                  kleinLoopAClass
                  (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                    kleinLoopBClass n))
                kleinLoopBClass := hfront
        _ =
              LoopQuot.comp
                (LoopQuot.comp
                  (LoopQuot.inv
                    (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                      kleinLoopBClass n))
                  kleinLoopAClass)
                kleinLoopBClass := by
                    rw [ih]
        _ =
              LoopQuot.comp
                (LoopQuot.inv
                  (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                    kleinLoopBClass n))
                (LoopQuot.comp
                  kleinLoopAClass
                  kleinLoopBClass) := by
                    exact
                      LoopQuot.comp_assoc
                        (A := KleinBottle) (a := kleinBase)
                        (x :=
                          LoopQuot.inv
                            (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                              kleinLoopBClass n))
                        (y := kleinLoopAClass)
                        (z := kleinLoopBClass)
        _ =
              LoopQuot.comp
                (LoopQuot.inv
                  (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                    kleinLoopBClass n))
                (LoopQuot.comp
                  (LoopQuot.inv kleinLoopBClass)
                  kleinLoopAClass) := by
                    rw [kleinLoopAClass_mul_loopBClass]
        _ =
              LoopQuot.comp
                (LoopQuot.comp
                  (LoopQuot.inv
                    (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                      kleinLoopBClass n))
                  (LoopQuot.inv kleinLoopBClass))
                kleinLoopAClass := by
                    exact
                      (LoopQuot.comp_assoc
                        (A := KleinBottle) (a := kleinBase)
                        (x :=
                          LoopQuot.inv
                            (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                              kleinLoopBClass n))
                        (y := LoopQuot.inv kleinLoopBClass)
                        (z := kleinLoopAClass)).symm
        _ =
              LoopQuot.comp
                (LoopQuot.comp
                  (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                    (LoopQuot.inv kleinLoopBClass) n)
                  (LoopQuot.inv kleinLoopBClass))
                kleinLoopAClass := by
                    rw [kleinLoopBClass_pow_inv (n := n)]
        _ =
              LoopQuot.comp
                (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                  (LoopQuot.inv kleinLoopBClass) (Nat.succ n))
                kleinLoopAClass := by
                    rfl
        _ =
              LoopQuot.comp
                (LoopQuot.inv
                  (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
                    kleinLoopBClass (Nat.succ n)))
                kleinLoopAClass := by
                    rw [kleinLoopBClass_pow_inv (n := Nat.succ n)]
@[simp] theorem kleinLoopAClass_mul_loopBClass_zpow (n : Int) :
    LoopQuot.comp kleinLoopAClass
        (LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
          kleinLoopBClass n) =
      LoopQuot.comp
        (LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
          (LoopQuot.inv kleinLoopBClass) n)
        kleinLoopAClass := by
  classical
  cases n using Int.rec with
  | ofNat m =>
      change
        LoopQuot.comp kleinLoopAClass
            (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
              kleinLoopBClass m) =
          LoopQuot.comp
            (LoopQuot.pow (A := KleinBottle) (a := kleinBase)
              (LoopQuot.inv kleinLoopBClass) m)
            kleinLoopAClass
      have h := kleinLoopAClass_mul_loopBClass_pow (n := m)
      -- Rewrite the right-hand side using `kleinLoopBClass_pow_inv`.
      have h' := h
      rw [kleinLoopBClass_pow_inv (n := m)] at h'
      exact h'
  | negSucc m =>
      let pb :=
        LoopQuot.pow (A := KleinBottle) (a := kleinBase)
          kleinLoopBClass (Nat.succ m)
      let pinv :=
        LoopQuot.pow (A := KleinBottle) (a := kleinBase)
          (LoopQuot.inv kleinLoopBClass) (Nat.succ m)
      change
        LoopQuot.comp kleinLoopAClass (LoopQuot.inv pb) =
          LoopQuot.comp (LoopQuot.inv pinv) kleinLoopAClass
      have hpos :
          LoopQuot.comp kleinLoopAClass pb =
            LoopQuot.comp pinv kleinLoopAClass := by
        have h :=
          kleinLoopAClass_mul_loopBClass_pow (n := Nat.succ m)
        have pb_def :
            LoopQuot.pow (A := KleinBottle) (a := kleinBase)
              kleinLoopBClass (Nat.succ m) = pb := rfl
        have pinv_def :
            LoopQuot.pow (A := KleinBottle) (a := kleinBase)
              (LoopQuot.inv kleinLoopBClass) (Nat.succ m) = pinv := rfl
        have h' := h
        rw [kleinLoopBClass_pow_inv (n := Nat.succ m)] at h'
        -- replace the explicit powers with the abbreviations `pb` and `pinv`.
        have h'' := h'
        rw [pb_def, pinv_def] at h''
        exact h''

      have hleft_val :
          LoopQuot.comp
              (LoopQuot.comp kleinLoopAClass (LoopQuot.inv pb))
              pb =
            kleinLoopAClass := by
        calc
          LoopQuot.comp
              (LoopQuot.comp kleinLoopAClass (LoopQuot.inv pb))
              pb
              =
            LoopQuot.comp
              kleinLoopAClass
              (LoopQuot.comp (LoopQuot.inv pb) pb) :=
                LoopQuot.comp_assoc
                  (x := kleinLoopAClass)
                  (y := LoopQuot.inv pb)
                  (z := pb)
          _ =
            LoopQuot.comp
              kleinLoopAClass
              LoopQuot.id := by
                rw [LoopQuot.inv_comp
                  (A := KleinBottle) (a := kleinBase)
                  (x := pb)]
          _ = kleinLoopAClass :=
            LoopQuot.comp_id
              (A := KleinBottle) (a := kleinBase)
              (x := kleinLoopAClass)
      have hright_val :
          LoopQuot.comp
              (LoopQuot.comp (LoopQuot.inv pinv) kleinLoopAClass)
              pb =
            kleinLoopAClass := by
        calc
          LoopQuot.comp
              (LoopQuot.comp (LoopQuot.inv pinv) kleinLoopAClass)
              pb
              =
            LoopQuot.comp
              (LoopQuot.inv pinv)
              (LoopQuot.comp kleinLoopAClass pb) :=
                LoopQuot.comp_assoc
                  (x := LoopQuot.inv pinv)
                  (y := kleinLoopAClass)
                  (z := pb)
          _ =
            LoopQuot.comp
              (LoopQuot.inv pinv)
              (LoopQuot.comp pinv kleinLoopAClass) := by
                rw [hpos]
          _ =
            LoopQuot.comp
              (LoopQuot.comp
                (LoopQuot.inv pinv)
                pinv)
              kleinLoopAClass :=
                (LoopQuot.comp_assoc
                  (x := LoopQuot.inv pinv)
                  (y := pinv)
                  (z := kleinLoopAClass)).symm
          _ =
            LoopQuot.comp LoopQuot.id kleinLoopAClass := by
                rw [LoopQuot.inv_comp
                  (A := KleinBottle) (a := kleinBase)
                  (x := pinv)]
          _ = kleinLoopAClass :=
            LoopQuot.id_comp
              (A := KleinBottle) (a := kleinBase)
              (x := kleinLoopAClass)
      have hgoal :
          LoopQuot.comp kleinLoopAClass (LoopQuot.inv pb) =
            LoopQuot.comp (LoopQuot.inv pinv) kleinLoopAClass := by
        apply LoopQuot.comp_right_cancel
        exact hleft_val.trans hright_val.symm
      exact hgoal

@[simp] theorem kleinLoopBClass_mul_loopAClass :
    LoopQuot.comp kleinLoopBClass kleinLoopAClass =
      LoopQuot.comp kleinLoopAClass (LoopQuot.inv kleinLoopBClass) := by
  classical
  have h :=
    kleinLoopAClass_mul_loopBClass_zpow (n := (-1 : Int))
  have hzpow :
      LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
        kleinLoopBClass (-1) =
        LoopQuot.inv kleinLoopBClass :=
    LoopQuot.zpow_neg_one
      (A := KleinBottle) (a := kleinBase)
      (x := kleinLoopBClass)
  have hzpow_inv_raw :=
    LoopQuot.zpow_neg_one
      (A := KleinBottle) (a := kleinBase)
      (x := LoopQuot.inv kleinLoopBClass)
  have hzpow_inv :
      LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
        (LoopQuot.inv kleinLoopBClass) (-1) =
        kleinLoopBClass :=
    hzpow_inv_raw.trans
      (LoopQuot.inv_inv
        (A := KleinBottle) (a := kleinBase)
        (x := kleinLoopBClass))
  have hspec := h
  rw [hzpow] at hspec
  rw [hzpow_inv] at hspec
  exact hspec.symm

@[simp] theorem kleinPiOne_mul_loopB_zpow (n : Int) :
    PiOne.mul kleinLoopAElement (PiOne.zpow kleinLoopBElement n) =
      PiOne.mul (PiOne.zpow (PiOne.inv kleinLoopBElement) n) kleinLoopAElement := by
  unfold PiOne.mul PiOne.inv kleinLoopAElement kleinLoopBElement
  change
    LoopQuot.comp kleinLoopAClass
        (LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
          kleinLoopBClass n) =
      LoopQuot.comp
        (LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
          (LoopQuot.inv kleinLoopBClass) n)
        kleinLoopAClass
  exact kleinLoopAClass_mul_loopBClass_zpow (n := n)

end

/-- Decode a pair of integers as the loop class `a^m ⋅ b^n`. -/
noncomputable def kleinDecode (p : Int × Int) : kleinPiOne :=
  LoopQuot.comp
    (LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
      kleinLoopAClass p.1)
    (LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
      kleinLoopBClass p.2)

@[simp] theorem kleinDecode_zero_zero :
    kleinDecode (0, 0) = LoopQuot.id := by
  have hA :
      LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
        kleinLoopAClass (0 : Int) = LoopQuot.id :=
    LoopQuot.zpow_zero
      (A := KleinBottle) (a := kleinBase) (x := kleinLoopAClass)
  have hB :
      LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
        kleinLoopBClass (0 : Int) = LoopQuot.id :=
    LoopQuot.zpow_zero
      (A := KleinBottle) (a := kleinBase) (x := kleinLoopBClass)
  unfold kleinDecode
  rw [hA, hB, LoopQuot.comp_id]

@[simp] theorem kleinDecode_loopA :
    kleinDecode (1, 0) = kleinLoopAClass := by
  have hA :
      LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
        kleinLoopAClass (1 : Int) = kleinLoopAClass :=
    LoopQuot.zpow_one
      (A := KleinBottle) (a := kleinBase) (x := kleinLoopAClass)
  have hB :
      LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
        kleinLoopBClass (0 : Int) = LoopQuot.id :=
    LoopQuot.zpow_zero
      (A := KleinBottle) (a := kleinBase) (x := kleinLoopBClass)
  unfold kleinDecode
  rw [hA, hB, LoopQuot.comp_id]

@[simp] theorem kleinDecode_loopB :
    kleinDecode (0, 1) = kleinLoopBClass := by
  have hA :
      LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
        kleinLoopAClass (0 : Int) = LoopQuot.id :=
    LoopQuot.zpow_zero
      (A := KleinBottle) (a := kleinBase) (x := kleinLoopAClass)
  have hB :
      LoopQuot.zpow (A := KleinBottle) (a := kleinBase)
        kleinLoopBClass (1 : Int) = kleinLoopBClass :=
    LoopQuot.zpow_one
      (A := KleinBottle) (a := kleinBase) (x := kleinLoopBClass)
  unfold kleinDecode
  rw [hA, hB, LoopQuot.id_comp]

@[simp] theorem kleinDecode_pair (m n : Int) :
    kleinDecode (m, n) = KleinBottleWord.toLoopQuot ⟨m, n⟩ := by
  unfold kleinDecode
  exact
    (KleinBottleWord.toLoopQuot_eq_zpow (w := ⟨m, n⟩)).symm

@[simp] theorem kleinDecode_ofPair (p : Int × Int) :
    kleinDecode p =
      KleinBottleWord.toLoopQuot (KleinBottleWord.ofPair p) := by
  cases p with
  | mk m n =>
      change kleinDecode (m, n) = KleinBottleWord.toLoopQuot ⟨m, n⟩
      exact kleinDecode_pair (m := m) (n := n)

/-! ## Klein sign lemmas for the semidirect product structure -/

/-- Parity toggle: `kleinSign (m + 1) = -kleinSign m`. -/
theorem kleinSign_succ (m : Int) : kleinSign (m + 1) = -kleinSign m := by
  classical
  unfold kleinSign
  cases m with
  | ofNat n =>
      have hsucc : (Int.ofNat n + 1).natAbs = n + 1 := by
        simp only [Int.ofNat_eq_coe]
        rfl
      simp only [hsucc]
      by_cases h : n % 2 = 0
      · have hsucc_odd : (n + 1) % 2 = 1 := by omega
        simp [h, hsucc_odd]
      · have hn_odd : n % 2 = 1 := by omega
        have hsucc_even : (n + 1) % 2 = 0 := by omega
        simp [hn_odd, hsucc_even]
  | negSucc n =>
      simp only [Int.natAbs_negSucc]
      have hneg : (Int.negSucc n + 1).natAbs = n := by
        cases n with
        | zero => rfl
        | succ n =>
            have : Int.negSucc (n + 1) + 1 = Int.negSucc n := rfl
            simp only [this, Int.natAbs_negSucc]
      simp only [hneg]
      by_cases h : (n + 1) % 2 = 0
      · have hn_odd : n % 2 = 1 := by omega
        simp [h, hn_odd]
      · have hn_succ_odd : (n + 1) % 2 = 1 := by omega
        have hn_even : n % 2 = 0 := by omega
        simp [hn_succ_odd, hn_even]

/-- `kleinSign (m - 1) = -kleinSign m`. -/
theorem kleinSign_pred (m : Int) : kleinSign (m - 1) = -kleinSign m := by
  have h := kleinSign_succ (m - 1)
  simp only [Int.sub_add_cancel] at h
  have hnegeq : -kleinSign m = -(-kleinSign (m - 1)) := _root_.congrArg (fun x => -x) h
  simp only [Int.neg_neg] at hnegeq
  exact hnegeq.symm

/-- `kleinSign` is multiplicative: `kleinSign (m + n) = kleinSign m * kleinSign n`. -/
theorem kleinSign_add (m n : Int) : kleinSign (m + n) = kleinSign m * kleinSign n := by
  classical
  induction n using LoopQuot.int_induction with
  | base =>
      simp only [Int.add_zero, kleinSign_zero, Int.mul_one]
  | succ n ih =>
      rw [← Int.add_assoc, kleinSign_succ, ih, kleinSign_succ, Int.neg_mul_eq_mul_neg]
  | pred n ih =>
      have hstep : m + (n - 1) = m + n - 1 := by omega
      rw [hstep, kleinSign_pred, ih, kleinSign_pred, Int.neg_mul_eq_mul_neg]

/-- Negating the exponent doesn't change the sign. -/
@[simp] theorem kleinSign_neg' (m : Int) : kleinSign (-m) = kleinSign m := kleinSign_neg m

/-- `kleinSign 1 = -1`. -/
@[simp] theorem kleinSign_one : kleinSign 1 = -1 := by
  simp [kleinSign]

/-- `kleinSign (-1) = -1`. -/
@[simp] theorem kleinSign_neg_one : kleinSign (-1) = -1 := by
  simp [kleinSign]

/-- `zpow (inv x) n = zpow x (-n)` for loop quotients. -/
theorem LoopQuot.zpow_inv_eq_zpow_neg {A : Type _} {a : A}
    (x : LoopQuot A a) (n : Int) :
    LoopQuot.zpow (LoopQuot.inv x) n = LoopQuot.zpow x (-n) := by
  induction n using LoopQuot.int_induction with
  | base =>
    simp only [LoopQuot.zpow_zero, Int.neg_zero]
  | succ n ih =>
    rw [LoopQuot.zpow_succ]
    rw [ih]
    have hneg : -(n + 1) = -n + (-1) := by omega
    rw [hneg, LoopQuot.zpow_add, LoopQuot.zpow_neg_one]
  | pred n ih =>
    rw [LoopQuot.zpow_pred]
    rw [ih]
    have hneg : -(n - 1) = -n + 1 := by omega
    rw [hneg, LoopQuot.zpow_add, LoopQuot.zpow_one]
    have hinv : LoopQuot.inv (LoopQuot.inv x) = x :=
      LoopQuot.inv_inv (A := A) (a := a) (x := x)
    rw [hinv]

/-- Reformulation: `a ⋅ b^n = b^{-n} ⋅ a` -/
theorem kleinLoopAClass_mul_loopBClass_zpow' (n : Int) :
    LoopQuot.comp kleinLoopAClass
        (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass n) =
      LoopQuot.comp
        (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (-n))
        kleinLoopAClass := by
  have h := kleinLoopAClass_mul_loopBClass_zpow (n := n)
  rw [LoopQuot.zpow_inv_eq_zpow_neg] at h
  exact h

/-- Swapped form: `b^n ⋅ a = a ⋅ b^{-n}` -/
theorem kleinLoopBClass_zpow_mul_loopAClass' (n : Int) :
    LoopQuot.comp
        (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass n)
        kleinLoopAClass =
      LoopQuot.comp
        kleinLoopAClass
        (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (-n)) := by
  have h := kleinLoopAClass_mul_loopBClass_zpow' (n := -n)
  simp only [Int.neg_neg] at h
  exact h.symm

/-! ## Key commutation lemma for zpow of both generators -/

/-- `b^n ⋅ a^m = a^m ⋅ b^{kleinSign m ⋅ n}` - the fundamental commutation relation
    in the Klein bottle loop quotient. -/
theorem kleinLoopBClass_zpow_mul_loopAClass_zpow (n m : Int) :
    LoopQuot.comp
        (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass n)
        (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass m) =
      LoopQuot.comp
        (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass m)
        (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (kleinSign m * n)) := by
  classical
  induction m using LoopQuot.int_induction with
  | base =>
      simp only [kleinSign_zero, LoopQuot.zpow_zero, LoopQuot.id_comp, LoopQuot.comp_id]
      have heq : (1 : Int) * n = n := Int.one_mul n
      rw [heq]
  | succ m ih =>
      have hassoc1 :
          LoopQuot.comp
              (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass n)
              (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass (m + 1)) =
            LoopQuot.comp
              (LoopQuot.comp
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass n)
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass m))
              kleinLoopAClass := by
        rw [LoopQuot.zpow_succ]
        exact (LoopQuot.comp_assoc _ _ _).symm
      rw [hassoc1, ih]
      have hcomm :
          LoopQuot.comp
              (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (kleinSign m * n))
              kleinLoopAClass =
            LoopQuot.comp
              kleinLoopAClass
              (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (-(kleinSign m * n))) :=
        kleinLoopBClass_zpow_mul_loopAClass' (n := kleinSign m * n)
      calc
        LoopQuot.comp
            (LoopQuot.comp
              (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass m)
              (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (kleinSign m * n)))
            kleinLoopAClass
            = LoopQuot.comp
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass m)
                (LoopQuot.comp
                  (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (kleinSign m * n))
                  kleinLoopAClass) := LoopQuot.comp_assoc _ _ _
        _ = LoopQuot.comp
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass m)
                (LoopQuot.comp
                  kleinLoopAClass
                  (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (-(kleinSign m * n)))) := by
            rw [hcomm]
        _ = LoopQuot.comp
                (LoopQuot.comp
                  (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass m)
                  kleinLoopAClass)
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (-(kleinSign m * n))) := by
            rw [← LoopQuot.comp_assoc]
        _ = LoopQuot.comp
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass (m + 1))
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (-(kleinSign m * n))) := by
            rw [← LoopQuot.zpow_succ]
        _ = LoopQuot.comp
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass (m + 1))
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (kleinSign (m + 1) * n)) := by
            congr 1
            rw [kleinSign_succ]
            simp only [Int.neg_mul]
  | pred m ih =>
      have hassoc1 :
          LoopQuot.comp
              (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass n)
              (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass (m - 1)) =
            LoopQuot.comp
              (LoopQuot.comp
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass n)
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass m))
              (LoopQuot.inv kleinLoopAClass) := by
        rw [LoopQuot.zpow_pred]
        exact (LoopQuot.comp_assoc _ _ _).symm
      rw [hassoc1, ih]
      have hcomm :
          LoopQuot.comp
              (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (kleinSign m * n))
              (LoopQuot.inv kleinLoopAClass) =
            LoopQuot.comp
              (LoopQuot.inv kleinLoopAClass)
              (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (-(kleinSign m * n))) := by
        have hrel := kleinLoopBClass_zpow_mul_loopAClass' (n := -(kleinSign m * n))
        simp only [Int.neg_neg] at hrel
        have hstep1 :
            LoopQuot.comp
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (-(kleinSign m * n)))
                (LoopQuot.comp kleinLoopAClass (LoopQuot.inv kleinLoopAClass)) =
              LoopQuot.comp
                (LoopQuot.comp kleinLoopAClass
                  (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (kleinSign m * n)))
                (LoopQuot.inv kleinLoopAClass) := by
          calc
            LoopQuot.comp
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (-(kleinSign m * n)))
                (LoopQuot.comp kleinLoopAClass (LoopQuot.inv kleinLoopAClass))
                = LoopQuot.comp
                    (LoopQuot.comp
                      (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (-(kleinSign m * n)))
                      kleinLoopAClass)
                    (LoopQuot.inv kleinLoopAClass) := by rw [LoopQuot.comp_assoc]
            _ = LoopQuot.comp
                    (LoopQuot.comp kleinLoopAClass
                      (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (kleinSign m * n)))
                    (LoopQuot.inv kleinLoopAClass) := by rw [hrel]
        rw [LoopQuot.comp_inv, LoopQuot.comp_id] at hstep1
        have hstep2 :
            LoopQuot.comp (LoopQuot.inv kleinLoopAClass)
              (LoopQuot.comp
                (LoopQuot.comp kleinLoopAClass
                  (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (kleinSign m * n)))
                (LoopQuot.inv kleinLoopAClass)) =
              LoopQuot.comp (LoopQuot.inv kleinLoopAClass)
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (-(kleinSign m * n))) := by
          rw [hstep1]
        rw [← LoopQuot.comp_assoc] at hstep2
        rw [← LoopQuot.comp_assoc (x := LoopQuot.inv kleinLoopAClass) (y := kleinLoopAClass)] at hstep2
        rw [LoopQuot.inv_comp, LoopQuot.id_comp] at hstep2
        exact hstep2
      calc
        LoopQuot.comp
            (LoopQuot.comp
              (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass m)
              (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (kleinSign m * n)))
            (LoopQuot.inv kleinLoopAClass)
            = LoopQuot.comp
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass m)
                (LoopQuot.comp
                  (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (kleinSign m * n))
                  (LoopQuot.inv kleinLoopAClass)) := LoopQuot.comp_assoc _ _ _
        _ = LoopQuot.comp
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass m)
                (LoopQuot.comp
                  (LoopQuot.inv kleinLoopAClass)
                  (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (-(kleinSign m * n)))) := by
            rw [hcomm]
        _ = LoopQuot.comp
                (LoopQuot.comp
                  (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass m)
                  (LoopQuot.inv kleinLoopAClass))
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (-(kleinSign m * n))) := by
            rw [← LoopQuot.comp_assoc]
        _ = LoopQuot.comp
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass (m - 1))
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (-(kleinSign m * n))) := by
            rw [← LoopQuot.zpow_pred]
        _ = LoopQuot.comp
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass (m - 1))
                (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (kleinSign (m - 1) * n)) := by
            congr 1
            rw [kleinSign_pred]
            rw [Int.neg_mul]

/-! ## Homomorphism property of toLoopQuot -/

/-- `toLoopQuot` respects the semidirect multiplication law. -/
theorem KleinBottleWord.toLoopQuot_mul (w₁ w₂ : KleinBottleWord) :
    toLoopQuot (mul w₁ w₂) =
      LoopQuot.comp (toLoopQuot w₁) (toLoopQuot w₂) := by
  simp only [toLoopQuot_eq_zpow, mul]
  rw [LoopQuot.zpow_add (A := KleinBottle) (a := kleinBase) (x := kleinLoopAClass)]
  rw [LoopQuot.zpow_add (A := KleinBottle) (a := kleinBase) (x := kleinLoopBClass)]
  rw [LoopQuot.comp_assoc, LoopQuot.comp_assoc]
  have hcomm := kleinLoopBClass_zpow_mul_loopAClass_zpow w₁.b w₂.a
  rw [← LoopQuot.comp_assoc
      (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass w₂.a)
      (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass (kleinSign w₂.a * w₁.b))
      (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass w₂.b)]
  rw [← hcomm]
  rw [LoopQuot.comp_assoc
      (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass w₁.b)
      (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopAClass w₂.a)
      (LoopQuot.zpow (A := KleinBottle) (a := kleinBase) kleinLoopBClass w₂.b)]

/-- `kleinDecode` respects the semidirect multiplication law on pairs. -/
@[simp] theorem kleinDecode_pairMul (p q : Int × Int) :
    kleinDecode (KleinBottleWord.pairMul p q) =
      LoopQuot.comp (kleinDecode p) (kleinDecode q) := by
  rw [kleinDecode_ofPair, kleinDecode_ofPair, kleinDecode_ofPair]
  rw [KleinBottleWord.ofPair_pairMul]
  exact KleinBottleWord.toLoopQuot_mul _ _

/-! ## Semidirect product structure -/

/-- The semidirect product on `Int × Int` corresponding to the Klein bottle
    group structure: `(m₁, n₁) * (m₂, n₂) = (m₁ + m₂, kleinSign(m₂) * n₁ + n₂)`. -/
def kleinSemidirectMul (p q : Int × Int) : Int × Int :=
  (p.1 + q.1, kleinSign q.1 * p.2 + q.2)

/-- The inverse in the semidirect product. -/
def kleinSemidirectInv (p : Int × Int) : Int × Int :=
  (-p.1, -kleinSign p.1 * p.2)

/-- Identity element of the semidirect product. -/
def kleinSemidirectOne : Int × Int := (0, 0)

/-- Left identity law for semidirect multiplication. -/
theorem kleinSemidirectMul_one_left (p : Int × Int) :
    kleinSemidirectMul kleinSemidirectOne p = p := by
  simp [kleinSemidirectMul, kleinSemidirectOne]

/-- Right identity law for semidirect multiplication. -/
theorem kleinSemidirectMul_one_right (p : Int × Int) :
    kleinSemidirectMul p kleinSemidirectOne = p := by
  simp [kleinSemidirectMul, kleinSemidirectOne]

/-- The semidirect multiplication matches `KleinBottleWord.pairMul`. -/
theorem kleinSemidirectMul_eq_pairMul (p q : Int × Int) :
    kleinSemidirectMul p q = KleinBottleWord.pairMul p q := by
  rfl

/-! ## Encode-Decode Equivalence

Following the torus pattern, we define a type family `kleinCode : KleinBottle → Type`
and use transport to define the encode map. The key difference from the torus is that
transport along `kleinLoopA` negates the b-coordinate, reflecting `a⋅b⋅a⁻¹ = b⁻¹`.
-/

/-- Equality lemma for SimpleEquiv used for surface coherence. -/
theorem SimpleEquiv_eq {α : Type u} {β : Type v} (e1 e2 : SimpleEquiv α β)
    (h1 : e1.toFun = e2.toFun) (h2 : e1.invFun = e2.invFun) : e1 = e2 := by
  cases e1
  cases e2
  congr

/-- Equivalence for transport along `kleinLoopA`: flips the sign of the second coordinate.
    This captures that `a⋅b⋅a⁻¹ = b⁻¹`. -/
def kleinEquivA : SimpleEquiv (Int × Int) (Int × Int) where
  toFun := fun (m, n) => (m + 1, -n)
  invFun := fun (m, n) => (m - 1, -n)
  left_inv := by intro (m, n); simp
  right_inv := by intro (m, n); simp

/-- Equivalence for transport along `kleinLoopB`: increments the second coordinate. -/
def kleinEquivB : SimpleEquiv (Int × Int) (Int × Int) where
  toFun := fun (m, n) => (m, n + 1)
  invFun := fun (m, n) => (m, n - 1)
  left_inv := by intro (m, n); simp
  right_inv := by intro (m, n); simp

/-- The Klein bottle surface relation at the code level:
    `(a ⋅ b ⋅ a⁻¹) = b⁻¹` corresponds to `A ∘ B ∘ A⁻¹ = B⁻¹` as equivalences. -/
theorem kleinEquiv_surf :
    SimpleEquiv.comp (SimpleEquiv.comp kleinEquivA kleinEquivB) (SimpleEquiv.symm kleinEquivA) =
      SimpleEquiv.symm kleinEquivB := by
  apply SimpleEquiv_eq
  · funext ⟨m, n⟩
    simp only [SimpleEquiv.comp_apply, SimpleEquiv.symm_apply]
    simp only [kleinEquivA, kleinEquivB]
    simp only [Prod.mk.injEq]
    constructor <;> omega
  · funext ⟨m, n⟩
    simp only [SimpleEquiv.comp_inv_apply, SimpleEquiv.symm]
    simp only [kleinEquivA, kleinEquivB]
    simp only [Prod.mk.injEq]
    constructor <;> omega

/-- Data for the code type family over the Klein bottle. -/
noncomputable def kleinCodeData : KleinBottleRecData (Type _) where
  base := Int × Int
  loopA := Path.ua kleinEquivA
  loopB := Path.ua kleinEquivB
  surf := by
    rw [ua_trans, ua_symm, ua_trans, ua_symm]
    exact Path.toEq (Path.congrArg Path.ua (Path.ofEq kleinEquiv_surf))

/-- Universal-cover code family for the Klein bottle. -/
noncomputable def kleinCode : KleinBottle → Type _ :=
  kleinRec kleinCodeData

@[simp] theorem kleinCode_base :
    kleinCode kleinBase = (Int × Int) := by
  unfold kleinCode
  exact kleinRec_base kleinCodeData

/-- View an element of `kleinCode kleinBase` as a pair of integers. -/
@[simp] def kleinCodeToProd : kleinCode kleinBase → Int × Int :=
  fun z => Eq.mp kleinCode_base z

/-- Interpret a pair of integers as an element of `kleinCode kleinBase`. -/
@[simp] def kleinCodeOfProd : Int × Int → kleinCode kleinBase :=
  fun z => Eq.mpr kleinCode_base z

@[simp] theorem kleinCodeToProd_ofProd (z : Int × Int) :
    kleinCodeToProd (kleinCodeOfProd z) = z := by
  simp [kleinCodeToProd, kleinCodeOfProd]

@[simp] theorem kleinCodeOfProd_toProd (z : kleinCode kleinBase) :
    kleinCodeOfProd (kleinCodeToProd z) = z := by
  simp [kleinCodeToProd, kleinCodeOfProd]

theorem cast_kleinCode_base_kleinCodeOfProd (z : Int × Int) :
    cast kleinCode_base (kleinCodeOfProd z) = z := by
  unfold kleinCodeOfProd
  change cast kleinCode_base (cast kleinCode_base.symm z) = z
  rw [cast_cast]
  rfl

/-- Chosen basepoint in the code fibre at the Klein bottle base. -/
@[simp] def kleinCodeZero : kleinCode kleinBase :=
  kleinCodeOfProd (0, 0)

/-- Transport the base code point along a loop to encode a path. -/
@[simp] def kleinEncodeRaw (x : KleinBottle) :
    Path kleinBase x → kleinCode x :=
  fun p => Path.transport (A := KleinBottle) (D := kleinCode) p kleinCodeZero

/-- Encode a loop `p : base = base` as a pair of integers. -/
@[simp] def kleinEncodePath :
    Path kleinBase kleinBase → Int × Int :=
  fun p => kleinCodeToProd (kleinEncodeRaw kleinBase p)

@[simp] theorem kleinEncodePath_refl : kleinEncodePath (Path.refl kleinBase) = (0, 0) := by
  unfold kleinEncodePath
  simp
  exact cast_kleinCode_base_kleinCodeOfProd (0, 0)

@[simp] theorem kleinEncodePath_rweq
    {p q : Path kleinBase kleinBase} (h : RwEq p q) :
    kleinEncodePath p = kleinEncodePath q := by
  unfold kleinEncodePath kleinEncodeRaw
  have hEq : p.toEq = q.toEq := rweq_toEq (p := p) (q := q) h
  have htransport :=
    Path.transport_of_toEq_eq (A := KleinBottle) (D := kleinCode)
      (p := p) (q := q) (x := kleinCodeZero) hEq
  exact _root_.congrArg kleinCodeToProd htransport

@[simp] theorem kleinCode_loopA_path :
    Path.trans (Path.symm (Path.ofEq kleinCode_base))
        (Path.trans (Path.congrArg kleinCode kleinLoopA)
          (Path.ofEq kleinCode_base)) =
      Path.ua kleinEquivA :=
  kleinRec_loopA kleinCodeData

@[simp] theorem kleinCode_loopB_path :
    Path.trans (Path.symm (Path.ofEq kleinCode_base))
        (Path.trans (Path.congrArg kleinCode kleinLoopB)
          (Path.ofEq kleinCode_base)) =
      Path.ua kleinEquivB :=
  kleinRec_loopB kleinCodeData

/-- Helper for Int arithmetic. -/
theorem eq_sub_of_add_eq' {a b c : Int} (h : a + b = c) : a = c - b := by omega

/-- Transport along `kleinLoopA` applies `kleinEquivA`. -/
@[simp] theorem kleinCode_transport_loopA (z : Int × Int) :
    kleinCodeToProd (Path.transport (A := KleinBottle) (D := kleinCode)
      kleinLoopA (kleinCodeOfProd z)) = (z.1 + 1, -z.2) := by
  let p1 := Path.ofEq kleinCode_base
  let q := Path.congrArg kleinCode kleinLoopA
  let z_code := kleinCodeOfProd z
  have hEq : Path.trans (Path.symm p1) (Path.trans q p1) = Path.ua kleinEquivA :=
    kleinCode_loopA_path
  have hLeftStep :=
    Path.transport_trans (A := Type _) (D := fun X => X)
      (p := Path.symm p1) (q := Path.trans q p1)
      (x := Path.transport (A := Type _) (D := fun X => X) p1 z_code)
  have hLeftCancel :=
    _root_.congrArg
      (fun w =>
        Path.transport (A := Type _) (D := fun X => X)
          (Path.trans q p1) w)
      (Path.transport_symm_left (A := Type _) (D := fun X => X)
        (p := p1) (x := z_code))
  have hLeftSimp :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans (Path.symm p1) (Path.trans q p1))
        (Path.transport (A := Type _) (D := fun X => X) p1 z_code)
      =
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) z_code := by
    exact hLeftStep.trans hLeftCancel
  have hComb :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) z_code
      =
      Path.transport (A := Type _) (D := fun X => X)
        (Path.ua kleinEquivA)
        (Path.transport (A := Type _) (D := fun X => X) p1 z_code) := by
    rw [← hLeftSimp]
    rw [hEq]
  have hAssoc :=
    Path.transport_trans (A := Type _) (D := fun X => X)
      (p := q) (q := p1) (x := z_code)
  have hMove :=
    (Path.transport_congrArg (A := KleinBottle) (D := kleinCode)
      (p := kleinLoopA) (x := z_code))
  have hLHS :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) z_code
      =
      kleinCodeToProd
        (Path.transport (A := KleinBottle) (D := kleinCode) kleinLoopA z_code) := by
    have hSplit :
        Path.transport (A := Type _) (D := fun X => X)
          (Path.trans q p1) z_code
        =
        Path.transport (A := Type _) (D := fun X => X) p1
          (Path.transport (A := Type _) (D := fun X => X) q z_code) := by
      simpa using hAssoc
    have hInner :
        Path.transport (A := Type _) (D := fun X => X) q z_code
        = Path.transport (A := KleinBottle) (D := kleinCode) kleinLoopA z_code := by
      exact hMove.symm
    exact hSplit.trans (_root_.congrArg (fun w => p1.transport w) hInner)
  have hBase :
      Path.transport (A := Type _) (D := fun X => X) p1 z_code
      = z := by
    exact cast_kleinCode_base_kleinCodeOfProd z
  have hRHS :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.ua kleinEquivA) z
      = (z.1 + 1, -z.2) := by
    simp [Path.ua_beta, kleinEquivA]
  exact (hLHS.trans hComb).trans (by simpa [hBase] using hRHS)

/-- Transport along `kleinLoopB` applies `kleinEquivB`. -/
@[simp] theorem kleinCode_transport_loopB (z : Int × Int) :
    kleinCodeToProd (Path.transport (A := KleinBottle) (D := kleinCode)
      kleinLoopB (kleinCodeOfProd z)) = (z.1, z.2 + 1) := by
  let p1 := Path.ofEq kleinCode_base
  let q := Path.congrArg kleinCode kleinLoopB
  let z_code := kleinCodeOfProd z
  have hEq : Path.trans (Path.symm p1) (Path.trans q p1) = Path.ua kleinEquivB :=
    kleinCode_loopB_path
  have hLeftStep :=
    Path.transport_trans (A := Type _) (D := fun X => X)
      (p := Path.symm p1) (q := Path.trans q p1)
      (x := Path.transport (A := Type _) (D := fun X => X) p1 z_code)
  have hLeftCancel :=
    _root_.congrArg
      (fun w =>
        Path.transport (A := Type _) (D := fun X => X)
          (Path.trans q p1) w)
      (Path.transport_symm_left (A := Type _) (D := fun X => X)
        (p := p1) (x := z_code))
  have hLeftSimp :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans (Path.symm p1) (Path.trans q p1))
        (Path.transport (A := Type _) (D := fun X => X) p1 z_code)
      =
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) z_code := by
    exact hLeftStep.trans hLeftCancel
  have hComb :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) z_code
      =
      Path.transport (A := Type _) (D := fun X => X)
        (Path.ua kleinEquivB)
        (Path.transport (A := Type _) (D := fun X => X) p1 z_code) := by
    rw [← hLeftSimp]
    rw [hEq]
  have hAssoc :=
    Path.transport_trans (A := Type _) (D := fun X => X)
      (p := q) (q := p1) (x := z_code)
  have hMove :=
    (Path.transport_congrArg (A := KleinBottle) (D := kleinCode)
      (p := kleinLoopB) (x := z_code))
  have hLHS :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.trans q p1) z_code
      =
      kleinCodeToProd
        (Path.transport (A := KleinBottle) (D := kleinCode) kleinLoopB z_code) := by
    have hSplit :
        Path.transport (A := Type _) (D := fun X => X)
          (Path.trans q p1) z_code
        =
        Path.transport (A := Type _) (D := fun X => X) p1
          (Path.transport (A := Type _) (D := fun X => X) q z_code) := by
      simpa using hAssoc
    have hInner :
        Path.transport (A := Type _) (D := fun X => X) q z_code
        = Path.transport (A := KleinBottle) (D := kleinCode) kleinLoopB z_code := by
      exact hMove.symm
    exact hSplit.trans (_root_.congrArg (fun w => p1.transport w) hInner)
  have hBase :
      Path.transport (A := Type _) (D := fun X => X) p1 z_code
      = z := by
    exact cast_kleinCode_base_kleinCodeOfProd z
  have hRHS :
      Path.transport (A := Type _) (D := fun X => X)
        (Path.ua kleinEquivB) z
      = (z.1, z.2 + 1) := by
    simp [Path.ua_beta, kleinEquivB]
  exact (hLHS.trans hComb).trans (by simpa [hBase] using hRHS)

/-- Transport along inverse of `kleinLoopA`. -/
@[simp] theorem kleinCode_transport_loopA_inv (z : Int × Int) :
    kleinCodeToProd (Path.transport (A := KleinBottle) (D := kleinCode)
      (Path.symm kleinLoopA) (kleinCodeOfProd z)) = (z.1 - 1, -z.2) := by
  let x := kleinCodeOfProd z
  have h : kleinCodeToProd (Path.transport (A := KleinBottle) (D := kleinCode) kleinLoopA
      (Path.transport (A := KleinBottle) (D := kleinCode) (Path.symm kleinLoopA) x)) = z := by
    rw [Path.transport_symm_right]
    exact cast_kleinCode_base_kleinCodeOfProd z
  have h2 := kleinCode_transport_loopA (kleinCodeToProd (Path.transport (A := KleinBottle) (D := kleinCode) (Path.symm kleinLoopA) x))
  rw [kleinCodeOfProd_toProd] at h2
  rw [h] at h2
  -- h2 : z = (z'.fst + 1, -z'.snd) where z' is the transported value
  let z' := kleinCodeToProd (Path.transport (A := KleinBottle) (D := kleinCode) (Path.symm kleinLoopA) x)
  have hfst_eq : z.fst = z'.fst + 1 := _root_.congrArg Prod.fst h2
  have hsnd_eq : z.snd = -z'.snd := _root_.congrArg Prod.snd h2
  apply Prod.ext
  · -- z'.fst = z.fst - 1
    show z'.fst = z.fst - 1
    simp only [hfst_eq, Int.add_sub_cancel]
  · -- z'.snd = -z.snd
    show z'.snd = -z.snd
    simp only [hsnd_eq, Int.neg_neg]

/-- Transport along inverse of `kleinLoopB`. -/
@[simp] theorem kleinCode_transport_loopB_inv (z : Int × Int) :
    kleinCodeToProd (Path.transport (A := KleinBottle) (D := kleinCode)
      (Path.symm kleinLoopB) (kleinCodeOfProd z)) = (z.1, z.2 - 1) := by
  let x := kleinCodeOfProd z
  have h : kleinCodeToProd (Path.transport (A := KleinBottle) (D := kleinCode) kleinLoopB
      (Path.transport (A := KleinBottle) (D := kleinCode) (Path.symm kleinLoopB) x)) = z := by
    rw [Path.transport_symm_right]
    exact cast_kleinCode_base_kleinCodeOfProd z
  have h2 := kleinCode_transport_loopB (kleinCodeToProd (Path.transport (A := KleinBottle) (D := kleinCode) (Path.symm kleinLoopB) x))
  rw [kleinCodeOfProd_toProd] at h2
  rw [h] at h2
  ext
  · simp at h2
    have h2_1 := _root_.congrArg Prod.fst h2
    simp at h2_1
    exact h2_1.symm
  · simp at h2
    have h2_2 := _root_.congrArg Prod.snd h2
    simp at h2_2
    exact eq_sub_of_add_eq' h2_2.symm

/-- Encoding a path composed with `kleinLoopA`. -/
theorem kleinEncodePath_trans_loopA (p : Path kleinBase kleinBase) :
    kleinEncodePath (Path.trans p kleinLoopA) =
      ((kleinEncodePath p).1 + 1, -(kleinEncodePath p).2) := by
  let z := kleinEncodePath p
  have h : kleinEncodePath (Path.trans p kleinLoopA) =
      kleinCodeToProd (Path.transport (A := KleinBottle) (D := kleinCode)
        kleinLoopA (kleinCodeOfProd z)) := by
    simp only [kleinEncodePath, kleinEncodeRaw, Path.transport_trans]
    congr 2
    dsimp only [z, kleinEncodePath, kleinEncodeRaw]
    rw [kleinCodeOfProd_toProd]
  rw [h, kleinCode_transport_loopA]

/-- Encoding a path composed with `kleinLoopB`. -/
theorem kleinEncodePath_trans_loopB (p : Path kleinBase kleinBase) :
    kleinEncodePath (Path.trans p kleinLoopB) =
      ((kleinEncodePath p).1, (kleinEncodePath p).2 + 1) := by
  let z := kleinEncodePath p
  have h : kleinEncodePath (Path.trans p kleinLoopB) =
      kleinCodeToProd (Path.transport (A := KleinBottle) (D := kleinCode)
        kleinLoopB (kleinCodeOfProd z)) := by
    simp only [kleinEncodePath, kleinEncodeRaw, Path.transport_trans]
    congr 2
    dsimp only [z, kleinEncodePath, kleinEncodeRaw]
    rw [kleinCodeOfProd_toProd]
  rw [h, kleinCode_transport_loopB]

/-- Encoding a path composed with inverse of `kleinLoopA`. -/
theorem kleinEncodePath_trans_symm_loopA (p : Path kleinBase kleinBase) :
    kleinEncodePath (Path.trans p (Path.symm kleinLoopA)) =
      ((kleinEncodePath p).1 - 1, -(kleinEncodePath p).2) := by
  let z := kleinEncodePath p
  have h : kleinEncodePath (Path.trans p (Path.symm kleinLoopA)) =
      kleinCodeToProd (Path.transport (A := KleinBottle) (D := kleinCode)
        (Path.symm kleinLoopA) (kleinCodeOfProd z)) := by
    simp only [kleinEncodePath, kleinEncodeRaw, Path.transport_trans]
    congr 2
    dsimp only [z, kleinEncodePath, kleinEncodeRaw]
    rw [kleinCodeOfProd_toProd]
  rw [h, kleinCode_transport_loopA_inv]

/-- Encoding a path composed with inverse of `kleinLoopB`. -/
theorem kleinEncodePath_trans_symm_loopB (p : Path kleinBase kleinBase) :
    kleinEncodePath (Path.trans p (Path.symm kleinLoopB)) =
      ((kleinEncodePath p).1, (kleinEncodePath p).2 - 1) := by
  let z := kleinEncodePath p
  have h : kleinEncodePath (Path.trans p (Path.symm kleinLoopB)) =
      kleinCodeToProd (Path.transport (A := KleinBottle) (D := kleinCode)
        (Path.symm kleinLoopB) (kleinCodeOfProd z)) := by
    simp only [kleinEncodePath, kleinEncodeRaw, Path.transport_trans]
    congr 2
    dsimp only [z, kleinEncodePath, kleinEncodeRaw]
    rw [kleinCodeOfProd_toProd]
  rw [h, kleinCode_transport_loopB_inv]

@[simp] theorem kleinEncodePath_loopA : kleinEncodePath kleinLoopA = (1, 0) := by
  rw [← Path.trans_refl_left kleinLoopA]
  rw [kleinEncodePath_trans_loopA]
  rw [kleinEncodePath_refl]
  simp

@[simp] theorem kleinEncodePath_loopB : kleinEncodePath kleinLoopB = (0, 1) := by
  rw [← Path.trans_refl_left kleinLoopB]
  rw [kleinEncodePath_trans_loopB]
  rw [kleinEncodePath_refl]
  simp

theorem sub_eq_add_neg' (a b : Int) : a - b = a + -b := rfl

theorem Int.negSucc_add_neg_one' (n : Nat) : Int.negSucc n + -1 = Int.negSucc (n + 1) := rfl

/-- Encoding `a^n` for integer powers. The key point is that repeatedly going
    around `a` alternates the sign of the second coordinate. -/
theorem kleinEncodePath_trans_loopAPathZPow (p : Path kleinBase kleinBase) (n : Int) :
    kleinEncodePath (Path.trans p (kleinLoopAPathZPow n)) =
      ((kleinEncodePath p).1 + n, kleinSign n * (kleinEncodePath p).2) := by
  revert p
  cases n with
  | ofNat n =>
    induction n with
    | zero =>
      intro p
      simp only [kleinLoopAPathZPow, kleinLoopAPathPow, Path.trans_refl_right, Int.ofNat_eq_coe]
      simp [Int.add_zero, kleinSign_zero, Int.one_mul]
    | succ n ih =>
      intro p
      simp only [kleinLoopAPathZPow, kleinLoopAPathPow]
      rw [← Path.trans_assoc]
      rw [kleinEncodePath_trans_loopA]
      simp only [kleinLoopAPathZPow] at ih
      rw [ih]
      apply Prod.ext
      · simp [Int.add_assoc]
      · simp [kleinSign_succ, Int.neg_mul]
  | negSucc n =>
    induction n with
    | zero =>
      intro p
      simp only [kleinLoopAPathZPow, kleinLoopAPathPow]
      simp only [Path.trans_refl_left]
      rw [kleinEncodePath_trans_symm_loopA]
      simp [sub_eq_add_neg', Int.neg_mul, Int.one_mul]
    | succ n ih =>
      intro p
      have h_decomp : kleinLoopAPathZPow (Int.negSucc (n + 1)) =
          Path.trans (Path.symm kleinLoopA) (kleinLoopAPathZPow (Int.negSucc n)) := by
        simp only [kleinLoopAPathZPow, kleinLoopAPathPow]
        rw [Path.symm_trans]
      rw [h_decomp]
      rw [← Path.trans_assoc]
      have ih_applied := ih (Path.trans p (Path.symm kleinLoopA))
      rw [kleinEncodePath_trans_symm_loopA] at ih_applied
      conv =>
        lhs
        erw [ih_applied]
      -- Now we need to prove:
      -- (p.kleinEncodePath.fst - 1 + Int.negSucc n, kleinSign (Int.negSucc n) * -(p.kleinEncodePath.snd))
      -- = (p.kleinEncodePath.fst + Int.negSucc (n + 1), kleinSign (Int.negSucc (n + 1)) * p.kleinEncodePath.snd)
      apply Prod.ext
      · -- First coordinate: p.fst - 1 + negSucc n = p.fst + negSucc (n + 1)
        simp only [sub_eq_add_neg', Int.add_assoc]
        rw [Int.add_comm (-1)]
        rw [Int.negSucc_add_neg_one']
      · -- Second coordinate involves sign manipulation
        simp only
        have sign_n : kleinSign (Int.negSucc n) = if (n + 1) % 2 = 0 then 1 else -1 := by
          simp [kleinSign]
        have sign_n1 : kleinSign (Int.negSucc (n + 1)) = if (n + 2) % 2 = 0 then 1 else -1 := by
          unfold kleinSign
          simp only [Int.natAbs_negSucc]
        rw [sign_n, sign_n1]
        by_cases h : (n + 1) % 2 = 0
        · have h2 : (n + 2) % 2 = 1 := by omega
          simp [h, h2, Int.neg_mul, Int.one_mul]
        · have h1 : (n + 1) % 2 = 1 := by omega
          have h2 : (n + 2) % 2 = 0 := by omega
          simp [h1, h2, Int.neg_mul, Int.neg_neg, Int.one_mul]

/-- Encoding a path followed by `b^n`. -/
theorem kleinEncodePath_trans_loopBPathZPow (p : Path kleinBase kleinBase) (n : Int) :
    kleinEncodePath (Path.trans p (kleinLoopBPathZPow n)) =
      ((kleinEncodePath p).1, (kleinEncodePath p).2 + n) := by
  revert p
  cases n with
  | ofNat n =>
    induction n with
    | zero =>
      intro p
      simp only [kleinLoopBPathZPow, kleinLoopBPathPow, Path.trans_refl_right, Int.ofNat_eq_coe]
      simp [Int.add_zero]
    | succ n ih =>
      intro p
      simp only [kleinLoopBPathZPow, kleinLoopBPathPow]
      rw [← Path.trans_assoc]
      rw [kleinEncodePath_trans_loopB]
      simp only [kleinLoopBPathZPow] at ih
      rw [ih]
      simp [Int.add_assoc]
  | negSucc n =>
    induction n with
    | zero =>
      intro p
      simp only [kleinLoopBPathZPow, kleinLoopBPathPow]
      simp only [Path.trans_refl_left]
      rw [kleinEncodePath_trans_symm_loopB]
      simp [sub_eq_add_neg']
    | succ n ih =>
      intro p
      have h_decomp : kleinLoopBPathZPow (Int.negSucc (n + 1)) =
          Path.trans (Path.symm kleinLoopB) (kleinLoopBPathZPow (Int.negSucc n)) := by
        simp only [kleinLoopBPathZPow, kleinLoopBPathPow]
        rw [Path.symm_trans]
      rw [h_decomp]
      rw [← Path.trans_assoc]
      conv =>
        lhs
        erw [ih (Path.trans p (Path.symm kleinLoopB))]
      rw [kleinEncodePath_trans_symm_loopB]
      dsimp
      apply Prod.ext
      · rfl
      · rw [sub_eq_add_neg', Int.add_assoc]
        rw [Int.add_comm (-1)]
        rw [Int.negSucc_add_neg_one']

/-- Decode a pair of integers as a Klein bottle path `a^m ⋅ b^n`. -/
noncomputable def kleinDecodePath (z : Int × Int) : Path kleinBase kleinBase :=
  Path.trans (kleinLoopAPathZPow z.1) (kleinLoopBPathZPow z.2)

/-- `encode ∘ decode = id` on `ℤ × ℤ`. -/
theorem kleinEncode_decode (z : Int × Int) :
    kleinEncodePath (kleinDecodePath z) = z := by
  unfold kleinDecodePath
  rw [kleinEncodePath_trans_loopBPathZPow]
  have h : kleinEncodePath (kleinLoopAPathZPow z.fst) = (z.fst, 0) := by
    have h2 := kleinEncodePath_trans_loopAPathZPow (Path.refl kleinBase) z.fst
    rw [Path.trans_refl_left] at h2
    rw [h2]
    rw [kleinEncodePath_refl]
    simp
  rw [h]
  simp

/-- Encode map on the quotient level. -/
@[simp] noncomputable def kleinEncodeLift : KleinBottleLoopQuot → Int × Int :=
  Quot.lift (fun (p : Path kleinBase kleinBase) => kleinEncodePath p)
    (by
      intro p q h
      exact kleinEncodePath_rweq (p := p) (q := q) h)

@[simp] theorem kleinEncodeLift_ofLoop (p : Path kleinBase kleinBase) :
    kleinEncodeLift (LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase) p) =
      kleinEncodePath p := rfl

/-- Fundamental-group encoding map `π₁(K) → ℤ × ℤ`. -/
@[simp] noncomputable def kleinEncode : kleinPiOne → Int × Int :=
  kleinEncodeLift

/-- Decode a pair of integers as a Klein bottle loop class. -/
@[simp] noncomputable def kleinDecodeQuot : Int × Int → kleinPiOne :=
  fun z =>
    LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase) (kleinDecodePath z)

@[simp] theorem kleinEncode_loopAClass :
    kleinEncode kleinLoopAClass = (1, 0) := kleinEncodePath_loopA

@[simp] theorem kleinEncode_loopBClass :
    kleinEncode kleinLoopBClass = (0, 1) := kleinEncodePath_loopB

/-- Encode∘decode is the identity on ℤ × ℤ. -/
@[simp] theorem kleinEncode_kleinDecodeQuot (z : Int × Int) :
    kleinEncode (kleinDecodeQuot z) = z := kleinEncode_decode z

@[simp] theorem kleinDecodePath_zero_zero :
    kleinDecodePath (0, 0) = Path.refl kleinBase := by
  unfold kleinDecodePath
  simp [kleinLoopAPathZPow, kleinLoopAPathPow,
    kleinLoopBPathZPow, kleinLoopBPathPow]

@[simp] theorem kleinDecodeQuot_zero_zero :
    kleinDecodeQuot (0, 0) = LoopQuot.id := by
  unfold kleinDecodeQuot kleinDecodePath
  have htrans :
      Path.trans (kleinLoopAPathZPow 0) (kleinLoopBPathZPow 0) =
        Path.refl kleinBase := by
    simp [kleinLoopAPathZPow, kleinLoopAPathPow,
      kleinLoopBPathZPow, kleinLoopBPathPow]
  change LoopQuot.ofLoop
      (Path.trans (kleinLoopAPathZPow 0) (kleinLoopBPathZPow 0)) =
    LoopQuot.id
  rw [htrans]
  rfl

@[simp] theorem kleinDecodeEq_kleinEncodeEq
    (e : kleinBase = kleinBase) :
    (kleinDecodePath (kleinEncodePath (Path.ofEq e))).toEq = e := by
  cases e
  simp

@[simp] theorem kleinDecodeQuot_kleinEncode (x : kleinPiOne) :
    kleinDecodeQuot (kleinEncode x) = x := by
  apply PathRwQuot.eq_of_toEq_eq (A := KleinBottle) (a := kleinBase) (b := kleinBase)
  refine Quot.inductionOn x ?_
  intro p
  have hcanon :
      kleinEncodePath (Path.ofEq p.toEq) = kleinEncodePath p := by
    have hcanonRw : RwEq (Path.ofEq p.toEq) p := (rweq_canon (p := p)).symm
    exact kleinEncodePath_rweq (h := hcanonRw)
  have hgoal₀ := kleinDecodeEq_kleinEncodeEq (e := p.toEq)
  have hcanonDecode :
      (kleinDecodePath (kleinEncodePath (Path.ofEq p.toEq))).toEq =
        (kleinDecodePath (kleinEncodePath p)).toEq := by
    have := _root_.congrArg (fun z : Int × Int => kleinDecodePath z) hcanon.symm
    exact _root_.congrArg Path.toEq this
  have hgoal :
      (kleinDecodePath (kleinEncodePath p)).toEq = p.toEq :=
    hcanonDecode ▸ hgoal₀
  change
      (kleinDecodePath (kleinEncodePath p)).toEq = p.toEq
  exact hgoal

/-- **Fundamental group of the Klein bottle is equivalent to ℤ ⋊ ℤ.**

This is the main result: π₁(K) ≅ ℤ × ℤ as sets, where the group structure
on ℤ × ℤ is the semidirect product with multiplication
`(m₁, n₁) * (m₂, n₂) = (m₁ + m₂, (-1)^{m₂} · n₁ + n₂)`. -/
noncomputable def kleinPiOneEquivIntProd :
    SimpleEquiv kleinPiOne (Int × Int) where
  toFun := kleinEncode
  invFun := kleinDecodeQuot
  left_inv := by
    intro x
    exact kleinDecodeQuot_kleinEncode (x := x)
  right_inv := by
    intro z
    exact kleinEncode_kleinDecodeQuot (z := z)

/-! ## Summary

We have fully established the fundamental group of the Klein bottle:

### Main Result

**`kleinPiOneEquivIntProd : SimpleEquiv kleinPiOne (Int × Int)`**

This is a constructive equivalence (no axioms beyond the HIT axioms) proving
that π₁(K, base) is isomorphic to ℤ × ℤ as sets.

### Group Structure

The group operation on ℤ × ℤ is the **semidirect product** ℤ ⋊ ℤ:
```
(m₁, n₁) * (m₂, n₂) = (m₁ + m₂, (-1)^{m₂} · n₁ + n₂)
```

This is captured by `kleinSemidirectMul` and proved to be respected by `kleinDecode`
via `kleinDecode_pairMul`.

### Key Theorems

1. **`kleinEncode_kleinDecodeQuot`**: encode ∘ decode = id
2. **`kleinDecodeQuot_kleinEncode`**: decode ∘ encode = id
3. **`kleinLoopBClass_zpow_mul_loopAClass_zpow`**: b^n · a^m = a^m · b^{(-1)^m · n}
4. **`KleinBottleWord.toLoopQuot_mul`**: decode respects semidirect multiplication

### Method

The proof follows the **encode-decode** pattern from HoTT:
- Define a type family `kleinCode : KleinBottle → Type` via the recursor
- Transport along `kleinLoopA` negates the second coordinate (reflecting a·b·a⁻¹ = b⁻¹)
- Transport along `kleinLoopB` increments the second coordinate
- The encode map `kleinEncode` transports the basepoint (0,0) along loops
- The decode map `kleinDecodePath` constructs a^m · b^n from (m,n)
- The roundtrip properties follow from the transport laws
-/

end Path
end ComputationalPaths
