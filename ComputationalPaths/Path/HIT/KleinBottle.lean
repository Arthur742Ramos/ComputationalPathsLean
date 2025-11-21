/-
# The Klein bottle as a higher-inductive type (axiomatic skeleton)

This module follows the same pattern as `Circle` and `Torus`: we introduce an
abstract type equipped with the fundamental loops and the characteristic
surface relation `aba⁻¹ = b⁻¹`.  Providing this HIT-like API now lets us stage
the forthcoming fundamental-group calculation without committing to a concrete
realisation yet.
-/

import ComputationalPaths.Path.Basic
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

/-- Natural powers of the `b`-loop at the path level. -/
def kleinLoopBPathPow : Nat → Path kleinBase kleinBase
  | 0 => Path.refl _
  | Nat.succ n => Path.trans (kleinLoopBPathPow n) kleinLoopB

@[simp] theorem kleinLoopBPathPow_zero :
    kleinLoopBPathPow 0 = Path.refl _ := rfl

@[simp] theorem kleinLoopBPathPow_succ (n : Nat) :
    kleinLoopBPathPow (Nat.succ n) =
      Path.trans (kleinLoopBPathPow n) kleinLoopB := rfl

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

/-- Conjugation relation expressed in π₁(K, base). -/
@[simp] theorem kleinPiOne_relation :
    PiOne.mul
        (PiOne.mul kleinLoopAElement kleinLoopBElement)
        (PiOne.inv kleinLoopAElement) =
      PiOne.inv kleinLoopBElement := by
  unfold PiOne.mul PiOne.inv kleinLoopAElement kleinLoopBElement
  exact kleinLoop_relation_class

end LoopAlgebra

end

-- As with the torus, the higher coherence coming from `kleinSurf` is deferred
-- until the globular 2-path algebra is fully integrated.

end Path
end ComputationalPaths
