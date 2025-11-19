/-
# The torus as a higher-inductive type (axiomatic skeleton)

This module introduces `Torus` together with its base-point, two fundamental loops,
and a surface path witnessing their commutativity.  We provide an eliminator
stated in the computational-path style.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Basic.Univalence
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup

namespace ComputationalPaths
namespace Path

universe u v

/-- Abstract torus type. -/
axiom Torus : Type u

/-- Distinguished point on the torus. -/
axiom torusBase : Torus

/-- First fundamental loop around the torus. -/
axiom torusLoop1 : Path (A := Torus) torusBase torusBase

/-- Second fundamental loop around the torus. -/
axiom torusLoop2 : Path (A := Torus) torusBase torusBase

/-- Surface path witnessing the commutativity of the two loops. -/
axiom torusSurf :
  Path.trans torusLoop1 torusLoop2 = Path.trans torusLoop2 torusLoop1

/-- Data required to eliminate from the torus into a target type `C`. -/
structure TorusRecData (C : Type v) where
  base : C
  loop1 : Path base base
  loop2 : Path base base
  surf : Path.trans loop1 loop2 = Path.trans loop2 loop1

/-- Torus eliminator (recursor). -/
axiom torusRec {C : Type v} (data : TorusRecData C) : Torus → C

/-- β-rule for `torusRec` at the base point. -/
axiom torusRec_base {C : Type v} (data : TorusRecData C) :
  torusRec data torusBase = data.base

/-- β-rule for `torusRec` on the first fundamental loop. -/
axiom torusRec_loop1 {C : Type v} (data : TorusRecData C) :
  Path.trans
    (Path.symm (Path.ofEq (torusRec_base (C := C) data)))
    (Path.trans
      (Path.congrArg (torusRec data) torusLoop1)
      (Path.ofEq (torusRec_base (C := C) data))) =
  data.loop1

/-- β-rule for `torusRec` on the second fundamental loop. -/
axiom torusRec_loop2 {C : Type v} (data : TorusRecData C) :
  Path.trans
    (Path.symm (Path.ofEq (torusRec_base (C := C) data)))
    (Path.trans
      (Path.congrArg (torusRec data) torusLoop2)
      (Path.ofEq (torusRec_base (C := C) data))) =
  data.loop2

/-- Data for the dependent eliminator of the torus. -/
structure TorusIndData (C : Torus → Type v) where
  base : C torusBase
  loop1 : Path (Path.transport (A := Torus) (D := C) torusLoop1 base) base
  loop2 : Path (Path.transport (A := Torus) (D := C) torusLoop2 base) base
  -- Note: Surface coherence omitted for now.

/-- Dependent eliminator (induction principle) for the torus. -/
axiom torusInd {C : Torus → Type v} (data : TorusIndData C) :
  (x : Torus) → C x

/-- β-rule for the dependent eliminator at the base point. -/
axiom torusInd_base {C : Torus → Type v} (data : TorusIndData C) :
  torusInd data torusBase = data.base

/-- Dependent β-rule for the first fundamental loop. -/
axiom torusInd_loop1 {C : Torus → Type v} (data : TorusIndData C) :
  Path.trans
    (Path.symm
      (Path.congrArg
        (fun x =>
          Path.transport (A := Torus) (D := fun y => C y) torusLoop1 x)
        (Path.ofEq (torusInd_base (C := C) data))))
    (Path.trans
      (Path.apd (A := Torus) (B := fun y => C y)
        (f := torusInd data) torusLoop1)
      (Path.ofEq (torusInd_base (C := C) data))) =
  data.loop1

/-- Dependent β-rule for the second fundamental loop. -/
axiom torusInd_loop2 {C : Torus → Type v} (data : TorusIndData C) :
  Path.trans
    (Path.symm
      (Path.congrArg
        (fun x =>
          Path.transport (A := Torus) (D := fun y => C y) torusLoop2 x)
        (Path.ofEq (torusInd_base (C := C) data))))
    (Path.trans
      (Path.apd (A := Torus) (B := fun y => C y)
        (f := torusInd data) torusLoop2)
      (Path.ofEq (torusInd_base (C := C) data))) =
  data.loop2

-- Note: The β-rule for the surface is more complex to state and is omitted for now
-- as it requires 2-dimensional path algebra which is partially available in `Globular`.

noncomputable section

open SimpleEquiv

/-- Equivalence shifting the first coordinate of the plane. -/
def torusEquiv1 : SimpleEquiv (Int × Int) (Int × Int) where
  toFun := fun (x, y) => (x + 1, y)
  invFun := fun (x, y) => (x - 1, y)
  left_inv := by intro (x, y); simp
  right_inv := by intro (x, y); simp

/-- Equivalence shifting the second coordinate of the plane. -/
def torusEquiv2 : SimpleEquiv (Int × Int) (Int × Int) where
  toFun := fun (x, y) => (x, y + 1)
  invFun := fun (x, y) => (x, y - 1)
  left_inv := by intro (x, y); simp
  right_inv := by intro (x, y); simp

theorem SimpleEquiv_eq {α : Type u} {β : Type v} (e1 e2 : SimpleEquiv α β)
  (h1 : e1.toFun = e2.toFun) (h2 : e1.invFun = e2.invFun) : e1 = e2 := by
  cases e1
  cases e2
  congr

theorem torusEquiv_comm :
    SimpleEquiv.comp torusEquiv1 torusEquiv2 =
      SimpleEquiv.comp torusEquiv2 torusEquiv1 := by
  apply SimpleEquiv_eq
  . rfl
  . rfl

def torusCodeData : TorusRecData (Type _) where
  base := Int × Int
  loop1 := Path.ua torusEquiv1
  loop2 := Path.ua torusEquiv2
  surf := by
    rw [ua_trans, ua_trans]
    exact Path.toEq (Path.congrArg Path.ua (Path.ofEq torusEquiv_comm))

/-- Universal-cover code family for the torus, landing in the plane. -/
noncomputable def torusCode : Torus → Type _ :=
  torusRec torusCodeData

@[simp] theorem torusCode_base :
    torusCode torusBase = (Int × Int) :=
  torusRec_base torusCodeData

/-- View an element of `torusCode torusBase` as a pair of integers. -/
@[simp] def torusCodeToProd : torusCode torusBase → Int × Int :=
  fun z => Eq.mp torusCode_base z

/-- Interpret a pair of integers as an element of `torusCode torusBase`. -/
@[simp] def torusCodeOfProd : Int × Int → torusCode torusBase :=
  fun z => Eq.mpr torusCode_base z

@[simp] theorem torusCodeToProd_ofProd (z : Int × Int) :
    torusCodeToProd (torusCodeOfProd z) = z := by
  simp [torusCodeToProd, torusCodeOfProd]

@[simp] theorem torusCodeOfProd_toProd (z : torusCode torusBase) :
    torusCodeOfProd (torusCodeToProd z) = z := by
  simp [torusCodeToProd, torusCodeOfProd]

/-- Chosen basepoint in the code fibre at the torus base. -/
@[simp] def torusCodeZero : torusCode torusBase :=
  torusCodeOfProd (0, 0)

/-- Transport the base code point along a loop to encode a path. -/
@[simp] def torusEncodeRaw (x : Torus) :
    Path torusBase x → torusCode x :=
  fun p => Path.transport (A := Torus) (D := torusCode) p torusCodeZero

/-- Encode a loop `p : base = base` as a pair of integers. -/
@[simp] def torusEncodePath :
    Path torusBase torusBase → Int × Int :=
  fun p => torusCodeToProd (torusEncodeRaw torusBase p)

@[simp] theorem torusEncodePath_refl :
    torusEncodePath (Path.refl torusBase) = (0, 0) := by
  change torusCodeToProd torusCodeZero = (0, 0)
  simp [torusCodeZero, torusCodeToProd]

@[simp] theorem torusCode_loop1_path :
    Path.trans (Path.symm (Path.ofEq torusCode_base))
        (Path.trans (Path.congrArg torusCode torusLoop1)
          (Path.ofEq torusCode_base)) =
      Path.ua torusEquiv1 :=
  torusRec_loop1 torusCodeData

@[simp] theorem torusCode_loop2_path :
    Path.trans (Path.symm (Path.ofEq torusCode_base))
        (Path.trans (Path.congrArg torusCode torusLoop2)
          (Path.ofEq torusCode_base)) =
      Path.ua torusEquiv2 :=
  torusRec_loop2 torusCodeData

/-- Iterate the first fundamental loop `n` times. -/
def torusLoop1PathPow : Nat → Path torusBase torusBase
  | 0 => Path.refl torusBase
  | Nat.succ n => Path.trans (torusLoop1PathPow n) torusLoop1

def torusLoop1PathZPow : Int → Path torusBase torusBase
  | Int.ofNat n => torusLoop1PathPow n
  | Int.negSucc n => Path.symm (torusLoop1PathPow (Nat.succ n))

/-- Iterate the second fundamental loop `n` times. -/
def torusLoop2PathPow : Nat → Path torusBase torusBase
  | 0 => Path.refl torusBase
  | Nat.succ n => Path.trans (torusLoop2PathPow n) torusLoop2

def torusLoop2PathZPow : Int → Path torusBase torusBase
  | Int.ofNat n => torusLoop2PathPow n
  | Int.negSucc n => Path.symm (torusLoop2PathPow (Nat.succ n))

/-- Decode a pair of integers into a loop on the torus. -/
def torusDecodePath (z : Int × Int) : Path torusBase torusBase :=
  Path.trans (torusLoop1PathZPow z.1) (torusLoop2PathZPow z.2)

end

end Path
end ComputationalPaths
