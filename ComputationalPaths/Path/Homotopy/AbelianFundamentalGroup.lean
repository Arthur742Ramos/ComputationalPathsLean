/-
# Abelian Fundamental Groups via Eckmann-Hilton

This module packages an Eckmann-Hilton style criterion for commutativity and
applies it to the torus fundamental group computed as Z x Z.

## Key Results

- `PiOneOps`: minimal multiplication/unit data for a pi_1-style group.
- `PiOneInterchange`: a second multiplication with an interchange law.
- `piOne_comm_of_interchange`: Eckmann-Hilton commutativity lemma.
- `torusPiOne_interchange`: interchange law for torus pi_1 via Z x Z addition.
- `torusPiOne_abelian`: torus pi_1 is abelian.

## References

- Eckmann & Hilton (1962)
- HoTT Book, Theorem 2.1.6
- de Queiroz et al., Computational Paths
-/

import ComputationalPaths.Path.CompPath.TorusStep

namespace ComputationalPaths
namespace Path
namespace Homotopy

universe u

/-! ## Eckmann-Hilton Data -/

/-- Multiplication and unit data for a fundamental-group-like structure. -/
structure PiOneOps (G : Type u) where
  /-- Multiplication. -/
  mul : G → G → G
  /-- Unit element. -/
  one : G
  /-- Left unit law. -/
  one_mul : ∀ x, mul one x = x
  /-- Right unit law. -/
  mul_one : ∀ x, mul x one = x

/-- A pi_1-style multiplication is abelian when it commutes. -/
noncomputable def PiOneAbelian (G : Type u) (ops : PiOneOps G) : Prop :=
  ∀ x y : G, ops.mul x y = ops.mul y x

/-- Interchange data for two multiplications with a common unit. -/
structure PiOneInterchange (G : Type u) (ops : PiOneOps G) where
  /-- Horizontal multiplication. -/
  hmul : G → G → G
  /-- Left unit for the horizontal multiplication. -/
  hmul_one_left : ∀ x, hmul ops.one x = x
  /-- Right unit for the horizontal multiplication. -/
  hmul_one_right : ∀ x, hmul x ops.one = x
  /-- Interchange law between vertical and horizontal multiplication. -/
  interchange : ∀ x1 x2 y1 y2,
      hmul (ops.mul x1 x2) (ops.mul y1 y2) =
        ops.mul (hmul x1 y1) (hmul x2 y2)

/-! ## Eckmann-Hilton Commutativity -/

/-- **Eckmann-Hilton**: interchange implies commutativity. -/
theorem piOne_comm_of_interchange {G : Type u} {ops : PiOneOps G}
    (H : PiOneInterchange G ops) : PiOneAbelian G ops := by
  intro x y
  have mul_eq_hmul : ops.mul x y = H.hmul x y := by
    calc
      ops.mul x y
          = ops.mul (H.hmul x ops.one) (H.hmul ops.one y) := by
              simp [H.hmul_one_left, H.hmul_one_right]
      _ = H.hmul (ops.mul x ops.one) (ops.mul ops.one y) := by
              simpa using (H.interchange x ops.one ops.one y).symm
      _ = H.hmul x y := by
              simp [ops.mul_one, ops.one_mul]
  calc
    ops.mul x y = H.hmul x y := mul_eq_hmul
    _ = H.hmul (ops.mul ops.one x) (ops.mul y ops.one) := by
          simp [ops.one_mul, ops.mul_one]
    _ = ops.mul (H.hmul ops.one y) (H.hmul x ops.one) := by
          simpa using (H.interchange ops.one x y ops.one)
    _ = ops.mul y x := by
          simp [H.hmul_one_left, H.hmul_one_right]

/-! ## Torus pi_1 (Z x Z) -/

/-- Componentwise addition on integer pairs. -/
noncomputable def intProdAdd (x y : Int × Int) : Int × Int :=
  (x.1 + y.1, x.2 + y.2)

/-- Zero element in `Int × Int`. -/
noncomputable def intProdZero : Int × Int :=
  (0, 0)

@[simp] theorem intProdAdd_zero_left (x : Int × Int) :
    intProdAdd intProdZero x = x := by
  cases x
  simp [intProdAdd, intProdZero]

@[simp] theorem intProdAdd_zero_right (x : Int × Int) :
    intProdAdd x intProdZero = x := by
  cases x
  simp [intProdAdd, intProdZero]

theorem intProdAdd_interchange (x1 x2 y1 y2 : Int × Int) :
    intProdAdd (intProdAdd x1 x2) (intProdAdd y1 y2) =
      intProdAdd (intProdAdd x1 y1) (intProdAdd x2 y2) := by
  cases x1
  cases x2
  cases y1
  cases y2
  simp [intProdAdd, Int.add_comm, Int.add_left_comm]

section TorusPiOne

variable [HasTorusPiOneEncode]

local notation "encode" => HasTorusPiOneEncode.encode

@[simp] theorem encode_torusDecode (z : Int × Int) : encode (torusDecode z) = z :=
  (HasTorusPiOneEncode.encode_torusDecode z).toEq

/-- Torus pi_1 multiplication induced by Z x Z addition. -/
noncomputable def torusPiOneMul (x y : torusPiOne) : torusPiOne :=
  torusDecode (intProdAdd (encode x) (encode y))

/-- Identity element in torus pi_1. -/
noncomputable def torusPiOneOne : torusPiOne :=
  torusDecode intProdZero

@[simp] theorem torusPiOneEncode_mul (x y : torusPiOne) :
    encode (torusPiOneMul x y) = intProdAdd (encode x) (encode y) := by
  unfold torusPiOneMul
  simp [intProdAdd]

@[simp] theorem torusPiOneEncode_one :
    encode torusPiOneOne = intProdZero := by
  unfold torusPiOneOne
  simp

theorem torusPiOneEncode_injective {x y : torusPiOne}
    (h : encode x = encode y) : x = y := by
  calc
    x = torusDecode (encode x) :=
      (HasTorusPiOneEncode.torusDecode_encode (x := x)).toEq.symm
    _ = torusDecode (encode y) := by rw [h]
    _ = y := (HasTorusPiOneEncode.torusDecode_encode (x := y)).toEq

theorem torusPiOneMul_one_left (x : torusPiOne) :
    torusPiOneMul torusPiOneOne x = x := by
  apply torusPiOneEncode_injective
  calc
    encode (torusPiOneMul torusPiOneOne x) =
        intProdAdd (encode torusPiOneOne) (encode x) := by
          simp [torusPiOneEncode_mul]
    _ = intProdAdd intProdZero (encode x) := by
          rw [torusPiOneEncode_one]
    _ = encode x := by
          simp [intProdAdd_zero_left]

theorem torusPiOneMul_one_right (x : torusPiOne) :
    torusPiOneMul x torusPiOneOne = x := by
  apply torusPiOneEncode_injective
  calc
    encode (torusPiOneMul x torusPiOneOne) =
        intProdAdd (encode x) (encode torusPiOneOne) := by
          simp [torusPiOneEncode_mul]
    _ = intProdAdd (encode x) intProdZero := by
          rw [torusPiOneEncode_one]
    _ = encode x := by
          simp [intProdAdd_zero_right]

theorem torusPiOne_interchange (x1 x2 y1 y2 : torusPiOne) :
    torusPiOneMul (torusPiOneMul x1 x2) (torusPiOneMul y1 y2) =
      torusPiOneMul (torusPiOneMul x1 y1) (torusPiOneMul x2 y2) := by
  apply torusPiOneEncode_injective
  apply Prod.ext <;>
    simp [torusPiOneMul, intProdAdd, Int.add_assoc, Int.add_left_comm]

/-- Operations package for torus pi_1. -/
noncomputable def torusPiOneOps : PiOneOps torusPiOne where
  mul := torusPiOneMul
  one := torusPiOneOne
  one_mul := torusPiOneMul_one_left
  mul_one := torusPiOneMul_one_right

/-- Interchange data for torus pi_1 (using the same multiplication). -/
noncomputable def torusPiOneInterchange : PiOneInterchange torusPiOne torusPiOneOps where
  hmul := torusPiOneMul
  hmul_one_left := torusPiOneMul_one_left
  hmul_one_right := torusPiOneMul_one_right
  interchange := torusPiOne_interchange

/-- Torus pi_1 is abelian (Eckmann-Hilton). -/
theorem torusPiOne_abelian : PiOneAbelian torusPiOne torusPiOneOps :=
  piOne_comm_of_interchange (H := torusPiOneInterchange)

end TorusPiOne

/-! ## Summary

We formulated an interchange criterion for commutativity (Eckmann-Hilton) and
applied it to the torus fundamental group by transporting multiplication
through the Z x Z encode/decode interface.
-/

end Homotopy
end Path
end ComputationalPaths
