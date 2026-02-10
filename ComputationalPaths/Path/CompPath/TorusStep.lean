/-
# π₁(T²) ≃ ℤ × ℤ

This module packages the torus π₁ computation as a `PathSimpleEquiv`
between `π₁(T²)` and `ℤ × ℤ`.

## Key Results

- `torusPiOneEncode_torusDecode`: encoding after decoding is the identity (as a `Path`).
- `torusDecode_torusPiOneEncode`: decoding after encoding is the identity (as a `Path`).
- `torusPiOneEquivIntProd`: `π₁(T²)` is `PathSimpleEquiv` to `ℤ × ℤ`.
-/

import ComputationalPaths.Path.CompPath.Torus
import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.Rewrite.SimpleEquiv

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path
open CompPath
open SimpleEquiv

universe u v

/-- Path-based equivalence structure (inverse laws witnessed by `Path`). -/
structure PathSimpleEquiv (α : Type u) (β : Type v) where
  /-- Forward map. -/
  toFun : α → β
  /-- Inverse map. -/
  invFun : β → α
  /-- Inverse after forward map is the identity, as a `Path`. -/
  left_inv : ∀ x : α, Path (invFun (toFun x)) x
  /-- Forward after inverse map is the identity, as a `Path`. -/
  right_inv : ∀ y : β, Path (toFun (invFun y)) y

/-- Convert a `PathSimpleEquiv` into a `SimpleEquiv`. -/
def pathSimpleEquivToSimpleEquiv {α : Type u} {β : Type v}
    (e : PathSimpleEquiv α β) : SimpleEquiv α β :=
  { toFun := e.toFun
    invFun := e.invFun
    left_inv := fun x => (e.left_inv x).toEq
    right_inv := fun y => (e.right_inv y).toEq }

/-- A discharge-friendly interface for `π₁(T²) ≃ ℤ × ℤ`.

Unlike `HasTorusLoopDecode`, this class only talks about the loop *quotient*
(`π₁`) rather than raw loop normal forms.  Downstream developments that only
need the fundamental group can depend on this weaker hypothesis.
-/
class HasTorusPiOneEncode : Type u where
  /-- Winding-number map `π₁(T²) → ℤ × ℤ`. -/
  encode : torusPiOne → Int × Int
  /-- Encoding after decoding is the identity on `ℤ × ℤ`. -/
  encode_torusDecode : ∀ z : Int × Int, Path (encode (torusDecode z)) z
  /-- Decoding after encoding is the identity on `π₁(T²)`. -/
  torusDecode_encode : ∀ x : torusPiOne, Path (torusDecode (encode x)) x

/-- Winding-number map specialised from `HasTorusPiOneEncode`. -/
@[simp] def torusPiOneEncode [HasTorusPiOneEncode] : torusPiOne → Int × Int :=
  HasTorusPiOneEncode.encode

noncomputable def torusPiOneEncode_torusDecode [HasTorusPiOneEncode] (z : Int × Int) :
    Path (torusPiOneEncode (torusDecode z)) z :=
  HasTorusPiOneEncode.encode_torusDecode z

noncomputable def torusDecode_torusPiOneEncode [HasTorusPiOneEncode] (x : torusPiOne) :
    Path (torusDecode (torusPiOneEncode x)) x :=
  HasTorusPiOneEncode.torusDecode_encode x

@[simp] theorem torusPiOneEncode_torusDecode_eq [HasTorusPiOneEncode] (z : Int × Int) :
    torusPiOneEncode (torusDecode z) = z :=
  (torusPiOneEncode_torusDecode (z := z)).toEq

@[simp] theorem torusDecode_torusPiOneEncode_eq [HasTorusPiOneEncode] (x : torusPiOne) :
    torusDecode (torusPiOneEncode x) = x :=
  (torusDecode_torusPiOneEncode (x := x)).toEq

/-!
## Canonical instance from the circle π₁ computation

Because `Torus` is defined as `Circle × Circle`, we can construct the torus
π₁ encode/decode data from:
- the product fundamental group equivalence, and
- the circle π₁ encode/decode interface (`HasCirclePiOneEncode`).
-/
noncomputable instance instHasTorusPiOneEncode_ofCircle :
    HasTorusPiOneEncode.{u} where
  encode := fun x =>
    (circlePiOneEncode x.1, circlePiOneEncode x.2)
  encode_torusDecode := by
    intro z
    cases z with
    | mk z1 z2 =>
        exact
          Path.prodMk
            (Path.ofEq (circlePiOneEncode_circleDecode z1))
            (Path.ofEq (circlePiOneEncode_circleDecode z2))
  torusDecode_encode := by
    intro x
    cases x with
    | mk x1 x2 =>
        exact
          Path.prodMk
            (Path.ofEq (circleDecode_circlePiOneEncode x1))
            (Path.ofEq (circleDecode_circlePiOneEncode x2))



/-- Fundamental group of the torus is equivalent to `ℤ × ℤ`. -/
noncomputable def torusPiOneEquivIntProd [HasTorusPiOneEncode] :
    PathSimpleEquiv torusPiOne (Int × Int) where
  toFun := torusPiOneEncode
  invFun := torusDecode
  left_inv := by
    intro x
    simpa using (torusDecode_torusPiOneEncode (x := x))
  right_inv := by
    intro z
    simpa using (torusPiOneEncode_torusDecode (z := z))

/-- Eq-based equivalence for downstream developments. -/
noncomputable def torusPiOneEquivIntProdSimple [HasTorusPiOneEncode] :
    SimpleEquiv torusPiOne (Int × Int) :=
  pathSimpleEquivToSimpleEquiv torusPiOneEquivIntProd

end Path
end ComputationalPaths
