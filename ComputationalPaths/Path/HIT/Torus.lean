/-
# The torus as a higher-inductive type (axiomatic skeleton)

This module introduces `Torus` together with its base-point, two fundamental
loops, and a surface path witnessing their commutativity.

## Encode/decode note

Earlier versions of this development used a HoTT-style universal cover
construction (`Torus → Type`) whose transport along loops is described via a
univalence interface (`HasUnivalence`). In standard Lean, that interface is
inconsistent (see `docs/axioms.md`).

To keep the library consistent while retaining a useful π₁ computation API, we
axiomatise only the **winding-number classification data** for torus loops,
packaged as the typeclass `HasTorusLoopDecode`.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.SimpleEquiv

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path

universe u v

/-! ## HIT interface -/

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

noncomputable section

/-! ## Raw loop powers and decoding -/

/-- Iterate the first fundamental loop `n` times (natural powers). -/
@[simp] def torusLoop1PathPow : Nat → Path torusBase torusBase
  | 0 => Path.refl torusBase
  | Nat.succ n => Path.trans (torusLoop1PathPow n) torusLoop1

/-- Integer iteration of the first fundamental loop. -/
@[simp] def torusLoop1PathZPow : Int → Path torusBase torusBase
  | Int.ofNat n => torusLoop1PathPow n
  | Int.negSucc n => Path.symm (torusLoop1PathPow (Nat.succ n))

/-- Iterate the second fundamental loop `n` times (natural powers). -/
@[simp] def torusLoop2PathPow : Nat → Path torusBase torusBase
  | 0 => Path.refl torusBase
  | Nat.succ n => Path.trans (torusLoop2PathPow n) torusLoop2

/-- Integer iteration of the second fundamental loop. -/
@[simp] def torusLoop2PathZPow : Int → Path torusBase torusBase
  | Int.ofNat n => torusLoop2PathPow n
  | Int.negSucc n => Path.symm (torusLoop2PathPow (Nat.succ n))

/-- Decode a pair of integers as the loop `loop1^m ⬝ loop2^n`. -/
@[simp] def torusDecodePath (z : Int × Int) : Path torusBase torusBase :=
  Path.trans (torusLoop1PathZPow z.1) (torusLoop2PathZPow z.2)

/-! ## Winding-number encode/decode interface -/

/-- Encode/decode data for the torus: winding numbers for raw loops. -/
class HasTorusLoopDecode : Type u where
  /-- Integer pair assigned to a raw loop. -/
  encodePath : Path torusBase torusBase → Int × Int
  /-- The winding number is invariant under rewrite equality. -/
  encodePath_rweq :
      ∀ {p q : Path torusBase torusBase}, RwEq p q → encodePath p = encodePath q
  /-- Encoding the canonical decoded loop returns the integer pair. -/
  encodePath_torusDecodePath : ∀ z : Int × Int, encodePath (torusDecodePath z) = z
  /-- Every loop is rewrite-equal to the canonical normal form. -/
  torusLoop_rweq_decode :
      ∀ p : Path torusBase torusBase, RwEq p (torusDecodePath (encodePath p))

/-- Encode a raw torus loop as an integer pair. -/
@[simp] def torusEncodePath [HasTorusLoopDecode] (p : Path torusBase torusBase) : Int × Int :=
  HasTorusLoopDecode.encodePath p

/-- Encoding is invariant under rewrite equality for raw loops. -/
@[simp] theorem torusEncodePath_rweq [h : HasTorusLoopDecode]
    {p q : Path torusBase torusBase} (hpq : RwEq p q) :
    torusEncodePath p = torusEncodePath q :=
  h.encodePath_rweq hpq

/-- Encoding a decoded raw loop returns the integer pair. -/
@[simp] theorem torusEncodePath_torusDecodePath [h : HasTorusLoopDecode] (z : Int × Int) :
    torusEncodePath (torusDecodePath z) = z :=
  h.encodePath_torusDecodePath z

/-- Every loop is `RwEq` to the decoded form of its winding numbers. -/
theorem torusLoop_rweq_decode [h : HasTorusLoopDecode] (p : Path torusBase torusBase) :
    RwEq p (torusDecodePath (torusEncodePath p)) :=
  h.torusLoop_rweq_decode p

/-! ## Loop quotient and fundamental group -/

/-- Loop space of the torus. -/
abbrev TorusLoopSpace : Type u :=
  LoopSpace Torus torusBase

/-- Loop quotient of the torus, i.e. π₁(T²). -/
abbrev TorusLoopQuot : Type u :=
  LoopQuot Torus torusBase

/-- Fundamental group π₁(T², base) as rewrite classes of loops. -/
abbrev torusPiOne : Type u :=
  PiOne Torus torusBase

/-- Strict group structure on π₁(T², base). -/
abbrev torusPiOneGroup : LoopGroup Torus torusBase :=
  PiOneGroup Torus torusBase

/-- The first fundamental loop represented in the quotient. -/
@[simp] def torusLoop1Class : TorusLoopQuot :=
  LoopQuot.ofLoop (A := Torus) (a := torusBase) torusLoop1

/-- The second fundamental loop represented in the quotient. -/
@[simp] def torusLoop2Class : TorusLoopQuot :=
  LoopQuot.ofLoop (A := Torus) (a := torusBase) torusLoop2

/-- Quotient-lifted encoding from loop classes to winding numbers. -/
@[simp] def torusEncodeLift [h : HasTorusLoopDecode] : TorusLoopQuot → Int × Int :=
  Quot.lift (fun p : Path torusBase torusBase => torusEncodePath p)
    (by
      intro p q hpq
      exact torusEncodePath_rweq (h := h) hpq)

@[simp] theorem torusEncodeLift_ofLoop [HasTorusLoopDecode] (p : Path torusBase torusBase) :
    torusEncodeLift (LoopQuot.ofLoop (A := Torus) (a := torusBase) p) = torusEncodePath p := rfl

/-- Encode map `π₁(T²) → ℤ × ℤ`. -/
@[simp] def torusEncode [HasTorusLoopDecode] : torusPiOne → Int × Int :=
  torusEncodeLift

/-- Decode map `ℤ × ℤ → π₁(T²)`. -/
@[simp] def torusDecode : Int × Int → torusPiOne :=
  fun z =>
    LoopQuot.ofLoop (A := Torus) (a := torusBase) (torusDecodePath z)

/-- Encoding after decoding is the identity on `ℤ × ℤ`. -/
@[simp] theorem torusEncode_torusDecode [HasTorusLoopDecode] (z : Int × Int) :
    torusEncode (torusDecode z) = z := by
  change torusEncodePath (torusDecodePath z) = z
  exact torusEncodePath_torusDecodePath (z := z)

/-- Decoding after encoding is the identity on `π₁(T²)`. -/
theorem torusDecode_torusEncode [HasTorusLoopDecode] (x : torusPiOne) :
    torusDecode (torusEncode x) = x := by
  refine Quot.inductionOn x ?_
  intro p
  have hrweq : RwEq (torusDecodePath (torusEncodePath p)) p :=
    rweq_symm (torusLoop_rweq_decode (p := p))
  exact Quot.sound hrweq

/-- Fundamental group of the torus is equivalent to `ℤ × ℤ`.

This version depends on the raw loop normal-form interface `HasTorusLoopDecode`.
For a discharge-friendly π₁-level interface, see `TorusStep.lean`.
-/
noncomputable def torusPiOneEquivIntProd_ofLoopDecode [HasTorusLoopDecode] :
    SimpleEquiv torusPiOne (Int × Int) where
  toFun := torusEncode
  invFun := torusDecode
  left_inv := torusDecode_torusEncode
  right_inv := torusEncode_torusDecode

end

end Path
end ComputationalPaths
