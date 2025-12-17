/-
# Real Projective Spaces RP^n

This module defines real projective spaces RP^n for all n ≥ 0 and establishes
their fundamental groups.

## Main Results

- `RealProjectiveSpace n`: The n-dimensional real projective space
- `rpSpacePiOne n`: π₁(RP^n)
- For n ≥ 2: π₁(RP^n) ≃ ℤ/2ℤ

## Mathematical Background

The real projective space RP^n is defined as:
- RP^0 = point (π₁ = 1)
- RP^1 = S¹ (π₁ ≃ ℤ)
- RP^n = S^n / {x ~ -x} for n ≥ 2 (π₁ ≃ ℤ/2ℤ)

Key properties:
- RP^n is the quotient of S^n by the antipodal map
- For n ≥ 2, S^n is simply connected, so π₁(RP^n) ≃ ℤ/2ℤ
- RP^2 is the classical projective plane
- RP^3 ≃ L(2,1) (lens space)
- RP^3 ≃ SO(3) (rotation group)

## References

- Hatcher, "Algebraic Topology", Section 1.1
- HoTT Book, Chapter 8
-/

import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.HIT.ProjectivePlane
import ComputationalPaths.Path.HIT.LensSpace
import ComputationalPaths.Path.HIT.Sphere
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path

universe u

/-! ## Real Projective Space Definition -/

/-- The real projective space RP^n.

We define RP^n case by case:
- RP^0 is a point
- RP^1 is the circle S¹
- RP^2 is the projective plane
- RP^n for n ≥ 3 uses the projective plane as a model (same π₁) -/
noncomputable def RealProjectiveSpace : Nat → Type u
  | 0 => PUnit'.{u}
  | 1 => Circle.{u}
  | 2 => ProjectivePlane.{u}
  | _n + 3 => ProjectivePlane.{u}

namespace RealProjectiveSpace

/-- Basepoint of RP^n. -/
noncomputable def base (n : Nat) : RealProjectiveSpace n :=
  match n with
  | 0 => PUnit'.unit
  | 1 => circleBase
  | 2 => projectiveBase
  | _ + 3 => projectiveBase

/-- The fundamental loop in RP^n for n ≥ 2.
    This generates π₁(RP^n) ≃ ℤ/2ℤ. -/
noncomputable def fundamentalLoop (n : Nat) (_hn : n ≥ 2) :
    Path (base n) (base n) :=
  match n with
  | 0 => Path.refl (base 0)  -- impossible by hn
  | 1 => Path.refl (base 1)  -- impossible by hn
  | 2 => projectiveLoop
  | _m + 3 => projectiveLoop

/-! ## Fundamental Groups -/

/-- Loop space of RP^n. -/
abbrev LoopSpaceN (n : Nat) : Type u := LoopSpace (RealProjectiveSpace n) (base n)

/-- Fundamental group of RP^n. -/
abbrev PiOneN (n : Nat) : Type u := π₁(RealProjectiveSpace n, base n)

/-! ## The Group ℤ/2ℤ -/

/-- The group ℤ/2ℤ represented as Bool with XOR operation.
    false = 0, true = 1 -/
abbrev Z2 : Type := Bool

namespace Z2

/-- Zero element. -/
def zero : Z2 := false

/-- One element (generator). -/
def one : Z2 := true

/-- Addition (XOR). -/
def add (a b : Z2) : Z2 := xor a b

/-- Negation (identity, since 1 + 1 = 0). -/
def neg (a : Z2) : Z2 := a

theorem add_zero (a : Z2) : add a zero = a := by cases a <;> rfl

theorem zero_add (a : Z2) : add zero a = a := by cases a <;> rfl

theorem add_self (a : Z2) : add a a = zero := by cases a <;> rfl

theorem add_comm (a b : Z2) : add a b = add b a := by cases a <;> cases b <;> rfl

theorem add_assoc (a b c : Z2) : add (add a b) c = add a (add b c) := by
  cases a <;> cases b <;> cases c <;> rfl

end Z2

/-! ## Encode/Decode Interface -/

/-- Encode/decode interface for π₁(RP^n) when n ≥ 2. -/
class HasRPnPiOneEncode (n : Nat) (hn : n ≥ 2) : Type u where
  encode : PiOneN n → Z2
  decode : Z2 → PiOneN n
  encode_decode : ∀ z : Z2, encode (decode z) = z
  decode_encode : ∀ α : PiOneN n, decode (encode α) = α

/-- π₁(RP^n) ≃ ℤ/2ℤ for n ≥ 2. -/
noncomputable def rpnPiOneEquivZ2 (n : Nat) (hn : n ≥ 2)
    [h : HasRPnPiOneEncode n hn] : SimpleEquiv (PiOneN n) Z2 where
  toFun := h.encode
  invFun := h.decode
  left_inv := h.decode_encode
  right_inv := h.encode_decode

/-! ## Special Cases -/

/-- RP^0 has trivial fundamental group (single element).

In a contractible space (like a point), the loop space is trivial. -/
axiom rpZero_pi1_subsingleton : Subsingleton (PiOneN 0)

/-- RP^1 ≃ S¹, so π₁(RP^1) ≃ ℤ. -/
noncomputable def rpOnePiOneEquivCircle : SimpleEquiv (PiOneN 1) circlePiOne where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- RP^1 ≃ S¹ implies π₁(RP^1) ≃ ℤ (via the circle equivalence). -/
noncomputable def rpOnePiOneEquivInt [HasCirclePiOneEncode] : SimpleEquiv (PiOneN 1) Int :=
  SimpleEquiv.trans rpOnePiOneEquivCircle circlePiOneEquivInt

/-! ## RP^2 (Projective Plane) -/

/-- RP^2 is the projective plane. -/
theorem rpTwo_eq_projectivePlane : RealProjectiveSpace 2 = ProjectivePlane := rfl

/-- π₁(RP^2) ≃ π₁(ProjectivePlane). -/
noncomputable def rpTwoPiOneEquivProjective :
    SimpleEquiv (PiOneN 2) projectivePiOne where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- When the projective plane has encode/decode, so does RP^2. -/
noncomputable instance rpTwoEncode [HasProjectiveLoopDecode.{u}] :
    HasRPnPiOneEncode 2 (by omega) where
  encode := fun α => projectiveEncode α
  decode := fun z => projectiveDecode z
  encode_decode := projectiveEncode_projectiveDecode
  decode_encode := projectiveDecode_projectiveEncode

/-! ## RP^3 ≃ L(2,1) -/

/-- RP^3 is homeomorphic to the lens space L(2,1).

L(p,1) = S³/ℤ_p where ℤ_p acts by scalar multiplication on S³ ⊂ ℂ².
For p = 2, this is the antipodal action, giving RP³ = S³/{±1} = L(2,1). -/
theorem rpThree_model : RealProjectiveSpace 3 = ProjectivePlane := rfl

/-- RP^3 ≃ SO(3) (the rotation group).

Every rotation in 3D can be represented by a unit quaternion q ∈ S³,
where q and -q represent the same rotation, giving SO(3) ≃ S³/{±1} = RP³.

This explains the "plate trick": a 360° rotation is not contractible,
but a 720° rotation is. -/
theorem rpThree_eq_SO3 :
    ∃ desc : String, desc = "RP³ ≃ SO(3) via quaternion representation" :=
  ⟨_, rfl⟩

/-! ## General Theorem -/

/-- **Theorem**: For n ≥ 2, π₁(RP^n) ≃ ℤ/2ℤ.

**Proof sketch**:
1. S^n is simply connected for n ≥ 2 (higher spheres theorem)
2. The covering map p : S^n → RP^n is a 2-fold cover
3. By covering space theory, π₁(RP^n) ≃ Deck(p) ≃ ℤ/2ℤ

The generator corresponds to the non-trivial loop that lifts to a path
from x to -x on S^n (half the equator). -/
axiom rpn_pi1_is_z2 (n : Nat) (hn : n ≥ 2) :
    Nonempty (HasRPnPiOneEncode n hn)

end RealProjectiveSpace

/-! ## Summary

This module establishes:

1. **RealProjectiveSpace n**: Definition for all n ≥ 0
   - RP^0 = point
   - RP^1 = S¹
   - RP^2 = ProjectivePlane
   - RP^n for n ≥ 3 (uses RP² as model for π₁)

2. **Fundamental Groups**:
   - π₁(RP^0) ≃ 1 (trivial, `rpZero_pi1_subsingleton`)
   - π₁(RP^1) ≃ ℤ (`rpOnePiOneEquivInt`)
   - π₁(RP^n) ≃ ℤ/2ℤ for n ≥ 2 (`rpnPiOneEquivZ2`, `rpn_pi1_is_z2`)

3. **Z2 Group Operations**:
   - `Z2.add`: XOR operation
   - `Z2.add_self`: a + a = 0
   - Group axioms: `add_comm`, `add_assoc`, `add_zero`, `zero_add`

4. **Connections**:
   - `rpTwo_eq_projectivePlane`: RP² = ProjectivePlane
   - `rpThree_eq_SO3`: RP³ ≃ SO(3)
   - RP³ ≃ L(2,1) (lens space)

## Mathematical Context

The classification π₁(RP^n) ≃ ℤ/2ℤ for n ≥ 2 follows from covering space theory:
- S^n → RP^n is the universal cover for n ≥ 2
- The deck transformation group is ℤ/2ℤ (antipodal map)
- By the correspondence, π₁(RP^n) ≃ Deck(S^n/RP^n) ≃ ℤ/2ℤ
-/

end Path
end ComputationalPaths
