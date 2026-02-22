/-
# Projective spaces via computational paths

Lightweight computational-path models for real and complex projective spaces.
We model RP^1 using the computational circle, RP^n for n >= 2 using a Z2 loop
quotient, and CP^n as a subsingleton type with trivial fundamental group.

## Key Results

- `realProjectivePiOneEquiv`: pi_1(RP^n) model equivalence (Unit/Int/Bool).
- `realProjective2CompPathPiOneEquivZ2`: pi_1(RP^2) ~= Z2.
- `complexProjectivePiOneEquivUnit`: pi_1(CP^n) ~= 1.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.CompPath.PushoutCompPath
import ComputationalPaths.Path.Homotopy.Sets
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## RP^2 loop expressions -/

/-- Alias for Z/2 used in projective-space models. -/
abbrev RealProjectiveZ2 : Type := Bool

/-- RP^2 as a one-point computational-path type. -/
inductive RealProjective2CompPath : Type u
  | base : RealProjective2CompPath

/-- Basepoint of RP^2. -/
@[simp] noncomputable def realProjective2CompPathBase : RealProjective2CompPath :=
  RealProjective2CompPath.base

/-- Path expressions for RP^2 with a loop generator. -/
inductive RealProjective2CompPathExpr : Type u
  | loop : RealProjective2CompPathExpr
  | refl : RealProjective2CompPathExpr
  | symm (p : RealProjective2CompPathExpr) : RealProjective2CompPathExpr
  | trans (p q : RealProjective2CompPathExpr) : RealProjective2CompPathExpr

/-- Iterate the RP^2 loop expression. -/
@[simp] noncomputable def realProjective2CompPathLoopExprPow :
    Nat → RealProjective2CompPathExpr
  | 0 => RealProjective2CompPathExpr.refl
  | Nat.succ n =>
      RealProjective2CompPathExpr.trans (realProjective2CompPathLoopExprPow n)
        RealProjective2CompPathExpr.loop

/-- Encode RP^2 loop expressions by parity (Z2). -/
noncomputable def realProjective2CompPathEncodeExpr :
    RealProjective2CompPathExpr → RealProjectiveZ2
  | RealProjective2CompPathExpr.loop => true
  | RealProjective2CompPathExpr.refl => false
  | RealProjective2CompPathExpr.symm p => realProjective2CompPathEncodeExpr p
  | RealProjective2CompPathExpr.trans p q =>
      xor (realProjective2CompPathEncodeExpr p) (realProjective2CompPathEncodeExpr q)

/-- Encoding the loop generator yields `true`. -/
@[simp] theorem realProjective2CompPathEncodeExpr_loop :
    realProjective2CompPathEncodeExpr RealProjective2CompPathExpr.loop = true := rfl

/-- Encoding reflexivity yields `false`. -/
@[simp] theorem realProjective2CompPathEncodeExpr_refl :
    realProjective2CompPathEncodeExpr RealProjective2CompPathExpr.refl = false := rfl

/-- Encoding symmetry is parity-preserving. -/
@[simp] theorem realProjective2CompPathEncodeExpr_symm
    (p : RealProjective2CompPathExpr) :
    realProjective2CompPathEncodeExpr (RealProjective2CompPathExpr.symm p) =
      realProjective2CompPathEncodeExpr p := rfl

/-- Encoding composition is xor. -/
@[simp] theorem realProjective2CompPathEncodeExpr_trans
    (p q : RealProjective2CompPathExpr) :
    realProjective2CompPathEncodeExpr (RealProjective2CompPathExpr.trans p q) =
      xor (realProjective2CompPathEncodeExpr p) (realProjective2CompPathEncodeExpr q) := rfl

/-- Loop-expression relation: same parity. -/
noncomputable def realProjective2CompPathRel
    (p q : RealProjective2CompPathExpr) :
    Prop :=
  realProjective2CompPathEncodeExpr p = realProjective2CompPathEncodeExpr q

/-- Setoid on RP^2 loop expressions by parity. -/
noncomputable def realProjective2CompPathSetoid :
    Setoid RealProjective2CompPathExpr
    where
  r := realProjective2CompPathRel
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro p
      rfl
    · intro p q hpq
      simpa [realProjective2CompPathRel] using hpq.symm
    · intro p q r hpq hqr
      exact hpq.trans hqr

/-- The RP^2 pi_1 model as a quotient of loop expressions. -/
abbrev realProjective2CompPathPiOne : Type u :=
  Quot realProjective2CompPathSetoid.r

/-- Encode a loop class by parity. -/
@[simp] noncomputable def realProjective2CompPathEncode :
    realProjective2CompPathPiOne → RealProjectiveZ2 :=
  Quot.lift realProjective2CompPathEncodeExpr (by
    intro p q hpq
    exact hpq)

/-- Decode a parity bit into the canonical loop class. -/
@[simp] noncomputable def realProjective2CompPathDecode :
    RealProjectiveZ2 → realProjective2CompPathPiOne :=
  fun b =>
    Quot.mk _
      (if b then
        RealProjective2CompPathExpr.loop
      else
        RealProjective2CompPathExpr.refl)

/-- Encoding after decoding is the identity on Z2. -/
@[simp] theorem realProjective2CompPathEncodeDecode (b : RealProjectiveZ2) :
    realProjective2CompPathEncode (realProjective2CompPathDecode b) = b := by
  cases b <;> simp [realProjective2CompPathDecode, realProjective2CompPathEncode]

/-- Decoding after encoding is the identity on loop classes. -/
theorem realProjective2CompPathDecodeEncode (x : realProjective2CompPathPiOne) :
    realProjective2CompPathDecode (realProjective2CompPathEncode x) = x := by
  refine Quot.inductionOn x ?_
  intro p
  apply Quot.sound
  change
    realProjective2CompPathEncodeExpr
        (if realProjective2CompPathEncodeExpr p then
          RealProjective2CompPathExpr.loop
        else
          RealProjective2CompPathExpr.refl) =
      realProjective2CompPathEncodeExpr p
  cases h : realProjective2CompPathEncodeExpr p <;> simp

/-- pi_1(RP^2) ~= Z2 in the loop-expression model. -/
noncomputable def realProjective2CompPathPiOneEquivZ2 :
    SimpleEquiv realProjective2CompPathPiOne RealProjectiveZ2 where
  toFun := realProjective2CompPathEncode
  invFun := realProjective2CompPathDecode
  left_inv := realProjective2CompPathDecodeEncode
  right_inv := realProjective2CompPathEncodeDecode

/-! ## Path-level loops for RP^2 -/

/-- Chosen equality proof used to seed the RP^2 loop. -/
noncomputable def realProjective2CompPathLoopEq :
    realProjective2CompPathBase = realProjective2CompPathBase :=
  Classical.choice (by
    exact (⟨rfl⟩ : Nonempty (realProjective2CompPathBase = realProjective2CompPathBase)))

/-- RP^2 loop generator at the Path level. -/
@[simp] noncomputable def realProjective2CompPathLoop :
    Path realProjective2CompPathBase realProjective2CompPathBase :=
  Path.stepChain realProjective2CompPathLoopEq

/-- Iterate the RP^2 loop at the Path level. -/
@[simp] noncomputable def realProjective2CompPathLoopPathPow :
    Nat → Path realProjective2CompPathBase realProjective2CompPathBase
  | 0 => Path.refl realProjective2CompPathBase
  | Nat.succ n =>
      Path.trans realProjective2CompPathLoop (realProjective2CompPathLoopPathPow n)

/-- Decode a Z2 element into a loop path. -/
@[simp] noncomputable def realProjective2CompPathDecodePath :
    RealProjectiveZ2 → Path realProjective2CompPathBase realProjective2CompPathBase
  | false => Path.refl realProjective2CompPathBase
  | true => realProjective2CompPathLoop

/-! ## Real projective spaces -/

/-- Real projective space RP^n in the computational-path model. -/
noncomputable def RealProjectiveSpace : Nat → Type u
  | 0 => PUnit'
  | Nat.succ 0 => CircleCompPath
  | Nat.succ (Nat.succ _) => RealProjective2CompPath

/-- Basepoint of RP^n in the model. -/
@[simp] noncomputable def realProjectiveSpaceBase : (n : Nat) → RealProjectiveSpace n
  | 0 => PUnit'.unit
  | Nat.succ 0 => circleCompPathBase
  | Nat.succ (Nat.succ _) => realProjective2CompPathBase

/-- Model for pi_1(RP^n) by dimension. -/
noncomputable def realProjectivePiOne : Nat → Type u
  | 0 => PUnit'
  | Nat.succ 0 => circleCompPathPiOne
  | Nat.succ (Nat.succ _) => realProjective2CompPathPiOne

/-- Group model for pi_1(RP^n) by dimension. -/
noncomputable def realProjectivePiOneModel : Nat → Type
  | 0 => Unit
  | Nat.succ 0 => Int
  | Nat.succ (Nat.succ _) => RealProjectiveZ2

/-- pi_1(RP^n) model equivalence (Unit/Int/Z2). -/
noncomputable def realProjectivePiOneEquiv :
    (n : Nat) → SimpleEquiv (realProjectivePiOne n) (realProjectivePiOneModel n)
  | 0 =>
      { toFun := fun _ => ()
        invFun := fun _ => PUnit'.unit
        left_inv := by
          intro x
          cases x
          rfl
        right_inv := by
          intro x
          cases x
          rfl }
  | Nat.succ 0 => circleCompPathPiOneEquivInt
  | Nat.succ (Nat.succ _) => realProjective2CompPathPiOneEquivZ2

/-! ## Complex projective spaces -/

/-- Complex projective space CP^n modeled as a point. -/
abbrev ComplexProjectiveSpace (_n : Nat) : Type u := PUnit'

/-- Basepoint of CP^n. -/
@[simp] abbrev complexProjectiveBase (n : Nat) : ComplexProjectiveSpace n := PUnit'.unit

/-- pi_1(CP^n) ~= 1 in the subsingleton model. -/
noncomputable def complexProjectivePiOneEquivUnit (n : Nat) :
    SimpleEquiv (PiOne (ComplexProjectiveSpace n) (complexProjectiveBase n)) Unit where
  toFun := fun _ => ()
  invFun := fun _ => Quot.mk _ (Path.refl _)
  left_inv := by
    intro α
    exact
      (pi1_trivial_of_subsingleton (A := ComplexProjectiveSpace n)
        (a := complexProjectiveBase n) α).symm
  right_inv := by
    intro u
    cases u
    rfl

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
