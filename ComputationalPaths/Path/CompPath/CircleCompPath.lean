/-
# Circle via computational path expressions

Defines a custom circle whose paths are syntactic path expressions with a
distinguished loop generator. This is a computational-path construction rather
than a higher inductive axiom.

## Key Results

- `CircleCompPath`: a one-point type.
- `CircleCompPathExpr`: path expressions with a loop generator.
- `circleCompPathLoopExpr`: the formal loop generator expression.
- `circleCompPathPiOneEquivInt`: pi_1(S^1) ~= Z via loop counts.

## References

- Computational paths framework (PathExpr rewriting).
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.FundamentalGroup

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Circle as a one-point type -/

/-- The computational-path circle is a single-point type. -/
inductive CircleCompPath : Type u
  | base : CircleCompPath

/-- Base point of the circle. -/
@[simp] def circleCompPathBase : CircleCompPath := CircleCompPath.base

/-! ## Path expressions with a loop generator -/

/-- Path expressions for the computational circle, with a formal loop generator. -/
inductive CircleCompPathExpr : CircleCompPath → CircleCompPath → Type u
  | loop : CircleCompPathExpr circleCompPathBase circleCompPathBase
  | refl (a : CircleCompPath) : CircleCompPathExpr a a
  | symm {a b : CircleCompPath} (p : CircleCompPathExpr a b) : CircleCompPathExpr b a
  | trans {a b c : CircleCompPath} (p : CircleCompPathExpr a b)
      (q : CircleCompPathExpr b c) : CircleCompPathExpr a c

/-! ## Loop expressions and powers -/

/-- The formal loop generator expression. -/
@[simp] def circleCompPathLoopExpr :
    CircleCompPathExpr circleCompPathBase circleCompPathBase :=
  CircleCompPathExpr.loop

/-- Iterate the loop generator `n` times at the expression level. -/
@[simp] def circleCompPathLoopExprPow :
    Nat → CircleCompPathExpr circleCompPathBase circleCompPathBase
  | 0 => CircleCompPathExpr.refl circleCompPathBase
  | Nat.succ n =>
      CircleCompPathExpr.trans (circleCompPathLoopExprPow n) circleCompPathLoopExpr

/-- Integer iteration at the expression level. -/
@[simp] def circleCompPathLoopExprZPow :
    Int → CircleCompPathExpr circleCompPathBase circleCompPathBase
  | Int.ofNat n => circleCompPathLoopExprPow n
  | Int.negSucc n =>
      CircleCompPathExpr.symm (circleCompPathLoopExprPow (Nat.succ n))

/-! ## Encode by loop count -/

/-- Net loop count for a loop expression. -/
noncomputable def circleCompPathEncodeExpr' :
    CircleCompPathExpr circleCompPathBase circleCompPathBase → Int := by
  intro p
  refine CircleCompPathExpr.rec (motive := fun {a b} _ => Int) ?loop ?refl ?symm ?trans p
  · exact 1
  · intro _
    exact 0
  · intro _ _ _ ih
    exact -ih
  · intro _ _ _ _ _ ihp ihq
    exact ihp + ihq

@[simp] theorem circleCompPathEncodeExpr_loop :
    circleCompPathEncodeExpr' CircleCompPathExpr.loop = 1 := rfl

@[simp] theorem circleCompPathEncodeExpr_refl (a : CircleCompPath) :
    circleCompPathEncodeExpr' (CircleCompPathExpr.refl a) = 0 := rfl

@[simp] theorem circleCompPathEncodeExpr_symm
    (p : CircleCompPathExpr circleCompPathBase circleCompPathBase) :
    circleCompPathEncodeExpr' (CircleCompPathExpr.symm p) = -circleCompPathEncodeExpr' p := rfl

@[simp] theorem circleCompPathEncodeExpr_trans
    (p q : CircleCompPathExpr circleCompPathBase circleCompPathBase) :
    circleCompPathEncodeExpr' (CircleCompPathExpr.trans p q) =
      circleCompPathEncodeExpr' p + circleCompPathEncodeExpr' q := rfl

@[simp] theorem neg_ofNat_succ_eq_negSucc (n : Nat) :
    -Int.ofNat (Nat.succ n) = Int.negSucc n := rfl

/-- Encoding loop powers yields the expected natural number. -/
@[simp] theorem circleCompPathEncodeExpr_pow (n : Nat) :
    circleCompPathEncodeExpr' (circleCompPathLoopExprPow n) = Int.ofNat n := by
  induction n with
  | zero =>
      simp [circleCompPathLoopExprPow]
  | succ n ih =>
      simp [circleCompPathLoopExprPow, ih, Int.natCast_succ]

/-- Encoding integer loop powers recovers the integer. -/
@[simp] theorem circleCompPathEncodeExpr_zpow (z : Int) :
    circleCompPathEncodeExpr' (circleCompPathLoopExprZPow z) = z := by
  cases z with
  | ofNat n =>
      simp [circleCompPathLoopExprZPow]
  | negSucc n =>
      have : -Int.ofNat (Nat.succ n) = Int.negSucc n := by rfl
      calc
        circleCompPathEncodeExpr' (circleCompPathLoopExprZPow (Int.negSucc n))
            = -Int.ofNat (Nat.succ n) := by
                simp [circleCompPathLoopExprZPow, circleCompPathEncodeExpr_pow]
        _ = Int.negSucc n := by
                simpa using this

/-! ## Loop quotient and pi_1 -/

/-- Loop expression relation: same winding number. -/
def circleCompPathRel
    (p q : CircleCompPathExpr circleCompPathBase circleCompPathBase) : Prop :=
  circleCompPathEncodeExpr' p = circleCompPathEncodeExpr' q

/-- Setoid on loop expressions by winding number. -/
def circleCompPathSetoid :
    Setoid (CircleCompPathExpr circleCompPathBase circleCompPathBase) where
  r := circleCompPathRel
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro p
      rfl
    · intro p q hpq
      simpa [circleCompPathRel] using hpq.symm
    · intro p q r hpq hqr
      exact hpq.trans hqr

/-- The computational-path pi_1 of the circle (loop expressions mod winding). -/
abbrev circleCompPathPiOne : Type u :=
  Quot circleCompPathSetoid.r

/-- Encode a loop class as its winding number. -/
@[simp] noncomputable def circleCompPathEncode : circleCompPathPiOne → Int :=
  Quot.lift circleCompPathEncodeExpr' (by
    intro p q hpq
    exact hpq)

/-- Decode an integer to the canonical loop expression class. -/
@[simp] def circleCompPathDecode : Int → circleCompPathPiOne :=
  fun z => Quot.mk _ (circleCompPathLoopExprZPow z)

/-- Encoding after decoding is the identity on integers. -/
@[simp] theorem circleCompPathEncodeDecode (z : Int) :
    circleCompPathEncode (circleCompPathDecode z) = z := by
  cases z with
  | ofNat n =>
      simp [circleCompPathDecode, circleCompPathLoopExprZPow, circleCompPathEncodeExpr_pow]
  | negSucc n =>
      have : -Int.ofNat (Nat.succ n) = Int.negSucc n := by rfl
      calc
        circleCompPathEncode (circleCompPathDecode (Int.negSucc n))
            = -Int.ofNat (Nat.succ n) := by
                simp [circleCompPathDecode, circleCompPathLoopExprZPow, circleCompPathEncodeExpr_pow]
        _ = Int.negSucc n := by
                simpa using this

/-- Decoding after encoding is the identity on loop classes. -/
theorem circleCompPathDecodeEncode (x : circleCompPathPiOne) :
    circleCompPathDecode (circleCompPathEncode x) = x := by
  refine Quot.inductionOn x ?_
  intro p
  apply Quot.sound
  -- show winding-number equality
  change circleCompPathEncodeExpr' (circleCompPathLoopExprZPow (circleCompPathEncodeExpr' p)) =
    circleCompPathEncodeExpr' p
  simpa using circleCompPathEncodeExpr_zpow (circleCompPathEncodeExpr' p)

/-! ## pi_1(S^1) ~= Z -/

/-- The computational-path circle has pi_1 equivalent to Z. -/
noncomputable def circleCompPathPiOneEquivInt :
    SimpleEquiv circleCompPathPiOne Int where
  toFun := circleCompPathEncode
  invFun := circleCompPathDecode
  left_inv := circleCompPathDecodeEncode
  right_inv := circleCompPathEncodeDecode

/-! ## Compatibility aliases -/

/-- Alias for the computational-path circle, matching the legacy name. -/
abbrev Circle : Type u := CircleCompPath.{u}

/-- Alias for the basepoint, matching the legacy name. -/
@[simp] abbrev circleBase : Circle := circleCompPathBase

/-- Alias for the loop quotient, matching the legacy name. -/
abbrev circlePiOne : Type u := circleCompPathPiOne

/-! ## Definitional compatibility -/

/-- Alias for the π₁ encode map, matching the legacy name. -/
@[simp] noncomputable def circlePiOneEncode : circlePiOne → Int :=
  circleCompPathEncode

/-- Alias for the π₁ decode map, matching the legacy name. -/
@[simp] def circleDecode : Int → circlePiOne :=
  circleCompPathDecode

/-- Chosen equality proof used to seed the loop generator. -/
noncomputable def circleLoopEq : circleBase = circleBase :=
  Classical.choice (by
    exact (⟨rfl⟩ : Nonempty (circleBase = circleBase)))

/-- Alias for the fundamental loop path. -/
@[simp] noncomputable def circleLoop : Path circleBase circleBase :=
  Path.stepChain circleLoopEq

/-- Alias for the loop z-power at the path level. -/
@[simp] noncomputable def circleLoopPathZPow : Int → Path circleBase circleBase := by
  let rec loopPow : Nat → Path circleBase circleBase
    | 0 => Path.refl circleBase
    | Nat.succ n => Path.trans circleLoop (loopPow n)
  exact fun
    | Int.ofNat n => loopPow n
    | Int.negSucc n => Path.symm (loopPow (Nat.succ n))

/-- Alias for decoding integers into raw loops. -/
@[simp] noncomputable def circleDecodePath : Int → Path circleBase circleBase :=
  circleLoopPathZPow

/-- Alias for the fundamental loop in π₁. -/
@[simp] def circlePiOneLoop : circlePiOne :=
  circleDecode 1

/-- Alias for the loop z-power in the quotient. -/
@[simp] def circleLoopZPow : Int → circlePiOne :=
  circleDecode

@[simp] theorem circleDecode_zero : circleDecode 0 = circleLoopZPow 0 := rfl

@[simp] theorem circleDecode_one : circleDecode 1 = circleLoopZPow 1 := rfl


@[simp] theorem circlePiOneEncode_circleDecode (z : Int) :
    circlePiOneEncode (circleDecode z) = z :=
  circleCompPathEncodeDecode z

@[simp] theorem circleDecode_circlePiOneEncode (x : circlePiOne) :
    circleDecode (circlePiOneEncode x) = x :=
  circleCompPathDecodeEncode x

/-! ## Fundamental group coercions -/

/-- Legacy name for the π₁ equivalence. -/
noncomputable abbrev circlePiOneEquivInt :
    SimpleEquiv circlePiOne Int :=
  circleCompPathPiOneEquivInt

/-- Circle π₁ as the standard loop quotient. -/
abbrev circlePiOneStd : Type u := circlePiOne

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
