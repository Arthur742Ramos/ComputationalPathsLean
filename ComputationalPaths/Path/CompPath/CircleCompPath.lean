/-
# Synthetic circle winding expressions over a one-point carrier

Defines a one-constructor carrier together with a separate syntax of loop
expressions and a quotient by winding number.  The expression quotient is a
useful synthetic presentation, but it is not the genuine
`PathRwQuot CircleCompPath base base`: interpreting the formal generator as a
raw `Path` sends it to reflexivity.

## Key Results

- `CircleCompPath`: a one-point type.
- `CircleCompPathExpr`: path expressions with a loop generator.
- `circleCompPathLoopExpr`: the formal loop generator expression.
- `circleCompPathPiOneEquivInt`: the synthetic winding quotient is equivalent
  to `Int`.

## References

- Computational paths framework (PathExpr rewriting).
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
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
@[simp] noncomputable def circleCompPathLoopExpr :
    CircleCompPathExpr circleCompPathBase circleCompPathBase :=
  CircleCompPathExpr.loop

/-- Iterate the loop generator `n` times at the expression level. -/
@[simp] noncomputable def circleCompPathLoopExprPow :
    Nat → CircleCompPathExpr circleCompPathBase circleCompPathBase
  | 0 => CircleCompPathExpr.refl circleCompPathBase
  | Nat.succ n =>
      CircleCompPathExpr.trans (circleCompPathLoopExprPow n) circleCompPathLoopExpr

/-- Integer iteration at the expression level. -/
@[simp] noncomputable def circleCompPathLoopExprZPow :
    Int → CircleCompPathExpr circleCompPathBase circleCompPathBase
  | Int.ofNat n => circleCompPathLoopExprPow n
  | Int.negSucc n =>
      CircleCompPathExpr.symm (circleCompPathLoopExprPow (Nat.succ n))

/-- Forgetful path-level image of the synthetic generator.  Because the
carrier has one constructor and no HIT loop constructor, this is reflexivity. -/
@[simp] noncomputable def circleLoopPath :
    Path circleCompPathBase circleCompPathBase :=
  Path.refl circleCompPathBase

/-- Forget loop-expression winding data and interpret expressions as raw
computational paths on the one-point carrier. -/
@[simp] noncomputable def circleLoopExpr_toPath :
    CircleCompPathExpr circleCompPathBase circleCompPathBase →
      Path circleCompPathBase circleCompPathBase := by
  intro p
  refine CircleCompPathExpr.rec (motive := fun {a b} _ => Path a b) ?loop ?refl ?symm ?trans p
  · exact circleLoopPath
  · intro a
    exact Path.refl a
  · intro _ _ _ ih
    exact Path.symm ih
  · intro _ _ _ _ _ ihp ihq
    exact Path.trans ihp ihq

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

/-! ## Synthetic winding quotient -/

/-- Loop expression relation: same winding number. -/
noncomputable def circleCompPathRel
    (p q : CircleCompPathExpr circleCompPathBase circleCompPathBase) : Prop :=
  circleCompPathEncodeExpr' p = circleCompPathEncodeExpr' q

/-- Setoid on loop expressions by winding number. -/
noncomputable def circleCompPathSetoid :
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

/-- Synthetic loop-expression quotient by winding number.  This is not the
genuine `PathRwQuot` loop fiber of `CircleCompPath`. -/
abbrev circleCompPathPiOne : Type u :=
  Quot circleCompPathSetoid.r

/-- Encode a loop class as its winding number. -/
@[simp] noncomputable def circleCompPathEncode : circleCompPathPiOne → Int :=
  Quot.lift circleCompPathEncodeExpr' (by
    intro p q hpq
    exact hpq)

/-- Decode an integer to the canonical loop expression class. -/
@[simp] noncomputable def circleCompPathDecode : Int → circleCompPathPiOne :=
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

/-! ## Synthetic winding quotient `≃ Int` -/

/-- The synthetic circle winding quotient is equivalent to `Int`. -/
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
@[simp] noncomputable abbrev circleBase : Circle := circleCompPathBase

/-- Legacy alias for the synthetic winding quotient. -/
abbrev circlePiOne : Type u := circleCompPathPiOne

/-! ## Definitional compatibility -/

/-- Legacy encode name for the synthetic winding quotient. -/
@[simp] noncomputable def circlePiOneEncode : circlePiOne → Int :=
  circleCompPathEncode

/-- Legacy decode name for the synthetic winding quotient. -/
@[simp] noncomputable def circleDecode : Int → circlePiOne :=
  circleCompPathDecode

/-- Chosen reflexive equality used by the raw image of the synthetic loop. -/
noncomputable def circleLoopEq : circleBase = circleBase :=
  circleLoopPath.toEq

/-- Raw path named by the legacy synthetic loop API.  It is a singleton
reflexivity step and does not carry the expression's winding number. -/
@[simp] noncomputable def circleLoop : Path circleBase circleBase :=
  Path.stepChain circleLoopEq

/-- Alias for the loop z-power at the path level. -/
@[simp] noncomputable def circleLoopPathPow :
    Nat → Path circleBase circleBase
  | 0 => Path.refl circleBase
  | Nat.succ n => Path.trans (circleLoopPathPow n) circleLoopPath

/-- Alias for the loop z-power at the path level. -/
@[simp] noncomputable def circleLoopPathZPow : Int → Path circleBase circleBase
  | Int.ofNat n => circleLoopPathPow n
  | Int.negSucc n => Path.symm (circleLoopPathPow (Nat.succ n))

/-- Alias for decoding integers into raw loops. -/
@[simp] noncomputable def circleDecodePath : Int → Path circleBase circleBase :=
  fun z => circleLoopExpr_toPath (circleCompPathLoopExprZPow z)

@[simp] theorem circleLoopExpr_toPath_zpow_eq_decodePath (z : Int) :
    circleLoopExpr_toPath (circleCompPathLoopExprZPow z) = circleDecodePath z := rfl

/-- Path-level encode/decode coherence between expression and loop-path presentations. -/
noncomputable def circleLoopPath_encode_decode_rweq (z : Int) :
    RwEq (circleLoopExpr_toPath (circleCompPathLoopExprZPow z)) (circleDecodePath z) :=
  rweq_of_eq (circleLoopExpr_toPath_zpow_eq_decodePath z)

/-- Additivity of natural loop powers at the path level (rewrite-equivalence form). -/
noncomputable def circleLoopZPow_add_rweq (m n : Nat) :
    RwEq (Path.trans (circleLoopPathPow m) (circleLoopPathPow n))
      (circleLoopPathPow (m + n)) := by
  induction n with
  | zero =>
      simpa [circleLoopPathPow] using
        (rweq_cmpA_refl_right (p := circleLoopPathPow m))
  | succ n ih =>
      have hAssoc :
          RwEq
            (Path.trans (circleLoopPathPow m)
              (Path.trans (circleLoopPathPow n) circleLoopPath))
            (Path.trans
              (Path.trans (circleLoopPathPow m) (circleLoopPathPow n))
              circleLoopPath) :=
        rweq_symm (rweq_tt (circleLoopPathPow m) (circleLoopPathPow n) circleLoopPath)
      have hCongr :
          RwEq
            (Path.trans
              (Path.trans (circleLoopPathPow m) (circleLoopPathPow n))
              circleLoopPath)
            (Path.trans (circleLoopPathPow (m + n)) circleLoopPath) :=
        rweq_trans_congr_left circleLoopPath ih
      have hTotal := rweq_trans hAssoc hCongr
      simpa [circleLoopPathPow, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTotal

/-- Legacy name for winding number one in the synthetic quotient. -/
@[simp] noncomputable def circlePiOneLoop : circlePiOne :=
  circleDecode 1

/-- Alias for the loop z-power in the quotient. -/
@[simp] noncomputable def circleLoopZPow : Int → circlePiOne :=
  circleDecode

@[simp] theorem circleDecode_zero : circleDecode 0 = circleLoopZPow 0 := rfl

@[simp] theorem circleDecode_one : circleDecode 1 = circleLoopZPow 1 := rfl


@[simp] theorem circlePiOneEncode_circleDecode (z : Int) :
    circlePiOneEncode (circleDecode z) = z :=
  circleCompPathEncodeDecode z

@[simp] theorem circleDecode_circlePiOneEncode (x : circlePiOne) :
    circleDecode (circlePiOneEncode x) = x :=
  circleCompPathDecodeEncode x

/-! ## Legacy synthetic-presentation aliases -/

/-- Legacy name for the synthetic winding equivalence. -/
noncomputable abbrev circlePiOneEquivInt :
    SimpleEquiv circlePiOne Int :=
  circleCompPathPiOneEquivInt

/-- Legacy alias for the synthetic winding quotient; despite the historical
name, this is not `PathRwQuot Circle circleBase circleBase`. -/
abbrev circlePiOneStd : Type u := circlePiOne

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
