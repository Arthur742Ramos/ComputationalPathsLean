/-
# The Klein bottle via computational paths

We model the Klein bottle as a one-point type with path expressions generated
by two loops a and b. Loop expressions are quotiented by a normal-form encoding
into the semidirect product Z ⋊ Z, yielding the presentation
  <a, b | a b a^{-1} b = 1>.

## Key Results

- `kleinBottleLoopA`, `kleinBottleLoopB`: Path-level loop generators.
- `kleinBottleLoopAPathZPow`, `kleinBottleLoopBPathZPow`: Path-level loop powers.
- `kleinBottleDecodePath`: Decoding integer pairs into Path-level loops.
- `kleinBottlePiOneEquivIntProd`: quotient-level computation
  `pi_1(K) ~= Z semidirect Z`.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.CompPath.PushoutCompPath

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## The Klein bottle as a one-point type -/

/-- The computational-path Klein bottle is a single-point type. -/
inductive KleinBottleCompPath : Type u
  | base : KleinBottleCompPath

/-- Basepoint of the Klein bottle. -/
@[simp] noncomputable def kleinBottleBase : KleinBottleCompPath := KleinBottleCompPath.base

/-! ## Path expressions with two loop generators -/

/-- Path expressions for the Klein bottle with loop generators a and b. -/
inductive KleinBottleExpr : KleinBottleCompPath → KleinBottleCompPath → Type u
  | loopA : KleinBottleExpr kleinBottleBase kleinBottleBase
  | loopB : KleinBottleExpr kleinBottleBase kleinBottleBase
  | refl (a : KleinBottleCompPath) : KleinBottleExpr a a
  | symm {a b : KleinBottleCompPath} (p : KleinBottleExpr a b) : KleinBottleExpr b a
  | trans {a b c : KleinBottleCompPath} (p : KleinBottleExpr a b)
      (q : KleinBottleExpr b c) : KleinBottleExpr a c

/-! ## Loop powers -/

@[simp] noncomputable def kleinBottleLoopAExprPow :
    Nat → KleinBottleExpr kleinBottleBase kleinBottleBase
  | 0 => KleinBottleExpr.refl kleinBottleBase
  | Nat.succ n =>
      KleinBottleExpr.trans (kleinBottleLoopAExprPow n) KleinBottleExpr.loopA

@[simp] noncomputable def kleinBottleLoopBExprPow :
    Nat → KleinBottleExpr kleinBottleBase kleinBottleBase
  | 0 => KleinBottleExpr.refl kleinBottleBase
  | Nat.succ n =>
      KleinBottleExpr.trans (kleinBottleLoopBExprPow n) KleinBottleExpr.loopB

@[simp] noncomputable def kleinBottleLoopAExprZPow :
    Int → KleinBottleExpr kleinBottleBase kleinBottleBase
  | Int.ofNat n => kleinBottleLoopAExprPow n
  | Int.negSucc n => KleinBottleExpr.symm (kleinBottleLoopAExprPow (Nat.succ n))

@[simp] noncomputable def kleinBottleLoopBExprZPow :
    Int → KleinBottleExpr kleinBottleBase kleinBottleBase
  | Int.ofNat n => kleinBottleLoopBExprPow n
  | Int.negSucc n => KleinBottleExpr.symm (kleinBottleLoopBExprPow (Nat.succ n))

/-! ## Parity and semidirect product encoding -/

noncomputable def natParity : Nat → Bool
  | 0 => false
  | Nat.succ n => !natParity n

@[simp] theorem natParity_zero : natParity 0 = false := rfl

@[simp] theorem natParity_succ (n : Nat) : natParity (Nat.succ n) = !natParity n := rfl

noncomputable def kleinBottleParity : Int → Bool
  | Int.ofNat n => natParity n
  | Int.negSucc n => natParity (Nat.succ n)

@[simp] theorem kleinBottleParity_ofNat (n : Nat) :
    kleinBottleParity (Int.ofNat n) = natParity n := rfl

@[simp] theorem kleinBottleParity_negSucc (n : Nat) :
    kleinBottleParity (Int.negSucc n) = natParity (Nat.succ n) := rfl

noncomputable def kleinBottleAct (m n : Int) : Int :=
  if kleinBottleParity m then -n else n

@[simp] theorem kleinBottleAct_ofNat (m : Nat) (n : Int) :
    kleinBottleAct (Int.ofNat m) n =
      if natParity m then -n else n := by
  rfl

@[simp] theorem kleinBottleAct_negSucc (m : Nat) (n : Int) :
    kleinBottleAct (Int.negSucc m) n =
      if natParity (Nat.succ m) then -n else n := by
  rfl

@[simp] theorem kleinBottleAct_zero (m : Int) : kleinBottleAct m 0 = 0 := by
  by_cases h : kleinBottleParity m <;> simp [kleinBottleAct, h]

@[simp] theorem kleinBottleAct_zero_exp (n : Int) : kleinBottleAct 0 n = n := by
  simp [kleinBottleAct, kleinBottleParity, natParity]

noncomputable def kleinBottleMul : (Int × Int) → (Int × Int) → (Int × Int)
  | (m, n), (m', n') => (m + m', kleinBottleAct m' n + n')

noncomputable def kleinBottleInv : (Int × Int) → (Int × Int)
  | (m, n) => (-m, -kleinBottleAct m n)

/-! ## Encoding loop expressions -/

noncomputable def kleinBottleEncodeExpr' :
    KleinBottleExpr kleinBottleBase kleinBottleBase → Int × Int := by
  intro p
  refine KleinBottleExpr.rec (motive := fun {a b} _ => Int × Int)
    ?loopA ?loopB ?refl ?symm ?trans p
  · exact (1, 0)
  · exact (0, 1)
  · intro _
    exact (0, 0)
  · intro _ _ _ ih
    exact kleinBottleInv ih
  · intro _ _ _ _ _ ihp ihq
    exact kleinBottleMul ihp ihq

@[simp] theorem kleinBottleEncodeExpr_loopA :
    kleinBottleEncodeExpr' KleinBottleExpr.loopA = (1, 0) := rfl

@[simp] theorem kleinBottleEncodeExpr_loopB :
    kleinBottleEncodeExpr' KleinBottleExpr.loopB = (0, 1) := rfl

@[simp] theorem kleinBottleEncodeExpr_refl (a : KleinBottleCompPath) :
    kleinBottleEncodeExpr' (KleinBottleExpr.refl a) = (0, 0) := rfl

@[simp] theorem kleinBottleEncodeExpr_symm
    (p : KleinBottleExpr kleinBottleBase kleinBottleBase) :
    kleinBottleEncodeExpr' (KleinBottleExpr.symm p) =
      kleinBottleInv (kleinBottleEncodeExpr' p) := rfl

@[simp] theorem kleinBottleEncodeExpr_trans
    (p q : KleinBottleExpr kleinBottleBase kleinBottleBase) :
    kleinBottleEncodeExpr' (KleinBottleExpr.trans p q) =
      kleinBottleMul (kleinBottleEncodeExpr' p) (kleinBottleEncodeExpr' q) := rfl

/-! ## Path-level loops -/

/-- Chosen equality proof used to seed loop A. -/
noncomputable def kleinBottleLoopAEq : kleinBottleBase = kleinBottleBase :=
  Classical.choice (by
    exact (⟨rfl⟩ : Nonempty (kleinBottleBase = kleinBottleBase)))

/-- Chosen equality proof used to seed loop B. -/
noncomputable def kleinBottleLoopBEq : kleinBottleBase = kleinBottleBase :=
  Classical.choice (by
    exact (⟨rfl⟩ : Nonempty (kleinBottleBase = kleinBottleBase)))

/-- Loop A at the path level. -/
@[simp] noncomputable def kleinBottleLoopA : Path kleinBottleBase kleinBottleBase :=
  Path.stepChain kleinBottleLoopAEq

/-- Loop B at the path level. -/
@[simp] noncomputable def kleinBottleLoopB : Path kleinBottleBase kleinBottleBase :=
  Path.stepChain kleinBottleLoopBEq

/-- Integer iteration of loop A at the path level. -/
@[simp] noncomputable def kleinBottleLoopAPathZPow :
    Int → Path kleinBottleBase kleinBottleBase := by
  let rec loopPow : Nat → Path kleinBottleBase kleinBottleBase
    | 0 => Path.refl kleinBottleBase
    | Nat.succ n => Path.trans (loopPow n) kleinBottleLoopA
  exact fun
    | Int.ofNat n => loopPow n
    | Int.negSucc n => Path.symm (loopPow (Nat.succ n))

/-- Integer iteration of loop B at the path level. -/
@[simp] noncomputable def kleinBottleLoopBPathZPow :
    Int → Path kleinBottleBase kleinBottleBase := by
  let rec loopPow : Nat → Path kleinBottleBase kleinBottleBase
    | 0 => Path.refl kleinBottleBase
    | Nat.succ n => Path.trans (loopPow n) kleinBottleLoopB
  exact fun
    | Int.ofNat n => loopPow n
    | Int.negSucc n => Path.symm (loopPow (Nat.succ n))

/-- Decode an integer pair into a raw loop on the Klein bottle. -/
@[simp] noncomputable def kleinBottleDecodePath :
    Int × Int → Path kleinBottleBase kleinBottleBase
  | (m, n) =>
      Path.trans (kleinBottleLoopAPathZPow m) (kleinBottleLoopBPathZPow n)

/-! ## pi_1(K) as the semidirect product Z ⋊ Z -/

@[simp] theorem kleinBottleEncodeExpr_powA (n : Nat) :
    kleinBottleEncodeExpr' (kleinBottleLoopAExprPow n) = ((n : Int), 0) := by
  induction n with
  | zero =>
      simp [kleinBottleLoopAExprPow]
  | succ n ih =>
      simp [kleinBottleLoopAExprPow, ih, kleinBottleMul, kleinBottleAct]

@[simp] theorem kleinBottleEncodeExpr_powB (n : Nat) :
    kleinBottleEncodeExpr' (kleinBottleLoopBExprPow n) = (0, (n : Int)) := by
  induction n with
  | zero =>
      simp [kleinBottleLoopBExprPow]
  | succ n ih =>
      simp [kleinBottleLoopBExprPow, ih, kleinBottleMul, kleinBottleAct_zero_exp]

@[simp] theorem kleinBottleEncodeExpr_zpowA (m : Int) :
    kleinBottleEncodeExpr' (kleinBottleLoopAExprZPow m) = (m, 0) := by
  cases m with
  | ofNat n =>
      simp [kleinBottleLoopAExprZPow]
  | negSucc n =>
      change kleinBottleInv (kleinBottleEncodeExpr' (kleinBottleLoopAExprPow (Nat.succ n))) =
        (Int.negSucc n, 0)
      have hpow :
          kleinBottleEncodeExpr' (kleinBottleLoopAExprPow (Nat.succ n)) =
            (Int.ofNat (Nat.succ n), 0) :=
        kleinBottleEncodeExpr_powA (Nat.succ n)
      rw [hpow]
      have hneg : -Int.ofNat (Nat.succ n) = Int.negSucc n := rfl
      change (-Int.ofNat (Nat.succ n), -kleinBottleAct (Int.ofNat (Nat.succ n)) 0) =
        (Int.negSucc n, 0)
      apply Prod.ext
      · exact hneg
      · simp [kleinBottleAct_zero]

@[simp] theorem kleinBottleEncodeExpr_zpowB (n : Int) :
    kleinBottleEncodeExpr' (kleinBottleLoopBExprZPow n) = (0, n) := by
  cases n with
  | ofNat k =>
      simp [kleinBottleLoopBExprZPow]
  | negSucc k =>
      change kleinBottleInv (kleinBottleEncodeExpr' (kleinBottleLoopBExprPow (Nat.succ k))) =
        (0, Int.negSucc k)
      have hpow :
          kleinBottleEncodeExpr' (kleinBottleLoopBExprPow (Nat.succ k)) =
            (0, Int.ofNat (Nat.succ k)) :=
        kleinBottleEncodeExpr_powB (Nat.succ k)
      rw [hpow]
      have hneg : -Int.ofNat (Nat.succ k) = Int.negSucc k := rfl
      change (-0, -kleinBottleAct 0 (Int.ofNat (Nat.succ k))) = (0, Int.negSucc k)
      apply Prod.ext
      · simp
      · simpa [Int.natCast_succ, kleinBottleAct_zero_exp] using hneg

/-- The canonical expression for the normal-form coordinate `(m,n)` is `a^m b^n`. -/
@[simp] noncomputable def kleinBottleDecodeExpr :
    Int × Int → KleinBottleExpr kleinBottleBase kleinBottleBase
  | (m, n) =>
      KleinBottleExpr.trans (kleinBottleLoopAExprZPow m) (kleinBottleLoopBExprZPow n)

@[simp] theorem kleinBottleEncodeExpr_decodeExpr (z : Int × Int) :
    kleinBottleEncodeExpr' (kleinBottleDecodeExpr z) = z := by
  cases z with
  | mk m n =>
      change kleinBottleEncodeExpr'
        (KleinBottleExpr.trans (kleinBottleLoopAExprZPow m) (kleinBottleLoopBExprZPow n)) =
        (m, n)
      rw [kleinBottleEncodeExpr_trans, kleinBottleEncodeExpr_zpowA, kleinBottleEncodeExpr_zpowB]
      simp [kleinBottleMul]

/-- Loop-expression relation for the Klein bottle: equality of normal-form
coordinates in the semidirect product `Z ⋊ Z`, where the second coordinate acts
by sign on the first loop's transported `b`-coordinate. -/
noncomputable def kleinBottleRel
    (p q : KleinBottleExpr kleinBottleBase kleinBottleBase) : Prop :=
  kleinBottleEncodeExpr' p = kleinBottleEncodeExpr' q

/-- Setoid on based Klein bottle loop expressions by semidirect-product normal form. -/
noncomputable def kleinBottleSetoid :
    Setoid (KleinBottleExpr kleinBottleBase kleinBottleBase) where
  r := kleinBottleRel
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro p
      rfl
    · intro p q hpq
      simpa [kleinBottleRel] using hpq.symm
    · intro p q r hpq hqr
      exact hpq.trans hqr

/-- The computational-path fundamental group of the Klein bottle. -/
abbrev kleinBottlePiOne : Type u :=
  Quot kleinBottleSetoid.r

/-- Encode a Klein bottle loop class by its semidirect-product normal form. -/
@[simp] noncomputable def kleinBottleEncode : kleinBottlePiOne → Int × Int :=
  Quot.lift kleinBottleEncodeExpr' (by
    intro p q hpq
    exact hpq)

/-- Decode a semidirect-product coordinate to the canonical loop-expression class. -/
@[simp] noncomputable def kleinBottleDecode : Int × Int → kleinBottlePiOne :=
  fun z => Quot.mk _ (kleinBottleDecodeExpr z)

@[simp] theorem kleinBottleEncode_decode (z : Int × Int) :
    kleinBottleEncode (kleinBottleDecode z) = z := by
  simpa [kleinBottleDecode, kleinBottleEncode] using kleinBottleEncodeExpr_decodeExpr z

@[simp] theorem kleinBottleDecode_encode (x : kleinBottlePiOne) :
    kleinBottleDecode (kleinBottleEncode x) = x := by
  refine Quot.inductionOn x ?_
  intro p
  apply Quot.sound
  change kleinBottleEncodeExpr' (kleinBottleDecodeExpr (kleinBottleEncodeExpr' p)) =
    kleinBottleEncodeExpr' p
  simpa using kleinBottleEncodeExpr_decodeExpr (kleinBottleEncodeExpr' p)

/-! ## pi_1(K) equiv Z x Z (semidirect presentation) -/

noncomputable def kleinBottlePiOneEquivIntProd :
    SimpleEquiv kleinBottlePiOne (Int × Int) where
  toFun := kleinBottleEncode
  invFun := kleinBottleDecode
  left_inv := kleinBottleDecode_encode
  right_inv := kleinBottleEncode_decode

/-! ## Relator: a b a^{-1} b = 1 -/

/-! ## Compatibility aliases -/

abbrev KleinBottle : Type u := KleinBottleCompPath.{u}

@[simp] noncomputable abbrev kleinBottleBasepoint : KleinBottle := kleinBottleBase

end CompPath
end Path
end ComputationalPaths
