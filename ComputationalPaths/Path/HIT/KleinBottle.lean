/-
# The Klein bottle as a higher-inductive type (axiomatic skeleton)

This module introduces `KleinBottle` together with its base-point, two
fundamental loops, and the characteristic surface relation

`a ⬝ b ⬝ a⁻¹ = b⁻¹`.

## Encode/decode note

Some earlier developments model the universal cover using a `Type`-valued code
family and a univalence-style transport axiom. In standard Lean that approach
is inconsistent (see `docs/axioms.md`).

To keep the library consistent, we axiomatise only the **loop classification
data** needed to state `π₁(K) ≃ ℤ ⋊ ℤ` (as an equivalence of underlying sets),
packaged as `HasKleinLoopDecode`.

We keep the parity sign function `kleinSign` and its key lemma
`kleinSign_add`, because they are used by the SVK-based development in
`KleinBottleSVK.lean`.
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

/-- Abstract Klein bottle type. -/
axiom KleinBottle : Type u

/-- Distinguished point on the Klein bottle. -/
axiom kleinBase : KleinBottle

/-- Horizontal generator (`a`). -/
axiom kleinLoopA : Path (A := KleinBottle) kleinBase kleinBase

/-- Vertical generator (`b`). -/
axiom kleinLoopB : Path (A := KleinBottle) kleinBase kleinBase

/-- Surface relation encoding `a ⬝ b ⬝ a⁻¹ = b⁻¹`. -/
axiom kleinSurf :
  Path.trans (Path.trans kleinLoopA kleinLoopB) (Path.symm kleinLoopA) =
    Path.symm kleinLoopB

noncomputable section

/-! ## Parity sign `(-1)^m` -/

/-- Parity-based sign `(-1)^m` used to describe the Klein bottle multiplication law. -/
def kleinSign (m : Int) : Int :=
  if m.natAbs % 2 = 0 then 1 else -1

@[simp] theorem kleinSign_zero : kleinSign 0 = 1 := by
  classical
  simp [kleinSign]

@[simp] theorem kleinSign_neg (m : Int) : kleinSign (-m) = kleinSign m := by
  classical
  unfold kleinSign
  have : (-m).natAbs = m.natAbs := Int.natAbs_neg _
  simp [this]

theorem kleinSign_succ (m : Int) : kleinSign (m + 1) = -kleinSign m := by
  classical
  unfold kleinSign
  cases m with
  | ofNat n =>
      have hsucc : (Int.ofNat n + 1).natAbs = n + 1 := by
        simp only [Int.ofNat_eq_coe]
        rfl
      simp only [hsucc]
      by_cases h : n % 2 = 0
      · have hsucc_odd : (n + 1) % 2 = 1 := by omega
        simp [h, hsucc_odd]
      · have hn_odd : n % 2 = 1 := by omega
        have hsucc_even : (n + 1) % 2 = 0 := by omega
        simp [hn_odd, hsucc_even]
  | negSucc n =>
      simp only [Int.natAbs_negSucc]
      have hneg : (Int.negSucc n + 1).natAbs = n := by
        cases n with
        | zero => rfl
        | succ n =>
            have : Int.negSucc (n + 1) + 1 = Int.negSucc n := rfl
            simp only [this, Int.natAbs_negSucc]
      simp only [hneg]
      by_cases h : (n + 1) % 2 = 0
      · have hn_odd : n % 2 = 1 := by omega
        simp [h, hn_odd]
      · have hn_succ_odd : (n + 1) % 2 = 1 := by omega
        have hn_even : n % 2 = 0 := by omega
        simp [hn_succ_odd, hn_even]

theorem kleinSign_pred (m : Int) : kleinSign (m - 1) = -kleinSign m := by
  have h := kleinSign_succ (m - 1)
  simp only [Int.sub_add_cancel] at h
  have hnegeq : -kleinSign m = -(-kleinSign (m - 1)) := _root_.congrArg (fun x => -x) h
  simp only [Int.neg_neg] at hnegeq
  exact hnegeq.symm

/-- `kleinSign` is multiplicative: `kleinSign (m + n) = kleinSign m * kleinSign n`. -/
theorem kleinSign_add (m n : Int) : kleinSign (m + n) = kleinSign m * kleinSign n := by
  classical
  induction n using LoopQuot.int_induction with
  | base =>
      simp only [Int.add_zero, kleinSign_zero, Int.mul_one]
  | succ n ih =>
      rw [← Int.add_assoc, kleinSign_succ, ih, kleinSign_succ, Int.neg_mul_eq_mul_neg]
  | pred n ih =>
      have hstep : m + (n - 1) = m + n - 1 := by omega
      rw [hstep, kleinSign_pred, ih, kleinSign_pred, Int.neg_mul_eq_mul_neg]

/-! ## Loop powers and decoding -/

/-- Natural powers of the `a` loop at the raw path level. -/
@[simp] def kleinLoopAPathPow : Nat → Path kleinBase kleinBase
  | 0 => Path.refl _
  | Nat.succ n => Path.trans (kleinLoopAPathPow n) kleinLoopA

/-- Integer powers of the `a` loop at the raw path level. -/
@[simp] def kleinLoopAPathZPow : Int → Path kleinBase kleinBase
  | Int.ofNat n => kleinLoopAPathPow n
  | Int.negSucc n => Path.symm (kleinLoopAPathPow (Nat.succ n))

/-- Natural powers of the `b` loop at the raw path level. -/
@[simp] def kleinLoopBPathPow : Nat → Path kleinBase kleinBase
  | 0 => Path.refl _
  | Nat.succ n => Path.trans (kleinLoopBPathPow n) kleinLoopB

/-- Integer powers of the `b` loop at the raw path level. -/
@[simp] def kleinLoopBPathZPow : Int → Path kleinBase kleinBase
  | Int.ofNat n => kleinLoopBPathPow n
  | Int.negSucc n => Path.symm (kleinLoopBPathPow (Nat.succ n))

/-- Decode a pair of integers as the loop `a^m ⬝ b^n`. -/
@[simp] def kleinDecodePath (z : Int × Int) : Path kleinBase kleinBase :=
  Path.trans (kleinLoopAPathZPow z.1) (kleinLoopBPathZPow z.2)

/-! ## Loop encode/decode interface -/

/-- Encode/decode data for the Klein bottle: normal forms `a^m b^n`. -/
class HasKleinLoopDecode : Type u where
  /-- Integer pair assigned to a raw loop. -/
  encodePath : Path kleinBase kleinBase → Int × Int
  /-- Encoding is invariant under rewrite equality. -/
  encodePath_rweq :
      ∀ {p q : Path kleinBase kleinBase}, RwEq p q → encodePath p = encodePath q
  /-- Encoding the canonical decoded loop returns the integer pair. -/
  encodePath_kleinDecodePath : ∀ z : Int × Int, encodePath (kleinDecodePath z) = z
  /-- Every loop is rewrite-equal to its decoded normal form. -/
  kleinLoop_rweq_decode :
      ∀ p : Path kleinBase kleinBase, RwEq p (kleinDecodePath (encodePath p))

/-- Encode a raw loop as an integer pair. -/
@[simp] def kleinEncodePath [HasKleinLoopDecode] (p : Path kleinBase kleinBase) : Int × Int :=
  HasKleinLoopDecode.encodePath p

@[simp] theorem kleinEncodePath_rweq [h : HasKleinLoopDecode]
    {p q : Path kleinBase kleinBase} (hpq : RwEq p q) :
    kleinEncodePath p = kleinEncodePath q :=
  h.encodePath_rweq hpq

@[simp] theorem kleinEncodePath_kleinDecodePath [h : HasKleinLoopDecode] (z : Int × Int) :
    kleinEncodePath (kleinDecodePath z) = z :=
  h.encodePath_kleinDecodePath z

theorem kleinLoop_rweq_decode [h : HasKleinLoopDecode] (p : Path kleinBase kleinBase) :
    RwEq p (kleinDecodePath (kleinEncodePath p)) :=
  h.kleinLoop_rweq_decode p

/-! ## Quotient-level encode/decode and π₁ equivalence -/

abbrev KleinBottleLoopQuot : Type u :=
  LoopQuot KleinBottle kleinBase

abbrev kleinPiOne : Type u :=
  PiOne KleinBottle kleinBase

/-- Decode `ℤ × ℤ` as a fundamental-group element. -/
@[simp] def kleinDecode : Int × Int → kleinPiOne :=
  fun z => LoopQuot.ofLoop (A := KleinBottle) (a := kleinBase) (kleinDecodePath z)

/-- Encode `π₁(K)` as an integer pair. -/
@[simp] def kleinEncode [h : HasKleinLoopDecode] : kleinPiOne → Int × Int :=
  Quot.lift (fun p : Path kleinBase kleinBase => kleinEncodePath p)
    (by
      intro p q hpq
      exact kleinEncodePath_rweq (h := h) hpq)

@[simp] theorem kleinEncode_kleinDecode [HasKleinLoopDecode] (z : Int × Int) :
    kleinEncode (kleinDecode z) = z := by
  change kleinEncodePath (kleinDecodePath z) = z
  exact kleinEncodePath_kleinDecodePath (z := z)

theorem kleinDecode_kleinEncode [HasKleinLoopDecode] (x : kleinPiOne) :
    kleinDecode (kleinEncode x) = x := by
  refine Quot.inductionOn x ?_
  intro p
  have hrweq : RwEq p (kleinDecodePath (kleinEncodePath p)) :=
    kleinLoop_rweq_decode (p := p)
  exact Quot.sound (rweq_symm hrweq)

/-- Fundamental group of the Klein bottle, packaged as an equivalence
`π₁(K) ≃ ℤ × ℤ` (normal-form coordinates). -/
noncomputable def kleinPiOneEquivIntProd_ofLoopDecode [HasKleinLoopDecode] :
    SimpleEquiv kleinPiOne (Int × Int) where
  toFun := kleinEncode
  invFun := kleinDecode
  left_inv := kleinDecode_kleinEncode
  right_inv := kleinEncode_kleinDecode

end

end Path
end ComputationalPaths
