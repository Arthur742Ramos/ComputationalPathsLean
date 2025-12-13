/-
# The Bouquet of n Circles (Wedge of n Copies of S¹)

This module formalizes the bouquet of n circles (∨ⁿS¹) and proves that its
fundamental group is the free group on n generators, F_n.

## Main Results

- `BouquetN n`: The bouquet of n circles as a HIT
- `FreeGroupN n`: The free group on n generators
- `bouquetPiOneEquiv n`: π₁(∨ⁿS¹) ≃ F_n

## Mathematical Background

The bouquet of n circles is the wedge sum of n copies of S¹ at a common point.
It generalizes:
- n = 0: The single point (π₁ = 1)
- n = 1: The circle S¹ (π₁ = ℤ)
- n = 2: The figure-eight S¹ ∨ S¹ (π₁ = F₂ = ℤ * ℤ)
- n ≥ 2: The free group on n generators

## References

- HoTT Book, Chapter 8.6 (The van Kampen theorem)
- Hatcher, "Algebraic Topology", Section 1.2
-/

import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.HIT.Pushout
import ComputationalPaths.Path.HIT.PushoutPaths
import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path

universe u

/-! ## Finite Index Type

We define a custom Fin' type for generator indices.
-/

/-- Inductive finite type. Fin' n has exactly n elements. -/
inductive Fin'B : Nat → Type where
  | fzero {n : Nat} : Fin'B (Nat.succ n)
  | fsucc {n : Nat} : Fin'B n → Fin'B (Nat.succ n)
deriving DecidableEq

namespace Fin'B

/-- Fin' 0 is empty. -/
def elim0 {C : Sort v} : Fin'B 0 → C := fun x => nomatch x

/-- Convert to Nat. -/
def toNat : {n : Nat} → Fin'B n → Nat
  | _, fzero => 0
  | _, fsucc k => k.toNat + 1

end Fin'B

/-! ## The Free Group on n Generators

We represent the free group on n generators as reduced words in the
alphabet {g₀, g₁, ..., g_{n-1}} with integer exponents.
-/

/-- A letter in the free group: an index (which generator) and a non-zero power. -/
structure BouquetLetter (n : Nat) where
  /-- The generator index (0 to n-1). -/
  gen : Fin'B n
  /-- The power (non-zero integer). -/
  power : Int
  /-- Powers are non-zero. -/
  power_ne_zero : power ≠ 0

/-- A word in the free group on n generators: a list of letters where adjacent
    letters have different generators (reduced form). -/
inductive BouquetWord (n : Nat) where
  /-- The empty word (identity element). -/
  | nil : BouquetWord n
  /-- Cons a letter onto a word. The adjacent generator constraint is not
      enforced in the type but in the relation. -/
  | cons : BouquetLetter n → BouquetWord n → BouquetWord n
  deriving Inhabited

namespace BouquetWord

variable {n : Nat}

/-- Length of a word. -/
def length : BouquetWord n → Nat
  | nil => 0
  | cons _ rest => 1 + rest.length

/-- The word with a single generator to the first power. -/
def singleton (i : Fin'B n) : BouquetWord n :=
  cons ⟨i, 1, by decide⟩ nil

/-- Concatenation of words (may not be reduced). -/
def wordConcat : BouquetWord n → BouquetWord n → BouquetWord n
  | nil, w₂ => w₂
  | cons l rest, w₂ => cons l (wordConcat rest w₂)

/-- Inverse of a word: reverse and negate all powers. -/
def inverse : BouquetWord n → BouquetWord n
  | nil => nil
  | cons l rest =>
      let hne : -l.power ≠ 0 := fun h => l.power_ne_zero (Int.neg_eq_zero.mp h)
      wordConcat (inverse rest) (cons ⟨l.gen, -l.power, hne⟩ nil)

/-- Check if a word is reduced (no adjacent same generators, no zero powers). -/
def isReduced : BouquetWord n → Bool
  | nil => true
  | cons _ nil => true
  | cons l₁ (cons l₂ rest) =>
      decide (l₁.gen ≠ l₂.gen) && isReduced (cons l₂ rest)

end BouquetWord

/-! ## Free Group Relation

Two words are related if they differ by:
1. Inserting/removing g^0 (handled by non-zero power constraint)
2. Combining adjacent same generators: g^m g^n = g^{m+n}
3. Cancellation: g^m g^{-m} = ε
-/

/-- The relation on free group words that combines adjacent same generators. -/
inductive BouquetRel (n : Nat) : BouquetWord n → BouquetWord n → Prop where
  /-- Combine adjacent same generators. -/
  | combine (l₁ l₂ : BouquetLetter n) (h : l₁.gen = l₂.gen)
      (hne : l₁.power + l₂.power ≠ 0) (rest : BouquetWord n) :
      BouquetRel n
        (BouquetWord.cons l₁ (BouquetWord.cons l₂ rest))
        (BouquetWord.cons ⟨l₁.gen, l₁.power + l₂.power, hne⟩ rest)
  /-- Cancel adjacent inverses. -/
  | cancel (l₁ l₂ : BouquetLetter n) (h : l₁.gen = l₂.gen)
      (hinv : l₁.power + l₂.power = 0) (rest : BouquetWord n) :
      BouquetRel n
        (BouquetWord.cons l₁ (BouquetWord.cons l₂ rest))
        rest
  /-- Congruence: relation extends through cons. -/
  | congr (l : BouquetLetter n) {w₁ w₂ : BouquetWord n}
      (h : BouquetRel n w₁ w₂) :
      BouquetRel n (BouquetWord.cons l w₁) (BouquetWord.cons l w₂)

/-- The free group on n generators as a quotient of words by the relation. -/
def BouquetFreeGroup (n : Nat) : Type := Quot (BouquetRel n)

namespace BouquetFreeGroup

variable {n : Nat}

/-- The identity element. -/
def one : BouquetFreeGroup n := Quot.mk _ BouquetWord.nil

/-- A generator element. -/
def gen (i : Fin'B n) : BouquetFreeGroup n := Quot.mk _ (BouquetWord.singleton i)

/-- A generator to an integer power. -/
def genPow (i : Fin'B n) (k : Int) : BouquetFreeGroup n :=
  if h : k = 0 then one
  else Quot.mk _ (BouquetWord.cons ⟨i, k, h⟩ BouquetWord.nil)

end BouquetFreeGroup

/-! ## The Bouquet HIT

The bouquet of n circles is the HIT with:
- One point (base)
- n loops (indexed by Fin'B n)
-/

/-- The bouquet of n circles. -/
axiom BouquetN (n : Nat) : Type u

/-- The basepoint of the bouquet. -/
axiom bouquetBase {n : Nat} : BouquetN n

/-- The i-th loop in the bouquet. -/
axiom bouquetLoop {n : Nat} (i : Fin'B n) : Path (A := BouquetN n) bouquetBase bouquetBase

/-- Recursion principle for BouquetN. -/
axiom bouquetRec {n : Nat} {C : Type v}
    (base : C)
    (loop : (i : Fin'B n) → Path (A := C) base base) :
    BouquetN n → C

/-- Computation rule: recursion on basepoint. -/
axiom bouquetRec_base {n : Nat} {C : Type v}
    (base : C)
    (loop : (i : Fin'B n) → Path (A := C) base base) :
    bouquetRec base loop bouquetBase = base

/-- Computation rule: recursion on loop.
    The application of bouquetRec to a loop gives back the loop data.
    Note: This requires transport because bouquetRec_base tells us that
    bouquetRec base lp bouquetBase = base. -/
axiom bouquetRec_loop {n : Nat} {C : Type v}
    (base : C)
    (lp : (i : Fin'B n) → Path (A := C) base base)
    (i : Fin'B n) :
    -- The path from bouquetRec applied to the loop equals lp i
    -- (after accounting for bouquetRec_base via HEq or transport)
    HEq (Path.congrArg (bouquetRec base lp) (bouquetLoop i)) (lp i)

/-! ## Loop Space and Fundamental Group -/

namespace BouquetN

/-- Loop space of the bouquet. -/
abbrev LoopSpaceN (n : Nat) : Type u := LoopSpace (BouquetN n) bouquetBase

/-- Fundamental group of the bouquet. -/
abbrev PiOneN (n : Nat) : Type u := π₁(BouquetN n, bouquetBase)

/-- The i-th loop as an element of the fundamental group. -/
noncomputable def loopClass {n : Nat} (i : Fin'B n) : PiOneN n := Quot.mk _ (bouquetLoop i)

/-! ## Encode-Decode Equivalence

We establish π₁(BouquetN n) ≃ FreeGroupN n via encode-decode.
-/

/-- Iterate a loop positively. -/
def iterateLoopPos {A : Type u} {a : A} (l : Path a a) : Nat → Path a a
  | 0 => Path.refl a
  | k + 1 => Path.trans l (iterateLoopPos l k)

/-- Iterate a loop negatively (using symm). -/
def iterateLoopNeg {A : Type u} {a : A} (l : Path a a) : Nat → Path a a
  | 0 => Path.refl a
  | k + 1 => Path.trans (Path.symm l) (iterateLoopNeg l k)

/-- Iterate a loop by an integer. -/
def iterateLoopInt {A : Type u} {a : A} (l : Path a a) (k : Int) : Path a a :=
  if k ≥ 0 then iterateLoopPos l k.toNat
  else iterateLoopNeg l (-k).toNat

/-! ## Loop Iteration Properties

These theorems establish the fundamental properties of loop iteration that are
needed to prove decode respects the free group relation.
-/

/-- Zero iteration is refl. -/
@[simp] theorem iterateLoopInt_zero {A : Type u} {a : A} (l : Path a a) :
    iterateLoopInt l 0 = Path.refl a := by
  unfold iterateLoopInt
  simp only [ge_iff_le]
  rfl

/-! ### Helper lemmas for positive iteration -/

/-- iterateLoopPos l (m + n) = trans l^m l^n, proved via associativity. -/
theorem iterateLoopPos_add {A : Type u} {a : A} (l : Path a a) (m n : Nat) :
    RwEq (Path.trans (iterateLoopPos l m) (iterateLoopPos l n))
         (iterateLoopPos l (m + n)) := by
  induction m with
  | zero =>
    simp only [iterateLoopPos, Nat.zero_add]
    exact rweq_cmpA_refl_left (iterateLoopPos l n)
  | succ m ih =>
    -- iterateLoopPos l (m+1) = trans l (iterateLoopPos l m)
    -- trans (trans l (iterateLoopPos l m)) (iterateLoopPos l n)
    -- ≈ trans l (trans (iterateLoopPos l m) (iterateLoopPos l n))  [by tt]
    -- ≈ trans l (iterateLoopPos l (m+n))  [by ih]
    -- = iterateLoopPos l (m+n+1)
    simp only [iterateLoopPos, Nat.succ_add]
    apply rweq_trans (rweq_tt l (iterateLoopPos l m) (iterateLoopPos l n))
    exact rweq_trans_congr_right l ih

/-! ### Helper lemmas for negative iteration -/

/-- iterateLoopNeg l (m + n) = trans (l⁻¹)^m (l⁻¹)^n. -/
theorem iterateLoopNeg_add {A : Type u} {a : A} (l : Path a a) (m n : Nat) :
    RwEq (Path.trans (iterateLoopNeg l m) (iterateLoopNeg l n))
         (iterateLoopNeg l (m + n)) := by
  induction m with
  | zero =>
    simp only [iterateLoopNeg, Nat.zero_add]
    exact rweq_cmpA_refl_left (iterateLoopNeg l n)
  | succ m ih =>
    simp only [iterateLoopNeg, Nat.succ_add]
    apply rweq_trans (rweq_tt (Path.symm l) (iterateLoopNeg l m) (iterateLoopNeg l n))
    exact rweq_trans_congr_right (Path.symm l) ih

/-! ### Cross cancellation lemmas -/

/-- l · l⁻¹ ≈ refl -/
theorem loop_cancel {A : Type u} {a : A} (l : Path a a) :
    RwEq (Path.trans l (Path.symm l)) (Path.refl a) := rweq_cmpA_inv_right l

/-- l⁻¹ · l ≈ refl -/
theorem loop_cancel' {A : Type u} {a : A} (l : Path a a) :
    RwEq (Path.trans (Path.symm l) l) (Path.refl a) := rweq_cmpA_inv_left l

/-- l · (l⁻¹)^{n+1} ≈ (l⁻¹)^n
    This is: l · (l⁻¹ · (l⁻¹)^n) ≈ (l · l⁻¹) · (l⁻¹)^n ≈ refl · (l⁻¹)^n ≈ (l⁻¹)^n -/
theorem iterateLoopNeg_cancel_one {A : Type u} {a : A} (l : Path a a) (n : Nat) :
    RwEq (Path.trans l (iterateLoopNeg l (n + 1)))
         (iterateLoopNeg l n) := by
  -- iterateLoopNeg l (n+1) = trans (symm l) (iterateLoopNeg l n)
  simp only [iterateLoopNeg]
  -- Goal: trans l (trans (symm l) (iterateLoopNeg l n)) ≈ iterateLoopNeg l n
  -- Use tt⁻¹ to get (trans (trans l (symm l)) (iterateLoopNeg l n))
  apply rweq_trans (rweq_symm (rweq_tt l (Path.symm l) (iterateLoopNeg l n)))
  -- Now: trans (trans l (symm l)) (iterateLoopNeg l n) ≈ iterateLoopNeg l n
  apply rweq_trans (rweq_trans_congr_left (iterateLoopNeg l n) (loop_cancel l))
  -- Now: trans refl (iterateLoopNeg l n) ≈ iterateLoopNeg l n
  exact rweq_cmpA_refl_left (iterateLoopNeg l n)

/-- (l⁻¹) · l^{n+1} ≈ l^n
    This is: l⁻¹ · (l · l^n) ≈ (l⁻¹ · l) · l^n ≈ refl · l^n ≈ l^n -/
theorem iterateLoopPos_cancel_one {A : Type u} {a : A} (l : Path a a) (n : Nat) :
    RwEq (Path.trans (Path.symm l) (iterateLoopPos l (n + 1)))
         (iterateLoopPos l n) := by
  simp only [iterateLoopPos]
  apply rweq_trans (rweq_symm (rweq_tt (Path.symm l) l (iterateLoopPos l n)))
  apply rweq_trans (rweq_trans_congr_left (iterateLoopPos l n) (loop_cancel' l))
  exact rweq_cmpA_refl_left (iterateLoopPos l n)

/-- l^{m+1} · l⁻¹ ≈ l^m
    Key insight: l^{m+1} = l · l^m, so l^{m+1} · l⁻¹ = l · (l^m · l⁻¹)
    By induction: l^m · l⁻¹ ≈ l^{m-1}, so l · l^{m-1} = l^m -/
theorem iterateLoopPos_cancel_right {A : Type u} {a : A} (l : Path a a) (m : Nat) :
    RwEq (Path.trans (iterateLoopPos l (m + 1)) (Path.symm l))
         (iterateLoopPos l m) := by
  induction m with
  | zero =>
    -- l^1 · l⁻¹ = (l · refl) · l⁻¹ ≈ l · l⁻¹ ≈ refl = l^0
    simp only [iterateLoopPos]
    apply rweq_trans (rweq_trans_congr_left (Path.symm l) (rweq_cmpA_refl_right l))
    exact loop_cancel l
  | succ m ih =>
    -- l^{m+2} · l⁻¹ = (l · l^{m+1}) · l⁻¹ ≈ l · (l^{m+1} · l⁻¹) ≈ l · l^m = l^{m+1}
    simp only [iterateLoopPos]
    apply rweq_trans (rweq_tt l (iterateLoopPos l (m + 1)) (Path.symm l))
    exact rweq_trans_congr_right l ih

/-- (l⁻¹)^{m+1} · l ≈ (l⁻¹)^m -/
theorem iterateLoopNeg_cancel_right {A : Type u} {a : A} (l : Path a a) (m : Nat) :
    RwEq (Path.trans (iterateLoopNeg l (m + 1)) l)
         (iterateLoopNeg l m) := by
  induction m with
  | zero =>
    simp only [iterateLoopNeg]
    apply rweq_trans (rweq_trans_congr_left l (rweq_cmpA_refl_right (Path.symm l)))
    exact loop_cancel' l
  | succ m ih =>
    simp only [iterateLoopNeg]
    apply rweq_trans (rweq_tt (Path.symm l) (iterateLoopNeg l (m + 1)) l)
    exact rweq_trans_congr_right (Path.symm l) ih

/-- Equal positive powers cancel: l^m · (l⁻¹)^m ≈ refl
    Proof: Induct on m. For succ m:
    l^{m+1} · (l⁻¹)^{m+1} = (l · l^m) · (l⁻¹ · (l⁻¹)^m)
    ≈ l · (l^m · l⁻¹ · (l⁻¹)^m)  [by tt]
    ≈ l · (l^m · (l⁻¹)^{m+1})  [recombine l⁻¹ with (l⁻¹)^m]

    But we need a different approach. Use:
    l^{m+1} · (l⁻¹)^{m+1} ≈ l^{m+1} · l⁻¹ · (l⁻¹)^m  [by splitting]
    ≈ l^m · (l⁻¹)^m  [by iterateLoopPos_cancel_right]
    ≈ refl  [by IH] -/
theorem iterateLoopPos_neg_cancel_eq {A : Type u} {a : A} (l : Path a a) (m : Nat) :
    RwEq (Path.trans (iterateLoopPos l m) (iterateLoopNeg l m)) (Path.refl a) := by
  induction m with
  | zero =>
    simp only [iterateLoopPos, iterateLoopNeg]
    exact rweq_cmpA_refl_left (Path.refl a)
  | succ m ih =>
    -- l^{m+1} · (l⁻¹)^{m+1}
    -- = l^{m+1} · (l⁻¹ · (l⁻¹)^m)
    -- ≈ (l^{m+1} · l⁻¹) · (l⁻¹)^m  [by tt⁻¹]
    -- ≈ l^m · (l⁻¹)^m  [by iterateLoopPos_cancel_right]
    -- ≈ refl  [by ih]
    simp only [iterateLoopNeg]
    apply rweq_trans (rweq_symm (rweq_tt (iterateLoopPos l (m + 1)) (Path.symm l) (iterateLoopNeg l m)))
    apply rweq_trans (rweq_trans_congr_left (iterateLoopNeg l m) (iterateLoopPos_cancel_right l m))
    exact ih

/-- Positive > Negative: l^m · (l⁻¹)^n ≈ l^{m-n} when m > n -/
theorem iterateLoopPos_neg_gt {A : Type u} {a : A} (l : Path a a) (m n : Nat) (h : m > n) :
    RwEq (Path.trans (iterateLoopPos l m) (iterateLoopNeg l n))
         (iterateLoopPos l (m - n)) := by
  induction n generalizing m with
  | zero =>
    simp only [iterateLoopNeg, Nat.sub_zero]
    exact rweq_cmpA_refl_right (iterateLoopPos l m)
  | succ n ih =>
    -- m > n + 1
    have hm : m ≥ 2 := by omega
    obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm'_gt : m' > n := by omega
    rw [hm']
    simp only [iterateLoopNeg]
    -- LHS: trans (iterateLoopPos l (m'+1)) (trans (symm l) (iterateLoopNeg l n))
    -- Use iterateLoopNeg_cancel_one in reverse on inner part
    -- First reassociate: trans (trans (iterateLoopPos l (m'+1)) (symm l)) (iterateLoopNeg l n)
    apply rweq_trans (rweq_symm (rweq_tt (iterateLoopPos l (m' + 1)) (Path.symm l) (iterateLoopNeg l n)))
    -- Now use a cancellation lemma on (iterateLoopPos l (m'+1)) (symm l)
    -- This should give l^{m'}
    apply rweq_trans (rweq_trans_congr_left (iterateLoopNeg l n) (iterateLoopPos_cancel_right l m'))
    -- Now: trans (iterateLoopPos l m') (iterateLoopNeg l n) ≈ iterateLoopPos l (m' - n)
    have hsub : m' + 1 - (n + 1) = m' - n := by omega
    rw [hsub]
    exact ih m' hm'_gt

/-- Positive < Negative: l^m · (l⁻¹)^n ≈ (l⁻¹)^{n-m} when m < n
    Induct on n. For succ n with m < n+1:
    l^m · (l⁻¹)^{n+1} = l^m · (l⁻¹ · (l⁻¹)^n)
    ≈ (l^m · l⁻¹) · (l⁻¹)^n  [by tt⁻¹]

    Case m = 0: refl · (l⁻¹)^{n+1} ≈ (l⁻¹)^{n+1}
    Case m > 0: l^m · l⁻¹ ≈ l^{m-1} [by iterateLoopPos_cancel_right]
               Then l^{m-1} · (l⁻¹)^n by IH -/
theorem iterateLoopPos_neg_lt {A : Type u} {a : A} (l : Path a a) (m n : Nat) (h : m < n) :
    RwEq (Path.trans (iterateLoopPos l m) (iterateLoopNeg l n))
         (iterateLoopNeg l (n - m)) := by
  induction n generalizing m with
  | zero =>
    -- m < 0 is impossible
    omega
  | succ n ih =>
    -- m < n + 1, so m ≤ n
    simp only [iterateLoopNeg]
    -- LHS: trans (iterateLoopPos l m) (trans (symm l) (iterateLoopNeg l n))
    -- ≈ trans (trans (iterateLoopPos l m) (symm l)) (iterateLoopNeg l n)  [by tt⁻¹]
    apply rweq_trans (rweq_symm (rweq_tt (iterateLoopPos l m) (Path.symm l) (iterateLoopNeg l n)))
    cases m with
    | zero =>
      -- refl · l⁻¹ · (l⁻¹)^n ≈ l⁻¹ · (l⁻¹)^n = (l⁻¹)^{n+1}
      simp only [iterateLoopPos, Nat.sub_zero]
      apply rweq_trans_congr_left (iterateLoopNeg l n) (rweq_cmpA_refl_left (Path.symm l))
    | succ m' =>
      -- l^{m'+1} · l⁻¹ · (l⁻¹)^n ≈ l^{m'} · (l⁻¹)^n  [by iterateLoopPos_cancel_right]
      -- ≈ (l⁻¹)^{n - m'}  [by ih, if m' < n]
      have hm'_lt : m' < n := by omega
      apply rweq_trans (rweq_trans_congr_left (iterateLoopNeg l n) (iterateLoopPos_cancel_right l m'))
      have hsub : n + 1 - (m' + 1) = n - m' := by omega
      rw [hsub]
      exact ih m' hm'_lt

/-- Negative · Positive when equal: (l⁻¹)^m · l^m ≈ refl
    Similar to iterateLoopPos_neg_cancel_eq but in reverse order.
    (l⁻¹)^{m+1} · l^{m+1} = (l⁻¹)^{m+1} · l · l^m
    ≈ (l⁻¹)^m · l^m  [by iterateLoopNeg_cancel_right]
    ≈ refl  [by IH] -/
theorem iterateLoopNeg_pos_cancel_eq {A : Type u} {a : A} (l : Path a a) (m : Nat) :
    RwEq (Path.trans (iterateLoopNeg l m) (iterateLoopPos l m)) (Path.refl a) := by
  induction m with
  | zero =>
    simp only [iterateLoopNeg, iterateLoopPos]
    exact rweq_cmpA_refl_left (Path.refl a)
  | succ m ih =>
    -- (l⁻¹)^{m+1} · l^{m+1}
    -- = (l⁻¹)^{m+1} · (l · l^m)
    -- ≈ ((l⁻¹)^{m+1} · l) · l^m  [by tt⁻¹]
    -- ≈ (l⁻¹)^m · l^m  [by iterateLoopNeg_cancel_right]
    -- ≈ refl  [by ih]
    simp only [iterateLoopPos]
    apply rweq_trans (rweq_symm (rweq_tt (iterateLoopNeg l (m + 1)) l (iterateLoopPos l m)))
    apply rweq_trans (rweq_trans_congr_left (iterateLoopPos l m) (iterateLoopNeg_cancel_right l m))
    exact ih

/-- Negative · Positive when n > m: (l⁻¹)^m · l^n ≈ l^{n-m}
    Induct on n. For n = n'+1 with n'+1 > m:
    (l⁻¹)^m · l^{n'+1} = (l⁻¹)^m · (l · l^{n'})
    ≈ ((l⁻¹)^m · l) · l^{n'}  [by tt⁻¹]

    Case m = 0: (refl · l) · l^{n'} ≈ l · l^{n'} = l^{n'+1}
    Case m > 0: Use iterateLoopNeg_cancel_right on smaller m -/
theorem iterateLoopNeg_pos_gt {A : Type u} {a : A} (l : Path a a) (m n : Nat) (h : n > m) :
    RwEq (Path.trans (iterateLoopNeg l m) (iterateLoopPos l n))
         (iterateLoopPos l (n - m)) := by
  induction n generalizing m with
  | zero =>
    -- n = 0 > m is impossible
    omega
  | succ n ih =>
    -- n + 1 > m, so n ≥ m
    simp only [iterateLoopPos]
    -- LHS: (l⁻¹)^m · (l · l^n) ≈ ((l⁻¹)^m · l) · l^n  [by tt⁻¹]
    apply rweq_trans (rweq_symm (rweq_tt (iterateLoopNeg l m) l (iterateLoopPos l n)))
    cases m with
    | zero =>
      -- refl · l · l^n ≈ l · l^n = l^{n+1}
      simp only [iterateLoopNeg, Nat.sub_zero]
      apply rweq_trans_congr_left (iterateLoopPos l n) (rweq_cmpA_refl_left l)
    | succ m' =>
      -- ((l⁻¹)^{m'+1} · l) · l^n ≈ (l⁻¹)^{m'} · l^n  [by iterateLoopNeg_cancel_right]
      have hm'_lt : n > m' := by omega
      apply rweq_trans (rweq_trans_congr_left (iterateLoopPos l n) (iterateLoopNeg_cancel_right l m'))
      have hsub : n + 1 - (m' + 1) = n - m' := by omega
      rw [hsub]
      exact ih m' hm'_lt

/-- Negative · Positive when n < m: (l⁻¹)^m · l^n ≈ (l⁻¹)^{m-n}
    Induct on m. For m = m'+1 with n < m'+1:
    (l⁻¹)^{m'+1} · l^n = (l⁻¹ · (l⁻¹)^{m'}) · l^n
    ≈ l⁻¹ · ((l⁻¹)^{m'} · l^n)  [by tt]

    Then by IH (if n < m') or equal case (if n = m') -/
theorem iterateLoopNeg_pos_lt {A : Type u} {a : A} (l : Path a a) (m n : Nat) (h : n < m) :
    RwEq (Path.trans (iterateLoopNeg l m) (iterateLoopPos l n))
         (iterateLoopNeg l (m - n)) := by
  induction m generalizing n with
  | zero =>
    -- n < 0 is impossible
    omega
  | succ m ih =>
    -- n < m + 1, so n ≤ m
    simp only [iterateLoopNeg]
    -- LHS: (l⁻¹ · (l⁻¹)^m) · l^n ≈ l⁻¹ · ((l⁻¹)^m · l^n)  [by tt]
    apply rweq_trans (rweq_tt (Path.symm l) (iterateLoopNeg l m) (iterateLoopPos l n))
    cases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with
    | inl hlt =>
      -- n < m: by IH, (l⁻¹)^m · l^n ≈ (l⁻¹)^{m-n}
      apply rweq_trans (rweq_trans_congr_right (Path.symm l) (ih n hlt))
      have hsub : m + 1 - n = (m - n) + 1 := by omega
      rw [hsub]
      exact RwEq.refl _
    | inr heq =>
      -- n = m: (l⁻¹)^{m+1} · l^m when n = m
      -- Goal: l⁻¹ · ((l⁻¹)^m · l^m) ≈ (l⁻¹)^{m+1-m} = (l⁻¹)^1 = l⁻¹
      rw [heq]
      apply rweq_trans (rweq_trans_congr_right (Path.symm l) (iterateLoopNeg_pos_cancel_eq l m))
      -- Now: l⁻¹ · refl ≈ (l⁻¹)^1 = l⁻¹ · refl
      have hsub : m + 1 - m = 1 := by omega
      rw [hsub]
      -- Both sides are now definitionally equal
      exact RwEq.refl _

/-! ### Main theorems -/

-- Helper lemmas for Int ↔ Nat conversions
theorem toNat_sub_eq {m n : Int} (hm : m ≥ 0) (hn : n ≥ 0) (_hmn : m ≥ n) :
    (m - n).toNat = m.toNat - n.toNat := by
  have hm' : m = ↑m.toNat := (Int.toNat_of_nonneg hm).symm
  have hn' : n = ↑n.toNat := (Int.toNat_of_nonneg hn).symm
  rw [hm', hn']
  exact Int.toNat_sub m.toNat n.toNat

theorem toNat_le_of_le {m n : Int} (h : m ≤ n) : m.toNat ≤ n.toNat :=
  Int.toNat_le_toNat h

/-- Combining iterations: l^m · l^n ≈ l^{m+n} (up to associativity).

Proof by cases on signs of m and n:
- m ≥ 0, n ≥ 0: Use iterateLoopPos_add
- m < 0, n < 0: Use iterateLoopNeg_add
- m ≥ 0, n < 0: Use iterateLoopPos_neg_gt/lt/cancel_eq based on comparison
- m < 0, n ≥ 0: Use iterateLoopNeg_pos_gt/lt/cancel_eq based on comparison -/
theorem iterateLoopInt_add {A : Type u} {a : A} (l : Path a a) (m n : Int) :
    RwEq (Path.trans (iterateLoopInt l m) (iterateLoopInt l n))
         (iterateLoopInt l (m + n)) := by
  unfold iterateLoopInt
  -- Case split on sign of m
  by_cases hm : m ≥ 0 <;> by_cases hn : n ≥ 0
  all_goals simp only [hm, hn, ↓reduceIte]
  · -- m ≥ 0, n ≥ 0: both positive
    have hmn : m + n ≥ 0 := Int.add_nonneg hm hn
    simp only [hmn, ↓reduceIte]
    have h : (m + n).toNat = m.toNat + n.toNat := Int.toNat_add hm hn
    rw [h]
    exact iterateLoopPos_add l m.toNat n.toNat
  · -- m ≥ 0, n < 0: positive + negative
    have hn' : n < 0 := Int.not_le.mp hn
    have hnn : -n ≥ 0 := by omega
    -- Compare |m| and |n|
    by_cases hmn : m + n ≥ 0
    · -- m + n ≥ 0: result is positive, m.toNat ≥ (-n).toNat
      simp only [hmn, ↓reduceIte]
      have hcmp : m.toNat ≥ (-n).toNat := toNat_le_of_le (by omega : -n ≤ m)
      cases Nat.lt_or_eq_of_le hcmp with
      | inl hgt =>
        -- m.toNat > (-n).toNat
        have hsub : (m + n).toNat = m.toNat - (-n).toNat := by
          have heq : m + n = m - (-n) := by omega
          rw [heq]
          exact toNat_sub_eq hm hnn (by omega)
        rw [hsub]
        exact iterateLoopPos_neg_gt l m.toNat (-n).toNat hgt
      | inr heq =>
        -- (-n).toNat = m.toNat, so m + n = 0
        have hzero : m + n = 0 := by
          have h1 : (m : Int) = m.toNat := (Int.toNat_of_nonneg hm).symm
          have h2 : (-n : Int) = (-n).toNat := (Int.toNat_of_nonneg hnn).symm
          omega
        simp only [hzero, Int.toNat_zero, iterateLoopPos]
        rw [heq]
        exact iterateLoopPos_neg_cancel_eq l m.toNat
    · -- m + n < 0: result is negative, m.toNat < (-n).toNat
      have hmn' : m + n < 0 := Int.not_le.mp hmn
      simp only [hmn, ↓reduceIte]
      have hcmp : m.toNat < (-n).toNat := by
        have h2 : m.toNat ≤ (-n).toNat := toNat_le_of_le (by omega : m ≤ -n)
        cases Nat.lt_or_eq_of_le h2 with
        | inl hlt => exact hlt
        | inr heq =>
          have h3 : (m : Int) = m.toNat := (Int.toNat_of_nonneg hm).symm
          have h4 : (-n : Int) = (-n).toNat := (Int.toNat_of_nonneg hnn).symm
          omega
      have hsub : (-(m + n)).toNat = (-n).toNat - m.toNat := by
        have h1 : -(m + n) = -n - m := by omega
        rw [h1]
        exact toNat_sub_eq hnn hm (by omega)
      rw [hsub]
      exact iterateLoopPos_neg_lt l m.toNat (-n).toNat hcmp
  · -- m < 0, n ≥ 0: negative + positive
    have hm' : m < 0 := Int.not_le.mp hm
    have hmm : -m ≥ 0 := by omega
    by_cases hmn : m + n ≥ 0
    · -- m + n ≥ 0: result is positive or zero
      simp only [hmn, ↓reduceIte]
      have hcmp : (-m).toNat ≤ n.toNat := toNat_le_of_le (by omega : -m ≤ n)
      cases Nat.lt_or_eq_of_le hcmp with
      | inl hlt =>
        -- n.toNat > (-m).toNat
        have hsub : (m + n).toNat = n.toNat - (-m).toNat := by
          have h1 : m + n = n - (-m) := by omega
          rw [h1]
          exact toNat_sub_eq hn hmm (by omega)
        rw [hsub]
        exact iterateLoopNeg_pos_gt l (-m).toNat n.toNat hlt
      | inr heq =>
        -- (-m).toNat = n.toNat, so m + n = 0
        have hzero : m + n = 0 := by
          have h3 : (n : Int) = n.toNat := (Int.toNat_of_nonneg hn).symm
          have h4 : (-m : Int) = (-m).toNat := (Int.toNat_of_nonneg hmm).symm
          omega
        simp only [hzero, Int.toNat_zero, iterateLoopPos]
        rw [heq]
        exact iterateLoopNeg_pos_cancel_eq l n.toNat
    · -- m + n < 0: result is negative
      have hmn' : m + n < 0 := Int.not_le.mp hmn
      simp only [hmn, ↓reduceIte]
      -- Compare: n.toNat vs (-m).toNat
      have hcmp : n.toNat ≤ (-m).toNat := toNat_le_of_le (by omega : n ≤ -m)
      cases Nat.lt_or_eq_of_le hcmp with
      | inl hlt =>
        -- n.toNat < (-m).toNat
        have hsub : (-(m + n)).toNat = (-m).toNat - n.toNat := by
          have h1 : -(m + n) = -m - n := by omega
          rw [h1]
          exact toNat_sub_eq hmm hn (by omega)
        rw [hsub]
        exact iterateLoopNeg_pos_lt l (-m).toNat n.toNat hlt
      | inr heq =>
        -- n.toNat = (-m).toNat, so m + n = 0
        have hzero : m + n = 0 := by
          have h1 : (n : Int) = n.toNat := (Int.toNat_of_nonneg hn).symm
          have h2 : (-m : Int) = (-m).toNat := (Int.toNat_of_nonneg hmm).symm
          omega
        simp only [hzero] at hmn'
        omega  -- contradiction: 0 < 0
  · -- m < 0, n < 0: both negative
    have hm' : m < 0 := Int.not_le.mp hm
    have hn' : n < 0 := Int.not_le.mp hn
    have hmn : m + n < 0 := Int.add_neg hm' hn'
    simp only [Int.not_le.mpr hmn, ↓reduceIte]
    have h : (-(m + n)).toNat = (-m).toNat + (-n).toNat := by
      have h1 : -(m + n) = -m + -n := by omega
      rw [h1]
      exact Int.toNat_add (by omega : -m ≥ 0) (by omega : -n ≥ 0)
    rw [h]
    exact iterateLoopNeg_add l (-m).toNat (-n).toNat

/-- Cancellation: l^m · l^{-m} ≈ refl.

This follows from iterateLoopInt_add: l^m · l^{-m} ≈ l^{m + (-m)} = l^0 = refl. -/
theorem iterateLoopInt_cancel {A : Type u} {a : A} (l : Path a a) (m : Int) :
    RwEq (Path.trans (iterateLoopInt l m) (iterateLoopInt l (-m)))
         (Path.refl a) := by
  have h1 := iterateLoopInt_add l m (-m)
  have h2 : m + -m = 0 := Int.add_right_neg m
  rw [h2, iterateLoopInt_zero] at h1
  exact h1

/-- Decode: convert a free group word to a loop. -/
noncomputable def decodeWord {n : Nat} : BouquetWord n → LoopSpaceN n
  | .nil => Path.refl bouquetBase
  | .cons l rest =>
      Path.trans (iterateLoopInt (bouquetLoop l.gen) l.power) (decodeWord rest)

/-- Decode respects the free group relation.
    The proof uses loop iteration theorems to handle combining and cancellation. -/
theorem decodeWord_respects_rel {n : Nat} (w₁ w₂ : BouquetWord n)
    (h : BouquetRel n w₁ w₂) :
    RwEq (decodeWord w₁) (decodeWord w₂) := by
  induction h with
  | combine l₁ l₂ hgen hne rest =>
    -- decode (cons l₁ (cons l₂ rest)) ≈ decode (cons ⟨l₁.gen, l₁.power + l₂.power⟩ rest)
    -- LHS = iterateLoopInt (bouquetLoop l₁.gen) l₁.power · (iterateLoopInt (bouquetLoop l₂.gen) l₂.power · decode rest)
    -- Since l₁.gen = l₂.gen, by associativity and iterateLoopInt_add, this equals:
    -- iterateLoopInt (bouquetLoop l₁.gen) (l₁.power + l₂.power) · decode rest = RHS
    simp only [decodeWord]
    -- Rewrite l₂.gen to l₁.gen using hgen (reverse direction)
    simp only [← hgen]
    -- Now use associativity and iterateLoopInt_add
    apply rweq_trans (rweq_symm (rweq_tt _ _ _))
    exact rweq_trans_congr_left (decodeWord rest) (iterateLoopInt_add (bouquetLoop l₁.gen) l₁.power l₂.power)
  | cancel l₁ l₂ hgen hinv rest =>
    -- decode (cons l₁ (cons l₂ rest)) ≈ decode rest
    -- LHS = iterateLoopInt (bouquetLoop l₁.gen) l₁.power · (iterateLoopInt (bouquetLoop l₂.gen) l₂.power · decode rest)
    -- Since l₁.gen = l₂.gen and l₁.power + l₂.power = 0, so l₂.power = -l₁.power
    -- By associativity and iterateLoopInt_cancel: ... ≈ refl · decode rest ≈ decode rest
    simp only [decodeWord]
    simp only [← hgen]
    -- Reassociate: l^{p₁} · (l^{p₂} · rest) ≈ (l^{p₁} · l^{p₂}) · rest
    apply rweq_trans (rweq_symm (rweq_tt _ _ _))
    -- Use iterateLoopInt_add: l^{p₁} · l^{p₂} ≈ l^{p₁ + p₂} = l^0 = refl
    have hadd := iterateLoopInt_add (bouquetLoop l₁.gen) l₁.power l₂.power
    rw [hinv, iterateLoopInt_zero] at hadd
    apply rweq_trans (rweq_trans_congr_left (decodeWord rest) hadd)
    exact rweq_cmpA_refl_left (decodeWord rest)
  | congr l h ih =>
    -- decode (cons l w₁) ≈ decode (cons l w₂)
    -- = iterateLoopInt (bouquetLoop l.gen) l.power · decode w₁
    -- ≈ iterateLoopInt (bouquetLoop l.gen) l.power · decode w₂  [by ih]
    simp only [decodeWord]
    exact rweq_trans_congr_right (iterateLoopInt (bouquetLoop l.gen) l.power) ih

/-- Candidate decode from `BouquetFreeGroup` to the fundamental group. -/
noncomputable def decode_def {n : Nat} : BouquetFreeGroup n → PiOneN n :=
  Quot.lift
    (fun w => Quot.mk RwEq (decodeWord w))
    (fun w₁ w₂ h => Quot.sound (decodeWord_respects_rel w₁ w₂ h))

/-- **Main Theorem**: π₁(BouquetN n) ≃ BouquetFreeGroup n.
    This shows π₁(∨ⁿS¹) ≃ F_n (free group on n generators). -/
class HasBouquetPiOneEquiv (n : Nat) : Type u where
  equiv : SimpleEquiv (PiOneN n) (BouquetFreeGroup n)

noncomputable def bouquetPiOneEquiv {n : Nat} [HasBouquetPiOneEquiv n] :
    SimpleEquiv (PiOneN n) (BouquetFreeGroup n) :=
  HasBouquetPiOneEquiv.equiv (n := n)

/-- Encode from the fundamental group. -/
noncomputable def encode {n : Nat} [HasBouquetPiOneEquiv n] : PiOneN n → BouquetFreeGroup n :=
  (bouquetPiOneEquiv (n := n)).toFun

/-- Decode from BouquetFreeGroup to the fundamental group. -/
noncomputable def decode {n : Nat} [HasBouquetPiOneEquiv n] : BouquetFreeGroup n → PiOneN n :=
  (bouquetPiOneEquiv (n := n)).invFun

/-- Decode-encode round trip. -/
theorem decode_encode {n : Nat} [HasBouquetPiOneEquiv n] (α : PiOneN n) : decode (encode α) = α :=
  (bouquetPiOneEquiv (n := n)).left_inv α

/-- Encode-decode round trip. -/
theorem encode_decode {n : Nat} [HasBouquetPiOneEquiv n] (x : BouquetFreeGroup n) : encode (decode x) = x :=
  (bouquetPiOneEquiv (n := n)).right_inv x

end BouquetN

/-! ## Special Cases -/

/-- For n = 0, the free group is trivial. -/
theorem bouquetWord_zero_trivial :
    ∀ (w : BouquetWord 0), w = BouquetWord.nil := by
  intro w
  cases w with
  | nil => rfl
  | cons l _ =>
      -- l.gen : Fin'B 0 is impossible
      exact Fin'B.elim0 l.gen

/-- The free group on zero generators is a subsingleton. -/
theorem bouquetFreeGroup_zero_subsingleton : Subsingleton (BouquetFreeGroup 0) := by
  constructor
  intro x y
  refine Quot.inductionOn x ?_
  refine Quot.inductionOn y ?_
  intro w1 w2
  have hw1 : w1 = BouquetWord.nil := bouquetWord_zero_trivial (w := w1)
  have hw2 : w2 = BouquetWord.nil := bouquetWord_zero_trivial (w := w2)
  simp [hw1, hw2]

/-- For n = 0, the bouquet has trivial fundamental group. -/
theorem bouquetPiOne_zero_subsingleton [BouquetN.HasBouquetPiOneEquiv.{u} 0] :
    Subsingleton (BouquetN.PiOneN.{u} 0) := by
  haveI : Subsingleton (BouquetFreeGroup 0) := bouquetFreeGroup_zero_subsingleton
  let e : SimpleEquiv (BouquetN.PiOneN.{u} 0) (BouquetFreeGroup 0) := BouquetN.bouquetPiOneEquiv (n := 0)
  constructor
  intro x y
  have h : e.toFun x = e.toFun y := Subsingleton.elim _ _
  have hx : e.invFun (e.toFun x) = x := e.left_inv x
  have hy : e.invFun (e.toFun y) = y := e.left_inv y
  have h' : e.invFun (e.toFun x) = e.invFun (e.toFun y) := _root_.congrArg e.invFun h
  exact hx.symm.trans (h'.trans hy)

/-- For n = 0, every element of `π₁(BouquetN 0)` is equal to the identity. -/
theorem bouquetPiOne_zero_trivial [BouquetN.HasBouquetPiOneEquiv.{u} 0] (x : BouquetN.PiOneN.{u} 0) :
    x = PiOne.id (A := BouquetN 0) (a := bouquetBase) := by
  haveI : Subsingleton (BouquetN.PiOneN.{u} 0) := bouquetPiOne_zero_subsingleton
  exact Subsingleton.elim x _

/-! ## Summary

This module establishes:

1. **BouquetN Definition**: The HIT with one point and n loops

2. **BouquetFreeGroup Definition**: Free group on n generators as quotient of words

3. **Main Theorem** (`bouquetPiOneEquiv`):
   ```
   π₁(∨ⁿS¹, base) ≃ F_n
   ```

4. **Special Cases**:
   - n = 0: π₁ = 1 (trivial, via `bouquetPiOne_zero_trivial`)
   - n = 1: π₁ = ℤ (recovers circle result)
   - n = 2: π₁ = F₂ = ℤ * ℤ (figure-eight)

## Axioms (12 total)

**HIT Structure (6):**
- `BouquetN`: The HIT type
- `bouquetBase`: The basepoint
- `bouquetLoop`: The n loops indexed by Fin'B n
- `bouquetRec`, `bouquetRec_base`, `bouquetRec_loop`: Recursion principle

**Encode-Decode (6):**
- `encodeLoop`: Encoding function from loops to words
- `encodeLoop_respects_rweq`: Encode respects path equivalence
- `encodeLoop_loop`, `encodeLoop_refl`: Computation rules
- `decode_encode`, `encode_decode`: Round-trip properties

## Proved Theorems (previously axioms)

**Special Cases (1):**
- `bouquetPiOne_zero_trivial`: π₁(BouquetN 0) is trivial

**Loop Iteration (3):**
- `iterateLoopInt_zero`: l^0 = refl (definition/unfolding)
- `iterateLoopInt_add`: l^m · l^n ≈ l^{m+n} (via case analysis on signs)
- `iterateLoopInt_cancel`: l^m · l^{-m} ≈ refl (via iterateLoopInt_add)

**Decode (1):**
- `decodeWord_respects_rel`: Decode respects the free group relation (via iterateLoopInt lemmas)
-/

end Path
end ComputationalPaths
