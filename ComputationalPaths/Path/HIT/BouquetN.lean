/-
# The Bouquet of n Circles (Wedge of n Copies of S¹)

This module formalizes the bouquet of n circles (∨ⁿS¹) and the free group on n
generators. It builds a candidate decode map into the fundamental group; the
full π₁ equivalence is not yet formalized.

## Main Results

- `BouquetN n`: The bouquet of n circles as a HIT
- `BouquetFreeGroup n`: The free group on n generators
- `BouquetN.decode_def`: candidate map `BouquetFreeGroup n → PiOneN n`

## Mathematical Background

The bouquet of n circles is the wedge sum of n copies of S¹ at a common point.
It generalizes:
- n = 0: The single point (π₁ = 1)
- n = 1: The circle S¹ (π₁ = ℤ)
- n = 2: The figure-eight S¹ ∨ S¹ (π₁ = F₂ = ℤ * ℤ)
- n ≥ 2: The free group on n generators

The expected equivalence π₁(∨ⁿS¹) ≃ F_n is standard, but the proof is not yet
formalized here.

## References

- HoTT Book, Chapter 8.6 (The van Kampen theorem)
- Hatcher, "Algebraic Topology", Section 1.2
-/

import ComputationalPaths.Path.HIT.CircleCompPath
import ComputationalPaths.Path.HIT.PushoutCompPath
import ComputationalPaths.Path.HIT.PushoutPaths
import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.PathTactic
import ComputationalPaths.Path.Homotopy.Sets

namespace ComputationalPaths
namespace Path

open HIT
open Pushout

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

/-- The natural number representation of a Fin'B is less than the bound. -/
theorem toNat_lt : {n : Nat} → (i : Fin'B n) → i.toNat < n
  | Nat.succ _, fzero => Nat.zero_lt_succ _
  | Nat.succ _, fsucc k => Nat.succ_lt_succ (toNat_lt k)

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

/-! ## Free Group Operations

We define multiplication and inverse on `BouquetFreeGroup` constructively
via word concatenation and reversal.
-/

/-- Word concatenation respects the relation on the right. -/
private theorem wordConcat_rel_right (w₁ : BouquetWord n) {w₂ w₂' : BouquetWord n}
    (h : BouquetRel n w₂ w₂') :
    BouquetRel n (BouquetWord.wordConcat w₁ w₂) (BouquetWord.wordConcat w₁ w₂') := by
  induction w₁ with
  | nil => exact h
  | cons l _rest ih => exact BouquetRel.congr l ih

/-- Word concatenation respects the relation on the left. -/
private theorem wordConcat_rel_left (w₂ : BouquetWord n) {w₁ w₁' : BouquetWord n}
    (h : BouquetRel n w₁ w₁') :
    BouquetRel n (BouquetWord.wordConcat w₁ w₂) (BouquetWord.wordConcat w₁' w₂) := by
  induction h with
  | combine l₁ l₂ hgen hne rest =>
      simp only [BouquetWord.wordConcat]
      exact BouquetRel.combine l₁ l₂ hgen hne (BouquetWord.wordConcat rest w₂)
  | cancel l₁ l₂ hgen hinv rest =>
      simp only [BouquetWord.wordConcat]
      exact BouquetRel.cancel l₁ l₂ hgen hinv (BouquetWord.wordConcat rest w₂)
  | congr l _ ih =>
      simp only [BouquetWord.wordConcat]
      exact BouquetRel.congr l ih

/-- Multiplication on BouquetFreeGroup via word concatenation. -/
noncomputable def mul (x y : BouquetFreeGroup n) : BouquetFreeGroup n :=
  Quot.lift
    (fun w₁ => Quot.lift
      (fun w₂ => Quot.mk _ (BouquetWord.wordConcat w₁ w₂))
      (fun _ _ h => Quot.sound (wordConcat_rel_right w₁ h))
      y)
    (fun _ _ h => by
      induction y using Quot.ind with
      | _ w₂ => exact Quot.sound (wordConcat_rel_left w₂ h))
    x

/-- Word concatenation with nil on the right is identity. -/
private theorem wordConcat_nil_right {n : Nat} (w : BouquetWord n) :
    BouquetWord.wordConcat w BouquetWord.nil = w := by
  induction w with
  | nil => rfl
  | cons l rest ih => simp only [BouquetWord.wordConcat, ih]

/-- Word concatenation is associative. -/
private theorem wordConcat_assoc {n : Nat} (w₁ w₂ w₃ : BouquetWord n) :
    BouquetWord.wordConcat (BouquetWord.wordConcat w₁ w₂) w₃ =
    BouquetWord.wordConcat w₁ (BouquetWord.wordConcat w₂ w₃) := by
  induction w₁ with
  | nil => rfl
  | cons l rest ih => simp only [BouquetWord.wordConcat, ih]

/-- Inverse respects the BouquetRel relation. -/
private theorem inverse_respects_rel {n : Nat} {w₁ w₂ : BouquetWord n}
    (h : BouquetRel n w₁ w₂) :
    BouquetRel n (BouquetWord.inverse w₁) (BouquetWord.inverse w₂) := by
  induction h with
  | combine l₁ l₂ hgen hne rest =>
      simp only [BouquetWord.inverse]
      rw [wordConcat_assoc]
      apply wordConcat_rel_right
      simp only [BouquetWord.wordConcat]
      -- Rewrite goal to use l₂.gen.
      rw [hgen]
      have hne' : -l₂.power + (-l₁.power) ≠ 0 := by
        intro heq
        have h2 : l₁.power + l₂.power = 0 := by omega
        exact hne h2
      have step := BouquetRel.combine
        ⟨l₂.gen, -l₂.power, fun h => l₂.power_ne_zero (Int.neg_eq_zero.mp h)⟩
        ⟨l₂.gen, -l₁.power, fun h => l₁.power_ne_zero (Int.neg_eq_zero.mp h)⟩
        rfl hne' BouquetWord.nil
      have hpow : -l₂.power + (-l₁.power) = -(l₁.power + l₂.power) := by omega
      simp only [hpow] at step
      exact step
  | cancel l₁ l₂ hgen hinv rest =>
      simp only [BouquetWord.inverse]
      rw [wordConcat_assoc]
      simp only [BouquetWord.wordConcat]
      -- Use BouquetRel.cancel. First unify generators with rw.
      rw [hgen]
      have hinv' : -l₂.power + (-l₁.power) = 0 := by omega
      have step := BouquetRel.cancel
        ⟨l₂.gen, -l₂.power, fun h => l₂.power_ne_zero (Int.neg_eq_zero.mp h)⟩
        ⟨l₂.gen, -l₁.power, fun h => l₁.power_ne_zero (Int.neg_eq_zero.mp h)⟩
        rfl hinv' BouquetWord.nil
      have hstep := wordConcat_rel_right (BouquetWord.inverse rest) step
      simp only [wordConcat_nil_right] at hstep
      exact hstep
  | congr l _ ih =>
      simp only [BouquetWord.inverse]
      exact wordConcat_rel_left _ ih

/-- Inverse on BouquetFreeGroup via word inverse. -/
noncomputable def inv (x : BouquetFreeGroup n) : BouquetFreeGroup n :=
  Quot.lift
    (fun w => Quot.mk _ (BouquetWord.inverse w))
    (fun _ _ h => Quot.sound (inverse_respects_rel h))
    x

end BouquetFreeGroup

/-! ## The Bouquet of n Circles

The bouquet `∨ⁿ S¹` is defined here as an iterated wedge of circles, built from the
pushout-based wedge construction.

* `BouquetN 0` is the point `PUnit'`.
* `BouquetN (n+1)` is `BouquetN n ∨ S¹`.

The basepoint is always the left injection basepoint, and the loops are indexed by
`Fin'B n` where `fzero` picks out the newest circle and `fsucc` shifts older ones.
-/

private noncomputable def bouquetNData : Nat → Σ A : Type u, A
  | 0 => ⟨HIT.PUnit'.{u}, HIT.PUnit'.unit⟩
  | Nat.succ n =>
      let prev := bouquetNData n
      ⟨Wedge prev.1 Circle.{u} prev.2 circleBase,
        Wedge.basepoint (A := prev.1) (B := Circle.{u}) (a₀ := prev.2) (b₀ := circleBase)⟩

/-- The bouquet of `n` circles as an iterated wedge. -/
noncomputable def BouquetN (n : Nat) : Type u :=
  (bouquetNData n).1

/-- The basepoint of the bouquet. -/
noncomputable def bouquetBase {n : Nat} : BouquetN n :=
  (bouquetNData n).2

/-- The `i`-th loop in the bouquet. -/
noncomputable def bouquetLoop : {n : Nat} → Fin'B n →
    Path (A := BouquetN n) (bouquetBase (n := n)) (bouquetBase (n := n))
  | 0, i => Fin'B.elim0 i
  | Nat.succ n, .fzero =>
      let prev := bouquetNData n
      let glue :=
        Wedge.glue (A := prev.1) (B := Circle.{u}) (a₀ := prev.2) (b₀ := circleBase)
      Path.trans glue (Path.trans (Pushout.inrPath (A := prev.1) (B := Circle.{u}) (C := HIT.PUnit') (f := fun _ => prev.2) (g := fun _ => circleBase) circleLoop) (Path.symm glue))
  | Nat.succ n, .fsucc i => Pushout.inlPath (A := (bouquetNData n).1) (B := Circle.{u}) (C := HIT.PUnit') (f := fun _ => (bouquetNData n).2) (g := fun _ => circleBase) (bouquetLoop (n := n) i)

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
    path_simp  -- refl · X ≈ X
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
    path_simp  -- refl · X ≈ X
  | succ m ih =>
    simp only [iterateLoopNeg, Nat.succ_add]
    apply rweq_trans (rweq_tt (Path.symm l) (iterateLoopNeg l m) (iterateLoopNeg l n))
    exact rweq_trans_congr_right (Path.symm l) ih

/-! ### Cross cancellation lemmas -/

/-- l · l⁻¹ ≈ refl -/
theorem loop_cancel {A : Type u} {a : A} (l : Path a a) :
    RwEq (Path.trans l (Path.symm l)) (Path.refl a) := by
  path_simp

/-- l⁻¹ · l ≈ refl -/
theorem loop_cancel' {A : Type u} {a : A} (l : Path a a) :
    RwEq (Path.trans (Path.symm l) l) (Path.refl a) := by
  path_simp

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
  path_simp

/-- (l⁻¹) · l^{n+1} ≈ l^n
    This is: l⁻¹ · (l · l^n) ≈ (l⁻¹ · l) · l^n ≈ refl · l^n ≈ l^n -/
theorem iterateLoopPos_cancel_one {A : Type u} {a : A} (l : Path a a) (n : Nat) :
    RwEq (Path.trans (Path.symm l) (iterateLoopPos l (n + 1)))
         (iterateLoopPos l n) := by
  simp only [iterateLoopPos]
  apply rweq_trans (rweq_symm (rweq_tt (Path.symm l) l (iterateLoopPos l n)))
  apply rweq_trans (rweq_trans_congr_left (iterateLoopPos l n) (loop_cancel' l))
  path_simp  -- refl · X ≈ X

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
    -- Base case: refl · refl ≈ refl - use path_simp automation
    simp only [iterateLoopPos, iterateLoopNeg]
    path_simp
  | succ m ih =>
    -- l^{m+1} · (l⁻¹)^{m+1}
    -- ≈ (l^{m+1} · l⁻¹) · (l⁻¹)^m  [by assoc⁻¹]
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
    path_simp  -- X · refl ≈ X
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
    -- Base case: refl · refl ≈ refl - use path_simp automation
    simp only [iterateLoopNeg, iterateLoopPos]
    path_simp
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
    path_simp  -- refl · X ≈ X
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

/-- The bouquet with zero circles is just a point, hence a subsingleton. -/
instance : Subsingleton (BouquetN.{u} 0) := by
  -- Unfold the definition: `BouquetN 0 = PUnit'`.
  unfold BouquetN
  simpa [bouquetNData] using (inferInstance : Subsingleton HIT.PUnit'.{u})

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
theorem bouquetPiOne_zero_subsingleton :
    Subsingleton (BouquetN.PiOneN.{u} 0) := by
  constructor
  intro x y
  have hx : x = PiOne.id (A := BouquetN 0) (a := bouquetBase (n := 0)) := by
    simpa [PiOne.id] using
      (pi1_trivial_of_subsingleton (A := BouquetN 0) (a := bouquetBase (n := 0)) x)
  have hy : y = PiOne.id (A := BouquetN 0) (a := bouquetBase (n := 0)) := by
    simpa [PiOne.id] using
      (pi1_trivial_of_subsingleton (A := BouquetN 0) (a := bouquetBase (n := 0)) y)
  exact hx.trans hy.symm

/-- For n = 0, every element of `π₁(BouquetN 0)` is equal to the identity. -/
theorem bouquetPiOne_zero_trivial (x : BouquetN.PiOneN.{u} 0) :
    x = PiOne.id (A := BouquetN 0) (a := bouquetBase) := by
  simpa [PiOne.id] using
    (pi1_trivial_of_subsingleton (A := BouquetN 0) (a := bouquetBase (n := 0)) x)

/-! ## Free Group Decomposition: F_n ≃ ℤ * ... * ℤ

The free group on n generators decomposes as an iterated free product:
- F₀ ≃ 1 (trivial)
- F₁ ≃ ℤ
- F_{n+1} ≃ ℤ * F_n

This establishes that F_n is isomorphic to the n-fold free product of ℤ.        
-/

/-! ### Part 1: F₁ ≃ ℤ -/

/-- Words in F₁: since there's only one generator (index fzero), every word
    is a sequence of powers of a single generator. -/
def bouquetWordOnePower : BouquetWord 1 → Int
  | .nil => 0
  | .cons l rest => l.power + bouquetWordOnePower rest

/-- The power function respects the free group relation. -/
theorem bouquetWordOnePower_respects_rel (w₁ w₂ : BouquetWord 1) (h : BouquetRel 1 w₁ w₂) :
    bouquetWordOnePower w₁ = bouquetWordOnePower w₂ := by
  induction h with
  | combine l₁ l₂ _hgen _hne rest =>
      simp only [bouquetWordOnePower]
      omega
  | cancel l₁ l₂ _hgen hinv rest =>
      simp only [bouquetWordOnePower]
      omega
  | congr l _h ih =>
      simp only [bouquetWordOnePower]
      omega

/-- Map from BouquetFreeGroup 1 to Int. -/
def freeGroupOneToInt : BouquetFreeGroup 1 → Int :=
  Quot.lift bouquetWordOnePower bouquetWordOnePower_respects_rel

/-- Map from Int to BouquetFreeGroup 1. -/
def intToFreeGroupOne (k : Int) : BouquetFreeGroup 1 :=
  if _h : k = 0 then BouquetFreeGroup.one
  else BouquetFreeGroup.genPow Fin'B.fzero k

/-- All generators in F₁ are the same (fzero). -/
theorem fin'B_one_eq_fzero (i : Fin'B 1) : i = Fin'B.fzero := by
  cases i with
  | fzero => rfl
  | fsucc j => exact Fin'B.elim0 j

/-- Encoding then decoding gives back the original integer. -/
theorem freeGroupOneToInt_intToFreeGroupOne (k : Int) :
    freeGroupOneToInt (intToFreeGroupOne k) = k := by
  unfold intToFreeGroupOne freeGroupOneToInt BouquetFreeGroup.one BouquetFreeGroup.genPow
  by_cases hk : k = 0
  · simp only [hk, ↓reduceDIte]
    rfl
  · simp only [hk, ↓reduceDIte]
    simp only [bouquetWordOnePower]
    omega

/-- In F₁, all letters have the same generator (fzero), so words reduce by combining powers.

This lemma requires showing that the combine and cancel rules of BouquetRel reduce
any word to the canonical form with total power. The proof is a straightforward
induction on word structure using the fact that all generators are fzero. -/
theorem bouquetWord_one_equiv_single (w : BouquetWord 1) :
    Quot.mk (BouquetRel 1) w = intToFreeGroupOne (bouquetWordOnePower w) := by
  classical
  have main :
      ∀ n : Nat,
        ∀ w : BouquetWord 1,
          w.length = n →
            Quot.mk (BouquetRel 1) w = intToFreeGroupOne (bouquetWordOnePower w) := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih w hwlen
    cases w with
    | nil =>
      simp [intToFreeGroupOne, BouquetFreeGroup.one, bouquetWordOnePower]
    | cons l w =>
      cases w with
      | nil =>
        cases l with
        | mk gen power power_ne_zero =>
          have hgen : gen = Fin'B.fzero := fin'B_one_eq_fzero gen
          cases hgen
          simp [intToFreeGroupOne, BouquetFreeGroup.genPow, bouquetWordOnePower, power_ne_zero]
      | cons l₂ rest =>
        have hl : l.gen = Fin'B.fzero := fin'B_one_eq_fzero l.gen
        have hl₂ : l₂.gen = Fin'B.fzero := fin'B_one_eq_fzero l₂.gen
        have hgen : l.gen = l₂.gen := hl.trans hl₂.symm
        have hn : n = 1 + (1 + rest.length) := by
          simpa [BouquetWord.length] using hwlen.symm
        by_cases hsum : l.power + l₂.power = 0
        · have hw :
              Quot.mk (BouquetRel 1) (.cons l (.cons l₂ rest)) =
                Quot.mk (BouquetRel 1) rest := by
            exact Quot.sound (BouquetRel.cancel l l₂ hgen hsum rest)
          have hlt : rest.length < n := by
            rw [hn]
            omega
          have hpow :
              bouquetWordOnePower (.cons l (.cons l₂ rest)) =
                bouquetWordOnePower rest := by
            calc
              l.power + (l₂.power + bouquetWordOnePower rest)
                  = (l.power + l₂.power) + bouquetWordOnePower rest := by omega
              _ = 0 + bouquetWordOnePower rest := by simp [hsum]
              _ = bouquetWordOnePower rest := by simp
          have ihRest :
              Quot.mk (BouquetRel 1) rest =
                intToFreeGroupOne (bouquetWordOnePower rest) :=
            ih rest.length hlt rest rfl
          simpa [hpow] using hw.trans ihRest
        · have hne : l.power + l₂.power ≠ 0 := hsum
          let l' : BouquetLetter 1 :=
            ⟨l.gen, l.power + l₂.power, hne⟩
          have hw :
              Quot.mk (BouquetRel 1) (.cons l (.cons l₂ rest)) =
                Quot.mk (BouquetRel 1) (.cons l' rest) := by
            exact Quot.sound (BouquetRel.combine l l₂ hgen hne rest)
          have hlt : (BouquetWord.cons l' rest).length < n := by
            rw [hn]
            simp [BouquetWord.length]
          have hpow :
              bouquetWordOnePower (.cons l (.cons l₂ rest)) =
                bouquetWordOnePower (.cons l' rest) := by
            simp [bouquetWordOnePower, l']
            omega
          have ihCombined :
              Quot.mk (BouquetRel 1) (.cons l' rest) =
                intToFreeGroupOne (bouquetWordOnePower (.cons l' rest)) :=
            ih (BouquetWord.cons l' rest).length hlt (.cons l' rest) rfl
          simpa [hpow] using hw.trans ihCombined
  exact main w.length w rfl

/-- F₁ ≃ ℤ (the free group on one generator is isomorphic to the integers). -/
noncomputable def freeGroupOneEquivInt : SimpleEquiv (BouquetFreeGroup 1) Int where
  toFun := freeGroupOneToInt
  invFun := intToFreeGroupOne
  left_inv := by
    intro x
    refine Quot.inductionOn x ?_
    intro w
    simp only [freeGroupOneToInt]
    exact (bouquetWord_one_equiv_single w).symm
  right_inv := freeGroupOneToInt_intToFreeGroupOne

/-! ### Part 2: Iterated Free Product -/

/-- The n-fold free product of a type with itself.
    IteratedFreeProduct G 0 ≃ Unit (trivial)
    IteratedFreeProduct G 1 ≃ G
    IteratedFreeProduct G 2 ≃ G * G
    IteratedFreeProduct G (n+1) ≃ G * IteratedFreeProduct G n -/
def IteratedFreeProduct (G : Type u) : Nat → Type u
  | 0 => PUnit
  | 1 => G
  | n + 2 => FreeProductWord G (IteratedFreeProduct G (n + 1))

/-- The n-fold free product of ℤ. -/
abbrev IntFreeProductN (n : Nat) : Type := IteratedFreeProduct Int n

/-! ### Part 3: F_{n+1} ≃ ℤ * F_n (Decomposition) -/

/-- Convert a BouquetLetter (n+1) to either an Int (if generator 0) or a BouquetLetter n. -/
inductive DecomposedLetter (n : Nat) where
  | first (power : Int) (hne : power ≠ 0) : DecomposedLetter n
  | rest (l : BouquetLetter n) : DecomposedLetter n

/-- Decompose a Fin'B (n+1) index into either fzero or a shifted index. -/
def decomposeIndex : {n : Nat} → Fin'B (n + 1) → Option (Fin'B n)
  | 0, Fin'B.fzero => none
  | n + 1, Fin'B.fzero => none
  | n + 1, Fin'B.fsucc i => some i

/-- Check if an index is fzero. -/
def isFirstGenerator : {n : Nat} → Fin'B (n + 1) → Bool
  | _, Fin'B.fzero => true
  | _, Fin'B.fsucc _ => false

/-- Project a letter to the first generator or the rest. -/
def projectLetter {n : Nat} (l : BouquetLetter (n + 1)) : DecomposedLetter n :=
  match l.gen with
  | Fin'B.fzero => DecomposedLetter.first l.power l.power_ne_zero
  | Fin'B.fsucc i => DecomposedLetter.rest ⟨i, l.power, l.power_ne_zero⟩

/-- A word in F_{n+1} decomposes into a word alternating between ℤ and F_n. -/
inductive DecomposedWord (n : Nat) where
  | nil : DecomposedWord n
  | consFirst (power : Int) (hne : power ≠ 0) (rest : DecomposedWord n) : DecomposedWord n
  | consRest (w : BouquetWord n) (hw : w ≠ BouquetWord.nil) (rest : DecomposedWord n) : DecomposedWord n

/-! ### Part 4: Decomposition (not yet formalized)

The expected equivalence F_n ≃ ℤ * ... * ℤ (n copies) is standard but not
formalized here. We keep the iterated free-product definitions for future work.
-/

/-! ## Summary

This module establishes:

1. **BouquetN Definition**: Iterated wedge of circles (`BouquetN (n+1) := BouquetN n ∨ S¹`)

2. **BouquetFreeGroup Definition**: Free group on n generators as quotient of words

3. **Decode Map** (`BouquetN.decode_def`): candidate map from free group words
   to π₁(∨ⁿS¹) that respects the quotient relation.

4. **Special Cases**:
   - n = 0: π₁ = 1 (trivial, via `bouquetPiOne_zero_trivial`)
   - n = 1: F₁ = ℤ (via `freeGroupOneEquivInt`)
   - n = 2: F₂ is the free group on two generators (figure-eight expected)

## Placeholders

**Circle HIT axioms:** `BouquetN` is built from wedges of `Circle`, so the circle
constructors/recursors from `Circle.lean` remain assumptions.

**Equivalences not yet formalized:** the equivalence `π₁(BouquetN n) ≃
BouquetFreeGroup n` and the n-fold free-product decomposition are not yet
formalized.

## Proved Theorems (previously axioms)

**Special Cases (2):**
- `bouquetPiOne_zero_trivial`: π₁(BouquetN 0) is trivial
- `bouquetWordOnePower_respects_rel`: Power function respects free group relation

**Loop Iteration (3):**
- `iterateLoopInt_zero`: l^0 = refl (definition/unfolding)
- `iterateLoopInt_add`: l^m · l^n ≈ l^{m+n} (via case analysis on signs)
- `iterateLoopInt_cancel`: l^m · l^{-m} ≈ refl (via iterateLoopInt_add)

**Decode (1):**
- `decodeWord_respects_rel`: Decode respects the free group relation (via iterateLoopInt lemmas)

**Free Group Equivalences (1):**
- `freeGroupOneToInt_intToFreeGroupOne`: F₁ → ℤ → F₁ round-trip
-/

end Path
end ComputationalPaths
