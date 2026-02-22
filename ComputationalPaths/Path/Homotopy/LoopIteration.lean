/-
# Loop Iteration and Integer Powers

This module provides reusable infrastructure for iterating loops (paths from a point
to itself) and proving properties about integer powers of loops. This is useful for
fundamental group calculations where elements are represented as integer powers of
generator loops.

## Key Definitions

- `loopIter l n` - Natural number iteration: l^{n+1} (1-indexed for convenience)
- `loopIterZ l z` - Integer iteration: l^z

## Key Theorems

- `loopIter_add` - l^{m+1} · l^{n+1} ≈ l^{m+n+1} · l
- `loopIter_cancel_eq'` - l^{m+1} · (l^{-1})^{m+1} ≈ refl
- `loopIter_cancel_gt` - Cancellation when positive power > negative power
- `loopIter_cancel_lt` - Cancellation when positive power < negative power

## Usage

Import this module when working with π₁ calculations that involve integer powers
of generator loops, such as Circle and Torus.

## References

- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.PathTactic

namespace ComputationalPaths
namespace Path

universe u

/-! ## Basic Loop Cancellation -/

/-- Cancellation: l · l⁻¹ ≈ refl -/
noncomputable def loop_cancel_right {A : Type u} {a : A} (l : Path a a) :
    RwEq (Path.trans l (Path.symm l)) (Path.refl a) :=
  rweq_cmpA_inv_right (p := l)

/-- Cancellation: l⁻¹ · l ≈ refl -/
noncomputable def loop_cancel_left {A : Type u} {a : A} (l : Path a a) :
    RwEq (Path.trans (Path.symm l) l) (Path.refl a) :=
  rweq_cmpA_inv_left (p := l)

/-! ## Natural Number Iteration -/

/-- Natural number iteration of a loop (1-indexed for convenience).
    `loopIter l 0 = l` (i.e., l^1)
    `loopIter l n = l^{n+1}` -/
@[reducible] noncomputable def loopIter {A : Type u} {a : A} (l : Path a a) : Nat → Path a a :=
  fun n => Nat.recOn n l (fun _ acc => Path.trans acc l)

@[simp] theorem loopIter_zero {A : Type u} {a : A} (l : Path a a) :
    loopIter l 0 = l := rfl

@[simp] theorem loopIter_succ {A : Type u} {a : A} (l : Path a a) (n : Nat) :
    loopIter l (Nat.succ n) = Path.trans (loopIter l n) l := rfl

/-- Alternative characterization: loopIter l (n+1) = l · loopIter l n -/
noncomputable def loopIter_succ' {A : Type u} {a : A} (l : Path a a) (n : Nat) :
    RwEq (loopIter l (n + 1)) (Path.trans l (loopIter l n)) := by
  induction n with
  | zero => exact RwEq.refl _
  | succ n ih =>
    -- loopIter l (n+2) = trans (loopIter l (n+1)) l
    -- ≈ trans (trans l (loopIter l n)) l  [by ih on left]
    -- ≈ trans l (trans (loopIter l n) l)  [by tt]
    -- = trans l (loopIter l (n+1))
    apply rweq_trans (rweq_trans_congr_left l ih)
    exact rweq_tt l (loopIter l n) l

/-! ## Addition Law for Iteration -/

/-- Addition law: loopIter l m · loopIter l n ≈ loopIter l (m+n) · l
    This represents l^{m+1} · l^{n+1} = l^{m+n+2} -/
noncomputable def loopIter_add {A : Type u} {a : A} (l : Path a a) (m n : Nat) :
    RwEq (Path.trans (loopIter l m) (loopIter l n))
         (Path.trans (loopIter l (m + n)) l) := by
  induction n with
  | zero =>
    simp only [loopIter, Nat.add_zero]
    exact RwEq.refl _
  | succ n ih =>
    simp only [loopIter, Nat.add_succ]
    apply rweq_trans (rweq_symm (rweq_tt (loopIter l m) (loopIter l n) l))
    exact rweq_trans_congr_left l ih

/-- Corollary: loopIter l m · loopIter l n ≈ loopIter l (m+n+1) when we want l^{m+n+2} -/
noncomputable def loopIter_add' {A : Type u} {a : A} (l : Path a a) (m n : Nat) :
    RwEq (Path.trans (loopIter l m) (loopIter l n))
         (loopIter l (m + n + 1)) := by
  exact loopIter_add l m n

/-! ## Cancellation Lemmas -/

/-- Helper: l · (l^{-1})^{n+2} ≈ (l^{-1})^{n+1}
    One cancellation on the left of inverse iterations. -/
noncomputable def loopIter_symm_cancel_l {A : Type u} {a : A} (l : Path a a) (n : Nat) :
    RwEq (Path.trans l (loopIter (Path.symm l) (n + 1)))
         (loopIter (Path.symm l) n) := by
  induction n with
  | zero =>
    -- trans l (loopIter (symm l) 1) = trans l (trans (symm l) (symm l))
    -- ≈ trans (trans l (symm l)) (symm l) ≈ trans refl (symm l) ≈ symm l
    apply rweq_trans (rweq_symm (rweq_tt l (Path.symm l) (Path.symm l)))
    apply rweq_trans (rweq_trans_congr_left (Path.symm l) (loop_cancel_right l))
    exact rweq_cmpA_refl_left (p := Path.symm l)
  | succ n ih =>
    -- trans l (loopIter (symm l) (n+2))
    -- = trans l (trans (loopIter (symm l) (n+1)) (symm l))
    -- ≈ trans (trans l (loopIter (symm l) (n+1))) (symm l)
    -- ≈ trans (loopIter (symm l) n) (symm l)  [by ih]
    -- = loopIter (symm l) (n+1)
    apply rweq_trans (rweq_symm (rweq_tt l (loopIter (Path.symm l) (n + 1)) (Path.symm l)))
    exact rweq_trans_congr_left (Path.symm l) ih

/-- Symmetric helper: (l)^{n+2} · l^{-1} ≈ l^{n+1}
    One cancellation on the right. -/
noncomputable def loopIter_cancel_r {A : Type u} {a : A} (l : Path a a) (n : Nat) :
    RwEq (Path.trans (loopIter l (n + 1)) (Path.symm l))
         (loopIter l n) := by
  -- loopIter l (n+1) = trans (loopIter l n) l
  -- trans (trans (loopIter l n) l) (symm l)
  -- ≈ trans (loopIter l n) (trans l (symm l))  [by tt]
  -- ≈ trans (loopIter l n) refl  [by cancel]
  -- ≈ loopIter l n  [by refl_right]
  apply rweq_trans (rweq_tt (loopIter l n) l (Path.symm l))
  apply rweq_trans (rweq_trans_congr_right (loopIter l n) (loop_cancel_right l))
  exact rweq_cmpA_refl_right (p := loopIter l n)

/-- Helper: l^{-1} · l^{n+2} ≈ l^{n+1}
    One cancellation on the left. -/
noncomputable def loopIter_cancel_l {A : Type u} {a : A} (l : Path a a) (n : Nat) :
    RwEq (Path.trans (Path.symm l) (loopIter l (n + 1)))
         (loopIter l n) := by
  -- Use loopIter_succ' to get: loopIter l (n+1) ≈ trans l (loopIter l n)
  apply rweq_trans (rweq_trans_congr_right (Path.symm l) (loopIter_succ' l n))
  -- trans (symm l) (trans l (loopIter l n))
  -- ≈ trans (trans (symm l) l) (loopIter l n)
  apply rweq_trans (rweq_symm (rweq_tt (Path.symm l) l (loopIter l n)))
  -- ≈ trans refl (loopIter l n)
  apply rweq_trans (rweq_trans_congr_left (loopIter l n) (loop_cancel_left l))
  exact rweq_cmpA_refl_left (p := loopIter l n)

/-- Equal powers cancel: l^{m+1} · (l^{-1})^{m+1} ≈ refl -/
noncomputable def loopIter_cancel_eq' {A : Type u} {a : A} (l : Path a a) (m : Nat) :
    RwEq (Path.trans (loopIter l m) (loopIter (Path.symm l) m)) (Path.refl a) := by
  induction m with
  | zero => exact loop_cancel_right l
  | succ m ih =>
    -- trans (loopIter l (m+1)) (loopIter (symm l) (m+1))
    -- = trans (trans (loopIter l m) l) (loopIter (symm l) (m+1))
    -- ≈ trans (loopIter l m) (trans l (loopIter (symm l) (m+1)))  [by tt]
    -- ≈ trans (loopIter l m) (loopIter (symm l) m)  [by loopIter_symm_cancel_l]
    -- ≈ refl  [by ih]
    apply rweq_trans (rweq_tt (loopIter l m) l (loopIter (Path.symm l) (m + 1)))
    apply rweq_trans (rweq_trans_congr_right (loopIter l m) (loopIter_symm_cancel_l l m))
    exact ih

/-- Cancellation when m > n: l^{m+1} · (l^{-1})^{n+1} ≈ l^{m-n}
    More precisely: loopIter l m · loopIter (symm l) n ≈ loopIter l (m - n - 1) -/
noncomputable def loopIter_cancel_gt {A : Type u} {a : A} (l : Path a a) (m n : Nat) (h : m > n) :
    RwEq (Path.trans (loopIter l m) (loopIter (Path.symm l) n))
         (loopIter l (m - n - 1)) := by
  induction n generalizing m with
  | zero =>
    -- m > 0, so m = m' + 1 for some m'
    match m, h with
    | Nat.succ m', _ =>
      simpa [Nat.succ_sub_one] using (loopIter_cancel_r l m')
  | succ n ih =>
    -- m > n + 1, so m > n
    have h' : m > n := Nat.lt_of_succ_lt h
    apply rweq_trans (rweq_symm (rweq_tt (loopIter l m) (loopIter (Path.symm l) n) (Path.symm l)))
    apply rweq_trans (rweq_trans_congr_left (Path.symm l) (ih m h'))
    match m - n - 1, Nat.sub_pos_of_lt (by omega : n + 1 < m) with
    | Nat.succ k, _ =>
      simpa [Nat.succ_sub_one] using (loopIter_cancel_r l k)

/-- Cancellation when m < n: l^{m+1} · (l^{-1})^{n+1} ≈ (l^{-1})^{n-m}
    More precisely: loopIter l m · loopIter (symm l) n ≈ loopIter (symm l) (n - m - 1) -/
noncomputable def loopIter_cancel_lt {A : Type u} {a : A} (l : Path a a) (m n : Nat) (h : m < n) :
    RwEq (Path.trans (loopIter l m) (loopIter (Path.symm l) n))
         (loopIter (Path.symm l) (n - m - 1)) := by
  induction m generalizing n with
  | zero =>
    match n, h with
    | Nat.succ n', _ =>
      simpa [Nat.succ_sub_one] using (loopIter_symm_cancel_l l n')
  | succ m ih =>
    have h' : m < n := Nat.lt_of_succ_lt h
    match n, h with
    | Nat.succ n', hn =>
      apply rweq_trans (rweq_tt (loopIter l m) l (loopIter (Path.symm l) (n' + 1)))
      apply rweq_trans (rweq_trans_congr_right (loopIter l m) (loopIter_symm_cancel_l l n'))
      have h'' : m < n' := by omega
      have goal_eq : n' + 1 - (m + 1) - 1 = n' - m - 1 := by omega
      rw [goal_eq]
      exact ih n' h''

/-! ## Symmetry Iteration -/

/-- The symm-symm identity lifts to iterations:
    loopIter l k ≈ loopIter (symm (symm l)) k -/
noncomputable def loopIter_symm_symm {A : Type u} {a : A} (l : Path a a) (k : Nat) :
    RwEq (loopIter l k) (loopIter (Path.symm (Path.symm l)) k) := by
  induction k with
  | zero => exact rweq_symm (rweq_ss l)
  | succ k ih =>
    -- loopIter l (k+1) = trans (loopIter l k) l
    -- ≈ trans (loopIter (symm (symm l)) k) l  [by ih]
    -- ≈ trans (loopIter (symm (symm l)) k) (symm (symm l))  [by ss on right]
    -- = loopIter (symm (symm l)) (k+1)
    exact rweq_trans_congr ih (rweq_symm (rweq_ss l))

/-! ## Integer Powers (Optional Extension) -/

/-- Integer iteration of a loop. For z ≥ 0, this is l^z. For z < 0, this is (l^{-1})^{|z|}.
    Note: loopIterZ l 0 = refl, loopIterZ l 1 = l, loopIterZ l (-1) = symm l -/
noncomputable def loopIterZ {A : Type u} {a : A} (l : Path a a) : Int → Path a a
  | Int.ofNat 0 => Path.refl a
  | Int.ofNat (Nat.succ n) => loopIter l n
  | Int.negSucc n => loopIter (Path.symm l) n

@[simp] theorem loopIterZ_zero {A : Type u} {a : A} (l : Path a a) :
    loopIterZ l 0 = Path.refl a := rfl

@[simp] theorem loopIterZ_one {A : Type u} {a : A} (l : Path a a) :
    loopIterZ l 1 = l := rfl

@[simp] theorem loopIterZ_neg_one {A : Type u} {a : A} (l : Path a a) :
    loopIterZ l (-1) = Path.symm l := rfl

@[simp] theorem loopIterZ_pos {A : Type u} {a : A} (l : Path a a) (n : Nat) :
    loopIterZ l (Int.ofNat (n + 1)) = loopIter l n := rfl

@[simp] theorem loopIterZ_neg {A : Type u} {a : A} (l : Path a a) (n : Nat) :
    loopIterZ l (Int.negSucc n) = loopIter (Path.symm l) n := rfl

/-! ## Summary

This module provides a reusable framework for reasoning about integer powers of loops:

1. **Basic definitions**: `loopIter`, `loopIterZ`
2. **Addition law**: `loopIter_add` - composing iterations
3. **Cancellation lemmas**: Handle all cases of l^m · l^{-n}
4. **Symmetry**: `loopIter_symm_symm` for converting between l and symm(symm l)

These are essential for proving properties about loop normal forms in π₁
calculations.
-/

end Path
end ComputationalPaths
