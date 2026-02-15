/-
# Nielsen-Schreier Base Case (Path Witnesses)

This module records Path-typed witnesses for the Nielsen-Schreier base case
for the free group on one generator, reusing the computations from BouquetN
and FreeGroupProperties.

## Key Results
- `freeGroup_rank_formula_one_path`: Path witness of the rank formula base case.
- `intToFreeGroupOne_eq_genPow_path`: Path witness for the generator power form.
- `freeGroupOneToInt_mul_path`: Path witness for multiplication in F1.
- `freeGroupOneToInt_pow_path`: Path witness for powers in F1.
- `freeGroupOneToInt_intToFreeGroupOne_path`: Path witness of the Int round-trip.
- `intToFreeGroupOne_freeGroupOneToInt_path`: Path witness of the F1 round-trip.

## References
- Nielsen-Schreier theorem (base case)
- de Queiroz et al., SAJL 2016
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.FreeGroupProperties

namespace ComputationalPaths
namespace Path
namespace Algebra

open CompPath

noncomputable section

/-! ## Nielsen-Schreier base case: Path witnesses -/

/-- Path witness for the Nielsen-Schreier rank formula base case. -/
def freeGroup_rank_formula_one_path (k : Nat) :
    Path (freeGroupRank 1) (1 + k * (1 - 1)) :=
  freeGroup_rank_formula_one k

/-- Path witness for the generator power form in F1. -/
def intToFreeGroupOne_eq_genPow_path (k : Int) :
    Path (intToFreeGroupOne k) (BouquetFreeGroup.genPow Fin'B.fzero k) :=
  intToFreeGroupOne_eq_genPow k

/-- Path witness for multiplication in F1 under the Int encoding. -/
def freeGroupOneToInt_mul_path (x y : BouquetFreeGroup 1) :
    Path (freeGroupOneToInt (BouquetFreeGroup.mul x y))
      (freeGroupOneToInt x + freeGroupOneToInt y) :=
  Path.stepChain (freeGroupOneToInt_mul x y)

/-- Path witness for powers in F1 under the Int encoding. -/
def freeGroupOneToInt_pow_path (x : BouquetFreeGroup 1) (k : Nat) :
    Path (freeGroupOneToInt (BouquetFreeGroup.pow (n := 1) x k))
      ((Int.ofNat k) * freeGroupOneToInt x) :=
  Path.stepChain (freeGroupOneToInt_pow x k)

/-- Path witness of the Int -> F1 -> Int round-trip. -/
def freeGroupOneToInt_intToFreeGroupOne_path (k : Int) :
    Path (freeGroupOneToInt (intToFreeGroupOne k)) k :=
  Path.stepChain (freeGroupOneToInt_intToFreeGroupOne k)

/-- Path witness of the F1 -> Int -> F1 round-trip. -/
def intToFreeGroupOne_freeGroupOneToInt_path (x : BouquetFreeGroup 1) :
    Path (intToFreeGroupOne (freeGroupOneToInt x)) x := by
  refine Path.stepChain ?_
  refine Quot.inductionOn x ?_
  intro w
  simp [freeGroupOneToInt]
  exact (bouquetWord_one_equiv_single w).symm


theorem freeGroup_rank_formula_one_path_toEq (k : Nat) :
    (freeGroup_rank_formula_one_path k).toEq = (freeGroup_rank_formula_one k).toEq := by
  simp [Path.toEq]


theorem intToFreeGroupOne_eq_genPow_path_toEq (k : Int) :
    (intToFreeGroupOne_eq_genPow_path k).toEq = (intToFreeGroupOne_eq_genPow k).toEq := by
  simp [Path.toEq]

theorem freeGroupOneToInt_mul_path_toEq (x y : BouquetFreeGroup 1) :
    (freeGroupOneToInt_mul_path x y).toEq = freeGroupOneToInt_mul x y := by
  simp [Path.toEq]

theorem freeGroupOneToInt_pow_path_toEq (x : BouquetFreeGroup 1) (k : Nat) :
    (freeGroupOneToInt_pow_path x k).toEq = freeGroupOneToInt_pow x k := by
  simp [Path.toEq]

theorem freeGroupOneToInt_intToFreeGroupOne_path_toEq (k : Int) :
    (freeGroupOneToInt_intToFreeGroupOne_path k).toEq = freeGroupOneToInt_intToFreeGroupOne k := by
  simp [Path.toEq]

theorem intToFreeGroupOne_freeGroupOneToInt_path_refl_right (x : BouquetFreeGroup 1) :
    Path.trans (intToFreeGroupOne_freeGroupOneToInt_path x) (Path.refl x) =
      intToFreeGroupOne_freeGroupOneToInt_path x :=
  Path.trans_refl_right _

theorem freeGroupOneToInt_intToFreeGroupOne_path_refl_right (k : Int) :
    Path.trans (freeGroupOneToInt_intToFreeGroupOne_path k) (Path.refl k) =
      freeGroupOneToInt_intToFreeGroupOne_path k :=
  Path.trans_refl_right _



theorem freeGroupOneToInt_mul_path_functorial_id (x y : BouquetFreeGroup 1) :
    Path.congrArg (fun z : Int => z) (freeGroupOneToInt_mul_path x y) =
      freeGroupOneToInt_mul_path x y := by
  simp [Path.congrArg]


theorem freeGroupOneToInt_mul_path_assoc_refl (x y : BouquetFreeGroup 1) :
    Path.trans
      (Path.trans (freeGroupOneToInt_mul_path x y)
        (Path.refl (freeGroupOneToInt x + freeGroupOneToInt y)))
      (Path.refl (freeGroupOneToInt x + freeGroupOneToInt y)) =
      Path.trans
        (freeGroupOneToInt_mul_path x y)
        (Path.trans
          (Path.refl (freeGroupOneToInt x + freeGroupOneToInt y))
          (Path.refl (freeGroupOneToInt x + freeGroupOneToInt y))) :=
  Path.trans_assoc _ _ _

end

/-! ## Summary -/

/-
We provide Path-typed witnesses for the base-case Nielsen-Schreier equalities:
rank formula, generator power normalization, multiplicativity, power law, and
the two round-trip equalities between F1 and Int.
-/

end Algebra
end Path
end ComputationalPaths
