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
