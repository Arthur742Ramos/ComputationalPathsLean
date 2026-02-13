/-
# Nielsen-Schreier Derived Results

This module extends the Nielsen-Schreier base case with derived path witnesses
for the free group on one generator. We develop additional coherence lemmas,
rank-formula consequences, and structural results for F₁ and its relationship
to the integers.

## Key Results

- Path witnesses for rank formula identities
- Composition coherence for the F₁ ↔ ℤ equivalence
- Power-law coherence paths
- Inverse-law path witnesses
- Transport along the equivalence

## References

- Nielsen, "Om Regning med ikke-kommutative Faktorer"
- Schreier, "Die Untergruppen der freien Gruppen"
- de Queiroz et al., SAJL 2016
-/

import ComputationalPaths.Path.Algebra.NielsenSchreier
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace NielsenSchreierDerived

open CompPath

noncomputable section

/-! ## Rank formula derived identities -/

/-- The rank formula for n = 1 always simplifies: 1 + k * 0 = 1. -/
def rankFormula_always_one (k : Nat) :
    Path (1 + k * (1 - 1)) 1 :=
  Path.ofEq (by omega)

/-- Coherence: the rank formula path composed with the simplification path. -/
def rankFormula_coherence (k : Nat) :
    Path (freeGroupRank 1) 1 :=
  Path.trans (freeGroup_rank_formula_one_path k) (rankFormula_always_one k)

/-- The rank is definitionally 1. -/
def freeGroupOne_rank_is_one :
    Path (freeGroupRank 1) 1 :=
  Path.ofEqChain rfl

/-- The rank formula coherence composes with rank-is-one. -/
theorem rankFormula_coherence_eq (k : Nat) :
    (rankFormula_coherence k).toEq = freeGroupOne_rank_is_one.toEq := rfl

/-! ## Equivalence coherence paths -/

/-- Round-trip coherence: going ℤ → F₁ → ℤ is the identity, as a path. -/
def int_roundtrip_path (k : Int) :
    Path (freeGroupOneToInt (intToFreeGroupOne k)) k :=
  freeGroupOneToInt_intToFreeGroupOne_path k

/-- Round-trip for zero. -/
def int_roundtrip_zero :
    Path (freeGroupOneToInt (intToFreeGroupOne 0)) 0 :=
  int_roundtrip_path 0

/-- Round-trip for one. -/
def int_roundtrip_one :
    Path (freeGroupOneToInt (intToFreeGroupOne 1)) 1 :=
  int_roundtrip_path 1

/-- Round-trip for negative one. -/
def int_roundtrip_neg_one :
    Path (freeGroupOneToInt (intToFreeGroupOne (-1))) (-1) :=
  int_roundtrip_path (-1)

/-- Round-trip for an arbitrary natural number. -/
def int_roundtrip_ofNat (n : Nat) :
    Path (freeGroupOneToInt (intToFreeGroupOne (Int.ofNat n))) (Int.ofNat n) :=
  int_roundtrip_path (Int.ofNat n)

/-! ## Multiplication coherence -/

/-- Multiplication in F₁ commutes with the ℤ encoding, path version. -/
def mul_encoding_path (x y : BouquetFreeGroup 1) :
    Path (freeGroupOneToInt (BouquetFreeGroup.mul x y))
      (freeGroupOneToInt x + freeGroupOneToInt y) :=
  freeGroupOneToInt_mul_path x y

/-- Multiplication by the identity element on the left, path version. -/
def mul_one_left_path (x : BouquetFreeGroup 1) :
    Path (BouquetFreeGroup.mul (BouquetFreeGroup.one (n := 1)) x) x :=
  Path.ofEq (BouquetFreeGroup.one_mul (n := 1) x)

/-- Multiplication by the identity element on the right, path version. -/
def mul_one_right_path (x : BouquetFreeGroup 1) :
    Path (BouquetFreeGroup.mul x (BouquetFreeGroup.one (n := 1))) x :=
  Path.ofEq (BouquetFreeGroup.mul_one (n := 1) x)

/-! ## Power law coherence -/

/-- Power of zero is the identity element. -/
def pow_zero_path (x : BouquetFreeGroup 1) :
    Path (BouquetFreeGroup.pow (n := 1) x 0) (BouquetFreeGroup.one (n := 1)) :=
  Path.ofEq (BouquetFreeGroup.pow_zero (n := 1) x)

/-- Power of one is the element itself. -/
def pow_one_path (x : BouquetFreeGroup 1) :
    Path (BouquetFreeGroup.pow (n := 1) x 1) x :=
  Path.ofEq (BouquetFreeGroup.pow_one (n := 1) x)

/-- The encoding of a power is a multiple of the encoding. -/
def pow_encoding_path (x : BouquetFreeGroup 1) (k : Nat) :
    Path (freeGroupOneToInt (BouquetFreeGroup.pow (n := 1) x k))
      ((Int.ofNat k) * freeGroupOneToInt x) :=
  freeGroupOneToInt_pow_path x k

/-- Successor power law: pow x (k+1) = mul (pow x k) x. -/
def pow_succ_path (x : BouquetFreeGroup 1) (k : Nat) :
    Path (BouquetFreeGroup.pow (n := 1) x (k + 1))
      (BouquetFreeGroup.mul (BouquetFreeGroup.pow (n := 1) x k) x) :=
  Path.ofEq (BouquetFreeGroup.pow_succ (n := 1) x k)

/-- Power distributes over addition of exponents. -/
def pow_add_path (x : BouquetFreeGroup 1) (m k : Nat) :
    Path (BouquetFreeGroup.pow (n := 1) x (m + k))
      (BouquetFreeGroup.mul (BouquetFreeGroup.pow (n := 1) x m)
                            (BouquetFreeGroup.pow (n := 1) x k)) :=
  Path.ofEq (BouquetFreeGroup.pow_add (n := 1) x m k)

/-! ## Associativity witnesses -/

/-- Associativity of multiplication in F₁, path-valued. -/
def mul_assoc_path (x y z : BouquetFreeGroup 1) :
    Path (BouquetFreeGroup.mul (BouquetFreeGroup.mul x y) z)
      (BouquetFreeGroup.mul x (BouquetFreeGroup.mul y z)) :=
  Path.ofEq (BouquetFreeGroup.mul_assoc x y z)

/-- Inversion is involutive, path version. -/
def inv_inv_path (x : BouquetFreeGroup 1) :
    Path (BouquetFreeGroup.inv (BouquetFreeGroup.inv x)) x :=
  Path.ofEq (BouquetFreeGroup.inv_inv x)

/-- Inversion of the identity is the identity, path version. -/
def inv_one_path :
    Path (BouquetFreeGroup.inv (BouquetFreeGroup.one (n := 1)))
      (BouquetFreeGroup.one (n := 1)) :=
  Path.ofEq (BouquetFreeGroup.inv_one (n := 1))

/-- Inversion reverses multiplication, path version. -/
def inv_mul_path (x y : BouquetFreeGroup 1) :
    Path (BouquetFreeGroup.inv (BouquetFreeGroup.mul x y))
      (BouquetFreeGroup.mul (BouquetFreeGroup.inv y) (BouquetFreeGroup.inv x)) :=
  Path.ofEq (BouquetFreeGroup.inv_mul x y)

/-! ## Encoding naturality -/

/-- The equivalence is natural with respect to addition:
    encode(decode(m) * decode(n)) = m + n. -/
def equiv_natural_add (m n : Int) :
    Path (freeGroupOneToInt
            (BouquetFreeGroup.mul (intToFreeGroupOne m) (intToFreeGroupOne n)))
      (m + n) :=
  Path.trans
    (mul_encoding_path (intToFreeGroupOne m) (intToFreeGroupOne n))
    (Path.ofEq (by
      congr 1
      · exact (int_roundtrip_path m).toEq
      · exact (int_roundtrip_path n).toEq))

/-- Encoding of the identity via intToFreeGroupOne is zero. -/
def encoding_identity_via_roundtrip :
    Path (freeGroupOneToInt (intToFreeGroupOne 0)) 0 :=
  int_roundtrip_path 0

/-! ## Transport along the equivalence -/

/-- Transport a predicate on ℤ to a predicate on F₁ via the equivalence. -/
def transport_predicate_to_F1 (P : Int → Type) (k : Int) (px : P k) :
    P (freeGroupOneToInt (intToFreeGroupOne k)) :=
  Path.transport (Path.symm (int_roundtrip_path k)) px

/-- Transport a predicate on F₁ to a predicate on ℤ. -/
def transport_predicate_to_Int (P : BouquetFreeGroup 1 → Type)
    (x : BouquetFreeGroup 1) (px : P x) :
    P (intToFreeGroupOne (freeGroupOneToInt x)) :=
  Path.transport (Path.symm (intToFreeGroupOne_freeGroupOneToInt_path x)) px

/-- The two transports (forward then backward) cancel. -/
theorem transport_roundtrip_cancel (P : Int → Type) (k : Int)
    (px : P k) :
    Path.transport (int_roundtrip_path k)
      (transport_predicate_to_F1 P k px) = px := by
  simp only [transport_predicate_to_F1]
  exact Path.transport_symm_right (int_roundtrip_path k) px

/-! ## Coherence of generator power form -/

/-- Generator power path for k = 0. -/
def genPow_zero_path :
    Path (intToFreeGroupOne 0) (BouquetFreeGroup.genPow Fin'B.fzero 0) :=
  intToFreeGroupOne_eq_genPow_path 0

/-- Generator power path for k = 1. -/
def genPow_one_path :
    Path (intToFreeGroupOne 1) (BouquetFreeGroup.genPow Fin'B.fzero 1) :=
  intToFreeGroupOne_eq_genPow_path 1

/-- Generator power path for k = -1. -/
def genPow_neg_one_path :
    Path (intToFreeGroupOne (-1)) (BouquetFreeGroup.genPow Fin'B.fzero (-1)) :=
  intToFreeGroupOne_eq_genPow_path (-1)

/-- The generator power form is compatible with the round-trip. -/
def genPow_roundtrip (k : Int) :
    Path (BouquetFreeGroup.genPow Fin'B.fzero k)
      (intToFreeGroupOne k) :=
  Path.symm (intToFreeGroupOne_eq_genPow_path k)

end

/-! ## Summary

We have developed derived results for the Nielsen-Schreier base case:

1. **Rank formula identities**: the rank formula 1 + k(n-1) simplifies for n = 1
2. **Equivalence coherence**: round-trip paths for the F₁ ↔ ℤ equivalence
3. **Multiplication coherence**: encoding commutes with multiplication
4. **Power law coherence**: encoding commutes with powers, succ/add laws
5. **Associativity / inverse witnesses**: path-valued group laws for F₁
6. **Transport**: moving predicates across the equivalence
7. **Generator power form**: coherence for intToFreeGroupOne ↔ genPow
-/

end NielsenSchreierDerived
end Algebra
end Path
end ComputationalPaths
