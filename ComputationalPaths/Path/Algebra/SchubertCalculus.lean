/-!
# Schubert Calculus via Computational Paths

This module provides a computational-path oriented scaffold for Schubert
calculus: Schubert varieties/classes, Littlewood-Richardson and Pieri
combinatorics, double Schubert polynomials, K-theory of flag varieties,
and Peterson-Lam-Shimozono style affine positivity data.
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace SchubertCalculus

universe u

/-- A Schubert variety in a flag variety of rank `n`. -/
structure SchubertVariety (n : Nat) where
  index : Fin (n + 1)
  codim : Nat
  codim_le : codim ≤ n

/-- A Schubert cohomology class. -/
structure SchubertClass (n : Nat) where
  variety : SchubertVariety n
  degree : Nat
  degree_le : degree ≤ n

/-- Littlewood-Richardson data for multiplying Schubert classes. -/
structure LittlewoodRichardsonData (n : Nat) where
  left : SchubertClass n
  right : SchubertClass n
  output : SchubertClass n
  coeff : Nat

/-- Pieri data for multiplication by a special Schubert class. -/
structure PieriData (n : Nat) where
  source : SchubertClass n
  specialIndex : Nat
  target : SchubertClass n
  coefficient : Nat

/-- Double Schubert polynomial payload. -/
structure DoubleSchubertPolynomial (n : Nat) where
  degree : Nat
  numMonomials : Nat

/-- K-theory class of the flag variety. -/
structure FlagKTheory (n : Nat) where
  rank : Nat
  eulerChar : Int
  rank_le : rank ≤ n

/-- Peterson-Lam-Shimozono positivity data (simplified). -/
structure PetersonLamShimozonoData (n : Nat) where
  affineIndex : Nat
  translationLength : Nat
  positivityWeight : Nat

def bruhatLength (n : Nat) (v : SchubertVariety n) : Nat :=
  v.codim

def schubertCellDimension (n : Nat) (v : SchubertVariety n) : Nat :=
  n - v.codim

def oppositeSchubertDimension (n : Nat) (v : SchubertVariety n) : Nat :=
  v.codim

def schubertClassDegree (n : Nat) (c : SchubertClass n) : Nat :=
  c.degree

def cupProductDegree (n : Nat) (c₁ c₂ : SchubertClass n) : Nat :=
  c₁.degree + c₂.degree

def lrCoefficient (n : Nat) (lr : LittlewoodRichardsonData n) : Nat :=
  lr.coeff

def lrTableauCount (n : Nat) (lr : LittlewoodRichardsonData n) : Nat :=
  lr.coeff

def pieriCoefficient (n : Nat) (p : PieriData n) : Nat :=
  p.coefficient

def pieriExpansionSize (n : Nat) (p : PieriData n) : Nat :=
  p.specialIndex + 1

def doubleSchubertDegree (n : Nat) (d : DoubleSchubertPolynomial n) : Nat :=
  d.degree

def doubleSchubertSpecialization (n : Nat) (d : DoubleSchubertPolynomial n) : Nat :=
  d.numMonomials

def kTheoryEulerCharacteristic (n : Nat) (k : FlagKTheory n) : Int :=
  k.eulerChar

def kTheoryProductClass (n : Nat) (k₁ k₂ : FlagKTheory n) : Nat :=
  k₁.rank + k₂.rank

def petersonTranslation (n : Nat) (pls : PetersonLamShimozonoData n) : Nat :=
  pls.translationLength

def affineSchubertDegree (n : Nat) (pls : PetersonLamShimozonoData n) : Nat :=
  pls.affineIndex

def quantumSchubertIndex (n : Nat) (c : SchubertClass n) : Nat :=
  c.variety.index.1

def schubertPolynomialSupport (n : Nat) (d : DoubleSchubertPolynomial n) : Nat :=
  d.numMonomials

def schubertDivisorClass (n : Nat) (c : SchubertClass n) : Nat :=
  c.degree

def richardsonDimension (n : Nat) (v₁ v₂ : SchubertVariety n) : Nat :=
  n - (v₁.codim + v₂.codim)

def degeneracyLocusCodim (n : Nat) (v : SchubertVariety n) : Nat :=
  v.codim

def flagVarietyDimension (n : Nat) : Nat :=
  n * (n - 1) / 2

def plsPositivityWitness (n : Nat) (pls : PetersonLamShimozonoData n) : Nat :=
  pls.positivityWeight

theorem bruhatLength_refl (n : Nat) (v : SchubertVariety n) :
    bruhatLength n v = bruhatLength n v := rfl

theorem schubertCellDimension_refl (n : Nat) (v : SchubertVariety n) :
    schubertCellDimension n v = schubertCellDimension n v := rfl

theorem oppositeSchubertDimension_refl (n : Nat) (v : SchubertVariety n) :
    oppositeSchubertDimension n v = oppositeSchubertDimension n v := rfl

theorem schubertClassDegree_refl (n : Nat) (c : SchubertClass n) :
    schubertClassDegree n c = schubertClassDegree n c := rfl

theorem cupProductDegree_refl (n : Nat) (c₁ c₂ : SchubertClass n) :
    cupProductDegree n c₁ c₂ = cupProductDegree n c₁ c₂ := rfl

theorem lrCoefficient_refl (n : Nat) (lr : LittlewoodRichardsonData n) :
    lrCoefficient n lr = lrCoefficient n lr := rfl

theorem lrTableauCount_refl (n : Nat) (lr : LittlewoodRichardsonData n) :
    lrTableauCount n lr = lrTableauCount n lr := rfl

theorem pieriCoefficient_refl (n : Nat) (p : PieriData n) :
    pieriCoefficient n p = pieriCoefficient n p := rfl

theorem pieriExpansionSize_refl (n : Nat) (p : PieriData n) :
    pieriExpansionSize n p = pieriExpansionSize n p := rfl

theorem doubleSchubertDegree_refl (n : Nat) (d : DoubleSchubertPolynomial n) :
    doubleSchubertDegree n d = doubleSchubertDegree n d := rfl

theorem doubleSchubertSpecialization_refl (n : Nat) (d : DoubleSchubertPolynomial n) :
    doubleSchubertSpecialization n d = doubleSchubertSpecialization n d := rfl

theorem kTheoryEulerCharacteristic_refl (n : Nat) (k : FlagKTheory n) :
    kTheoryEulerCharacteristic n k = kTheoryEulerCharacteristic n k := rfl

theorem kTheoryProductClass_refl (n : Nat) (k₁ k₂ : FlagKTheory n) :
    kTheoryProductClass n k₁ k₂ = kTheoryProductClass n k₁ k₂ := rfl

theorem petersonTranslation_refl (n : Nat) (pls : PetersonLamShimozonoData n) :
    petersonTranslation n pls = petersonTranslation n pls := rfl

theorem affineSchubertDegree_refl (n : Nat) (pls : PetersonLamShimozonoData n) :
    affineSchubertDegree n pls = affineSchubertDegree n pls := rfl

theorem quantumSchubertIndex_refl (n : Nat) (c : SchubertClass n) :
    quantumSchubertIndex n c = quantumSchubertIndex n c := rfl

theorem schubertPolynomialSupport_rweq (n : Nat) (d : DoubleSchubertPolynomial n) :
    RwEq (Path.refl (schubertPolynomialSupport n d))
         (Path.refl (schubertPolynomialSupport n d)) :=
  RwEq.refl _

theorem petersonLamShimozono_path (n : Nat) (pls : PetersonLamShimozonoData n) :
    Path (petersonTranslation n pls + affineSchubertDegree n pls)
         (petersonTranslation n pls + affineSchubertDegree n pls) :=
  Path.refl _

end SchubertCalculus
end Algebra
end Path
end ComputationalPaths
