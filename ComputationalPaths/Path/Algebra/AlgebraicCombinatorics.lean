/-
# Algebraic Combinatorics (Computational Paths Skeleton)

Skeleton declarations for symmetric functions, Schur polynomials,
Robinson-Schensted, jeu de taquin, crystal combinatorics,
Littlewood-Richardson data, plethysm, and Macdonald-style data.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace AlgebraicCombinatorics

structure Partition where
  parts : List Nat

def Partition.size (P : Partition) : Nat :=
  P.parts.foldl (· + ·) 0

def Partition.length (P : Partition) : Nat :=
  P.parts.length

def partitionConjugateSizeModel (P : Partition) : Nat :=
  P.size

structure Tableau where
  shape : Partition
  entries : List Nat

def tableauWeight (T : Tableau) : Nat :=
  T.entries.foldl (· + ·) 0

def tableauShapeSize (T : Tableau) : Nat :=
  T.shape.size

structure SymmetricMonomial where
  coeff : Int
  exponents : List Nat

def monomialDegree (m : SymmetricMonomial) : Nat :=
  m.exponents.foldl (· + ·) 0

def monomialScale (c : Int) (m : SymmetricMonomial) : SymmetricMonomial :=
  ⟨c * m.coeff, m.exponents⟩

def monomialMultiply (m n : SymmetricMonomial) : SymmetricMonomial :=
  ⟨m.coeff * n.coeff, m.exponents ++ n.exponents⟩

structure SchurPolynomial where
  coeff : Partition → Int

def schurAt (S : SchurPolynomial) (P : Partition) : Int :=
  S.coeff P

def schurNormalize (S : SchurPolynomial) : SchurPolynomial :=
  S

structure RobinsonSchenstedPair where
  insertionShape : Partition
  recordingShape : Partition

def rsInsertionLength (R : RobinsonSchenstedPair) : Nat :=
  R.insertionShape.length

def rsRecordingLength (R : RobinsonSchenstedPair) : Nat :=
  R.recordingShape.length

def rsShapeAgreement (R : RobinsonSchenstedPair) : Nat :=
  if R.insertionShape.length = R.recordingShape.length then
    R.insertionShape.length
  else
    0

structure JeuDeTaquinSlide where
  before : Tableau
  after : Tableau

def jeuDeTaquinLength (J : JeuDeTaquinSlide) : Nat :=
  J.after.entries.length

structure CrystalNode where
  weight : Nat
  label : Nat

def crystalWeight (C : CrystalNode) : Nat :=
  C.weight

def crystalRaise (C : CrystalNode) : CrystalNode :=
  { C with weight := C.weight + 1 }

def crystalLower (C : CrystalNode) : CrystalNode :=
  { C with weight := C.weight }

structure LRTableauData where
  λ : Partition
  μ : Partition
  ν : Partition

def littlewoodRichardsonCoeff (L : LRTableauData) : Nat :=
  L.λ.size + L.μ.size + L.ν.size

def plethysmCoeff (L : LRTableauData) : Nat :=
  littlewoodRichardsonCoeff L + L.ν.length

structure MacdonaldDatum where
  λ : Partition
  q : Nat
  t : Nat

def macdonaldSpecialization (M : MacdonaldDatum) : Nat :=
  M.λ.size + M.q + M.t

def kostkaFoulkesModel (M : MacdonaldDatum) : Nat :=
  M.λ.length + M.q

def hallInnerProductModel (P Q : Partition) : Nat :=
  P.size + Q.size

def schurExpansionTerm (c : Nat) (P : Partition) : Nat :=
  c * P.size

theorem partition_size_nil :
    Partition.size ⟨[]⟩ = 0 := rfl

theorem partition_length_nil :
    Partition.length ⟨[]⟩ = 0 := rfl

theorem tableauShapeSize_def (T : Tableau) :
    tableauShapeSize T = T.shape.size := rfl

theorem tableauWeight_nonneg (T : Tableau) :
    0 ≤ tableauWeight T := Nat.zero_le _

theorem monomialDegree_nonneg (m : SymmetricMonomial) :
    0 ≤ monomialDegree m := Nat.zero_le _

theorem monomialScale_degree (c : Int) (m : SymmetricMonomial) :
    monomialDegree (monomialScale c m) = monomialDegree m := rfl

theorem monomialMultiply_degree (m n : SymmetricMonomial) :
    monomialDegree (monomialMultiply m n) =
      (m.exponents ++ n.exponents).foldl (· + ·) 0 := rfl

theorem schurAt_def (S : SchurPolynomial) (P : Partition) :
    schurAt S P = S.coeff P := rfl

theorem schurNormalize_id (S : SchurPolynomial) :
    schurNormalize S = S := rfl

theorem schurNormalize_idempotent (S : SchurPolynomial) :
    schurNormalize (schurNormalize S) = schurNormalize S := rfl

theorem rsInsertionLength_nonneg (R : RobinsonSchenstedPair) :
    0 ≤ rsInsertionLength R := Nat.zero_le _

theorem rsRecordingLength_nonneg (R : RobinsonSchenstedPair) :
    0 ≤ rsRecordingLength R := Nat.zero_le _

theorem rsShapeAgreement_eq (R : RobinsonSchenstedPair)
    (h : R.insertionShape.length = R.recordingShape.length) :
    rsShapeAgreement R = R.insertionShape.length := by
  simp [rsShapeAgreement, h]

theorem jeuDeTaquinLength_nonneg (J : JeuDeTaquinSlide) :
    0 ≤ jeuDeTaquinLength J := Nat.zero_le _

theorem crystalRaise_weight (C : CrystalNode) :
    (crystalRaise C).weight = C.weight + 1 := rfl

theorem crystalLower_weight (C : CrystalNode) :
    (crystalLower C).weight = C.weight := rfl

theorem littlewoodRichardsonCoeff_nonneg (L : LRTableauData) :
    0 ≤ littlewoodRichardsonCoeff L := Nat.zero_le _

theorem plethysmCoeff_nonneg (L : LRTableauData) :
    0 ≤ plethysmCoeff L := Nat.zero_le _

theorem macdonaldSpecialization_nonneg (M : MacdonaldDatum) :
    0 ≤ macdonaldSpecialization M := Nat.zero_le _

theorem kostkaFoulkesModel_nonneg (M : MacdonaldDatum) :
    0 ≤ kostkaFoulkesModel M := Nat.zero_le _

theorem hallInnerProductModel_symm (P Q : Partition) :
    hallInnerProductModel P Q = hallInnerProductModel Q P := by
  simp [hallInnerProductModel, Nat.add_comm]

theorem schurExpansionTerm_zero (P : Partition) :
    schurExpansionTerm 0 P = 0 := rfl

def rs_shape_path (R : RobinsonSchenstedPair) :
    Path (rsShapeAgreement R) (rsShapeAgreement R) :=
  Path.refl _

def rs_shape_path_trans (R : RobinsonSchenstedPair) :
    Path (rsShapeAgreement R) (rsShapeAgreement R) :=
  Path.trans (Path.refl _) (Path.refl _)

end AlgebraicCombinatorics
end Algebra
end Path
end ComputationalPaths
