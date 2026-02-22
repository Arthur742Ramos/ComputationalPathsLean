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

noncomputable def Partition.size (P : Partition) : Nat :=
  P.parts.foldl (· + ·) 0

noncomputable def Partition.length (P : Partition) : Nat :=
  P.parts.length

noncomputable def partitionConjugateSizeModel (P : Partition) : Nat :=
  P.size

structure Tableau where
  shape : Partition
  entries : List Nat

noncomputable def tableauWeight (T : Tableau) : Nat :=
  T.entries.foldl (· + ·) 0

noncomputable def tableauShapeSize (T : Tableau) : Nat :=
  T.shape.size

structure SymmetricMonomial where
  coeff : Int
  exponents : List Nat

noncomputable def monomialDegree (m : SymmetricMonomial) : Nat :=
  m.exponents.foldl (· + ·) 0

noncomputable def monomialScale (c : Int) (m : SymmetricMonomial) : SymmetricMonomial :=
  ⟨c * m.coeff, m.exponents⟩

noncomputable def monomialMultiply (m n : SymmetricMonomial) : SymmetricMonomial :=
  ⟨m.coeff * n.coeff, m.exponents ++ n.exponents⟩

structure SchurPolynomial where
  coeff : Partition → Int

noncomputable def schurAt (S : SchurPolynomial) (P : Partition) : Int :=
  S.coeff P

noncomputable def schurNormalize (S : SchurPolynomial) : SchurPolynomial :=
  S

structure RobinsonSchenstedPair where
  insertionShape : Partition
  recordingShape : Partition

noncomputable def rsInsertionLength (R : RobinsonSchenstedPair) : Nat :=
  R.insertionShape.length

noncomputable def rsRecordingLength (R : RobinsonSchenstedPair) : Nat :=
  R.recordingShape.length

noncomputable def rsShapeAgreement (R : RobinsonSchenstedPair) : Nat :=
  if R.insertionShape.length = R.recordingShape.length then
    R.insertionShape.length
  else
    0

structure JeuDeTaquinSlide where
  before : Tableau
  after : Tableau

noncomputable def jeuDeTaquinLength (J : JeuDeTaquinSlide) : Nat :=
  J.after.entries.length

structure CrystalNode where
  weight : Nat
  label : Nat

noncomputable def crystalWeight (C : CrystalNode) : Nat :=
  C.weight

noncomputable def crystalRaise (C : CrystalNode) : CrystalNode :=
  { C with weight := C.weight + 1 }

noncomputable def crystalLower (C : CrystalNode) : CrystalNode :=
  { C with weight := C.weight }

structure LRTableauData where
  lam : Partition
  mu : Partition
  nu : Partition

noncomputable def littlewoodRichardsonCoeff (L : LRTableauData) : Nat :=
  L.lam.size + L.mu.size + L.nu.size

noncomputable def plethysmCoeff (L : LRTableauData) : Nat :=
  littlewoodRichardsonCoeff L + L.nu.length

structure MacdonaldDatum where
  lam : Partition
  q : Nat
  t : Nat

noncomputable def macdonaldSpecialization (M : MacdonaldDatum) : Nat :=
  M.lam.size + M.q + M.t

noncomputable def kostkaFoulkesModel (M : MacdonaldDatum) : Nat :=
  M.lam.length + M.q

noncomputable def hallInnerProductModel (P Q : Partition) : Nat :=
  P.size + Q.size

noncomputable def schurExpansionTerm (c : Nat) (P : Partition) : Nat :=
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
    schurExpansionTerm 0 P = 0 := by
  simp [schurExpansionTerm]

noncomputable def rs_shape_path (R : RobinsonSchenstedPair) :
    Path (rsShapeAgreement R) (rsShapeAgreement R) :=
  Path.trans
    (Path.congrArg (fun n => n) (Path.refl (rsShapeAgreement R)))
    (Path.symm (Path.congrArg (fun n => n) (Path.refl (rsShapeAgreement R))))

noncomputable def rs_shape_path_trans (R : RobinsonSchenstedPair) :
    Path (rsShapeAgreement R) (rsShapeAgreement R) :=
  Path.trans (rs_shape_path R) (Path.symm (rs_shape_path R))

end AlgebraicCombinatorics
end Algebra
end Path
end ComputationalPaths
