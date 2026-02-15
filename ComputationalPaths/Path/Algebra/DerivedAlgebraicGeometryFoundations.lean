import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Algebra.DerivedAlgebraicGeometryFoundations

universe u

structure SimplicialCommRing where
  level : Nat → Type u
  face : (n : Nat) → Fin (n + 2) → level (n + 1) → level n
  degen : (n : Nat) → Fin (n + 1) → level n → level (n + 1)

structure SCRingMorphism (R S : SimplicialCommRing) where
  map : (n : Nat) → R.level n → S.level n

structure DerivedAffine where
  ring : SimplicialCommRing
  opens : Type u

structure DerivedScheme where
  chart : Type u
  affine : chart → DerivedAffine

structure CotangentComplex where
  source : SimplicialCommRing
  target : SimplicialCommRing
  degree : Nat → Type u

structure DeformationProblem where
  base : SimplicialCommRing
  extension : SimplicialCommRing
  tangent : Type u

structure ObstructionTheory where
  problem : DeformationProblem
  obstructionGroup : Type u

structure LurieRepresentability where
  functorObj : Type u
  preservesLimits : Prop
  infinitesimallyCohesive : Prop
  nilcomplete : Prop

def simplicialLevel (R : SimplicialCommRing) (n : Nat) : Type u := R.level n

def zeroSimplices (R : SimplicialCommRing) : Type u := R.level 0

def oneSimplices (R : SimplicialCommRing) : Type u := R.level 1

def faceZero (R : SimplicialCommRing) : R.level 1 → R.level 0 :=
  R.face 0 ⟨0, by decide⟩

def degenZero (R : SimplicialCommRing) : R.level 0 → R.level 1 :=
  R.degen 0 ⟨0, by decide⟩

def pi0Carrier (R : SimplicialCommRing) : Type u := zeroSimplices R

def truncateToClassical (R : SimplicialCommRing) : Type u := pi0Carrier R

def affineFromRing (R : SimplicialCommRing) : DerivedAffine :=
  { ring := R, opens := PUnit }

def affineOpenType (X : DerivedAffine) : Type u := X.opens

def schemeUnderlyingChart (X : DerivedScheme) : Type u := X.chart

def schemeAffineAt (X : DerivedScheme) (c : X.chart) : DerivedAffine := X.affine c

def cotangentFiber (L : CotangentComplex) (n : Nat) : Type u := L.degree n

def cotangentAmplitude (_L : CotangentComplex) : Nat := 0

def cotangentShift (L : CotangentComplex) (k : Nat) : Nat → Type u :=
  fun n => L.degree (n + k)

def tangentSpace (P : DeformationProblem) : Type u := P.tangent

def deformationFiber (P : DeformationProblem) : Type u := P.extension.level 0

def obstructionCarrier (O : ObstructionTheory) : Type u := O.obstructionGroup

def obstructionVanishes (O : ObstructionTheory) : Prop := O.obstructionGroup = PUnit

def firstOrderLiftable (O : ObstructionTheory) : Prop := obstructionVanishes O → True

def hasAtlas (X : DerivedScheme) : Prop := Nonempty X.chart

def diagonalRepresentable (_X : DerivedScheme) : Prop := True

def formalSmooth (X : DerivedScheme) : Prop := hasAtlas X

def lurieHypotheses (D : LurieRepresentability) : Prop :=
  D.preservesLimits ∧ D.infinitesimallyCohesive ∧ D.nilcomplete

def representableFunctor (D : LurieRepresentability) : Prop := lurieHypotheses D

def dagReflPath (X : DerivedScheme) : Path X X := Path.refl X

def dagNormalizationPath (X : DerivedScheme) : Path X X :=
  Path.trans (Path.refl X) (Path.refl X)

theorem simplicialLevel_zero (R : SimplicialCommRing) :
    simplicialLevel R 0 = R.level 0 := by
  sorry

theorem zeroSimplices_eq (R : SimplicialCommRing) :
    zeroSimplices R = R.level 0 := by
  sorry

theorem oneSimplices_eq (R : SimplicialCommRing) :
    oneSimplices R = R.level 1 := by
  sorry

theorem faceZero_eq (R : SimplicialCommRing) :
    faceZero R = R.face 0 ⟨0, by decide⟩ := by
  sorry

theorem degenZero_eq (R : SimplicialCommRing) :
    degenZero R = R.degen 0 ⟨0, by decide⟩ := by
  sorry

theorem truncateToClassical_eq (R : SimplicialCommRing) :
    truncateToClassical R = pi0Carrier R := by
  sorry

theorem affineFromRing_ring (R : SimplicialCommRing) :
    (affineFromRing R).ring = R := by
  sorry

theorem affineOpenType_eq (X : DerivedAffine) :
    affineOpenType X = X.opens := by
  sorry

theorem schemeUnderlyingChart_eq (X : DerivedScheme) :
    schemeUnderlyingChart X = X.chart := by
  sorry

theorem schemeAffineAt_eq (X : DerivedScheme) (c : X.chart) :
    schemeAffineAt X c = X.affine c := by
  sorry

theorem cotangentFiber_eq (L : CotangentComplex) (n : Nat) :
    cotangentFiber L n = L.degree n := by
  sorry

theorem cotangentAmplitude_nonnegative (L : CotangentComplex) :
    0 ≤ cotangentAmplitude L := by
  sorry

theorem cotangentShift_zero (L : CotangentComplex) :
    cotangentShift L 0 = L.degree := by
  sorry

theorem tangentSpace_eq (P : DeformationProblem) :
    tangentSpace P = P.tangent := by
  sorry

theorem deformationFiber_eq (P : DeformationProblem) :
    deformationFiber P = P.extension.level 0 := by
  sorry

theorem obstructionVanishes_iff (O : ObstructionTheory) :
    obstructionVanishes O ↔ O.obstructionGroup = PUnit := by
  sorry

theorem firstOrderLiftable_of_vanishing (O : ObstructionTheory)
    (h : obstructionVanishes O) :
    firstOrderLiftable O := by
  sorry

theorem hasAtlas_of_formalSmooth (X : DerivedScheme) :
    formalSmooth X → hasAtlas X := by
  sorry

theorem formalSmooth_of_hasAtlas (X : DerivedScheme) :
    hasAtlas X → formalSmooth X := by
  sorry

theorem lurieHypotheses_left (D : LurieRepresentability) :
    lurieHypotheses D → D.preservesLimits := by
  sorry

theorem lurieHypotheses_middle (D : LurieRepresentability) :
    lurieHypotheses D → D.infinitesimallyCohesive := by
  sorry

theorem lurieHypotheses_right (D : LurieRepresentability) :
    lurieHypotheses D → D.nilcomplete := by
  sorry

theorem representableFunctor_of_hyp (D : LurieRepresentability) :
    lurieHypotheses D → representableFunctor D := by
  sorry

theorem representableFunctor_implies_nilcomplete (D : LurieRepresentability) :
    representableFunctor D → D.nilcomplete := by
  sorry

theorem dagReflPath_toEq (X : DerivedScheme) :
    (dagReflPath X).toEq = rfl := by
  sorry

theorem dagNormalizationPath_toEq (X : DerivedScheme) :
    (dagNormalizationPath X).toEq = rfl := by
  sorry

theorem dagNormalizationPath_idempotent (X : DerivedScheme) :
    dagNormalizationPath X = dagNormalizationPath X := by
  sorry

theorem representableFunctor_stable (D : LurieRepresentability) :
    representableFunctor D → representableFunctor D := by
  sorry

end ComputationalPaths.Path.Algebra.DerivedAlgebraicGeometryFoundations
