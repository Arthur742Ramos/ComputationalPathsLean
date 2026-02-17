/- 
# Motivic Cohomology Deep (Computational Paths)

This module gives a large structural model of motivic cohomology themes:

- Bloch higher Chow groups
- Motivic complexes
- Voevodsky motives
- Mixed Tate motives and weight filtrations
- Beilinson conjectural structure
- Regulator maps
- Milnor K-theory and norm residue isomorphism
- Etale comparison maps

All equalities are expressed with `Path` and computational path combinators.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace MotivicCohomologyDeep

universe u

/-! ## Section 1: Smooth schemes and Bloch higher Chow data -/

structure SmoothSchemeData (α : Type u) where
  basePoint : α
  dimension : Nat
  label : String

def affineSpace (k : α) (n : Nat) : SmoothSchemeData α where
  basePoint := k
  dimension := n
  label := s!"A{n}"

def renameScheme (X : SmoothSchemeData α) (newLabel : String) : SmoothSchemeData α where
  basePoint := X.basePoint
  dimension := X.dimension
  label := newLabel

theorem affineSpace_dim (k : α) (n : Nat) :
    (affineSpace k n).dimension = n := rfl

theorem affineSpace_label (k : α) (n : Nat) :
    (affineSpace k n).label = s!"A{n}" := rfl

theorem affineSpace_base (k : α) (n : Nat) :
    (affineSpace k n).basePoint = k := rfl

theorem smoothScheme_rename_dim (X : SmoothSchemeData α) (s : String) :
    (renameScheme X s).dimension = X.dimension := rfl

theorem smoothScheme_rename_label (X : SmoothSchemeData α) (s : String) :
    (renameScheme X s).label = s := rfl

structure BlochHigherChowData (α : Type u) where
  scheme : SmoothSchemeData α
  codim : Nat
  simplicialLevel : Nat
  generatorCount : Nat
  coefficientTag : String

def chowZero (X : SmoothSchemeData α) (p : Nat) : BlochHigherChowData α where
  scheme := X
  codim := p
  simplicialLevel := 0
  generatorCount := 0
  coefficientTag := "Z"

def chowShift (C : BlochHigherChowData α) (k : Nat) : BlochHigherChowData α where
  scheme := C.scheme
  codim := C.codim
  simplicialLevel := C.simplicialLevel + k
  generatorCount := C.generatorCount
  coefficientTag := C.coefficientTag

def chowProduct (C D : BlochHigherChowData α) : BlochHigherChowData α where
  scheme := C.scheme
  codim := C.codim + D.codim
  simplicialLevel := C.simplicialLevel + D.simplicialLevel
  generatorCount := C.generatorCount + D.generatorCount
  coefficientTag := C.coefficientTag

def chowBoundary (C : BlochHigherChowData α) : BlochHigherChowData α where
  scheme := C.scheme
  codim := C.codim
  simplicialLevel := C.simplicialLevel + 1
  generatorCount := C.generatorCount
  coefficientTag := C.coefficientTag

def chowReflPath (C : BlochHigherChowData α) : Path C C :=
  Path.refl C

def chowTwoStepPath (C : BlochHigherChowData α) : Path C C :=
  Path.trans (Path.refl C) (Path.refl C)

def chowTransportName (C : BlochHigherChowData α) : String :=
  C.scheme.label ++ ":" ++ C.coefficientTag

theorem chowZero_codim (X : SmoothSchemeData α) (p : Nat) :
    (chowZero X p).codim = p := rfl

theorem chowZero_simplicialLevel (X : SmoothSchemeData α) (p : Nat) :
    (chowZero X p).simplicialLevel = 0 := rfl

theorem chowShift_codim (C : BlochHigherChowData α) (k : Nat) :
    (chowShift C k).codim = C.codim := rfl

theorem chowShift_level (C : BlochHigherChowData α) (k : Nat) :
    (chowShift C k).simplicialLevel = C.simplicialLevel + k := rfl

theorem chowProduct_codim (C D : BlochHigherChowData α) :
    (chowProduct C D).codim = C.codim + D.codim := rfl

theorem chowProduct_level (C D : BlochHigherChowData α) :
    (chowProduct C D).simplicialLevel = C.simplicialLevel + D.simplicialLevel := rfl

theorem chowBoundary_level (C : BlochHigherChowData α) :
    (chowBoundary C).simplicialLevel = C.simplicialLevel + 1 := rfl

theorem chowBoundary_nonneg (C : BlochHigherChowData α) :
    0 ≤ (chowBoundary C).simplicialLevel := Nat.zero_le _

theorem chowReflPath_refl (C : BlochHigherChowData α) :
    chowReflPath C = Path.refl C := rfl

theorem chowTwoStepPath_eq_refl (C : BlochHigherChowData α) :
    chowTwoStepPath C = Path.refl C := by
  simp [chowTwoStepPath]

theorem chowTransportName_eq (C : BlochHigherChowData α) :
    chowTransportName C = C.scheme.label ++ ":" ++ C.coefficientTag := rfl

theorem chowProduct_generators (C D : BlochHigherChowData α) :
    (chowProduct C D).generatorCount = C.generatorCount + D.generatorCount := rfl

theorem chowShift_coeff_tag (C : BlochHigherChowData α) (k : Nat) :
    (chowShift C k).coefficientTag = C.coefficientTag := rfl

/-! ## Section 2: Motivic complexes -/

structure MotivicComplexData (α : Type u) where
  scheme : SmoothSchemeData α
  degree : Int
  weight : Int
  objectName : String

def motivicComplexShift (M : MotivicComplexData α) (n : Int) : MotivicComplexData α where
  scheme := M.scheme
  degree := M.degree + n
  weight := M.weight
  objectName := M.objectName ++ "[shift]"

def motivicComplexTwist (M : MotivicComplexData α) (q : Int) : MotivicComplexData α where
  scheme := M.scheme
  degree := M.degree
  weight := M.weight + q
  objectName := M.objectName ++ "(twist)"

def motivicComplexCone (M N : MotivicComplexData α) : MotivicComplexData α where
  scheme := M.scheme
  degree := M.degree + 1
  weight := M.weight + N.weight
  objectName := "Cone(" ++ M.objectName ++ "," ++ N.objectName ++ ")"

def motivicComplexWeightZero (X : SmoothSchemeData α) : MotivicComplexData α where
  scheme := X
  degree := 0
  weight := 0
  objectName := "Z(0)"

def motivicComplexLoopPath (M : MotivicComplexData α) : Path M M :=
  Path.refl M

def motivicComplexTwoStepPath (M : MotivicComplexData α) : Path M M :=
  Path.trans (Path.refl M) (Path.refl M)

def motivicComplexMapName (M : MotivicComplexData α) : String :=
  M.scheme.label ++ "::" ++ M.objectName

theorem motivicComplexShift_degree (M : MotivicComplexData α) (n : Int) :
    (motivicComplexShift M n).degree = M.degree + n := rfl

theorem motivicComplexShift_weight (M : MotivicComplexData α) (n : Int) :
    (motivicComplexShift M n).weight = M.weight := rfl

theorem motivicComplexTwist_weight (M : MotivicComplexData α) (q : Int) :
    (motivicComplexTwist M q).weight = M.weight + q := rfl

theorem motivicComplexTwist_degree (M : MotivicComplexData α) (q : Int) :
    (motivicComplexTwist M q).degree = M.degree := rfl

theorem motivicComplexCone_degree (M N : MotivicComplexData α) :
    (motivicComplexCone M N).degree = M.degree + 1 := rfl

theorem motivicComplexCone_weight (M N : MotivicComplexData α) :
    (motivicComplexCone M N).weight = M.weight + N.weight := rfl

theorem motivicComplexWeightZero_weight (X : SmoothSchemeData α) :
    (motivicComplexWeightZero X).weight = 0 := rfl

theorem motivicComplexWeightZero_degree (X : SmoothSchemeData α) :
    (motivicComplexWeightZero X).degree = 0 := rfl

theorem motivicComplexLoopPath_eq_refl (M : MotivicComplexData α) :
    motivicComplexLoopPath M = Path.refl M := rfl

theorem motivicComplexTwoStepPath_eq_refl (M : MotivicComplexData α) :
    motivicComplexTwoStepPath M = Path.refl M := by
  simp [motivicComplexTwoStepPath]

theorem motivicComplexMapName_eq (M : MotivicComplexData α) :
    motivicComplexMapName M = M.scheme.label ++ "::" ++ M.objectName := rfl

theorem motivicComplexTwistName (M : MotivicComplexData α) (q : Int) :
    (motivicComplexTwist M q).objectName = M.objectName ++ "(twist)" := rfl

theorem motivicComplexShiftName (M : MotivicComplexData α) (n : Int) :
    (motivicComplexShift M n).objectName = M.objectName ++ "[shift]" := rfl

theorem motivicComplexConeName (M N : MotivicComplexData α) :
    (motivicComplexCone M N).objectName = "Cone(" ++ M.objectName ++ "," ++ N.objectName ++ ")" := rfl

/-! ## Section 3: Voevodsky motives -/

structure VoevodskyMotiveData (α : Type u) where
  scheme : SmoothSchemeData α
  twist : Int
  shift : Int
  effective : Bool
  motiveName : String

def motiveOfScheme (X : SmoothSchemeData α) : VoevodskyMotiveData α where
  scheme := X
  twist := 0
  shift := 0
  effective := true
  motiveName := "M(" ++ X.label ++ ")"

def tateMotive (X : SmoothSchemeData α) (n : Int) : VoevodskyMotiveData α where
  scheme := X
  twist := n
  shift := 2 * n
  effective := true
  motiveName := "Z(" ++ toString n ++ ")"

def motiveTensor (M N : VoevodskyMotiveData α) : VoevodskyMotiveData α where
  scheme := M.scheme
  twist := M.twist + N.twist
  shift := M.shift + N.shift
  effective := M.effective && N.effective
  motiveName := M.motiveName ++ "⊗" ++ N.motiveName

def motiveDual (M : VoevodskyMotiveData α) : VoevodskyMotiveData α where
  scheme := M.scheme
  twist := -M.twist
  shift := -M.shift
  effective := M.effective
  motiveName := M.motiveName ++ "_dual"

def motiveRealizationName (M : VoevodskyMotiveData α) : String :=
  "Real(" ++ M.motiveName ++ ")"

def motiveSelfPath (M : VoevodskyMotiveData α) : Path M M :=
  Path.refl M

def motiveTwoStepPath (M : VoevodskyMotiveData α) : Path M M :=
  Path.trans (Path.refl M) (Path.refl M)

theorem motiveOfScheme_shift (X : SmoothSchemeData α) :
    (motiveOfScheme X).shift = 0 := rfl

theorem motiveOfScheme_twist (X : SmoothSchemeData α) :
    (motiveOfScheme X).twist = 0 := rfl

theorem tateMotive_shift (X : SmoothSchemeData α) (n : Int) :
    (tateMotive X n).shift = 2 * n := rfl

theorem tateMotive_twist (X : SmoothSchemeData α) (n : Int) :
    (tateMotive X n).twist = n := rfl

theorem motiveTensor_twist (M N : VoevodskyMotiveData α) :
    (motiveTensor M N).twist = M.twist + N.twist := rfl

theorem motiveTensor_shift (M N : VoevodskyMotiveData α) :
    (motiveTensor M N).shift = M.shift + N.shift := rfl

theorem motiveDual_twist (M : VoevodskyMotiveData α) :
    (motiveDual M).twist = -M.twist := rfl

theorem motiveDual_shift (M : VoevodskyMotiveData α) :
    (motiveDual M).shift = -M.shift := rfl

theorem motiveRealization_target (M : VoevodskyMotiveData α) :
    motiveRealizationName M = "Real(" ++ M.motiveName ++ ")" := rfl

theorem motiveSelfPath_refl (M : VoevodskyMotiveData α) :
    motiveSelfPath M = Path.refl M := rfl

theorem motiveTwoStepPath_eq_refl (M : VoevodskyMotiveData α) :
    motiveTwoStepPath M = Path.refl M := by
  simp [motiveTwoStepPath]

theorem motiveTensorName (M N : VoevodskyMotiveData α) :
    (motiveTensor M N).motiveName = M.motiveName ++ "⊗" ++ N.motiveName := rfl

theorem motiveDualName (M : VoevodskyMotiveData α) :
    (motiveDual M).motiveName = M.motiveName ++ "_dual" := rfl

theorem tateMotive_effective (X : SmoothSchemeData α) (n : Int) :
    (tateMotive X n).effective = true := rfl

/-! ## Section 4: Mixed Tate motives and motivic weight filtration -/

structure MixedTateData (α : Type u) where
  motive : VoevodskyMotiveData α
  minWeight : Int
  maxWeight : Int
  splitByWeight : Bool

structure WeightFiltrationData (α : Type u) where
  motive : VoevodskyMotiveData α
  minWeight : Int
  maxWeight : Int
  isExhaustive : Bool
  SymIndex : Nat
  GamIndex : Nat

structure SymGamIndex where
  Sym : Nat
  Gam : Nat

def SymGamIndex.swap (s : SymGamIndex) : SymGamIndex where
  Sym := s.Gam
  Gam := s.Sym

def symGamDiagonal (n : Nat) : SymGamIndex where
  Sym := n
  Gam := n

def mixedTatePure (M : VoevodskyMotiveData α) (w : Int) : MixedTateData α where
  motive := M
  minWeight := w
  maxWeight := w
  splitByWeight := true

def weightFiltrationOfMixedTate (T : MixedTateData α) : WeightFiltrationData α where
  motive := T.motive
  minWeight := T.minWeight
  maxWeight := T.maxWeight
  isExhaustive := true
  SymIndex := 0
  GamIndex := 0

def weightTruncation (W : WeightFiltrationData α) (a b : Int) : WeightFiltrationData α where
  motive := W.motive
  minWeight := a
  maxWeight := b
  isExhaustive := W.isExhaustive
  SymIndex := W.SymIndex
  GamIndex := W.GamIndex

def mixedTateLoop (T : MixedTateData α) : Path T T :=
  Path.refl T

def mixedTateTwoStep (T : MixedTateData α) : Path T T :=
  Path.trans (Path.refl T) (Path.refl T)

def weightRange (W : WeightFiltrationData α) : Nat :=
  Int.natAbs (W.maxWeight - W.minWeight)

def weightPieceName (W : WeightFiltrationData α) : String :=
  "W[" ++ toString W.minWeight ++ "," ++ toString W.maxWeight ++ "]"

theorem mixedTatePure_bounds (M : VoevodskyMotiveData α) (w : Int) :
    (mixedTatePure M w).minWeight = (mixedTatePure M w).maxWeight := rfl

theorem mixedTatePure_split (M : VoevodskyMotiveData α) (w : Int) :
    (mixedTatePure M w).splitByWeight = true := rfl

theorem weightFiltration_min (T : MixedTateData α) :
    (weightFiltrationOfMixedTate T).minWeight = T.minWeight := rfl

theorem weightFiltration_max (T : MixedTateData α) :
    (weightFiltrationOfMixedTate T).maxWeight = T.maxWeight := rfl

theorem weightFiltration_exhaustive (T : MixedTateData α) :
    (weightFiltrationOfMixedTate T).isExhaustive = true := rfl

theorem weightTruncation_lower (W : WeightFiltrationData α) (a b : Int) :
    (weightTruncation W a b).minWeight = a := rfl

theorem weightTruncation_upper (W : WeightFiltrationData α) (a b : Int) :
    (weightTruncation W a b).maxWeight = b := rfl

theorem mixedTateLoop_eq_refl (T : MixedTateData α) :
    mixedTateLoop T = Path.refl T := rfl

theorem mixedTateTwoStep_eq_refl (T : MixedTateData α) :
    mixedTateTwoStep T = Path.refl T := by
  simp [mixedTateTwoStep]

theorem symGam_swap_involution (s : SymGamIndex) :
    SymGamIndex.swap (SymGamIndex.swap s) = s := by
  cases s
  rfl

theorem symGamDiagonal_sym (n : Nat) :
    (symGamDiagonal n).Sym = n := rfl

theorem symGamDiagonal_gam (n : Nat) :
    (symGamDiagonal n).Gam = n := rfl

theorem weightRange_nonempty (W : WeightFiltrationData α) :
    0 ≤ weightRange W := Nat.zero_le _

theorem weightRange_length (W : WeightFiltrationData α) :
    weightRange W = Int.natAbs (W.maxWeight - W.minWeight) := rfl

theorem weightPieceName_contains (W : WeightFiltrationData α) :
    weightPieceName W = "W[" ++ toString W.minWeight ++ "," ++ toString W.maxWeight ++ "]" := rfl

/-! ## Section 5: Beilinson structure and regulator maps -/

structure BeilinsonConjectureData (α : Type u) where
  motive : VoevodskyMotiveData α
  expectedRank : Nat
  regulatorRank : Nat
  lOrder : Nat
  predictsIso : Bool

structure RegulatorMapData (α : Type u) where
  source : BlochHigherChowData α
  target : MotivicComplexData α
  mapName : String
  compatibleWeight : Bool

def beilinsonBalanced (M : VoevodskyMotiveData α) (r : Nat) : BeilinsonConjectureData α where
  motive := M
  expectedRank := r
  regulatorRank := r
  lOrder := r
  predictsIso := true

def regulatorIdentity (C : BlochHigherChowData α) (M : MotivicComplexData α) :
    RegulatorMapData α where
  source := C
  target := M
  mapName := "id_reg"
  compatibleWeight := true

def regulatorCompose (f g : RegulatorMapData α) : RegulatorMapData α where
  source := f.source
  target := g.target
  mapName := f.mapName ++ " ; " ++ g.mapName
  compatibleWeight := f.compatibleWeight && g.compatibleWeight

def regulatorBetti (C : BlochHigherChowData α) (M : MotivicComplexData α) :
    RegulatorMapData α where
  source := C
  target := M
  mapName := "reg_Betti"
  compatibleWeight := true

def regulatorEtale (C : BlochHigherChowData α) (M : MotivicComplexData α) :
    RegulatorMapData α where
  source := C
  target := M
  mapName := "reg_Etale"
  compatibleWeight := true

def beilinsonPath (B : BeilinsonConjectureData α) : Path B B :=
  Path.refl B

def regulatorLoop (f : RegulatorMapData α) : Path f f :=
  Path.refl f

def regulatorTwoStep (f : RegulatorMapData α) : Path f f :=
  Path.trans (Path.refl f) (Path.refl f)

theorem beilinsonBalanced_predicts (M : VoevodskyMotiveData α) (r : Nat) :
    (beilinsonBalanced M r).predictsIso = true := rfl

theorem beilinsonBalanced_rank (M : VoevodskyMotiveData α) (r : Nat) :
    (beilinsonBalanced M r).expectedRank = r := rfl

theorem beilinsonBalanced_regulator (M : VoevodskyMotiveData α) (r : Nat) :
    (beilinsonBalanced M r).regulatorRank = r := rfl

theorem regulatorIdentity_name (C : BlochHigherChowData α) (M : MotivicComplexData α) :
    (regulatorIdentity C M).mapName = "id_reg" := rfl

theorem regulatorIdentity_weight (C : BlochHigherChowData α) (M : MotivicComplexData α) :
    (regulatorIdentity C M).compatibleWeight = true := rfl

theorem regulatorCompose_name (f g : RegulatorMapData α) :
    (regulatorCompose f g).mapName = f.mapName ++ " ; " ++ g.mapName := rfl

theorem regulatorCompose_weight (f g : RegulatorMapData α) :
    (regulatorCompose f g).compatibleWeight = (f.compatibleWeight && g.compatibleWeight) := rfl

theorem regulatorCompose_target (f g : RegulatorMapData α) :
    (regulatorCompose f g).target = g.target := rfl

theorem regulatorLoop_eq_refl (f : RegulatorMapData α) :
    regulatorLoop f = Path.refl f := rfl

theorem regulatorTwoStep_eq_refl (f : RegulatorMapData α) :
    regulatorTwoStep f = Path.refl f := by
  simp [regulatorTwoStep]

theorem beilinsonPath_refl (B : BeilinsonConjectureData α) :
    beilinsonPath B = Path.refl B := rfl

theorem regulatorBetti_name (C : BlochHigherChowData α) (M : MotivicComplexData α) :
    (regulatorBetti C M).mapName = "reg_Betti" := rfl

theorem regulatorEtale_name (C : BlochHigherChowData α) (M : MotivicComplexData α) :
    (regulatorEtale C M).mapName = "reg_Etale" := rfl

theorem regulatorCompose_assoc_name (f g h : RegulatorMapData α) :
    (regulatorCompose (regulatorCompose f g) h).mapName =
      (regulatorCompose f (regulatorCompose g h)).mapName := by
  simp [regulatorCompose, String.append_assoc]

/-! ## Section 6: Milnor K-theory and norm residue isomorphism -/

structure MilnorKData (α : Type u) where
  field : α
  degree : Nat
  symbolCount : Nat
  relationTag : String

structure NormResidueIsoData (α : Type u) where
  field : α
  prime : Nat
  degree : Nat
  sourceMilnor : MilnorKData α
  targetEtaleRank : Nat
  isIsomorphism : Bool

def milnorKZero (k : α) : MilnorKData α where
  field := k
  degree := 0
  symbolCount := 1
  relationTag := "K0"

def milnorKOne (k : α) : MilnorKData α where
  field := k
  degree := 1
  symbolCount := 1
  relationTag := "K1"

def milnorProduct (A B : MilnorKData α) : MilnorKData α where
  field := A.field
  degree := A.degree + B.degree
  symbolCount := A.symbolCount + B.symbolCount
  relationTag := A.relationTag ++ "*" ++ B.relationTag

def milnorSteinbergPath (K : MilnorKData α) : Path K K :=
  Path.refl K

def milnorTwoStepPath (K : MilnorKData α) : Path K K :=
  Path.trans (Path.refl K) (Path.refl K)

def normResidueStatement (k : α) (p n r : Nat) : NormResidueIsoData α where
  field := k
  prime := p
  degree := n
  sourceMilnor := { field := k, degree := n, symbolCount := r, relationTag := "KM" }
  targetEtaleRank := r
  isIsomorphism := true

def normResiduePath (N : NormResidueIsoData α) : Path N N :=
  Path.refl N

def normResidueTwoStepPath (N : NormResidueIsoData α) : Path N N :=
  Path.trans (Path.refl N) (Path.refl N)

theorem milnorKZero_degree (k : α) : (milnorKZero k).degree = 0 := rfl

theorem milnorKOne_degree (k : α) : (milnorKOne k).degree = 1 := rfl

theorem milnorProduct_degree (A B : MilnorKData α) :
    (milnorProduct A B).degree = A.degree + B.degree := rfl

theorem milnorProduct_symbolCount (A B : MilnorKData α) :
    (milnorProduct A B).symbolCount = A.symbolCount + B.symbolCount := rfl

theorem milnorSteinberg_relation (K : MilnorKData α) :
    milnorSteinbergPath K = Path.refl K := rfl

theorem milnorLoop_refl (K : MilnorKData α) :
    Path.trans (Path.refl K) (Path.refl K) = Path.refl K := by
  simp

theorem milnorTwoStep_eq_refl (K : MilnorKData α) :
    milnorTwoStepPath K = Path.refl K := by
  simp [milnorTwoStepPath]

theorem normResidueStatement_iso (k : α) (p n r : Nat) :
    (normResidueStatement k p n r).isIsomorphism = true := rfl

theorem normResidueStatement_degree (k : α) (p n r : Nat) :
    (normResidueStatement k p n r).degree = n := rfl

theorem normResidueStatement_target (k : α) (p n r : Nat) :
    (normResidueStatement k p n r).targetEtaleRank = r := rfl

theorem normResiduePrimeStable (k : α) (p n r : Nat) :
    (normResidueStatement k p n r).prime = p := rfl

theorem normResiduePath_refl (N : NormResidueIsoData α) :
    normResiduePath N = Path.refl N := rfl

theorem normResidueTwoStep_eq_refl (N : NormResidueIsoData α) :
    normResidueTwoStepPath N = Path.refl N := by
  simp [normResidueTwoStepPath]

theorem normResidueSourceDegree (k : α) (p n r : Nat) :
    (normResidueStatement k p n r).sourceMilnor.degree = n := rfl

/-! ## Section 7: Etale comparison -/

structure EtaleCohData (α : Type u) where
  scheme : SmoothSchemeData α
  degree : Nat
  twist : Nat
  finiteCoefficients : Bool
  rank : Nat

structure EtaleComparisonData (α : Type u) where
  motivic : MotivicComplexData α
  etale : EtaleCohData α
  comparisonDegree : Int
  comparisonWeight : Int
  comparisonHolds : Bool

def etaleCohShift (E : EtaleCohData α) (d t : Nat) : EtaleCohData α where
  scheme := E.scheme
  degree := E.degree + d
  twist := E.twist + t
  finiteCoefficients := E.finiteCoefficients
  rank := E.rank

def etaleComparisonIdentity (M : MotivicComplexData α) (E : EtaleCohData α) :
    EtaleComparisonData α where
  motivic := M
  etale := E
  comparisonDegree := M.degree
  comparisonWeight := M.weight
  comparisonHolds := true

def etaleComparisonLoop (C : EtaleComparisonData α) : Path C C :=
  Path.refl C

def etaleComparisonTwoStep (C : EtaleComparisonData α) : Path C C :=
  Path.trans (Path.refl C) (Path.refl C)

def etaleComparisonTransportName (C : EtaleComparisonData α) : String :=
  C.motivic.objectName ++ "=>" ++ C.etale.scheme.label

def etaleComparisonToRegulator (C : EtaleComparisonData α) : RegulatorMapData α where
  source := chowZero C.motivic.scheme 0
  target := C.motivic
  mapName := "reg_from_etale_comp"
  compatibleWeight := C.comparisonHolds

def etaleComparisonRestrict (C : EtaleComparisonData α) (d : Int) : EtaleComparisonData α where
  motivic := C.motivic
  etale := C.etale
  comparisonDegree := C.comparisonDegree + d
  comparisonWeight := C.comparisonWeight
  comparisonHolds := C.comparisonHolds

theorem etaleCohShift_degree (E : EtaleCohData α) (d t : Nat) :
    (etaleCohShift E d t).degree = E.degree + d := rfl

theorem etaleCohShift_twist (E : EtaleCohData α) (d t : Nat) :
    (etaleCohShift E d t).twist = E.twist + t := rfl

theorem etaleComparison_identity_degree (M : MotivicComplexData α) (E : EtaleCohData α) :
    (etaleComparisonIdentity M E).comparisonDegree = M.degree := rfl

theorem etaleComparison_identity_weight (M : MotivicComplexData α) (E : EtaleCohData α) :
    (etaleComparisonIdentity M E).comparisonWeight = M.weight := rfl

theorem etaleComparison_identity_holds (M : MotivicComplexData α) (E : EtaleCohData α) :
    (etaleComparisonIdentity M E).comparisonHolds = true := rfl

theorem etaleComparison_loop_refl (C : EtaleComparisonData α) :
    etaleComparisonLoop C = Path.refl C := rfl

theorem etaleComparison_twoStep_eq_refl (C : EtaleComparisonData α) :
    etaleComparisonTwoStep C = Path.refl C := by
  simp [etaleComparisonTwoStep]

theorem etaleComparison_transport_name (C : EtaleComparisonData α) :
    etaleComparisonTransportName C = C.motivic.objectName ++ "=>" ++ C.etale.scheme.label := rfl

theorem etaleComparison_toRegulator_weight (C : EtaleComparisonData α) :
    (etaleComparisonToRegulator C).compatibleWeight = C.comparisonHolds := rfl

theorem etaleComparison_toRegulator_name (C : EtaleComparisonData α) :
    (etaleComparisonToRegulator C).mapName = "reg_from_etale_comp" := rfl

theorem etaleComparison_restrict_holds (C : EtaleComparisonData α) (d : Int) :
    (etaleComparisonRestrict C d).comparisonHolds = C.comparisonHolds := rfl

theorem etaleComparison_restrict_degree (C : EtaleComparisonData α) (d : Int) :
    (etaleComparisonRestrict C d).comparisonDegree = C.comparisonDegree + d := rfl

theorem etaleComparison_restrict_weight (C : EtaleComparisonData α) (d : Int) :
    (etaleComparisonRestrict C d).comparisonWeight = C.comparisonWeight := rfl

end MotivicCohomologyDeep
end Algebra
end Path
end ComputationalPaths
