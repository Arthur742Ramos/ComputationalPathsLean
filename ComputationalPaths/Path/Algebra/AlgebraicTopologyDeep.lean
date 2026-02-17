/-
# Algebraic Topology Deep via Computational Paths

This module provides a large, path-centric scaffold for algebraic topology:

- CW complex combinatorial data
- Cellular homology chain complexes
- Mayer-Vietoris decompositions
- Excision encodings
- Hurewicz map profiles
- Universal coefficient bookkeeping
- Cup product structures
- Poincaré duality profiles
- Eilenberg-MacLane space encodings
- Obstruction theory states

All statements use `Path` equalities; path composition/symmetry provides
coherence. ZERO sorry, ZERO Path.ofEq.
-/

import ComputationalPaths.Path.Basic

set_option linter.unusedVariables false

namespace ComputationalPaths.Path.Algebra.AlgebraicTopologyDeep

open ComputationalPaths.Path

/-! ## CW complex combinatorial data -/

structure CWData where
  dim : Nat
  cells0 : Nat
  cells1 : Nat
  cells2 : Nat
  cellsN : Nat
  Sym : Nat
  Gam : Nat

def cwEuler (C : CWData) : Int :=
  (C.cells0 : Int) - (C.cells1 : Int) + (C.cells2 : Int)

def cwTotalCells (C : CWData) : Nat :=
  C.cells0 + C.cells1 + C.cells2 + C.cellsN

def cwSkeleton (C : CWData) (k : Nat) : Nat :=
  if k == 0 then C.cells0
  else if k == 1 then C.cells0 + C.cells1
  else if k == 2 then C.cells0 + C.cells1 + C.cells2
  else cwTotalCells C

def cwEuler_def (C : CWData) :
    Path (cwEuler C) ((C.cells0 : Int) - (C.cells1 : Int) + (C.cells2 : Int)) :=
  Path.refl _

def cwTotalCells_def (C : CWData) :
    Path (cwTotalCells C) (C.cells0 + C.cells1 + C.cells2 + C.cellsN) :=
  Path.refl _

def cwSkeleton_zero (C : CWData) :
    Path (cwSkeleton C 0) C.cells0 :=
  Path.refl _

def cwTotalCells_congr (C D : CWData) (p : Path C D) :
    Path (cwTotalCells C) (cwTotalCells D) :=
  Path.congrArg cwTotalCells p

def cwEuler_congr (C D : CWData) (p : Path C D) :
    Path (cwEuler C) (cwEuler D) :=
  Path.congrArg cwEuler p

/-! ## Cellular chain complex -/

structure CellChain where
  degree : Nat
  rank : Nat
  boundaryRank : Nat
  cycleRank : Nat

def homologyRank (Ch : CellChain) : Nat :=
  Ch.cycleRank - Ch.boundaryRank

def chainIndex (Ch : CellChain) : Nat :=
  Ch.degree + Ch.rank

def homologyRank_def (Ch : CellChain) :
    Path (homologyRank Ch) (Ch.cycleRank - Ch.boundaryRank) :=
  Path.refl _

def chainIndex_def (Ch : CellChain) :
    Path (chainIndex Ch) (Ch.degree + Ch.rank) :=
  Path.refl _

def homologyRank_congr (A B : CellChain) (p : Path A B) :
    Path (homologyRank A) (homologyRank B) :=
  Path.congrArg homologyRank p

def chainIndex_congr (A B : CellChain) (p : Path A B) :
    Path (chainIndex A) (chainIndex B) :=
  Path.congrArg chainIndex p

/-! ## Mayer-Vietoris decomposition -/

structure MayerVietoris where
  rankA : Nat
  rankB : Nat
  rankAB : Nat
  rankUnion : Nat
  degree : Nat

def mvConnecting (M : MayerVietoris) : Nat :=
  M.rankA + M.rankB - M.rankAB

def mvExactness (M : MayerVietoris) : Nat :=
  M.rankA + M.rankB + M.rankAB + M.rankUnion

def mvConnecting_def (M : MayerVietoris) :
    Path (mvConnecting M) (M.rankA + M.rankB - M.rankAB) :=
  Path.refl _

def mvExactness_def (M : MayerVietoris) :
    Path (mvExactness M) (M.rankA + M.rankB + M.rankAB + M.rankUnion) :=
  Path.refl _

def mvConnecting_congr (A B : MayerVietoris) (p : Path A B) :
    Path (mvConnecting A) (mvConnecting B) :=
  Path.congrArg mvConnecting p

def mvExactness_congr (A B : MayerVietoris) (p : Path A B) :
    Path (mvExactness A) (mvExactness B) :=
  Path.congrArg mvExactness p

/-! ## Excision encoding -/

structure ExcisionData where
  spaceRank : Nat
  subspaceRank : Nat
  excisedRank : Nat
  quotientRank : Nat

def excisionIndex (E : ExcisionData) : Nat :=
  E.spaceRank + E.subspaceRank + E.excisedRank

def excisionValid (E : ExcisionData) : Bool :=
  E.excisedRank ≤ E.subspaceRank

def excisionIndex_def (E : ExcisionData) :
    Path (excisionIndex E) (E.spaceRank + E.subspaceRank + E.excisedRank) :=
  Path.refl _

def excisionIndex_congr (A B : ExcisionData) (p : Path A B) :
    Path (excisionIndex A) (excisionIndex B) :=
  Path.congrArg excisionIndex p

/-! ## Hurewicz map profile -/

structure HurewiczProfile where
  homotopyRank : Nat
  homologyRank : Nat
  connectivity : Nat
  mapDegree : Nat

def hurewiczIndex (H : HurewiczProfile) : Nat :=
  H.homotopyRank + H.homologyRank + H.connectivity

def hurewiczIsIso (H : HurewiczProfile) : Bool :=
  H.homotopyRank == H.homologyRank && H.connectivity > 0

def hurewiczIndex_def (H : HurewiczProfile) :
    Path (hurewiczIndex H) (H.homotopyRank + H.homologyRank + H.connectivity) :=
  Path.refl _

def hurewiczIndex_congr (A B : HurewiczProfile) (p : Path A B) :
    Path (hurewiczIndex A) (hurewiczIndex B) :=
  Path.congrArg hurewiczIndex p

/-! ## Universal coefficients -/

structure UnivCoeffData where
  freeRank : Nat
  torsionRank : Nat
  extRank : Nat
  degree : Nat
  Sym : Nat
  Gam : Nat

def ucHomology (U : UnivCoeffData) : Nat :=
  U.freeRank + U.torsionRank

def ucCohomology (U : UnivCoeffData) : Nat :=
  U.freeRank + U.extRank

def ucIndex (U : UnivCoeffData) : Nat :=
  U.freeRank + U.torsionRank + U.extRank + U.Sym + U.Gam

def ucHomology_def (U : UnivCoeffData) :
    Path (ucHomology U) (U.freeRank + U.torsionRank) :=
  Path.refl _

def ucCohomology_def (U : UnivCoeffData) :
    Path (ucCohomology U) (U.freeRank + U.extRank) :=
  Path.refl _

def ucIndex_def (U : UnivCoeffData) :
    Path (ucIndex U) (U.freeRank + U.torsionRank + U.extRank + U.Sym + U.Gam) :=
  Path.refl _

def ucHomology_congr (A B : UnivCoeffData) (p : Path A B) :
    Path (ucHomology A) (ucHomology B) :=
  Path.congrArg ucHomology p

def ucCohomology_congr (A B : UnivCoeffData) (p : Path A B) :
    Path (ucCohomology A) (ucCohomology B) :=
  Path.congrArg ucCohomology p

def ucIndex_congr (A B : UnivCoeffData) (p : Path A B) :
    Path (ucIndex A) (ucIndex B) :=
  Path.congrArg ucIndex p

/-! ## Cup product structure -/

structure CupProductData where
  degreeA : Nat
  degreeB : Nat
  productDegree : Nat
  coeffRank : Nat

def cupDegreeSum (C : CupProductData) : Nat :=
  C.degreeA + C.degreeB

def cupGraded (C : CupProductData) : Bool :=
  C.productDegree == C.degreeA + C.degreeB

def cupDegreeSum_def (C : CupProductData) :
    Path (cupDegreeSum C) (C.degreeA + C.degreeB) :=
  Path.refl _

def cupDegreeSum_congr (A B : CupProductData) (p : Path A B) :
    Path (cupDegreeSum A) (cupDegreeSum B) :=
  Path.congrArg cupDegreeSum p

def cupCommutativity (a b : Nat) :
    Path (a + b) (b + a) :=
  Path.congrArg id (Nat.add_comm a b ▸ Path.refl (a + b))

/-! ## Poincaré duality profiles -/

structure PoincareDuality where
  manifoldDim : Nat
  degree : Nat
  dualDegree : Nat
  orientable : Bool

def pdDualSum (P : PoincareDuality) : Nat :=
  P.degree + P.dualDegree

def pdIsValid (P : PoincareDuality) : Bool :=
  P.degree + P.dualDegree == P.manifoldDim

def pdFlip (P : PoincareDuality) : PoincareDuality where
  manifoldDim := P.manifoldDim
  degree := P.dualDegree
  dualDegree := P.degree
  orientable := P.orientable

def pdDualSum_def (P : PoincareDuality) :
    Path (pdDualSum P) (P.degree + P.dualDegree) :=
  Path.refl _

def pdFlip_dim (P : PoincareDuality) :
    Path (pdFlip P).manifoldDim P.manifoldDim :=
  Path.refl _

def pdFlip_degree (P : PoincareDuality) :
    Path (pdFlip P).degree P.dualDegree :=
  Path.refl _

def pdFlip_dualDegree (P : PoincareDuality) :
    Path (pdFlip P).dualDegree P.degree :=
  Path.refl _

def pdFlip_orientable (P : PoincareDuality) :
    Path (pdFlip P).orientable P.orientable :=
  Path.refl _

def pdFlip_involutive (P : PoincareDuality) :
    Path (pdFlip (pdFlip P)) P := by
  cases P; exact Path.refl _

def pdDualSum_flip (P : PoincareDuality) :
    Path (pdDualSum (pdFlip P)) (P.dualDegree + P.degree) :=
  Path.refl _

def pdFlip_congr (A B : PoincareDuality) (p : Path A B) :
    Path (pdFlip A) (pdFlip B) :=
  Path.congrArg pdFlip p

/-! ## Eilenberg-MacLane space encoding -/

structure EilenbergMacLane where
  groupRank : Nat
  spaceDim : Nat
  homotopyLevel : Nat
  Sym : Nat
  Gam : Nat

def emIndex (E : EilenbergMacLane) : Nat :=
  E.groupRank + E.spaceDim + E.homotopyLevel + E.Sym + E.Gam

def emShift (E : EilenbergMacLane) (k : Nat) : EilenbergMacLane where
  groupRank := E.groupRank
  spaceDim := E.spaceDim + k
  homotopyLevel := E.homotopyLevel + k
  Sym := E.Sym
  Gam := E.Gam

def emIndex_def (E : EilenbergMacLane) :
    Path (emIndex E) (E.groupRank + E.spaceDim + E.homotopyLevel + E.Sym + E.Gam) :=
  Path.refl _

def emShift_groupRank (E : EilenbergMacLane) (k : Nat) :
    Path (emShift E k).groupRank E.groupRank :=
  Path.refl _

def emShift_spaceDim (E : EilenbergMacLane) (k : Nat) :
    Path (emShift E k).spaceDim (E.spaceDim + k) :=
  Path.refl _

def emShift_homotopyLevel (E : EilenbergMacLane) (k : Nat) :
    Path (emShift E k).homotopyLevel (E.homotopyLevel + k) :=
  Path.refl _

def emShift_Sym (E : EilenbergMacLane) (k : Nat) :
    Path (emShift E k).Sym E.Sym :=
  Path.refl _

def emShift_Gam (E : EilenbergMacLane) (k : Nat) :
    Path (emShift E k).Gam E.Gam :=
  Path.refl _

def emIndex_congr (A B : EilenbergMacLane) (p : Path A B) :
    Path (emIndex A) (emIndex B) :=
  Path.congrArg emIndex p

def emShift_congr (A B : EilenbergMacLane) (k : Nat) (p : Path A B) :
    Path (emShift A k) (emShift B k) :=
  Path.congrArg (fun e => emShift e k) p

/-! ## Obstruction theory states -/

structure ObstructionState where
  targetDim : Nat
  obstructionDegree : Nat
  cohomologyRank : Nat
  extensionPossible : Bool

def obstructionIndex (O : ObstructionState) : Nat :=
  O.targetDim + O.obstructionDegree + O.cohomologyRank

def obstructionStep (O : ObstructionState) : ObstructionState where
  targetDim := O.targetDim
  obstructionDegree := O.obstructionDegree + 1
  cohomologyRank := O.cohomologyRank
  extensionPossible := O.extensionPossible

def obstructionIndex_def (O : ObstructionState) :
    Path (obstructionIndex O) (O.targetDim + O.obstructionDegree + O.cohomologyRank) :=
  Path.refl _

def obstructionStep_degree (O : ObstructionState) :
    Path (obstructionStep O).obstructionDegree (O.obstructionDegree + 1) :=
  Path.refl _

def obstructionStep_targetDim (O : ObstructionState) :
    Path (obstructionStep O).targetDim O.targetDim :=
  Path.refl _

def obstructionStep_cohomology (O : ObstructionState) :
    Path (obstructionStep O).cohomologyRank O.cohomologyRank :=
  Path.refl _

def obstructionStep_extension (O : ObstructionState) :
    Path (obstructionStep O).extensionPossible O.extensionPossible :=
  Path.refl _

def obstructionIndex_step (O : ObstructionState) :
    Path (obstructionIndex (obstructionStep O))
      (O.targetDim + (O.obstructionDegree + 1) + O.cohomologyRank) :=
  Path.refl _

def obstructionIndex_congr (A B : ObstructionState) (p : Path A B) :
    Path (obstructionIndex A) (obstructionIndex B) :=
  Path.congrArg obstructionIndex p

def obstructionStep_congr (A B : ObstructionState) (p : Path A B) :
    Path (obstructionStep A) (obstructionStep B) :=
  Path.congrArg obstructionStep p

/-! ## Cross-domain path compositions -/

def cw_to_chain (C : CWData) : CellChain where
  degree := C.dim
  rank := C.cells0 + C.cells1
  boundaryRank := C.cells1
  cycleRank := C.cells0

def cw_to_chain_degree (C : CWData) :
    Path (cw_to_chain C).degree C.dim :=
  Path.refl _

def cw_to_chain_rank (C : CWData) :
    Path (cw_to_chain C).rank (C.cells0 + C.cells1) :=
  Path.refl _

def cw_to_chain_homology (C : CWData) :
    Path (homologyRank (cw_to_chain C)) (C.cells0 - C.cells1) :=
  Path.refl _

def cw_to_chain_congr (A B : CWData) (p : Path A B) :
    Path (cw_to_chain A) (cw_to_chain B) :=
  Path.congrArg cw_to_chain p

/-! ## Composition coherence lemmas -/

def pdFlip_dualSum_comm (P : PoincareDuality) :
    Path (pdDualSum (pdFlip (pdFlip P))) (pdDualSum P) :=
  Path.congrArg pdDualSum (pdFlip_involutive P)

def emShift_zero (E : EilenbergMacLane) :
    Path (emShift E 0) E := by
  cases E; exact Path.refl _

def obstruction_double_step_degree (O : ObstructionState) :
    Path (obstructionStep (obstructionStep O)).obstructionDegree
      (O.obstructionDegree + 2) :=
  Path.refl _

def mv_symmetry (M : MayerVietoris) : MayerVietoris where
  rankA := M.rankB
  rankB := M.rankA
  rankAB := M.rankAB
  rankUnion := M.rankUnion
  degree := M.degree

def mv_symmetry_involutive (M : MayerVietoris) :
    Path (mv_symmetry (mv_symmetry M)) M := by
  cases M; exact Path.refl _

def mv_symmetry_connecting (M : MayerVietoris) :
    Path (mvConnecting (mv_symmetry M)) (M.rankB + M.rankA - M.rankAB) :=
  Path.refl _

def mv_symmetry_congr (A B : MayerVietoris) (p : Path A B) :
    Path (mv_symmetry A) (mv_symmetry B) :=
  Path.congrArg mv_symmetry p

/-! ## Path chain examples -/

def excision_chain (E : ExcisionData) :
    Path (excisionIndex E) (E.spaceRank + E.subspaceRank + E.excisedRank) :=
  Path.trans (excisionIndex_def E) (Path.refl _)

def hurewicz_chain (H : HurewiczProfile) :
    Path (hurewiczIndex H) (H.homotopyRank + H.homologyRank + H.connectivity) :=
  Path.trans (hurewiczIndex_def H) (Path.refl _)

def uc_chain (U : UnivCoeffData) :
    Path (ucHomology U) (U.freeRank + U.torsionRank) :=
  Path.trans (ucHomology_def U) (Path.refl _)

def pd_chain (P : PoincareDuality) :
    Path (pdDualSum (pdFlip (pdFlip P))) (pdDualSum P) :=
  Path.trans (pdFlip_dualSum_comm P) (Path.refl _)

def em_chain (E : EilenbergMacLane) :
    Path (emShift E 0) E :=
  emShift_zero E

/-! ## Additional path algebra -/

def cwTotalCells_zero :
    Path (cwTotalCells ⟨0, 0, 0, 0, 0, 0, 0⟩) 0 :=
  Path.refl _

def excisionIndex_zero :
    Path (excisionIndex ⟨0, 0, 0, 0⟩) 0 :=
  Path.refl _

def hurewiczIndex_zero :
    Path (hurewiczIndex ⟨0, 0, 0, 0⟩) 0 :=
  Path.refl _

def ucHomology_zero :
    Path (ucHomology ⟨0, 0, 0, 0, 0, 0⟩) 0 :=
  Path.refl _

def ucCohomology_zero :
    Path (ucCohomology ⟨0, 0, 0, 0, 0, 0⟩) 0 :=
  Path.refl _

def emIndex_zero :
    Path (emIndex ⟨0, 0, 0, 0, 0⟩) 0 :=
  Path.refl _

def obstructionIndex_zero :
    Path (obstructionIndex ⟨0, 0, 0, true⟩) 0 :=
  Path.refl _

def pdDualSum_zero :
    Path (pdDualSum ⟨0, 0, 0, true⟩) 0 :=
  Path.refl _

def mvConnecting_zero :
    Path (mvConnecting ⟨0, 0, 0, 0, 0⟩) 0 :=
  Path.refl _

def chainIndex_zero :
    Path (chainIndex ⟨0, 0, 0, 0⟩) 0 :=
  Path.refl _

end ComputationalPaths.Path.Algebra.AlgebraicTopologyDeep
