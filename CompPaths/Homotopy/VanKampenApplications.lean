import CompPaths.Core
import ComputationalPaths.Path.Homotopy.SeifertVanKampen
import ComputationalPaths.Path.CompPath.FigureEightStep
import ComputationalPaths.Path.CompPath.KleinBottleStep
import ComputationalPaths.Path.CompPath.ProjectivePlaneStep

/-!
# Van Kampen applications in computational paths

This module packages three standard fundamental-group computations with explicit
path decompositions and `RwEq` identifications:

1. `π₁(S¹ ∨ S¹) = F₂` via the wedge-case van Kampen equivalence.
2. `π₁(Klein bottle)` via the relator decomposition `a b a⁻¹ b`.
3. `π₁(RP²)` via the order-two decomposition of the generator.
-/

namespace CompPaths
namespace Homotopy

open ComputationalPaths
open ComputationalPaths.Path
open ComputationalPaths.Path.CompPath

/-! ## π₁(S¹ ∨ S¹) = F₂ via van Kampen -/

/-- Free group on two generators, represented as free-product words. -/
abbrev FigureEightF2 : Type :=
  ComputationalPaths.Path.FigureEightFreeGroup

/-- van Kampen equivalence for the wedge of two circles. -/
noncomputable def figureEightPiOneEquivF2_vanKampen
    [HasWedgeSVKDecodeBijective Circle Circle circleBase circleBase] :
    SimpleEquiv FigureEight.FigureEightPiOne FigureEightF2 :=
  FigureEight.figureEightPiOneEquivFreeGroup

/-- Explicit loop decomposition `ab` in the figure-eight. -/
noncomputable def figureEightLoopABDecomposition :
    Path (A := FigureEight.FigureEight) FigureEight.base FigureEight.base :=
  Path.trans FigureEight.loopA FigureEight.loopB

theorem figureEightLoopABDecomposition_eq :
    figureEightLoopABDecomposition = FigureEight.loopAB :=
  rfl

/-- Explicit `RwEq` identification: `a · a⁻¹ ≈ refl`. -/
noncomputable def figureEightGeneratorCancelRwEq :
    RwEq (Path.trans FigureEight.loopA (Path.symm FigureEight.loopA))
      (Path.refl FigureEight.base) := by
  simpa [FigureEight.loopAInv] using FigureEight.loopA_inv_cancel

/-! ## π₁(Klein bottle) via van Kampen decomposition -/

/-- Relator decomposition `a b a⁻¹ b`. -/
noncomputable def kleinRelatorDecomposition :
    Path kleinBottleBase kleinBottleBase :=
  Path.trans (Path.trans (Path.trans kleinBottleLoopA kleinBottleLoopB)
    (Path.symm kleinBottleLoopA)) kleinBottleLoopB

theorem kleinRelatorDecomposition_eq :
    kleinRelatorDecomposition = KleinBottleStep.kleinRelatorWord :=
  rfl

/-- Explicit `RwEq` identification of a normalized relator expression. -/
noncomputable def kleinRelatorNormalizationRwEq :
    RwEq
      (Path.trans (Path.trans (Path.refl kleinBottleBase) kleinRelatorDecomposition)
        (Path.refl kleinBottleBase))
      kleinRelatorDecomposition := by
  simpa [kleinRelatorDecomposition] using KleinBottleStep.kleinRelatorNorm_rweq

/-- Explicit `RwEq` identification: `a · a⁻¹ ≈ refl`. -/
noncomputable def kleinGeneratorCancelRwEq :
    RwEq (Path.trans kleinBottleLoopA (Path.symm kleinBottleLoopA))
      (Path.refl kleinBottleBase) :=
  rweq_of_rw KleinBottleStep.kleinLoopA_cancel

/-- Computational model for the Klein bottle fundamental group. -/
noncomputable def kleinBottlePiOneEquiv_vanKampen :
    SimpleEquiv kleinBottlePiOne (Int × Int) :=
  kleinBottlePiOneEquivIntProd

/-! ## π₁(RP²) via van Kampen decomposition -/

abbrev rp2Basepoint : RealProjective2 :=
  ProjectivePlaneStep.rp2Base

/-- Explicit decomposition of the order-two generator as `loop · loop`. -/
noncomputable def rp2LoopSquaredDecomposition :
    Path (A := RealProjective2) rp2Basepoint rp2Basepoint :=
  Path.trans ProjectivePlaneStep.rp2Loop ProjectivePlaneStep.rp2Loop

theorem rp2LoopSquaredDecomposition_eq :
    rp2LoopSquaredDecomposition = ProjectivePlaneStep.rp2LoopSquared :=
  rfl

/-- Explicit `RwEq` identification from step normalization in RP². -/
noncomputable def rp2NormalizationRwEq :
    RwEq
      (Path.trans
        (Path.trans (Path.refl rp2Basepoint) ProjectivePlaneStep.rp2Loop)
        (Path.refl rp2Basepoint))
      ProjectivePlaneStep.rp2Loop := by
  simpa [rp2Basepoint] using ProjectivePlaneStep.rp2Normalization_rweq

/-- Explicit `RwEq` identification: `loop · loop⁻¹ ≈ refl`. -/
noncomputable def rp2GeneratorCancelRwEq :
    RwEq
      (Path.trans ProjectivePlaneStep.rp2Loop (Path.symm ProjectivePlaneStep.rp2Loop))
      (Path.refl rp2Basepoint) := by
  simpa [rp2Basepoint] using rweq_of_rw ProjectivePlaneStep.rp2LoopCancel

/-- Computational model for the RP² fundamental group. -/
noncomputable def rp2PiOneEquiv_vanKampen :
    SimpleEquiv rp2PiOne Z2 :=
  rp2PiOneEquivZ2

end Homotopy
end CompPaths
