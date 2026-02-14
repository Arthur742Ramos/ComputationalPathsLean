/- Root import for crystalline cohomology path infrastructure modules. -/

import ComputationalPaths.Crystalline.DeRhamWittPaths
import ComputationalPaths.Crystalline.CrystallineComparisonPaths

namespace ComputationalPaths
namespace Crystalline

open Path
open DeRhamWittPaths
open CrystallineComparisonPaths

universe u v

/-- Unified path infrastructure for de Rham-Witt and crystalline comparison data. -/
structure CrystallinePathInfrastructure (Ring : Type u) (X : Type v) where
  deRhamWitt : DeRhamWittPathData Ring
  comparison : CrystallineComparisonPathData deRhamWitt X
  /-- Primitive right-unit witness on the degree-0 comparison map. -/
  unitComparisonStep :
    ∀ x : X,
      Path.Step
        (Path.trans (comparison.comparisonPath 0 x)
          (Path.refl (comparison.deRhamWittClass 0 x)))
        (comparison.comparisonPath 0 x)

namespace CrystallinePathInfrastructure

variable {Ring : Type u} {X : Type v}
variable (I : CrystallinePathInfrastructure Ring X)

@[simp] theorem unitComparison_rweq (x : X) :
    RwEq
      (Path.trans (I.comparison.comparisonPath 0 x)
        (Path.refl (I.comparison.deRhamWittClass 0 x)))
      (I.comparison.comparisonPath 0 x) :=
  rweq_of_step (I.unitComparisonStep x)

/-- Trivial crystalline path infrastructure on `PUnit`. -/
def trivial (Ring : Type u) : CrystallinePathInfrastructure Ring PUnit where
  deRhamWitt := DeRhamWittPaths.trivialDeRhamWittPathData Ring
  comparison := CrystallineComparisonPaths.trivialCrystallineComparisonPathData Ring
  unitComparisonStep := fun _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)

end CrystallinePathInfrastructure

end Crystalline
end ComputationalPaths
