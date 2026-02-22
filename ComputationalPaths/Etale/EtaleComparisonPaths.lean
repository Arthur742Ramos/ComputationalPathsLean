import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Etale.EtaleSitePaths

/-!
# Etale cohomology paths: comparison theorems

This module packages etale/singular comparison data as path-preserving
constructions over the etale-site interface.
-/

namespace ComputationalPaths
namespace Etale
namespace EtaleComparisonPaths

open Path
open EtaleSitePaths

universe u v

/-- Domain-specific rewrite tags for etale comparison coherence moves. -/
inductive EtaleComparisonStep : Type
  | naturality
  | mapTransport
  | comparisonUnit

/-- Path-preserving comparison package between etale and singular cohomology. -/
structure EtaleComparisonPathData {Obj Cover : Type u}
    (S : EtaleSitePathData Obj Cover) (Coeff : Type v) where
  etaleCohomology : Nat → Obj → Coeff
  singularCohomology : Nat → Obj → Coeff
  etaleMap :
    {U V : Obj} → Path U V → (n : Nat) →
      Path (etaleCohomology n U) (etaleCohomology n V)
  singularMap :
    {U V : Obj} → Path U V → (n : Nat) →
      Path (singularCohomology n U) (singularCohomology n V)
  comparisonPath :
    ∀ n : Nat, ∀ U : Obj,
      Path (etaleCohomology n U) (singularCohomology n U)
  comparisonNaturality :
    {U V : Obj} → (p : Path U V) → (n : Nat) →
      Path
        (Path.trans (comparisonPath n U) (singularMap p n))
        (Path.trans (etaleMap p n) (comparisonPath n V))

namespace EtaleComparisonPathData

variable {Obj Cover : Type u} {Coeff : Type v}
variable {S : EtaleSitePathData Obj Cover}
variable (C : EtaleComparisonPathData S Coeff)

/-- Comparison map transported along a base path using singular functoriality. -/
noncomputable def comparisonAlong {U V : Obj} (p : Path U V) (n : Nat) :
    Path (C.etaleCohomology n U) (C.singularCohomology n V) :=
  Path.trans (C.comparisonPath n U) (C.singularMap p n)

/-- Naturality path between the two comparison transports. -/
noncomputable def comparisonNaturalityAlong {U V : Obj} (p : Path U V) (n : Nat) :
    Path
      (C.comparisonAlong p n)
      (Path.trans (C.etaleMap p n) (C.comparisonPath n V)) :=
  C.comparisonNaturality p n

/-- Step witness: right-unit normalization for comparison maps. -/
noncomputable def comparison_step (n : Nat) (U : Obj) :
    Path.Step
      (Path.trans (C.comparisonPath n U)
        (Path.refl (C.singularCohomology n U)))
      (C.comparisonPath n U) :=
  Path.Step.trans_refl_right (C.comparisonPath n U)

noncomputable def comparison_rweq (n : Nat) (U : Obj) :
    RwEq
      (Path.trans (C.comparisonPath n U)
        (Path.refl (C.singularCohomology n U)))
      (C.comparisonPath n U) :=
  rweq_of_step (C.comparison_step n U)

/-- Step witness: right-unit normalization for transported comparison maps. -/
noncomputable def comparisonAlong_step {U V : Obj} (p : Path U V) (n : Nat) :
    Path.Step
      (Path.trans (C.comparisonAlong p n)
        (Path.refl (C.singularCohomology n V)))
      (C.comparisonAlong p n) :=
  Path.Step.trans_refl_right (C.comparisonAlong p n)

noncomputable def comparisonAlong_rweq {U V : Obj} (p : Path U V) (n : Nat) :
    RwEq
      (Path.trans (C.comparisonAlong p n)
        (Path.refl (C.singularCohomology n V)))
      (C.comparisonAlong p n) :=
  rweq_of_step (C.comparisonAlong_step p n)

noncomputable def comparisonAlong_cancel_rweq {U V : Obj} (p : Path U V) (n : Nat) :
    RwEq
      (Path.trans (Path.symm (C.comparisonAlong p n)) (C.comparisonAlong p n))
      (Path.refl (C.singularCohomology n V)) :=
  rweq_cmpA_inv_left (C.comparisonAlong p n)

/-- Step witness: right-unit normalization for naturality paths. -/
noncomputable def comparisonNaturality_step {U V : Obj} (p : Path U V) (n : Nat) :
    Path.Step
      (Path.trans (C.comparisonNaturalityAlong p n)
        (Path.refl (Path.trans (C.etaleMap p n) (C.comparisonPath n V))))
      (C.comparisonNaturalityAlong p n) :=
  Path.Step.trans_refl_right (C.comparisonNaturalityAlong p n)

noncomputable def comparisonNaturality_rweq {U V : Obj} (p : Path U V) (n : Nat) :
    RwEq
      (Path.trans (C.comparisonNaturalityAlong p n)
        (Path.refl (Path.trans (C.etaleMap p n) (C.comparisonPath n V))))
      (C.comparisonNaturalityAlong p n) :=
  rweq_of_step (C.comparisonNaturality_step p n)

end EtaleComparisonPathData

/-- Trivial comparison package over the trivial etale site. -/
noncomputable def trivialEtaleComparisonPathData :
    EtaleComparisonPathData EtaleSitePaths.trivialEtaleSitePathData Nat where
  etaleCohomology := fun _ _ => 0
  singularCohomology := fun _ _ => 0
  etaleMap := fun _ _ => Path.refl 0
  singularMap := fun _ _ => Path.refl 0
  comparisonPath := fun _ _ => Path.refl 0
  comparisonNaturality := fun _ _ =>
    Path.refl (Path.trans (Path.refl 0) (Path.refl 0))

end EtaleComparisonPaths
end Etale
end ComputationalPaths
