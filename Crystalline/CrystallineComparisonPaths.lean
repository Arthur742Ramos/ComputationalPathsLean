import ComputationalPaths.Path.Rewrite.RwEq
import Crystalline.DeRhamWittPaths

/-!
# Crystalline cohomology paths: crystalline comparison

This module packages comparison maps from crystalline cohomology to the
de Rham-Witt complex with explicit computational-path witnesses.
-/

namespace ComputationalPaths
namespace Crystalline
namespace CrystallineComparisonPaths

open Path
open DeRhamWittPaths

universe u v

/-- Domain-specific rewrite tags for crystalline comparison coherence moves. -/
inductive CrystallineComparisonStep : Type
  | naturality
  | frobeniusCompatibility
  | filtrationCompatibility

/-- Path-preserving crystalline/de Rham-Witt comparison package. -/
structure CrystallineComparisonPathData {Ring : Type u}
    (W : DeRhamWittPathData Ring) (X : Type v) where
  crystallineClass : Nat → X → W.level 1
  deRhamWittClass : Nat → X → W.level 1
  crystallineMap :
    {x y : X} → Path x y → (n : Nat) →
      Path (crystallineClass n x) (crystallineClass n y)
  deRhamWittMap :
    {x y : X} → Path x y → (n : Nat) →
      Path (deRhamWittClass n x) (deRhamWittClass n y)
  comparisonPath :
    ∀ n : Nat, ∀ x : X,
      Path (crystallineClass n x) (deRhamWittClass n x)
  comparisonNaturality :
    {x y : X} → (p : Path x y) → (n : Nat) →
      Path
        (Path.trans (comparisonPath n x) (deRhamWittMap p n))
        (Path.trans (crystallineMap p n) (comparisonPath n y))

namespace CrystallineComparisonPathData

variable {Ring : Type u} {X : Type v}
variable {W : DeRhamWittPathData Ring}
variable (C : CrystallineComparisonPathData W X)

/-- Comparison map transported along a base path. -/
def comparisonAlong {x y : X} (p : Path x y) (n : Nat) :
    Path (C.crystallineClass n x) (C.deRhamWittClass n y) :=
  Path.trans (C.comparisonPath n x) (C.deRhamWittMap p n)

/-- Naturality path between transported comparison maps. -/
def comparisonNaturalityAlong {x y : X} (p : Path x y) (n : Nat) :
    Path
      (C.comparisonAlong p n)
      (Path.trans (C.crystallineMap p n) (C.comparisonPath n y)) :=
  C.comparisonNaturality p n

/-- Frobenius transport of the crystalline comparison path. -/
def frobeniusComparison (n : Nat) (x : X) :
    Path
      (W.frobenius 0 (C.crystallineClass n x))
      (W.frobenius 0 (C.deRhamWittClass n x)) :=
  Path.congrArg (W.frobenius 0) (C.comparisonPath n x)

/-- Step witness: right-unit normalization for comparison paths. -/
def comparison_step (n : Nat) (x : X) :
    Path.Step
      (Path.trans (C.comparisonPath n x) (Path.refl (C.deRhamWittClass n x)))
      (C.comparisonPath n x) :=
  Path.Step.trans_refl_right (C.comparisonPath n x)

@[simp] theorem comparison_rweq (n : Nat) (x : X) :
    RwEq
      (Path.trans (C.comparisonPath n x) (Path.refl (C.deRhamWittClass n x)))
      (C.comparisonPath n x) :=
  rweq_of_step (C.comparison_step n x)

/-- Step witness: right-unit normalization for transported comparisons. -/
def comparisonAlong_step {x y : X} (p : Path x y) (n : Nat) :
    Path.Step
      (Path.trans (C.comparisonAlong p n) (Path.refl (C.deRhamWittClass n y)))
      (C.comparisonAlong p n) :=
  Path.Step.trans_refl_right (C.comparisonAlong p n)

@[simp] theorem comparisonAlong_rweq {x y : X} (p : Path x y) (n : Nat) :
    RwEq
      (Path.trans (C.comparisonAlong p n) (Path.refl (C.deRhamWittClass n y)))
      (C.comparisonAlong p n) :=
  rweq_of_step (C.comparisonAlong_step p n)

@[simp] theorem comparisonAlong_cancel_rweq {x y : X} (p : Path x y) (n : Nat) :
    RwEq
      (Path.trans (Path.symm (C.comparisonAlong p n)) (C.comparisonAlong p n))
      (Path.refl (C.deRhamWittClass n y)) :=
  rweq_cmpA_inv_left (C.comparisonAlong p n)

/-- Step witness: right-unit normalization for naturality paths. -/
def comparisonNaturality_step {x y : X} (p : Path x y) (n : Nat) :
    Path.Step
      (Path.trans (C.comparisonNaturalityAlong p n)
        (Path.refl (Path.trans (C.crystallineMap p n) (C.comparisonPath n y))))
      (C.comparisonNaturalityAlong p n) :=
  Path.Step.trans_refl_right (C.comparisonNaturalityAlong p n)

@[simp] theorem comparisonNaturality_rweq {x y : X} (p : Path x y) (n : Nat) :
    RwEq
      (Path.trans (C.comparisonNaturalityAlong p n)
        (Path.refl (Path.trans (C.crystallineMap p n) (C.comparisonPath n y))))
      (C.comparisonNaturalityAlong p n) :=
  rweq_of_step (C.comparisonNaturality_step p n)

/-- Step witness: right-unit normalization for Frobenius compatibility transport. -/
def frobeniusComparison_step (n : Nat) (x : X) :
    Path.Step
      (Path.trans (C.frobeniusComparison n x)
        (Path.refl (W.frobenius 0 (C.deRhamWittClass n x))))
      (C.frobeniusComparison n x) :=
  Path.Step.trans_refl_right (C.frobeniusComparison n x)

@[simp] theorem frobeniusComparison_rweq (n : Nat) (x : X) :
    RwEq
      (Path.trans (C.frobeniusComparison n x)
        (Path.refl (W.frobenius 0 (C.deRhamWittClass n x))))
      (C.frobeniusComparison n x) :=
  rweq_of_step (C.frobeniusComparison_step n x)

end CrystallineComparisonPathData

/-- Trivial crystalline comparison package over the trivial de Rham-Witt model. -/
def trivialCrystallineComparisonPathData (Ring : Type u) :
    CrystallineComparisonPathData
      (W := DeRhamWittPaths.trivialDeRhamWittPathData Ring) PUnit where
  crystallineClass := fun _ _ => PUnit.unit
  deRhamWittClass := fun _ _ => PUnit.unit
  crystallineMap := fun _ _ => Path.refl PUnit.unit
  deRhamWittMap := fun _ _ => Path.refl PUnit.unit
  comparisonPath := fun _ _ => Path.refl PUnit.unit
  comparisonNaturality := fun _ _ =>
    Path.refl (Path.trans (Path.refl PUnit.unit) (Path.refl PUnit.unit))

end CrystallineComparisonPaths
end Crystalline
end ComputationalPaths
