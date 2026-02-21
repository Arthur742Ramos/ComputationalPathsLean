/- 
# Tropical geometry paths: tropical curves

This module packages tropical-curve combinatorics with explicit `Path.Step`
witnesses and derived `RwEq` normalization lemmas.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Tropical

open Path

universe u

/-- Minimal tropical-curve data with balancing and cycle paths. -/
structure TropicalCurvePathData (Vertex Edge : Type u) where
  source : Edge → Vertex
  target : Edge → Vertex
  weight : Edge → Nat
  balancingIndex : Vertex → Nat
  balancingPath :
    ∀ v : Vertex,
      Path (balancingIndex v + balancingIndex v) (balancingIndex v + balancingIndex v)
  balancingStep :
    ∀ v : Vertex,
      Path.Step
        (Path.trans (balancingPath v)
          (Path.refl (balancingIndex v + balancingIndex v)))
        (balancingPath v)
  cyclePath :
    ∀ e : Edge, Path (source e) (target e)
  cycleStep :
    ∀ e : Edge,
      Path.Step
        (Path.trans (Path.refl (source e)) (cyclePath e))
        (cyclePath e)

namespace TropicalCurvePathData

variable {Vertex Edge : Type u} (C : TropicalCurvePathData Vertex Edge)

@[simp] theorem balancing_rweq (v : Vertex) :
    RwEq
      (Path.trans (C.balancingPath v)
        (Path.refl (C.balancingIndex v + C.balancingIndex v)))
      (C.balancingPath v) :=
  rweq_of_step (C.balancingStep v)

@[simp] theorem cycle_rweq (e : Edge) :
    RwEq
      (Path.trans (Path.refl (C.source e)) (C.cyclePath e))
      (C.cyclePath e) :=
  rweq_of_step (C.cycleStep e)

@[simp] theorem cycle_cancel_rweq (e : Edge) :
    RwEq
      (Path.trans (Path.symm (C.cyclePath e)) (C.cyclePath e))
      (Path.refl (C.target e)) :=
  rweq_cmpA_inv_left (C.cyclePath e)

end TropicalCurvePathData

/-- Trivial tropical-curve path package on `PUnit`. -/
def trivialTropicalCurvePathData : TropicalCurvePathData PUnit PUnit where
  source := fun _ => PUnit.unit
  target := fun _ => PUnit.unit
  weight := fun _ => 1
  balancingIndex := fun _ => 0
  balancingPath := fun _ => Path.refl 0
  balancingStep := fun _ => Path.Step.trans_refl_right (Path.refl 0)
  cyclePath := fun _ => Path.refl PUnit.unit
  cycleStep := fun _ => Path.Step.trans_refl_left (Path.refl PUnit.unit)

end Tropical
end ComputationalPaths
