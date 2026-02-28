/- 
# Tropical geometry paths: valuations

This module packages valuation and tropicalization data with explicit
`Path.Step` witnesses and derived `RwEq` coherence lemmas.
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Tropical.TropicalCurvesPaths

namespace ComputationalPaths
namespace Tropical

open Path

universe u v

/-- Valuation package used to tropicalize algebraic data. -/
structure ValuationPathData (K : Type u) (Γ : Type v) where
  zeroK : K
  addK : K → K → K
  mulK : K → K → K
  val : K → Γ
  tropAdd : Γ → Γ → Γ
  tropMul : Γ → Γ → Γ
  mulValPath :
    ∀ x y : K,
      Path (val (mulK x y)) (tropMul (val x) (val y))
  mulValStep :
    ∀ x y : K,
      Path.Step
        (Path.trans (mulValPath x y) (Path.refl (tropMul (val x) (val y))))
        (mulValPath x y)
  addValPath :
    ∀ x y : K,
      Path (val (addK x y)) (tropAdd (val x) (val y))
  addValStep :
    ∀ x y : K,
      Path.Step
        (Path.trans (Path.refl (val (addK x y))) (addValPath x y))
        (addValPath x y)

namespace ValuationPathData

variable {K : Type u} {Γ : Type v} (V : ValuationPathData K Γ)

noncomputable def mul_val_rweq (x y : K) :
    RwEq
      (Path.trans (V.mulValPath x y)
        (Path.refl (V.tropMul (V.val x) (V.val y))))
      (V.mulValPath x y) :=
  rweq_of_step (V.mulValStep x y)

noncomputable def add_val_rweq (x y : K) :
    RwEq
      (Path.trans (Path.refl (V.val (V.addK x y))) (V.addValPath x y))
      (V.addValPath x y) :=
  rweq_of_step (V.addValStep x y)

noncomputable def add_val_cancel_rweq (x y : K) :
    RwEq
      (Path.trans (Path.symm (V.addValPath x y)) (V.addValPath x y))
      (Path.refl (V.tropAdd (V.val x) (V.val y))) :=
  rweq_cmpA_inv_left (V.addValPath x y)

noncomputable def mul_val_cancel_left_rweq (x y : K) :
    RwEq
      (Path.trans (Path.symm (V.mulValPath x y)) (V.mulValPath x y))
      (Path.refl (V.tropMul (V.val x) (V.val y))) :=
  rweq_cmpA_inv_left (V.mulValPath x y)

noncomputable def mul_val_cancel_right_rweq (x y : K) :
    RwEq
      (Path.trans (V.mulValPath x y) (Path.symm (V.mulValPath x y)))
      (Path.refl (V.val (V.mulK x y))) :=
  rweq_cmpA_inv_right (V.mulValPath x y)

end ValuationPathData

/-- Tropicalization data linking curve edges with valuation values. -/
structure TropicalizationPathData
    {Vertex Edge K : Type u} {Γ : Type v}
    (C : TropicalCurvePathData Vertex Edge) (V : ValuationPathData K Γ) where
  edgeLabel : Edge → K
  tropicalLength : Edge → Γ
  tropicalLengthPath :
    ∀ e : Edge, Path (V.val (edgeLabel e)) (tropicalLength e)
  tropicalLengthStep :
    ∀ e : Edge,
      Path.Step
        (Path.trans (tropicalLengthPath e) (Path.refl (tropicalLength e)))
        (tropicalLengthPath e)

namespace TropicalizationPathData

variable {Vertex Edge K : Type u} {Γ : Type v}
variable {C : TropicalCurvePathData Vertex Edge}
variable {V : ValuationPathData K Γ}
variable (T : TropicalizationPathData C V)

noncomputable def tropical_length_rweq (e : Edge) :
    RwEq
      (Path.trans (T.tropicalLengthPath e) (Path.refl (T.tropicalLength e)))
      (T.tropicalLengthPath e) :=
  rweq_of_step (T.tropicalLengthStep e)

noncomputable def tropical_length_cancel_rweq (e : Edge) :
    RwEq
      (Path.trans (Path.symm (T.tropicalLengthPath e)) (T.tropicalLengthPath e))
      (Path.refl (T.tropicalLength e)) :=
  rweq_cmpA_inv_left (T.tropicalLengthPath e)

noncomputable def tropical_length_roundtrip_rweq (e : Edge) :
    RwEq
      (Path.trans (T.tropicalLengthPath e) (Path.symm (T.tropicalLengthPath e)))
      (Path.refl (V.val (T.edgeLabel e))) :=
  rweq_cmpA_inv_right (T.tropicalLengthPath e)

end TropicalizationPathData

/-- Trivial valuation package to instantiate the tropical path interface. -/
noncomputable def trivialValuationPathData : ValuationPathData PUnit Nat where
  zeroK := PUnit.unit
  addK := fun _ _ => PUnit.unit
  mulK := fun _ _ => PUnit.unit
  val := fun _ => 0
  tropAdd := fun x y => x + y
  tropMul := fun x y => x + y
  mulValPath := fun _ _ => Path.refl 0
  mulValStep := fun _ _ => Path.Step.trans_refl_right (Path.refl 0)
  addValPath := fun _ _ => Path.refl 0
  addValStep := fun _ _ => Path.Step.trans_refl_left (Path.refl 0)

/-- Trivial tropicalization from the trivial curve and valuation packages. -/
noncomputable def trivialTropicalizationPathData :
    TropicalizationPathData trivialTropicalCurvePathData trivialValuationPathData where
  edgeLabel := fun _ => PUnit.unit
  tropicalLength := fun _ => 0
  tropicalLengthPath := fun _ => Path.refl 0
  tropicalLengthStep := fun _ => Path.Step.trans_refl_right (Path.refl 0)

end Tropical
end ComputationalPaths
