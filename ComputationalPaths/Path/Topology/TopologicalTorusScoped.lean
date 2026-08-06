import ComputationalPaths.Path.CompPath.CircleTopologicalRealization

/-!
# The actual topological torus in the scoped-path semantics

The torus is the product of two copies of the additive circle
`AddCircle (1 : ℝ)`.  This file records the product winding theorem for
ordinary interval paths.  It is deliberately separate from the older
synthetic `torusPiOne` carrier: the quotient here is the quotient of genuine
continuous torus loops by endpoint-fixed homotopy.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

namespace TopologicalTorus

open ComputationalPaths.Path.CompPath
open ComputationalPaths.Path.CompPath.CircleTopologicalRealization

attribute [local instance] _root_.Path.Homotopic.setoid

abbrev Carrier : Type := TopologicalCircle × TopologicalCircle

noncomputable abbrev base : Carrier := (0, 0)

abbrev Loop : Type := _root_.Path base base

noncomputable def coordinateFst (γ : Loop) :
    _root_.Path (0 : TopologicalCircle) 0 :=
  γ.map ContinuousMap.fst.continuous

noncomputable def coordinateSnd (γ : Loop) :
    _root_.Path (0 : TopologicalCircle) 0 :=
  γ.map ContinuousMap.snd.continuous

noncomputable def standardLoop (m n : ℤ) : Loop :=
  (CircleTopologicalRealization.standardLoop m).prod
    (CircleTopologicalRealization.standardLoop n)

noncomputable def winding (γ : Loop) : ℤ × ℤ :=
  (windingPath (coordinateFst γ), windingPath (coordinateSnd γ))

theorem coordinateFst_standardLoop (m n : ℤ) :
    coordinateFst (standardLoop m n) =
      CircleTopologicalRealization.standardLoop m := by
  apply _root_.Path.ext
  funext t
  rfl

theorem coordinateSnd_standardLoop (m n : ℤ) :
    coordinateSnd (standardLoop m n) =
      CircleTopologicalRealization.standardLoop n := by
  apply _root_.Path.ext
  funext t
  rfl

@[simp] theorem winding_standardLoop (m n : ℤ) :
    winding (standardLoop m n) = (m, n) := by
  apply Prod.ext
  · change windingPath (coordinateFst (standardLoop m n)) = m
    rw [coordinateFst_standardLoop]
    exact windingPath_standardLoop m
  · change windingPath (coordinateSnd (standardLoop m n)) = n
    rw [coordinateSnd_standardLoop]
    exact windingPath_standardLoop n

theorem winding_eq_of_homotopic {γ δ : Loop}
    (h : γ.Homotopic δ) : winding γ = winding δ := by
  apply Prod.ext
  · exact windingPath_eq_of_homotopic (by
      simpa [coordinateFst] using h.map ContinuousMap.fst)
  · exact windingPath_eq_of_homotopic (by
      simpa [coordinateSnd] using h.map ContinuousMap.snd)

theorem coordinate_product_eq (γ : Loop) :
    (coordinateFst γ).prod (coordinateSnd γ) = γ := by
  apply _root_.Path.ext
  funext t
  rfl

theorem coordinateFst_trans (γ δ : Loop) :
    coordinateFst (γ.trans δ) = (coordinateFst γ).trans (coordinateFst δ) := by
  simp [coordinateFst]

theorem coordinateSnd_trans (γ δ : Loop) :
    coordinateSnd (γ.trans δ) = (coordinateSnd γ).trans (coordinateSnd δ) := by
  simp [coordinateSnd]

theorem winding_trans (γ δ : Loop) :
    winding (γ.trans δ) =
      ((winding γ).1 + (winding δ).1,
        (winding γ).2 + (winding δ).2) := by
  apply Prod.ext
  · change windingPath (coordinateFst (γ.trans δ)) = _
    rw [coordinateFst_trans, windingPath_trans]
    rfl
  · change windingPath (coordinateSnd (γ.trans δ)) = _
    rw [coordinateSnd_trans, windingPath_trans]
    rfl

noncomputable def firstFactorLoop (m : ℤ) : Loop :=
  (CircleTopologicalRealization.standardLoop m).prod
    (_root_.Path.refl (0 : TopologicalCircle))

noncomputable def secondFactorLoop (n : ℤ) : Loop :=
  (_root_.Path.refl (0 : TopologicalCircle)).prod
    (CircleTopologicalRealization.standardLoop n)

noncomputable def sequentialLoop (m n : ℤ) : Loop :=
  (firstFactorLoop m).trans (secondFactorLoop n)

theorem winding_firstFactorLoop (m : ℤ) :
    winding (firstFactorLoop m) = (m, 0) := by
  apply Prod.ext
  · change windingPath (coordinateFst (firstFactorLoop m)) = m
    rw [show coordinateFst (firstFactorLoop m) =
      CircleTopologicalRealization.standardLoop m by
        apply _root_.Path.ext
        funext t
        rfl]
    exact windingPath_standardLoop m
  · change windingPath (coordinateSnd (firstFactorLoop m)) = 0
    rw [show coordinateSnd (firstFactorLoop m) =
      _root_.Path.refl (0 : TopologicalCircle) by
        apply _root_.Path.ext
        funext t
        rfl]
    exact windingPath_refl

theorem winding_secondFactorLoop (n : ℤ) :
    winding (secondFactorLoop n) = (0, n) := by
  apply Prod.ext
  · change windingPath (coordinateFst (secondFactorLoop n)) = 0
    rw [show coordinateFst (secondFactorLoop n) =
      _root_.Path.refl (0 : TopologicalCircle) by
        apply _root_.Path.ext
        funext t
        rfl]
    exact windingPath_refl
  · change windingPath (coordinateSnd (secondFactorLoop n)) = n
    rw [show coordinateSnd (secondFactorLoop n) =
      CircleTopologicalRealization.standardLoop n by
        apply _root_.Path.ext
        funext t
        rfl]
    exact windingPath_standardLoop n

@[simp] theorem winding_sequentialLoop (m n : ℤ) :
    winding (sequentialLoop m n) = (m, n) := by
  rw [sequentialLoop, winding_trans, winding_firstFactorLoop,
    winding_secondFactorLoop]
  simp

theorem standardLoop_homotopic (γ : Loop) :
    (standardLoop (winding γ).1 (winding γ).2).Homotopic γ := by
  have hfst := CircleTopologicalRealization.standardLoop_homotopic
    (coordinateFst γ)
  have hsnd := CircleTopologicalRealization.standardLoop_homotopic
    (coordinateSnd γ)
  rcases hfst with ⟨hfst⟩
  rcases hsnd with ⟨hsnd⟩
  have hprod := _root_.Path.Homotopic.prodHomotopy hfst hsnd
  rw [coordinate_product_eq γ] at hprod
  exact ⟨hprod⟩

theorem standardLoop_homotopic_sequentialLoop (m n : ℤ) :
    (standardLoop m n).Homotopic (sequentialLoop m n) := by
  simpa only [winding_sequentialLoop] using
    (standardLoop_homotopic (sequentialLoop m n))

abbrev LoopQuot : Type :=
  _root_.Path.Homotopic.Quotient base base

noncomputable def encode : LoopQuot → ℤ × ℤ :=
  Quotient.lift winding (fun _ _ h => winding_eq_of_homotopic h)

noncomputable def decode (z : ℤ × ℤ) : LoopQuot :=
  Quotient.mk' (standardLoop z.1 z.2)

@[simp] theorem encode_decode (z : ℤ × ℤ) :
    encode (decode z) = z := by
  change winding (standardLoop z.1 z.2) = z
  exact winding_standardLoop z.1 z.2

theorem decode_encode (x : LoopQuot) :
    decode (encode x) = x := by
  refine Quotient.inductionOn x ?_
  intro γ
  exact Quotient.sound (standardLoop_homotopic γ)

noncomputable def equivIntProd : LoopQuot ≃ (ℤ × ℤ) where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

/-! The product classification is retained as explicit computational data. -/

noncomputable def roundTripPath (x : LoopQuot) :
    ComputationalPaths.Path (decode (encode x)) x :=
  ComputationalPaths.Path.stepChain (decode_encode x)

noncomputable def productUnitRewrite :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl (0 : Nat))
        (ComputationalPaths.Path.refl 0))
      (ComputationalPaths.Path.refl 0) :=
  ComputationalPaths.Path.RwEq.step
    (ComputationalPaths.Path.Step.trans_refl_right
      (ComputationalPaths.Path.refl 0))

structure Certificate where
  winding_standard : ∀ m n : ℤ, winding (standardLoop m n) = (m, n)
  standard_representative : ∀ γ : Loop,
    (standardLoop (winding γ).1 (winding γ).2).Homotopic γ
  loop_equiv : LoopQuot ≃ (ℤ × ℤ)
  round_trip : ∀ x : LoopQuot, ComputationalPaths.Path (decode (encode x)) x

noncomputable def certificate : Certificate where
  winding_standard := winding_standardLoop
  standard_representative := standardLoop_homotopic
  loop_equiv := equivIntProd
  round_trip := roundTripPath

end TopologicalTorus
end GeometricTopology
end Path
end ComputationalPaths
