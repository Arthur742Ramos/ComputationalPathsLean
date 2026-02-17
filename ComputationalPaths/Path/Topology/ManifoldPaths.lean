/-
# Manifold-like Structures via Computational Paths

Charts, atlas compatibility, transition maps as path equivalences,
tangent bundles, smooth maps preserving path structure.

## References

- Lee, "Introduction to Smooth Manifolds"
- Tu, "An Introduction to Manifolds"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Topology
namespace ManifoldPaths

universe u

/-! ## Model Space -/

/-- A model space. -/
structure ModelSpace where
  carrier : Type u
  origin : carrier
  dim : Nat

/-- A manifold: a space locally modeled on a model space. -/
structure Manifold where
  carrier : Type u
  model : ModelSpace
  basePoint : carrier

/-! ## Charts -/

/-- A chart: a pair of inverse maps (global for simplicity). -/
structure Chart (M : Manifold) where
  toModel : M.carrier → M.model.carrier
  fromModel : M.model.carrier → M.carrier
  left_inv : ∀ x, Path (fromModel (toModel x)) x
  right_inv : ∀ y, Path (toModel (fromModel y)) y

/-- The transition map between two charts. -/
def transitionMap {M : Manifold} (φ ψ : Chart M) : M.model.carrier → M.model.carrier :=
  fun y => ψ.toModel (φ.fromModel y)

/-- Transition map in the reverse direction. -/
def transitionMapInv {M : Manifold} (φ ψ : Chart M) : M.model.carrier → M.model.carrier :=
  transitionMap ψ φ

/-- transitionMapInv is definitionally transitionMap with swapped args. -/
theorem transitionMapInv_eq {M : Manifold} (φ ψ : Chart M) :
    transitionMapInv φ ψ = transitionMap ψ φ := rfl

/-- Transition map is left-invertible. -/
def transition_left_inv {M : Manifold} (φ ψ : Chart M) (y : M.model.carrier) :
    Path (transitionMapInv φ ψ (transitionMap φ ψ y)) y := by
  unfold transitionMap transitionMapInv
  exact Path.trans (Path.congrArg φ.toModel (ψ.left_inv (φ.fromModel y))) (φ.right_inv y)

/-- Transition map is right-invertible. -/
def transition_right_inv {M : Manifold} (φ ψ : Chart M) (y : M.model.carrier) :
    Path (transitionMap φ ψ (transitionMapInv φ ψ y)) y := by
  unfold transitionMap transitionMapInv
  exact Path.trans (Path.congrArg ψ.toModel (φ.left_inv (ψ.fromModel y))) (ψ.right_inv y)

/-- Transition from chart to itself is identity. -/
def transition_self {M : Manifold} (φ : Chart M) (y : M.model.carrier) :
    Path (transitionMap φ φ y) y := by
  unfold transitionMap
  exact φ.right_inv y

/-- Composition of transition maps (path version). -/
def transition_comp_path {M : Manifold} (φ ψ χ : Chart M) (y : M.model.carrier) :
    Path (transitionMap ψ χ (transitionMap φ ψ y))
         (transitionMap φ χ y) := by
  unfold transitionMap
  exact Path.congrArg χ.toModel (ψ.left_inv (φ.fromModel y))

/-- Chart from-to-from is from. -/
def chart_from_to_from {M : Manifold} (φ : Chart M) (y : M.model.carrier) :
    Path (φ.fromModel (φ.toModel (φ.fromModel y))) (φ.fromModel y) :=
  φ.left_inv (φ.fromModel y)

/-- Chart to-from-to is to. -/
def chart_to_from_to {M : Manifold} (φ : Chart M) (x : M.carrier) :
    Path (φ.toModel (φ.fromModel (φ.toModel x))) (φ.toModel x) :=
  Path.congrArg φ.toModel (φ.left_inv x)

/-! ## Atlas -/

/-- An atlas: a nonempty list of charts. -/
structure Atlas (M : Manifold) where
  charts : List (Chart M)
  nonempty : 0 < charts.length

/-- Number of charts. -/
def Atlas.size {M : Manifold} (A : Atlas M) : Nat := A.charts.length

/-- Atlas size is positive. -/
theorem Atlas.size_pos {M : Manifold} (A : Atlas M) : 0 < A.size :=
  A.nonempty

/-- Path: atlas size is positive. -/
def Atlas.size_pos_path {M : Manifold} (A : Atlas M) :
    Path (0 < A.size) True :=
  Path.mk [Step.mk _ _ (propext ⟨fun _ => trivial, fun _ => A.nonempty⟩)]
    (propext ⟨fun _ => trivial, fun _ => A.nonempty⟩)

/-! ## Tangent Bundle -/

/-- A tangent vector: point plus model-space vector. -/
structure TangentVec (M : Manifold) where
  point : M.carrier
  vec : M.model.carrier

/-- Tangent bundle projection. -/
def tangentProj {M : Manifold} (v : TangentVec M) : M.carrier := v.point

/-- Zero tangent vector. -/
def zeroTangentVec (M : Manifold) (p : M.carrier) : TangentVec M where
  point := p
  vec := M.model.origin

/-- Projection of zero tangent. -/
theorem tangentProj_zero (M : Manifold) (p : M.carrier) :
    tangentProj (zeroTangentVec M p) = p := rfl

/-- Path: projection of zero tangent. -/
def tangentProj_zero_path (M : Manifold) (p : M.carrier) :
    Path (tangentProj (zeroTangentVec M p)) p := Path.refl _

/-! ## Chart-induced Tangent Map -/

/-- Chart round-trip on a tangent vector. -/
def chartRoundTrip {M : Manifold} (φ : Chart M) (v : TangentVec M) : TangentVec M where
  point := φ.fromModel (φ.toModel v.point)
  vec := v.vec

/-- Chart round-trip preserves vec. -/
theorem chartRoundTrip_vec {M : Manifold} (φ : Chart M) (v : TangentVec M) :
    (chartRoundTrip φ v).vec = v.vec := rfl

/-- Chart round-trip point is path-equivalent. -/
def chartRoundTrip_point {M : Manifold} (φ : Chart M) (v : TangentVec M) :
    Path (chartRoundTrip φ v).point v.point :=
  φ.left_inv v.point

/-- Double chart round-trip vec. -/
theorem chartRoundTrip_comp_vec {M : Manifold} (φ ψ : Chart M) (v : TangentVec M) :
    (chartRoundTrip ψ (chartRoundTrip φ v)).vec = v.vec := rfl

/-! ## Model Maps -/

/-- A map between manifolds (on carrier and model). -/
structure ModelMap (M N : Manifold) where
  toFun : M.carrier → N.carrier
  modelFun : M.model.carrier → N.model.carrier

/-- Identity model map. -/
def modelMapId (M : Manifold) : ModelMap M M where
  toFun := fun x => x
  modelFun := fun y => y

/-- Composition of model maps. -/
def modelMapComp {M N P : Manifold} (g : ModelMap N P) (f : ModelMap M N) : ModelMap M P where
  toFun := fun x => g.toFun (f.toFun x)
  modelFun := fun y => g.modelFun (f.modelFun y)

/-- Left identity (toFun). -/
theorem modelMapComp_id_left {M N : Manifold} (f : ModelMap M N) :
    (modelMapComp (modelMapId N) f).toFun = f.toFun := rfl

/-- Right identity (toFun). -/
theorem modelMapComp_id_right {M N : Manifold} (f : ModelMap M N) :
    (modelMapComp f (modelMapId M)).toFun = f.toFun := rfl

/-- Associativity (toFun). -/
theorem modelMapComp_assoc {M N P Q : Manifold}
    (h : ModelMap P Q) (g : ModelMap N P) (f : ModelMap M N) :
    (modelMapComp h (modelMapComp g f)).toFun = (modelMapComp (modelMapComp h g) f).toFun := rfl

/-- Left identity (modelFun). -/
theorem modelMapComp_id_left_model {M N : Manifold} (f : ModelMap M N) :
    (modelMapComp (modelMapId N) f).modelFun = f.modelFun := rfl

/-- Right identity (modelFun). -/
theorem modelMapComp_id_right_model {M N : Manifold} (f : ModelMap M N) :
    (modelMapComp f (modelMapId M)).modelFun = f.modelFun := rfl

/-- Associativity (modelFun). -/
theorem modelMapComp_assoc_model {M N P Q : Manifold}
    (h : ModelMap P Q) (g : ModelMap N P) (f : ModelMap M N) :
    (modelMapComp h (modelMapComp g f)).modelFun =
      (modelMapComp (modelMapComp h g) f).modelFun := rfl

/-! ## Pushforward -/

/-- Pushforward of tangent vector. -/
def pushforward {M N : Manifold} (f : ModelMap M N) (v : TangentVec M) : TangentVec N where
  point := f.toFun v.point
  vec := f.modelFun v.vec

/-- Pushforward of identity. -/
theorem pushforward_id (M : Manifold) (v : TangentVec M) :
    pushforward (modelMapId M) v = v := by cases v; rfl

/-- Path: pushforward of identity. -/
def pushforward_id_path (M : Manifold) (v : TangentVec M) :
    Path (pushforward (modelMapId M) v) v :=
  Path.mk [Step.mk _ _ (pushforward_id M v)] (pushforward_id M v)

/-- Chain rule for pushforward. -/
theorem pushforward_comp {M N P : Manifold} (g : ModelMap N P) (f : ModelMap M N)
    (v : TangentVec M) :
    pushforward (modelMapComp g f) v = pushforward g (pushforward f v) := by cases v; rfl

/-- Path: chain rule for pushforward. -/
def pushforward_comp_path {M N P : Manifold} (g : ModelMap N P) (f : ModelMap M N)
    (v : TangentVec M) :
    Path (pushforward (modelMapComp g f) v) (pushforward g (pushforward f v)) :=
  Path.mk [Step.mk _ _ (pushforward_comp g f v)] (pushforward_comp g f v)

/-- Pushforward projection. -/
theorem pushforward_proj {M N : Manifold} (f : ModelMap M N) (v : TangentVec M) :
    tangentProj (pushforward f v) = f.toFun (tangentProj v) := rfl

/-! ## Chart Compatibility -/

/-- Two charts are compatible: transition is invertible. -/
structure ChartCompat {M : Manifold} (φ ψ : Chart M) where
  fwd_inv : ∀ y, Path (transitionMapInv φ ψ (transitionMap φ ψ y)) y
  bwd_inv : ∀ y, Path (transitionMap φ ψ (transitionMapInv φ ψ y)) y

/-- Any chart is self-compatible. -/
def chartCompat_self {M : Manifold} (φ : Chart M) : ChartCompat φ φ where
  fwd_inv := transition_left_inv φ φ
  bwd_inv := transition_right_inv φ φ

/-- Chart compatibility is symmetric. -/
def chartCompat_symm {M : Manifold} {φ ψ : Chart M} (_ : ChartCompat φ ψ) :
    ChartCompat ψ φ where
  fwd_inv := transition_left_inv ψ φ
  bwd_inv := transition_right_inv ψ φ

/-! ## Dimension -/

/-- Dimension of a manifold. -/
def Manifold.dimension (M : Manifold) : Nat := M.model.dim

/-- Dimension equals model dim. -/
theorem dimension_eq (M : Manifold) : M.dimension = M.model.dim := rfl

/-- Path: dimension. -/
def dimension_path (M : Manifold) : Path M.dimension M.model.dim := Path.refl _

end ManifoldPaths
end Topology
end Path
end ComputationalPaths
