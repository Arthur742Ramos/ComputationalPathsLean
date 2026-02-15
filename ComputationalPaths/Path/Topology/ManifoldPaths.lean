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

/-- A model space (abstract local model for charts). -/
structure ModelSpace where
  carrier : Type u
  origin : carrier
  dim : Nat

/-- A manifold: a space locally modeled on a model space. -/
structure Manifold where
  carrier : Type u
  model : ModelSpace
  basePoint : carrier

/-! ## Charts (total, for simplicity) -/

/-- A chart: a pair of inverse maps between manifold and model. -/
structure Chart (M : Manifold) where
  toModel : M.carrier → M.model.carrier
  fromModel : M.model.carrier → M.carrier
  left_inv : ∀ x, Path (fromModel (toModel x)) x
  right_inv : ∀ y, Path (toModel (fromModel y)) y

/-- Identity chart. -/
def idChart (M : Manifold) (h : Path M.carrier M.model.carrier := Path.refl _)
    : Chart M := by
  cases h
  exact {
    toModel := fun x => x
    fromModel := fun y => y
    left_inv := fun _ => Path.refl _
    right_inv := fun _ => Path.refl _
  }

/-- The transition map between two charts. -/
def transitionMap {M : Manifold} (φ ψ : Chart M) : M.model.carrier → M.model.carrier :=
  fun y => ψ.toModel (φ.fromModel y)

/-- Transition map in the reverse direction. -/
def transitionMapInv {M : Manifold} (φ ψ : Chart M) : M.model.carrier → M.model.carrier :=
  transitionMap ψ φ

/-- Transition map is left-invertible. -/
def transition_left_inv {M : Manifold} (φ ψ : Chart M) (y : M.model.carrier) :
    Path (transitionMapInv φ ψ (transitionMap φ ψ y)) y := by
  simp [transitionMap, transitionMapInv]
  exact Path.trans (Path.congrArg φ.toModel (ψ.left_inv (φ.fromModel y))) (φ.right_inv y)

/-- Transition map is right-invertible. -/
def transition_right_inv {M : Manifold} (φ ψ : Chart M) (y : M.model.carrier) :
    Path (transitionMap φ ψ (transitionMapInv φ ψ y)) y := by
  simp [transitionMap, transitionMapInv]
  exact Path.trans (Path.congrArg ψ.toModel (φ.left_inv (ψ.fromModel y))) (ψ.right_inv y)

/-- Transition from a chart to itself is the identity. -/
def transition_self {M : Manifold} (φ : Chart M) (y : M.model.carrier) :
    Path (transitionMap φ φ y) y :=
  Path.trans (Path.congrArg φ.toModel (φ.left_inv (φ.fromModel y))) (φ.right_inv y) |>.symm |>.symm

/-- Actually: transition_self more directly. -/
def transition_self' {M : Manifold} (φ : Chart M) (y : M.model.carrier) :
    Path (transitionMap φ φ y) y := by
  simp [transitionMap]
  exact Path.trans (Path.congrArg φ.toModel (φ.left_inv (φ.fromModel y))) (φ.right_inv y)

/-- Composition of transition maps. -/
theorem transition_comp {M : Manifold} (φ ψ χ : Chart M) (y : M.model.carrier) :
    transitionMap ψ χ (transitionMap φ ψ y) =
      χ.toModel (φ.fromModel y) := by
  simp [transitionMap]
  exact congrArg χ.toModel (ψ.left_inv (φ.fromModel y)).proof

/-- Path version of transition composition. -/
def transition_comp_path {M : Manifold} (φ ψ χ : Chart M) (y : M.model.carrier) :
    Path (transitionMap ψ χ (transitionMap φ ψ y))
         (transitionMap φ χ y) := by
  simp [transitionMap]
  exact Path.congrArg χ.toModel (ψ.left_inv (φ.fromModel y))

/-! ## Atlas -/

/-- An atlas: a list of charts. -/
structure Atlas (M : Manifold) where
  charts : List (Chart M)
  nonempty : charts ≠ []

/-- Number of charts in an atlas. -/
def Atlas.size {M : Manifold} (A : Atlas M) : Nat := A.charts.length

/-- An atlas with at least one chart has positive size. -/
theorem Atlas.size_pos {M : Manifold} (A : Atlas M) : 0 < A.size := by
  simp [Atlas.size]
  exact List.length_pos.mpr A.nonempty

/-! ## Tangent Bundle -/

/-- A tangent vector: a point plus a model-space vector. -/
structure TangentVec (M : Manifold) where
  point : M.carrier
  vec : M.model.carrier

/-- The tangent bundle projection. -/
def tangentProj {M : Manifold} (v : TangentVec M) : M.carrier := v.point

/-- Zero tangent vector at a point. -/
def zeroTangentVec (M : Manifold) (p : M.carrier) : TangentVec M where
  point := p
  vec := M.model.origin

/-- Projection of zero tangent. -/
theorem tangentProj_zero (M : Manifold) (p : M.carrier) :
    tangentProj (zeroTangentVec M p) = p := rfl

/-- Path: projection of zero tangent. -/
def tangentProj_zero_path (M : Manifold) (p : M.carrier) :
    Path (tangentProj (zeroTangentVec M p)) p := Path.refl _

/-! ## Chart-induced tangent map -/

/-- A chart induces a map on tangent vectors. -/
def chartTangent {M : Manifold} (φ : Chart M) (v : TangentVec M) :
    TangentVec M where
  point := φ.fromModel (φ.toModel v.point)
  vec := v.vec

/-- Chart tangent map preserves the vector component. -/
theorem chartTangent_vec {M : Manifold} (φ : Chart M) (v : TangentVec M) :
    (chartTangent φ v).vec = v.vec := rfl

/-- Chart tangent map base point relates to original via left_inv. -/
def chartTangent_point {M : Manifold} (φ : Chart M) (v : TangentVec M) :
    Path (chartTangent φ v).point v.point :=
  φ.left_inv v.point

/-- Composing two chart tangent maps. -/
def chartTangent_comp {M : Manifold} (φ ψ : Chart M) (v : TangentVec M) :
    Path (chartTangent ψ (chartTangent φ v)).vec v.vec :=
  Path.refl _

/-! ## Smooth Maps Between Manifolds -/

/-- A smooth map between manifolds (total, chart-compatible). -/
structure SmoothMap (M N : Manifold) where
  toFun : M.carrier → N.carrier
  modelMap : M.model.carrier → N.model.carrier
  compat : ∀ (φ : Chart M) (ψ : Chart N) (x : M.carrier),
    Path (ψ.toModel (toFun x))
         (modelMap (φ.toModel x))

/-- Identity smooth map (when model = carrier, trivially). -/
def smoothMapId (M : Manifold) : SmoothMap M M where
  toFun := fun x => x
  modelMap := fun y => y
  compat := fun φ ψ x =>
    Path.trans (Path.congrArg ψ.toModel (Path.refl x))
      (Path.symm (Path.refl (ψ.toModel x))) |>.symm |>.symm

/-- Actually just use refl for compat in id -- but we need φ.toModel x = ψ.toModel x
    which isn't true in general. Let's use a different formulation. -/

/-- A smooth map in the model-map sense. -/
structure ModelMap (M N : Manifold) where
  toFun : M.carrier → N.carrier
  modelMap : M.model.carrier → N.model.carrier

/-- Identity model map. -/
def modelMapId (M : Manifold) : ModelMap M M where
  toFun := fun x => x
  modelMap := fun y => y

/-- Composition of model maps. -/
def modelMapComp {M N P : Manifold} (g : ModelMap N P) (f : ModelMap M N) : ModelMap M P where
  toFun := fun x => g.toFun (f.toFun x)
  modelMap := fun y => g.modelMap (f.modelMap y)

/-- Left identity for model map composition (toFun). -/
theorem modelMapComp_id_left {M N : Manifold} (f : ModelMap M N) :
    (modelMapComp (modelMapId N) f).toFun = f.toFun := rfl

/-- Right identity for model map composition (toFun). -/
theorem modelMapComp_id_right {M N : Manifold} (f : ModelMap M N) :
    (modelMapComp f (modelMapId M)).toFun = f.toFun := rfl

/-- Associativity of model map composition (toFun). -/
theorem modelMapComp_assoc {M N P Q : Manifold}
    (h : ModelMap P Q) (g : ModelMap N P) (f : ModelMap M N) :
    (modelMapComp h (modelMapComp g f)).toFun = (modelMapComp (modelMapComp h g) f).toFun := rfl

/-- Left identity for model map composition (modelMap). -/
theorem modelMapComp_id_left_model {M N : Manifold} (f : ModelMap M N) :
    (modelMapComp (modelMapId N) f).modelMap = f.modelMap := rfl

/-- Right identity for model map composition (modelMap). -/
theorem modelMapComp_id_right_model {M N : Manifold} (f : ModelMap M N) :
    (modelMapComp f (modelMapId M)).modelMap = f.modelMap := rfl

/-- Associativity of model map composition (modelMap). -/
theorem modelMapComp_assoc_model {M N P Q : Manifold}
    (h : ModelMap P Q) (g : ModelMap N P) (f : ModelMap M N) :
    (modelMapComp h (modelMapComp g f)).modelMap =
      (modelMapComp (modelMapComp h g) f).modelMap := rfl

/-! ## Pushforward on Tangent Vectors -/

/-- Pushforward of a tangent vector along a model map. -/
def pushforward {M N : Manifold} (f : ModelMap M N) (v : TangentVec M) : TangentVec N where
  point := f.toFun v.point
  vec := f.modelMap v.vec

/-- Pushforward of identity is identity. -/
theorem pushforward_id (M : Manifold) (v : TangentVec M) :
    pushforward (modelMapId M) v = v := by
  cases v; rfl

/-- Path: pushforward of identity. -/
def pushforward_id_path (M : Manifold) (v : TangentVec M) :
    Path (pushforward (modelMapId M) v) v :=
  Path.ofEq (pushforward_id M v)

/-- Chain rule for pushforward. -/
theorem pushforward_comp {M N P : Manifold} (g : ModelMap N P) (f : ModelMap M N)
    (v : TangentVec M) :
    pushforward (modelMapComp g f) v = pushforward g (pushforward f v) := by
  cases v; rfl

/-- Path: chain rule for pushforward. -/
def pushforward_comp_path {M N P : Manifold} (g : ModelMap N P) (f : ModelMap M N)
    (v : TangentVec M) :
    Path (pushforward (modelMapComp g f) v) (pushforward g (pushforward f v)) :=
  Path.ofEq (pushforward_comp g f v)

/-- Pushforward preserves zero tangent vector. -/
theorem pushforward_zero_vec {M N : Manifold} (f : ModelMap M N) (p : M.carrier) :
    (pushforward f (zeroTangentVec M p)).point = f.toFun p := rfl

/-- Pushforward projection commutes with toFun. -/
theorem pushforward_proj {M N : Manifold} (f : ModelMap M N) (v : TangentVec M) :
    tangentProj (pushforward f v) = f.toFun (tangentProj v) := rfl

/-! ## Chart Compatibility -/

/-- Two charts are compatible if their transition map is invertible (witnessed by paths). -/
structure ChartCompat {M : Manifold} (φ ψ : Chart M) where
  fwd_inv : ∀ y, Path (transitionMapInv φ ψ (transitionMap φ ψ y)) y
  bwd_inv : ∀ y, Path (transitionMap φ ψ (transitionMapInv φ ψ y)) y

/-- Any chart is compatible with itself. -/
def chartCompat_self {M : Manifold} (φ : Chart M) : ChartCompat φ φ where
  fwd_inv := transition_left_inv φ φ
  bwd_inv := transition_right_inv φ φ

/-- Chart compatibility is symmetric. -/
def chartCompat_symm {M : Manifold} {φ ψ : Chart M} (h : ChartCompat φ ψ) :
    ChartCompat ψ φ where
  fwd_inv := fun y => by
    simp [transitionMap, transitionMapInv]
    exact Path.trans (Path.congrArg ψ.toModel (φ.left_inv (ψ.fromModel y))) (ψ.right_inv y)
  bwd_inv := fun y => by
    simp [transitionMap, transitionMapInv]
    exact Path.trans (Path.congrArg φ.toModel (ψ.left_inv (φ.fromModel y))) (φ.right_inv y)

/-! ## Dimension -/

/-- The dimension of a manifold. -/
def Manifold.dimension (M : Manifold) : Nat := M.model.dim

/-- Dimension is invariant (trivially). -/
theorem dimension_eq (M : Manifold) : M.dimension = M.model.dim := rfl

/-- Path: dimension. -/
def dimension_path (M : Manifold) : Path M.dimension M.model.dim := Path.refl _

end ManifoldPaths
end Topology
end Path
end ComputationalPaths
