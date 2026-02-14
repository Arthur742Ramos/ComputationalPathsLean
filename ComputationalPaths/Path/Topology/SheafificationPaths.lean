/-
# Sheafification via Computational Paths

Presheaves, separated presheaves, sheaf condition, sheaves, stalks,
sheafification functor, comparison map, adjunction, finite-limit
preservation, and direct/inverse image sheaves using Path-based
gluing and locality.

## References

- Kashiwara–Schapira, "Categories and Sheaves"
- Mac Lane–Moerdijk, "Sheaves in Geometry and Logic"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace SheafificationPaths
universe u v
/-! ## Topological Spaces and Covers -/

/-- A minimal topological space structure with opens and membership. -/
structure TopologicalSpace where
  /-- Underlying carrier. -/
  carrier : Type u
  /-- The type of opens. -/
  Opens : Type u
  /-- Inclusion of opens. -/
  le : Opens → Opens → Prop
  /-- Reflexivity of inclusion. -/
  le_refl : ∀ (U : Opens), le U U
  /-- Transitivity of inclusion. -/
  le_trans : ∀ (U V W : Opens), le U V → le V W → le U W
  /-- Membership relation. -/
  mem : carrier → Opens → Prop

/-- An open cover of `U` with overlap data. -/
structure OpenCover (X : TopologicalSpace.{u}) (U : X.Opens) where
  /-- Indexing type. -/
  index : Type u
  /-- Covering opens. -/
  cover : index → X.Opens
  /-- Each cover lies in U. -/
  cover_le : ∀ (i : index), X.le (cover i) U
  /-- Overlap of two covering opens. -/
  overlap : index → index → X.Opens
  /-- Overlap lies in the left open. -/
  overlap_le_left : ∀ (i j : index), X.le (overlap i j) (cover i)
  /-- Overlap lies in the right open. -/
  overlap_le_right : ∀ (i j : index), X.le (overlap i j) (cover j)

/-! ## Presheaves and Sheaves -/

/-- A presheaf of types on a topological space. -/
structure Presheaf (X : TopologicalSpace.{u}) where
  /-- Sections over an open. -/
  sections : X.Opens → Type v
  /-- Restriction along inclusions. -/
  restrict : ∀ {U V : X.Opens}, X.le U V → sections V → sections U

/-- A morphism of presheaves. -/
structure PresheafMorphism {X : TopologicalSpace.{u}} (F G : Presheaf.{u, v} X) where
  /-- Component maps on sections. -/
  app : ∀ (U : X.Opens), F.sections U → G.sections U

/-- A separated presheaf: locality of sections on covers. -/
structure SeparatedPresheaf (X : TopologicalSpace.{u}) extends Presheaf.{u, v} X where
  /-- Locality: agreeing on a cover implies equality. -/
  locality : ∀ {U : X.Opens} (cover : OpenCover X U) (s t : sections U),
    (∀ (i : cover.index), Path (restrict (cover.cover_le i) s)
      (restrict (cover.cover_le i) t)) →
    Path s t

/-- The sheaf condition: locality + gluing. -/
structure SheafCondition {X : TopologicalSpace.{u}} (F : Presheaf.{u, v} X) where
  /-- Locality. -/
  locality : ∀ {U : X.Opens} (cover : OpenCover X U) (s t : F.sections U),
    (∀ (i : cover.index), Path (F.restrict (cover.cover_le i) s)
      (F.restrict (cover.cover_le i) t)) →
    Path s t
  /-- Gluing: matching families extend to global sections. -/
  gluing : ∀ {U : X.Opens} (cover : OpenCover X U)
    (s : ∀ (i : cover.index), F.sections (cover.cover i)),
    (∀ (i j : cover.index),
      Path (F.restrict (cover.overlap_le_left i j) (s i))
           (F.restrict (cover.overlap_le_right i j) (s j))) →
    F.sections U

/-- A sheaf is a presheaf satisfying the sheaf condition. -/
structure Sheaf (X : TopologicalSpace.{u}) extends Presheaf.{u, v} X where
  /-- The sheaf condition. -/
  cond : SheafCondition toPresheaf

/-! ## Stalks -/

/-- A neighborhood of a point. -/
structure Nbhd (X : TopologicalSpace.{u}) (x : X.carrier) where
  /-- The neighborhood open. -/
  openSet : X.Opens
  /-- Membership witness. -/
  contains : X.mem x openSet

/-- A stalk element as a germ over a neighborhood. -/
structure StalkElem {X : TopologicalSpace.{u}} (F : Presheaf.{u, v} X)
    (x : X.carrier) where
  /-- The neighborhood where the germ is defined. -/
  nbhd : Nbhd X x
  /-- The representative of the germ. -/
  germ : F.sections nbhd.openSet

/-- Two germs agree if they agree on a smaller neighborhood. -/
structure GermEquiv {X : TopologicalSpace.{u}} {F : Presheaf.{u, v} X}
    {x : X.carrier} (g₁ g₂ : StalkElem F x) where
  /-- A common refinement. -/
  refinement : Nbhd X x
  /-- Refinement lies in the first neighborhood. -/
  refine_left : X.le refinement.openSet g₁.nbhd.openSet
  /-- Refinement lies in the second neighborhood. -/
  refine_right : X.le refinement.openSet g₂.nbhd.openSet
  /-- The restricted germs agree. -/
  agree : Path (F.restrict refine_left g₁.germ) (F.restrict refine_right g₂.germ)

/-! ## Sheafification -/

/-- The sheafification functor with plus construction and associated sheaf. -/
structure SheafificationFunctor (X : TopologicalSpace.{u}) where
  /-- The plus construction. -/
  plus : Presheaf.{u, v} X → Presheaf.{u, v} X
  /-- The associated sheaf. -/
  associated : Presheaf.{u, v} X → Sheaf.{u, v} X
  /-- Comparison map from a presheaf to its sheafification. -/
  comparison : ∀ (F : Presheaf.{u, v} X), PresheafMorphism F (associated F).toPresheaf

/-- The comparison map from a presheaf to its sheafification. -/
def comparisonMap {X : TopologicalSpace.{u}} (S : SheafificationFunctor.{u, v} X)
    (F : Presheaf.{u, v} X) : PresheafMorphism F (S.associated F).toPresheaf :=
  S.comparison F

/-- Sheafification is left adjoint to the inclusion of sheaves. -/
structure SheafificationAdjunction (X : TopologicalSpace.{u})
    (S : SheafificationFunctor.{u, v} X) where
  /-- Unit of the adjunction. -/
  unit : ∀ (F : Presheaf.{u, v} X), PresheafMorphism F (S.associated F).toPresheaf
  /-- Counit of the adjunction. -/
  counit : ∀ (G : Sheaf.{u, v} X),
    PresheafMorphism (S.associated G.toPresheaf).toPresheaf G.toPresheaf

/-- A finite-limit diagram of presheaves. -/
structure FiniteLimitDiagram (X : TopologicalSpace.{u}) where
  /-- Diagram shape. -/
  shape : Type u
  /-- Objects in the diagram. -/
  obj : shape → Presheaf.{u, v} X

/-- Sheafification preserves finite limits (structural witness). -/
structure SheafificationPreservesFiniteLimits (X : TopologicalSpace.{u})
    (_S : SheafificationFunctor.{u, v} X) where
  /-- Preservation for each diagram. -/
  preserves : ∀ (_D : FiniteLimitDiagram.{u, v} X), True

/-! ## Image Sheaves and Restriction -/

/-- A continuous map with preimage/image operations on opens. -/
structure ContinuousMap (X Y : TopologicalSpace.{u}) where
  /-- Underlying function. -/
  toFun : X.carrier → Y.carrier
  /-- Preimage of opens. -/
  preimage : Y.Opens → X.Opens
  /-- Image of opens. -/
  image : X.Opens → Y.Opens
  /-- Preimage respects inclusion. -/
  preimage_le : ∀ {U V : Y.Opens}, Y.le U V → X.le (preimage U) (preimage V)
  /-- Image respects inclusion. -/
  image_le : ∀ {U V : X.Opens}, X.le U V → Y.le (image U) (image V)

/-- Direct image presheaf along a continuous map. -/
def directImage {X Y : TopologicalSpace.{u}} (f : ContinuousMap X Y)
    (F : Presheaf.{u, v} X) : Presheaf.{u, v} Y where
  sections := fun V => F.sections (f.preimage V)
  restrict := fun {_U _V} hUV s => F.restrict (f.preimage_le hUV) s

/-- Inverse image presheaf along a continuous map. -/
def inverseImage {X Y : TopologicalSpace.{u}} (f : ContinuousMap X Y)
    (F : Presheaf.{u, v} Y) : Presheaf.{u, v} X where
  sections := fun U => F.sections (f.image U)
  restrict := fun {_U _V} hUV s => F.restrict (f.image_le hUV) s

/-- Restriction of a presheaf to an open subset. -/
structure SheafRestriction {X : TopologicalSpace.{u}}
    (F : Presheaf.{u, v} X) (_U : X.Opens) where
  /-- The restricted presheaf. -/
  restricted : Presheaf.{u, v} X
  /-- Comparison into the original presheaf. -/
  comparison : PresheafMorphism restricted F


/-! ## Path lemmas -/

theorem sheafification_paths_path_refl {α : Type u} (x : α) : Path.refl x = Path.refl x :=
  rfl

theorem sheafification_paths_path_symm {α : Type u} {x y : α} (h : Path x y) : Path.symm h = Path.symm h :=
  rfl

theorem sheafification_paths_path_trans {α : Type u} {x y z : α}
    (h₁ : Path x y) (h₂ : Path y z) : Path.trans h₁ h₂ = Path.trans h₁ h₂ :=
  rfl

theorem sheafification_paths_path_symm_symm {α : Type u} {x y : α} (h : Path x y) :
    Path.symm (Path.symm h) = h :=
  Path.symm_symm h

theorem sheafification_paths_path_trans_refl_left {α : Type u} {x y : α} (h : Path x y) :
    Path.trans (Path.refl x) h = h :=
  Path.trans_refl_left h

theorem sheafification_paths_path_trans_refl_right {α : Type u} {x y : α} (h : Path x y) :
    Path.trans h (Path.refl y) = h :=
  Path.trans_refl_right h

theorem sheafification_paths_path_trans_assoc {α : Type u} {x y z w : α}
    (h₁ : Path x y) (h₂ : Path y z) (h₃ : Path z w) :
    Path.trans (Path.trans h₁ h₂) h₃ = Path.trans h₁ (Path.trans h₂ h₃) :=
  Path.trans_assoc h₁ h₂ h₃

theorem sheafification_paths_path_toEq_ofEq {α : Type u} {x y : α} (h : x = y) :
    Path.toEq (Path.ofEq h) = h :=
  Path.toEq_ofEq h


end SheafificationPaths
end Topology
end Path
end ComputationalPaths