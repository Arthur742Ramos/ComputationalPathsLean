/-
# 2-category infrastructure via computational paths

This module builds a path-based 2-category interface on top of
`HigherCategory.Bicategory`, keeping coherence data as explicit derivations.
-/

import ComputationalPaths.HigherCategory.Bicategory
import ComputationalPaths.Path.HigherPathOperations

namespace ComputationalPaths
namespace HigherCategory
namespace TwoCategory

open Path
open Path.OmegaGroupoid
open Path.HigherPathOperations

universe u

variable {A : Type u}
variable {a b c d e : A}

/-- 1-cells in the path 2-category. -/
abbrev Hom (x y : A) : Type u := Path x y

/-- 2-cells in the path 2-category. -/
abbrev TwoCell {x y : A} (f g : Hom x y) : Type u := Derivation₂ f g

/-- 3-cells in the path 2-category. -/
abbrev ThreeCell {x y : A} {f g : Hom x y} (α β : TwoCell f g) : Type u := Derivation₃ α β

/-- Identity 2-cell. -/
noncomputable def id₂ (f : Hom a b) : TwoCell f f := Derivation₂.refl f

/-- Vertical composition of 2-cells. -/
noncomputable def vcomp {f g h : Hom a b} (α : TwoCell f g) (β : TwoCell g h) : TwoCell f h :=
  Derivation₂.vcomp α β

/-- Left whiskering of a 2-cell. -/
noncomputable def whiskerLeft (f : Hom a b) {g h : Hom b c} (α : TwoCell g h) :
    TwoCell (Path.trans f g) (Path.trans f h) :=
  OmegaGroupoid.whiskerLeft f α

/-- Right whiskering of a 2-cell. -/
noncomputable def whiskerRight {f g : Hom a b} (α : TwoCell f g) (h : Hom b c) :
    TwoCell (Path.trans f h) (Path.trans g h) :=
  OmegaGroupoid.whiskerRight α h

/-- Horizontal composition of 2-cells. -/
noncomputable def hcomp {f f' : Hom a b} {g g' : Hom b c}
    (α : TwoCell f f') (β : TwoCell g g') :
    TwoCell (Path.trans f g) (Path.trans f' g') :=
  OmegaGroupoid.hcomp α β

/-- Interchange as a computational 3-cell (Godement law). -/
noncomputable def interchangeIdentity {f f' : Hom a b} {g g' : Hom b c}
    (α : TwoCell f f') (β : TwoCell g g') :
    ThreeCell
      (Derivation₂.vcomp (whiskerRight α g) (whiskerLeft f' β))
      (Derivation₂.vcomp (whiskerLeft f β) (whiskerRight α g')) :=
  godementInterchange α β

/-- Pentagon identity inherited as a computational 3-cell. -/
noncomputable def pentagonIdentity (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e) :
    ThreeCell (Bicategory.pentagonLeftPath f g h k) (Bicategory.pentagonRightPath f g h k) :=
  Bicategory.pentagonIdentity f g h k

/-- Triangle identity inherited as a computational 3-cell. -/
noncomputable def triangleIdentity (f : Hom a b) (g : Hom b c) :
    ThreeCell (Bicategory.triangleLeftPath f g) (Bicategory.triangleRightPath f g) :=
  Bicategory.triangleIdentity f g

theorem hom_eq_path (x y : A) : Hom x y = Path x y := by
  rfl

theorem twoCell_eq_derivation2 {x y : A} (f g : Hom x y) :
    TwoCell f g = Derivation₂ f g := by
  rfl

theorem threeCell_eq_derivation3 {x y : A} {f g : Hom x y} (α β : TwoCell f g) :
    ThreeCell α β = Derivation₃ α β := by
  rfl

theorem id₂_eq_refl (f : Hom a b) : id₂ f = Derivation₂.refl f := by
  rfl

theorem vcomp_eq_derivation {f g h : Hom a b} (α : TwoCell f g) (β : TwoCell g h) :
    vcomp α β = Derivation₂.vcomp α β := by
  rfl

theorem whiskerLeft_eq_omega (f : Hom a b) {g h : Hom b c} (α : TwoCell g h) :
    whiskerLeft f α = OmegaGroupoid.whiskerLeft f α := by
  rfl

theorem whiskerRight_eq_omega {f g : Hom a b} (α : TwoCell f g) (h : Hom b c) :
    whiskerRight α h = OmegaGroupoid.whiskerRight α h := by
  rfl

theorem hcomp_eq_omega {f f' : Hom a b} {g g' : Hom b c}
    (α : TwoCell f f') (β : TwoCell g g') :
    hcomp α β = OmegaGroupoid.hcomp α β := by
  rfl

theorem interchangeIdentity_eq_godement {f f' : Hom a b} {g g' : Hom b c}
    (α : TwoCell f f') (β : TwoCell g g') :
    interchangeIdentity α β = godementInterchange α β := by
  rfl

theorem pentagonIdentity_eq_bicategory (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e) :
    pentagonIdentity f g h k = Bicategory.pentagonIdentity f g h k := by
  rfl

theorem triangleIdentity_eq_bicategory (f : Hom a b) (g : Hom b c) :
    triangleIdentity f g = Bicategory.triangleIdentity f g := by
  rfl

theorem vcomp_id₂_left_explicit {f g : Hom a b} (α : TwoCell f g) :
    vcomp (id₂ f) α = Derivation₂.vcomp (Derivation₂.refl f) α := by
  rfl

theorem vcomp_id₂_right_explicit {f g : Hom a b} (α : TwoCell f g) :
    vcomp α (id₂ g) = Derivation₂.vcomp α (Derivation₂.refl g) := by
  rfl

theorem hcomp_id₂_components (f : Hom a b) (g : Hom b c) :
    hcomp (id₂ f) (id₂ g) =
      OmegaGroupoid.hcomp (Derivation₂.refl f) (Derivation₂.refl g) := by
  rfl

end TwoCategory
end HigherCategory
end ComputationalPaths
