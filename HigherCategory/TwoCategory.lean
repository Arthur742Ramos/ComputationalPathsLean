/-!
# 2-category infrastructure via computational paths

This module builds a path-based 2-category interface on top of
`HigherCategory.Bicategory`, keeping coherence data as explicit derivations.
-/

import HigherCategory.Bicategory
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
def id₂ (f : Hom a b) : TwoCell f f := Derivation₂.refl f

/-- Vertical composition of 2-cells. -/
def vcomp {f g h : Hom a b} (α : TwoCell f g) (β : TwoCell g h) : TwoCell f h :=
  Derivation₂.vcomp α β

/-- Left whiskering of a 2-cell. -/
def whiskerLeft (f : Hom a b) {g h : Hom b c} (α : TwoCell g h) :
    TwoCell (Path.trans f g) (Path.trans f h) :=
  OmegaGroupoid.whiskerLeft f α

/-- Right whiskering of a 2-cell. -/
def whiskerRight {f g : Hom a b} (α : TwoCell f g) (h : Hom b c) :
    TwoCell (Path.trans f h) (Path.trans g h) :=
  OmegaGroupoid.whiskerRight α h

/-- Horizontal composition of 2-cells. -/
def hcomp {f f' : Hom a b} {g g' : Hom b c}
    (α : TwoCell f f') (β : TwoCell g g') :
    TwoCell (Path.trans f g) (Path.trans f' g') :=
  OmegaGroupoid.hcomp α β

/-- Interchange as a computational 3-cell (Godement law). -/
def interchangeIdentity {f f' : Hom a b} {g g' : Hom b c}
    (α : TwoCell f f') (β : TwoCell g g') :
    ThreeCell
      (Derivation₂.vcomp (whiskerRight α g) (whiskerLeft f' β))
      (Derivation₂.vcomp (whiskerLeft f β) (whiskerRight α g')) :=
  godementInterchange α β

/-- Pentagon identity inherited as a computational 3-cell. -/
def pentagonIdentity (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e) :
    ThreeCell (Bicategory.pentagonLeftPath f g h k) (Bicategory.pentagonRightPath f g h k) :=
  Bicategory.pentagonIdentity f g h k

/-- Triangle identity inherited as a computational 3-cell. -/
def triangleIdentity (f : Hom a b) (g : Hom b c) :
    ThreeCell (Bicategory.triangleLeftPath f g) (Bicategory.triangleRightPath f g) :=
  Bicategory.triangleIdentity f g

end TwoCategory
end HigherCategory
end ComputationalPaths

