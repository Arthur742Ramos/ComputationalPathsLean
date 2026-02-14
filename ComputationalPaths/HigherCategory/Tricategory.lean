/-
# Tricategory coherence via computational paths

This module lifts bicategorical pentagon/triangle coherence to tricategorical
data: 3-cells for the identities and 4-cells/5-cells as higher modifications.
-/

import ComputationalPaths.HigherCategory.GrayCategory

namespace ComputationalPaths
namespace HigherCategory
namespace Tricategory

open Path
open Path.OmegaGroupoid

universe u

variable {A : Type u}
variable {a b c d e : A}

/-- 1-cells in the tricategory scaffold. -/
abbrev Hom (x y : A) : Type u := Path x y

/-- 2-cells in the tricategory scaffold. -/
abbrev TwoCell {x y : A} (f g : Hom x y) : Type u := Derivation₂ f g

/-- 3-cells in the tricategory scaffold. -/
abbrev ThreeCell {x y : A} {f g : Hom x y} (α β : TwoCell f g) : Type u := Derivation₃ α β

/-- 4-cells in the tricategory scaffold. -/
abbrev FourCell {x y : A} {f g : Hom x y} {α β : TwoCell f g}
    (m₁ m₂ : ThreeCell α β) : Type u := Derivation₄ m₁ m₂

/-- Canonical pentagon 3-cell. -/
def pentagonIdentity (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e) :
    ThreeCell (Bicategory.pentagonLeftPath f g h k) (Bicategory.pentagonRightPath f g h k) :=
  GrayCategory.pentagon3 f g h k

/-- Canonical triangle 3-cell. -/
def triangleIdentity (f : Hom a b) (g : Hom b c) :
    ThreeCell (Bicategory.triangleLeftPath f g) (Bicategory.triangleRightPath f g) :=
  GrayCategory.triangle3 f g

/-- Pentagonator: any pentagon witness is connected to the canonical one by a 4-cell. -/
def pentagonator (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e)
    (piCell : ThreeCell (Bicategory.pentagonLeftPath f g h k)
      (Bicategory.pentagonRightPath f g h k)) :
    FourCell (pentagonIdentity f g h k) piCell :=
  GrayCategory.pentagonContraction f g h k piCell

/-- Triangleator: any triangle witness is connected to the canonical one by a 4-cell. -/
def triangleator (f : Hom a b) (g : Hom b c)
    (tau : ThreeCell (Bicategory.triangleLeftPath f g) (Bicategory.triangleRightPath f g)) :
    FourCell (triangleIdentity f g) tau :=
  GrayCategory.triangleContraction f g tau

/-- Any two pentagonators are connected by a 5-cell (level-5 contractibility). -/
def pentagonatorHigher (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e)
    (piCell : ThreeCell (Bicategory.pentagonLeftPath f g h k)
      (Bicategory.pentagonRightPath f g h k))
    (m1 m2 : FourCell (pentagonIdentity f g h k) piCell) :
    DerivationHigh 0 m1 m2 :=
  contractibilityHigh 0 m1 m2

/-- Any two triangleators are connected by a 5-cell (level-5 contractibility). -/
def triangleatorHigher (f : Hom a b) (g : Hom b c)
    (tau : ThreeCell (Bicategory.triangleLeftPath f g) (Bicategory.triangleRightPath f g))
    (m1 m2 : FourCell (triangleIdentity f g) tau) :
    DerivationHigh 0 m1 m2 :=
  contractibilityHigh 0 m1 m2

end Tricategory
end HigherCategory
end ComputationalPaths
