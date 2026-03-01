/-
# Gray-category coherence via computational paths

This module packages Gray-style coherence data by treating 3-cells as primitive
computational witnesses and 4-cells as higher contractions between them.
-/

-- import ComputationalPaths.HigherCategory.TwoCategory  -- TEMPORARILY DISABLED: depends on broken Bicategory module

namespace ComputationalPaths
namespace HigherCategory
namespace GrayCategory

open Path
open Path.OmegaGroupoid

universe u

variable {A : Type u}
variable {a b c d e : A}

/-- 1-cells in the Gray-category scaffold. -/
abbrev Hom (x y : A) : Type u := Path x y

/-- 2-cells in the Gray-category scaffold. -/
abbrev TwoCell {x y : A} (f g : Hom x y) : Type u := Derivation₂ f g

/-- 3-cells in the Gray-category scaffold. -/
abbrev ThreeCell {x y : A} {f g : Hom x y} (α β : TwoCell f g) : Type u := Derivation₃ α β

/-- 4-cells in the Gray-category scaffold. -/
abbrev FourCell {x y : A} {f g : Hom x y} {α β : TwoCell f g}
    (m₁ m₂ : ThreeCell α β) : Type u := Derivation₄ m₁ m₂

/-- Pentagon 3-cell from the underlying bicategorical coherence. -/
noncomputable def pentagon3 (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e) :
    ThreeCell (Bicategory.pentagonLeftPath f g h k) (Bicategory.pentagonRightPath f g h k) :=
  TwoCategory.pentagonIdentity f g h k

/-- Triangle 3-cell from the underlying bicategorical coherence. -/
noncomputable def triangle3 (f : Hom a b) (g : Hom b c) :
    ThreeCell (Bicategory.triangleLeftPath f g) (Bicategory.triangleRightPath f g) :=
  TwoCategory.triangleIdentity f g

/-- Any pentagon 3-cell contracts to the canonical one by a computational 4-cell. -/
noncomputable def pentagonContraction (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e)
    (piCell : ThreeCell (Bicategory.pentagonLeftPath f g h k)
      (Bicategory.pentagonRightPath f g h k)) :
    FourCell (pentagon3 f g h k) piCell :=
  contractibility₄ (pentagon3 f g h k) piCell

/-- Any triangle 3-cell contracts to the canonical one by a computational 4-cell. -/
noncomputable def triangleContraction (f : Hom a b) (g : Hom b c)
    (tau : ThreeCell (Bicategory.triangleLeftPath f g) (Bicategory.triangleRightPath f g)) :
    FourCell (triangle3 f g) tau :=
  contractibility₄ (triangle3 f g) tau

end GrayCategory
end HigherCategory
end ComputationalPaths
