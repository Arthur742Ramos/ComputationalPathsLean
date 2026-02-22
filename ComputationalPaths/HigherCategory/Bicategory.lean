/-
# Bicategory coherence via computational paths

This module provides bicategorical coherence data where 2-cells are explicit
rewrite derivations (`Derivation₂`) and pentagon/triangle are witnessed by
3-cells (`Derivation₃`), not propositional equalities of proofs.
-/

import ComputationalPaths.Path.OmegaGroupoid

namespace ComputationalPaths
namespace HigherCategory
namespace Bicategory

open Path
open Path.OmegaGroupoid

universe u

variable {A : Type u}
variable {a b c d e : A}

/-- 1-cells in the bicategory are computational paths. -/
abbrev Hom (x y : A) : Type u := Path x y

/-- 2-cells are explicit rewrite derivations. -/
abbrev TwoCell {x y : A} (f g : Hom x y) : Type u := Derivation₂ f g

/-- 3-cells are derivations between parallel 2-cells. -/
abbrev ThreeCell {x y : A} {f g : Hom x y} (α β : TwoCell f g) : Type u := Derivation₃ α β

/-- Associator as an explicit 2-cell. -/
noncomputable def associatorPath (f : Hom a b) (g : Hom b c) (h : Hom c d) :
    TwoCell (Path.trans (Path.trans f g) h) (Path.trans f (Path.trans g h)) :=
  associator f g h

/-- Left unitor as an explicit 2-cell. -/
noncomputable def leftUnitorPath (f : Hom a b) : TwoCell (Path.trans (Path.refl a) f) f :=
  leftUnitor f

/-- Right unitor as an explicit 2-cell. -/
noncomputable def rightUnitorPath (f : Hom a b) : TwoCell (Path.trans f (Path.refl b)) f :=
  rightUnitor f

/-- Left route in Mac Lane's pentagon. -/
noncomputable abbrev pentagonLeftPath (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e) :
    TwoCell (Path.trans (Path.trans (Path.trans f g) h) k)
      (Path.trans f (Path.trans g (Path.trans h k))) :=
  pentagonLeft f g h k

/-- Right route in Mac Lane's pentagon. -/
noncomputable abbrev pentagonRightPath (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e) :
    TwoCell (Path.trans (Path.trans (Path.trans f g) h) k)
      (Path.trans f (Path.trans g (Path.trans h k))) :=
  pentagonRight f g h k

/-- Pentagon coherence witnessed by a genuine computational 3-cell. -/
noncomputable def pentagonIdentity (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e) :
    ThreeCell (pentagonLeftPath f g h k) (pentagonRightPath f g h k) :=
  Derivation₃.step (MetaStep₃.pentagon f g h k)

/-- Left route in the bicategorical triangle diagram. -/
noncomputable abbrev triangleLeftPath (f : Hom a b) (g : Hom b c) :
    TwoCell (Path.trans (Path.trans f (Path.refl b)) g) (Path.trans f g) :=
  triangleLeft f g

/-- Right route in the bicategorical triangle diagram. -/
noncomputable abbrev triangleRightPath (f : Hom a b) (g : Hom b c) :
    TwoCell (Path.trans (Path.trans f (Path.refl b)) g) (Path.trans f g) :=
  triangleRight f g

/-- Triangle coherence witnessed by a genuine computational 3-cell. -/
noncomputable def triangleIdentity (f : Hom a b) (g : Hom b c) :
    ThreeCell (triangleLeftPath f g) (triangleRightPath f g) :=
  Derivation₃.step (MetaStep₃.triangle f g)

end Bicategory
end HigherCategory
end ComputationalPaths
