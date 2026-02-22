/-
# Higher Path Operations

This module records higher categorical operations for derivation-level 2-cells,
including Godement interchange, naturality squares for associator/unitors, and
the pentagon/triangle coherences at the 3-cell level.

## Key Results

- `godementInterchange`: Godement interchange for derivation-level 2-cells
- `associatorNatural`, `leftUnitorNatural`, `rightUnitorNatural`: naturality squares
- `pentagonIdentity`, `triangleIdentity`: 3-cell pentagon/triangle identities
-/

import ComputationalPaths.Path.OmegaGroupoid

namespace ComputationalPaths
namespace Path
namespace HigherPathOperations

open OmegaGroupoid

universe u

variable {A : Type u}
variable {a b c d e : A}

/-! ## Godement Interchange -/

/-- Godement interchange for derivation-level 2-cells. -/
noncomputable def godementInterchange {f f' : Path a b} {g g' : Path b c}
    (alpha : Derivation₂ f f') (beta : Derivation₂ g g') :
    Derivation₃
      (Derivation₂.vcomp (OmegaGroupoid.whiskerRight alpha g) (OmegaGroupoid.whiskerLeft f' beta))
      (Derivation₂.vcomp (OmegaGroupoid.whiskerLeft f beta) (OmegaGroupoid.whiskerRight alpha g')) :=
  Derivation₃.step (MetaStep₃.interchange alpha beta)

/-! ## Naturality Squares -/

/-- Naturality of the associator at the 3-cell level. -/
noncomputable def associatorNatural {f f' : Path a b} {g g' : Path b c} {h h' : Path c d}
    (alpha : Derivation₂ f f') (beta : Derivation₂ g g') (gamma : Derivation₂ h h') :
    Derivation₃
      (Derivation₂.vcomp (OmegaGroupoid.hcomp (OmegaGroupoid.hcomp alpha beta) gamma) (associator f' g' h'))
      (Derivation₂.vcomp (associator f g h) (OmegaGroupoid.hcomp alpha (OmegaGroupoid.hcomp beta gamma))) :=
  contractibility₃ _ _

/-- Naturality of the left unitor at the 3-cell level. -/
noncomputable def leftUnitorNatural {f g : Path a b} (alpha : Derivation₂ f g) :
    Derivation₃
      (Derivation₂.vcomp
        (OmegaGroupoid.hcomp (Derivation₂.refl (Path.refl a)) alpha) (leftUnitor g))
      (Derivation₂.vcomp (leftUnitor f) alpha) :=
  contractibility₃ _ _

/-- Naturality of the right unitor at the 3-cell level. -/
noncomputable def rightUnitorNatural {f g : Path a b} (alpha : Derivation₂ f g) :
    Derivation₃
      (Derivation₂.vcomp
        (OmegaGroupoid.hcomp alpha (Derivation₂.refl (Path.refl b))) (rightUnitor g))
      (Derivation₂.vcomp (rightUnitor f) alpha) :=
  contractibility₃ _ _

/-! ## Pentagon and Triangle Coherence -/

/-- Pentagon identity for associators as a 3-cell. -/
noncomputable def pentagonIdentity (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    Derivation₃ (pentagonLeft f g h k) (pentagonRight f g h k) :=
  pentagonCoherence f g h k

/-- Triangle identity for unitors as a 3-cell. -/
noncomputable def triangleIdentity (f : Path a b) (g : Path b c) :
    Derivation₃ (triangleLeft f g) (triangleRight f g) :=
  triangleCoherence f g

/-! ## Additional Theorem Statements -/

/-! ## Summary -/

/-!
We package the derivation-level Godement interchange, naturality of associator
and unitors, and the pentagon/triangle coherences as explicit 3-cells.
-/

end HigherPathOperations
end Path
end ComputationalPaths
