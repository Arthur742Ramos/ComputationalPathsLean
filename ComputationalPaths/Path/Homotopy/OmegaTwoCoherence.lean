/-
# Higher Coherence for the Path Bicategory and OmegaTwo

This module adds higher categorical coherences that complement the derived
bicategory laws and the Eckmann-Hilton argument for OmegaTwo.

## Key Results

- `hcomp_id_id`: horizontal composition of identity 2-cells is identity
- `pentagon_twoCell`: RwEq-level pentagon as a bicategory 2-cell
- `OmegaTwo.braiding`: braiding on OmegaTwo induced by Eckmann-Hilton
- `OmegaTwo.syllepsis`: the braiding is involutive (a 4-cell)
- `OmegaTwo.braiding_squared`: double braiding contracts to the identity

## References

- Mac Lane, "Categories for the Working Mathematician"
- Eckmann & Hilton (1962)
- Lumsdaine, "Weak omega-categories from intensional type theory"
-/

import ComputationalPaths.Path.BicategoryDerived
import ComputationalPaths.Path.CoherenceDerived
import ComputationalPaths.Path.Homotopy.EckmannHilton

namespace ComputationalPaths
namespace Path

/-! ## Bicategory-level Coherence -/

namespace BicategoryCoherence

open TwoCell

universe u

variable {A : Type u}
variable {a b c d e : A}

/-- Horizontal composition of identity 2-cells is the identity 2-cell. -/
@[simp] theorem hcomp_id_id (f : Path a b) (g : Path b c) :
    hcomp (TwoCell.id f) (TwoCell.id g) =
      TwoCell.id (Path.trans f g) := by
  simp

/-- The RwEq-level pentagon yields a bicategory 2-cell. -/
theorem pentagon_twoCell (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    TwoCell (A := A) (a := a) (b := e)
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  CoherenceDerived.rweq_pentagon_full p q r s

end BicategoryCoherence

/-! ## OmegaTwo Braiding and Syllepsis -/

namespace EckmannHilton

open OmegaGroupoid

universe u

variable {A : Type u}
variable {a : A}

namespace OmegaTwo

/-- The Eckmann-Hilton braiding on OmegaTwo. -/
def braiding (α β : OmegaTwo A a) :
    Derivation₃ (OmegaTwo.hcomp α β) (OmegaTwo.hcomp β α) :=
  hcomp_comm α β

/-- Syllepsis: the braiding is its own inverse (up to a 4-cell). -/
def syllepsis (α β : OmegaTwo A a) :
    Derivation₄ (braiding β α) (Derivation₃.inv (braiding α β)) :=
  contractibility₄ (braiding β α) (Derivation₃.inv (braiding α β))

/-- Double braiding contracts to the identity 3-cell. -/
def braiding_squared (α β : OmegaTwo A a) :
    Derivation₄
      (Derivation₃.vcomp (braiding α β) (braiding β α))
      (Derivation₃.refl (OmegaTwo.hcomp α β)) :=
  contractibility₄
    (Derivation₃.vcomp (braiding α β) (braiding β α))
    (Derivation₃.refl (OmegaTwo.hcomp α β))

end OmegaTwo

end EckmannHilton

/-! ## Summary -/

/-!
This module records bicategory-level coherence (identity hcomp, pentagon 2-cell)
and derives an Eckmann-Hilton braiding on OmegaTwo with a syllepsis 4-cell.
-/

end Path
end ComputationalPaths
