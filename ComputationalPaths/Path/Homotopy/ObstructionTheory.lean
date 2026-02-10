/- 
# Obstruction theory for CW-complex extensions

This module packages a minimal obstruction-theoretic interface for extending maps over
relative CW complexes using Mathlib's categorical CW-complex definition.

## Key Results

- `Extension`: data of a map `Y ⟶ Z` extending `g : X ⟶ Z` along `f : X ⟶ Y`
- `obstructionFree`: existence of an extension (no obstruction)
- `cellRestriction`: restriction of a map to an attached cell
- `hom_ext_of_cells`, `extension_unique`: uniqueness of extensions from cell data

## References

- Mathlib `Topology/CWComplex/Abstract/Basic`
- Hatcher, *Algebraic Topology*, Chapter 4 (obstruction theory)
-/

import Mathlib.Topology.CWComplex.Abstract.Basic
import ComputationalPaths.Path.Basic.Core

open CategoryTheory
open HomotopicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace ObstructionTheory

universe u

variable {X Y Z : TopCat.{u}} {f : X ⟶ Y}

/-! ## Extension data -/

/-- Data of a map `Y ⟶ Z` extending `g : X ⟶ Z` along `f : X ⟶ Y`. -/
structure Extension (f : X ⟶ Y) (g : X ⟶ Z) where
  /-- The extended map. -/
  map : Y ⟶ Z
  /-- Compatibility on the base. -/
  comm : Path (f ≫ map) g

/-- The extension problem is obstruction-free if an extension exists. -/
def obstructionFree (f : X ⟶ Y) (g : X ⟶ Z) : Prop :=
  Nonempty (Extension f g)

/-! ## Cell restrictions -/

/-- Restrict a map to a CW cell of a relative CW complex. -/
noncomputable def cellRestriction (c : TopCat.RelativeCWComplex f) (φ : Y ⟶ Z)
    (γ : RelativeCellComplex.Cells c) :=
  γ.ι ≫ φ

/-- A map out of a relative CW complex is determined by its restriction to the base
and to each attached cell (Path form). -/
def hom_ext_of_cells (c : TopCat.RelativeCWComplex f) {φ₁ φ₂ : Y ⟶ Z}
    (h₀ : Path (f ≫ φ₁) (f ≫ φ₂))
    (hcell : ∀ γ, Path (cellRestriction (f := f) c φ₁ γ)
      (cellRestriction (f := f) c φ₂ γ)) :
    Path φ₁ φ₂ := by
  apply Path.ofEq
  apply RelativeCellComplex.hom_ext (c := c) h₀.toEq
  intro γ
  simpa [cellRestriction] using (hcell γ).toEq

/-- Extensions are unique once their restrictions to the base and all cells agree
    (Path between extension maps). -/
def extension_unique (c : TopCat.RelativeCWComplex f) {g : X ⟶ Z}
    {e₁ e₂ : Extension f g}
    (hcell : ∀ γ, Path (cellRestriction (f := f) c e₁.map γ)
      (cellRestriction (f := f) c e₂.map γ)) :
    Path e₁.map e₂.map := by
  apply hom_ext_of_cells (f := f) (c := c)
  · exact Path.trans e₁.comm (Path.symm e₂.comm)
  · exact hcell

/-! ## Summary

We package the extension problem for relative CW complexes as a map together with a
commuting triangle, define obstruction-freeness as existence of an extension, and
show that extensions are unique once their restrictions to the base and each cell
agree.
-/

end ObstructionTheory
end Homotopy
end Path
end ComputationalPaths
