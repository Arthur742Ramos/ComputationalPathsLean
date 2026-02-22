/- 
# Waldhausen K-theory of spaces

This module provides a lightweight scaffold for Waldhausen K-theory of spaces
in the computational paths framework. It reuses the homotopy-level Waldhausen
definitions and records the S-construction, A-theory splitting, additivity,
and Dennis trace data without introducing axioms.

## Key Definitions

- `WaldhausenCategory`: categories with cofibrations and weak equivalences
- `WaldhausenSConstruction`: the S-construction simplicial data
- `ATheory`: A-theory modeled as a split product
- `aTheorySplitting`: A(X) = Sigma^infty X_+ x Wh^Diff(X) (scaffold)
- `waldhausen_additivity`: additivity theorem witness
- `DennisTrace`: K(R) → THH(R) data

## References

- Waldhausen, "Algebraic K-theory of spaces"
- Dennis, "K-theory and Hochschild homology"
- Bokstedt-Hsiang-Madsen, "The cyclotomic trace"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Homotopy.PointedMapCategory
import ComputationalPaths.Path.Homotopy.AlgebraicKTheoryHomotopy
import ComputationalPaths.Path.Homotopy.THH
import ComputationalPaths.Path.Algebra.SpectralAlgebra

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace WaldhausenKTheory

open PointedMapCategory
open SpectralAlgebra

universe u

/-! ## Waldhausen categories and the S-construction -/

/-- Waldhausen category data (cofibrations and weak equivalences). -/
abbrev WaldhausenCategory :=
  Homotopy.AlgebraicKTheoryHomotopy.WaldhausenCategory

/-- The S_n level of the Waldhausen S-construction. -/
abbrev SnLevel :=
  Homotopy.AlgebraicKTheoryHomotopy.SnLevel

/-- Waldhausen S-construction simplicial data. -/
abbrev WaldhausenSConstruction :=
  Homotopy.AlgebraicKTheoryHomotopy.WaldhausenSConstruction

/-- Existence of an S-construction for a Waldhausen category. -/
abbrev WaldhausenSExists :=
  Homotopy.AlgebraicKTheoryHomotopy.WaldhausenSExists

/-- The K-theory space Omega |wS.C| packaged as data. -/
abbrev KTheorySpace :=
  Homotopy.AlgebraicKTheoryHomotopy.KTheorySpace

/-- Waldhausen additivity theorem data. -/
abbrev WaldhausenAdditivity :=
  Homotopy.AlgebraicKTheoryHomotopy.WaldhausenAdditivity

/-! ## A-theory of spaces -/

/-- Add a disjoint basepoint to a space. -/
noncomputable def addBasepoint (X : Type u) : PtdType.{u} where
  carrier := Option X
  pt := none

/-- Suspension spectrum of a space with a disjoint basepoint (skeletal). -/
noncomputable def suspensionSpectrum (X : Type u) : Spectrum.{u} where
  level := fun _ => (addBasepoint X).carrier
  basepoint := fun _ => (addBasepoint X).pt

/-- Smooth Whitehead spectrum placeholder. -/
noncomputable def whiteheadDiff (_X : Type u) : Spectrum.{u} where
  level := fun _ => PUnit
  basepoint := fun _ => PUnit.unit

/-- Levelwise product of spectra (skeletal). -/
noncomputable def spectrumProd (A B : Spectrum.{u}) : Spectrum.{u} where
  level := fun n => A.level n × B.level n
  basepoint := fun n => (A.basepoint n, B.basepoint n)

/-- A-theory of a space, modeled as a spectrum product. -/
noncomputable def ATheory (X : Type u) : Spectrum.{u} :=
  spectrumProd (suspensionSpectrum X) (whiteheadDiff X)

/-- The A-theory splitting A(X) = Sigma^infty X_+ x Wh^Diff(X). -/
noncomputable def aTheorySplitting (X : Type u) :
    Path (ATheory X)
      (spectrumProd (suspensionSpectrum X) (whiteheadDiff X)) :=
  Path.refl _

/-! ## Additivity -/

/-- Waldhausen additivity: a structural witness of the splitting. -/
theorem waldhausen_additivity {C D : WaldhausenCategory}
    (W : WaldhausenAdditivity C D) :
    ∃ f : C.obj → D.obj, f = W.functor :=
  Homotopy.AlgebraicKTheoryHomotopy.waldhausen_additivity_holds C D W

/-! ## Dennis trace -/

/-- The Dennis trace data from K-theory to THH. -/
abbrev DennisTrace (A : Homotopy.THH.RingSpectrum) :=
  Homotopy.THH.DennisTrace A

/-- The degree-n Dennis trace map K_n(R) → THH_n(R). -/
noncomputable def dennisTraceMap {A : Homotopy.THH.RingSpectrum}
    (D : DennisTrace A) (n : Nat) :
    D.kGroups n → D.thhGroups n :=
  D.trace n

/-! ## Summary

We re-exported the Waldhausen category and S-construction data, introduced a
skeletal A-theory splitting, recorded additivity, and exposed the Dennis trace
map in a minimal, axioms-free form.
-/

end WaldhausenKTheory
end Algebra
end Path
end ComputationalPaths
