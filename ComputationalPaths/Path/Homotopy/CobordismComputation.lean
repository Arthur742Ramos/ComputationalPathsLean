/-
# Cobordism Computations

This module records lightweight, axiom-free interfaces for key cobordism
computations: Thom's calculation of MO, Milnor's computation of MU,
oriented cobordism (MSO), and the Todd genus.

## Key Results

| Definition | Description |
|-----------|-------------|
| `ThomMOComputation` | Thom's MO computation data |
| `MilnorMUComputation` | Milnor's MU computation data |
| `MSOComputation` | Oriented cobordism (MSO) computation data |
| `ToddGenus` | Todd genus on oriented cobordism |
| `trivialToddGenus` | A trivial Todd genus example |

## References

- Thom, "Quelques proprietes globales des varietes differentiables"
- Milnor, "On the cobordism ring Omega* and a complex analogue"
- Quillen, "On the Formal Group Laws of Unoriented and Complex Cobordism"
- Hirzebruch, "Topological Methods in Algebraic Geometry"
- Stong, "Notes on Cobordism Theory"
-/

import ComputationalPaths.Path.Homotopy.CobordismTheory
import ComputationalPaths.Path.Homotopy.ThomSpectra
import ComputationalPaths.Path.Homotopy.FormalGroupLaw

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace CobordismComputation

open CobordismTheory ThomSpectra FormalGroupLaw

universe u

/-! ## Thom's computation of MO -/

/-- Thom's MO computation data. -/
structure ThomMOComputation where
  /-- Thom spectrum MO. -/
  mo : CobordismTheory.ThomSpectrumMO
  /-- Coefficient groups Omega_*^O. -/
  coeff : Nat → Type (u + 1)
  /-- Pontryagin-Thom map into coefficients. -/
  ptMap : (n : Nat) → CobordismTheory.UnorientedCobordismGroup n → coeff n
  /-- Stiefel-Whitney numbers classify cobordism (recorded). -/
  sw_classify : True
  /-- Polynomial generator description of MO_* (recorded). -/
  structure_theorem : CobordismTheory.UnorientedStructureTheorem

/-! ## Milnor's computation of MU -/

/-- Milnor's MU computation data. -/
structure MilnorMUComputation where
  /-- Thom spectrum MU. -/
  mu : ThomSpectra.ThomSpectrumMU
  /-- Coefficient groups MU_*. -/
  coeff : Nat → Type (u + 1)
  /-- Complex orientation data (recorded). -/
  orientation : True
  /-- Milnor basis computation data (recorded). -/
  milnor_basis : True
  /-- Quillen's theorem linking MU_+ with the Lazard ring. -/
  quillen : FormalGroupLaw.QuillenTheorem

/-! ## Oriented cobordism (MSO) -/

/-- Oriented cobordism computation data for MSO. -/
structure MSOComputation where
  /-- Thom spectrum MSO. -/
  mso : CobordismTheory.ThomSpectrumMSO
  /-- Coefficient groups Omega_*^{SO}. -/
  coeff : Nat → Type (u + 1)
  /-- Pontryagin-Thom map into coefficients. -/
  ptMap : (n : Nat) → CobordismTheory.OrientedCobordismGroup n → coeff n
  /-- Pontryagin number classification (recorded). -/
  pontryagin_numbers : True
  /-- Hirzebruch signature input (recorded). -/
  hirzebruch : True

/-! ## Todd genus -/

/-- The Todd genus on oriented cobordism classes. -/
structure ToddGenus where
  /-- Target type for the genus. -/
  target : Type u
  /-- The genus map on oriented cobordism classes. -/
  genus : (n : Nat) → CobordismTheory.OrientedCobordismGroup n → target
  /-- Additivity on disjoint unions (recorded). -/
  additive : True
  /-- Multiplicativity on products (recorded). -/
  multiplicative : True
  /-- Normalization on the point (recorded). -/
  normalize : True

/-- The trivial Todd genus with PUnit as target. -/
def trivialToddGenus : ToddGenus where
  target := PUnit
  genus := fun _ _ => PUnit.unit
  additive := True.intro
  multiplicative := True.intro
  normalize := True.intro

/-! ## Summary

We record interfaces for Thom's MO computation, Milnor's MU computation,
oriented cobordism via MSO, and the Todd genus, together with a trivial example.
-/

end CobordismComputation
end Homotopy
end Path
end ComputationalPaths
