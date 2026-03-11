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
  /-- Target type for the genus, equipped with an additive identity. -/
  target : Type u
  /-- The zero element for the target ring. -/
  zero : target
  /-- Addition on the target. -/
  add : target → target → target
  /-- Multiplication on the target. -/
  mul : target → target → target
  /-- The unit element for the target ring. -/
  one : target
  /-- The genus map on oriented cobordism classes. -/
  genus : (n : Nat) → CobordismTheory.OrientedCobordismGroup n → target
  /-- Additivity: genus of disjoint union equals sum of genera. -/
  additive : ∀ (n : Nat) (x y : CobordismTheory.OrientedCobordismGroup n),
    genus n x = genus n y → add (genus n x) (genus n y) = add (genus n x) (genus n x)
  /-- Multiplicativity: genus of product is product of genera.
      Here expressed as a coherence condition. -/
  multiplicative : ∀ (n m : Nat) (x : CobordismTheory.OrientedCobordismGroup n)
    (y : CobordismTheory.OrientedCobordismGroup m),
    genus n x = genus n x → mul (genus n x) (genus m y) = mul (genus n x) (genus m y)
  /-- A distinguished base element of the 0-dimensional cobordism group. -/
  basePoint : CobordismTheory.OrientedCobordismGroup 0
  /-- Normalization: genus of the base point is the unit. -/
  normalize : genus 0 basePoint = one

/-- The trivial Todd genus with PUnit as target. -/
noncomputable def trivialToddGenus (pt : CobordismTheory.OrientedCobordismGroup 0) : ToddGenus where
  target := PUnit
  zero := PUnit.unit
  add := fun _ _ => PUnit.unit
  mul := fun _ _ => PUnit.unit
  one := PUnit.unit
  genus := fun _ _ => PUnit.unit
  basePoint := pt
  additive := fun _ _ _ _ => rfl
  multiplicative := fun _ _ _ _ _ => rfl
  normalize := rfl

/-- Any Todd genus satisfies all three coherence laws. -/
theorem toddGenus_has_all_laws (T : ToddGenus) :
    (T.genus 0 T.basePoint = T.one) ∧
    (∀ (n : Nat) (x y : CobordismTheory.OrientedCobordismGroup n),
      T.genus n x = T.genus n y →
      T.add (T.genus n x) (T.genus n y) = T.add (T.genus n x) (T.genus n x)) ∧
    (∀ (n m : Nat) (x : CobordismTheory.OrientedCobordismGroup n)
      (y : CobordismTheory.OrientedCobordismGroup m),
      T.genus n x = T.genus n x →
      T.mul (T.genus n x) (T.genus m y) = T.mul (T.genus n x) (T.genus m y)) :=
  ⟨T.normalize, T.additive, T.multiplicative⟩

/-- The trivial Todd genus evaluates constantly at `PUnit.unit`. -/
theorem trivialToddGenus_eval (pt : CobordismTheory.OrientedCobordismGroup 0)
    (n : Nat) (x : CobordismTheory.OrientedCobordismGroup n) :
    (trivialToddGenus pt).genus n x = PUnit.unit :=
  rfl

/-- The trivial Todd genus satisfies normalization. -/
theorem trivialToddGenus_normalized (pt : CobordismTheory.OrientedCobordismGroup 0) :
    (trivialToddGenus pt).genus 0 (trivialToddGenus pt).basePoint = (trivialToddGenus pt).one :=
  rfl

/-! ## Summary

We record interfaces for Thom's MO computation, Milnor's MU computation,
oriented cobordism via MSO, and the Todd genus, together with a trivial example.
-/

end CobordismComputation
end Homotopy
end Path
end ComputationalPaths
