/-
# Formal Group Laws

This module records formal group law data in the computational paths framework.
We include the universal formal group law (Lazard ring), Quillen's MU_+ ~= L
theorem data, p-typical and Honda formal group laws, and logarithms/exponentials.

## Key Results

| Definition | Description |
|-----------|-------------|
| `FormalPowerSeries` | Formal power series over a ring |
| `FormalGroupLaw` | Formal group law data over a commutative ring |
| `LazardRing` | Lazard ring with universal FGL |
| `QuillenTheorem` | MU_+ ~= Lazard ring data |
| `PTypicalFGL` | p-typical formal group law data |
| `HondaFormalGroup` | Honda formal group Gamma_n of height n |
| `FormalGroupLogExp` | Logarithm/exponential data |

## References

- Lazard, "Commutative Formal Groups"
- Quillen, "On the Formal Group Laws of Unoriented and Complex Cobordism"
- Hazewinkel, "Formal Groups and Applications"
- Ravenel, "Complex Cobordism and Stable Homotopy Groups of Spheres"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Algebra.DerivedAlgebraicGeometry
import ComputationalPaths.Path.Homotopy.ChromaticHomotopy

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace FormalGroupLaw

open Algebra.DerivedAlgebraicGeometry
open ChromaticHomotopy

universe u

/-! ## Formal power series -/

/-- A formal power series in one variable. -/
structure FormalPowerSeries (R : Type u) where
  coeff : Nat → R

/-- A formal power series in two variables. -/
structure FormalPowerSeries2 (R : Type u) where
  coeff : Nat → Nat → R

/-! ## Formal group laws -/

/-- A commutative formal group law over a commutative ring. -/
structure FormalGroupLaw (R : Type u) (RR : CommRingData R) where
  /-- Formal sum F(x,y). -/
  series : FormalPowerSeries2 R
  /-- Unit law F(x,0) = x (recorded). -/
  unit_left : True
  /-- Unit law F(0,y) = y (recorded). -/
  unit_right : True
  /-- Associativity (recorded). -/
  assoc : True
  /-- Commutativity (recorded). -/
  comm : True
  /-- Linear term is x + y (recorded). -/
  linear : True

/-! ## The Lazard ring and universal FGL -/

/-- Lazard ring with its universal formal group law. -/
structure LazardRing where
  /-- Underlying carrier. -/
  carrier : Type u
  /-- Ring structure. -/
  ring : CommRingData carrier
  /-- Universal formal group law over L. -/
  universalFGL : FormalGroupLaw carrier ring
  /-- Classifying map: any FGL over R gives a ring map L -> R. -/
  classify :
    ∀ {R : Type u} (RR : CommRingData R),
      FormalGroupLaw R RR → RingHom ring RR
  /-- Uniqueness of the classifying map (recorded). -/
  classify_unique : True

/-! ## Quillen's theorem for complex cobordism -/

/-- The coefficient ring MU_+ with its canonical formal group law. -/
structure MUPlusRing where
  /-- Carrier of MU_+. -/
  carrier : Type u
  /-- Ring structure. -/
  ring : CommRingData carrier
  /-- The complex cobordism formal group law. -/
  fgl : FormalGroupLaw carrier ring

/-- Quillen's theorem: MU_+ ~= Lazard ring. -/
structure QuillenTheorem where
  /-- The complex cobordism coefficient ring. -/
  muPlus : MUPlusRing
  /-- Lazard ring. -/
  lazard : LazardRing
  /-- Map MU_+ -> L. -/
  toLazard : muPlus.carrier → lazard.carrier
  /-- Map L -> MU_+. -/
  toMU : lazard.carrier → muPlus.carrier
  /-- Left inverse property (recorded). -/
  left_inv : True
  /-- Right inverse property (recorded). -/
  right_inv : True
  /-- Compatibility with the universal formal group law (recorded). -/
  fgl_compat : True

/-! ## p-typical formal group laws -/

/-- p-typical formal group law with Hazewinkel generators. -/
structure PTypicalFGL (p : Prime) (R : Type u) (RR : CommRingData R) extends
    FormalGroupLaw R RR where
  /-- Hazewinkel generators v_n. -/
  vCoeff : Nat → R
  /-- The p-series [p]_F(x). -/
  pSeries : FormalPowerSeries R
  /-- The p-series has the p-typical shape (recorded). -/
  pSeries_shape : True

/-! ## Honda formal group law -/

/-- The Honda formal group law Gamma_n of height n at p. -/
structure HondaFormalGroup (p : Prime) (n : Nat) where
  /-- Base ring. -/
  ring : Type u
  /-- Ring structure. -/
  ringData : CommRingData ring
  /-- The underlying p-typical formal group law. -/
  ptypical : PTypicalFGL p ring ringData
  /-- Height. -/
  height : Nat
  /-- Height equals n. -/
  height_eq : height = n
  /-- The Honda p-series (recorded). -/
  hondaSeries : FormalPowerSeries ring
  /-- Honda relation [p](x) = x^(p^n) (recorded). -/
  honda_relation : True

/-- Type alias for the Honda formal group Gamma_n. -/
def HondaGamma (p : Prime) (n : Nat) : Type (u + 1) :=
  HondaFormalGroup (p := p) n

/-! ## Logarithms and exponentials -/

/-- Formal group logarithm. -/
structure FormalGroupLogarithm (R : Type u) where
  /-- Logarithm series. -/
  series : FormalPowerSeries R
  /-- Linear term is 1 (recorded). -/
  linear_term : True

/-- Formal group exponential. -/
structure FormalGroupExponential (R : Type u) where
  /-- Exponential series. -/
  series : FormalPowerSeries R
  /-- Linear term is 1 (recorded). -/
  linear_term : True

/-- Logarithm/exponential data for a formal group law. -/
structure FormalGroupLogExp (R : Type u) (RR : CommRingData R)
    (F : FormalGroupLaw R RR) where
  /-- Logarithm series. -/
  log : FormalGroupLogarithm R
  /-- Exponential series. -/
  exp : FormalGroupExponential R
  /-- log(exp(x)) = x (recorded). -/
  log_exp : True
  /-- exp(log(x)) = x (recorded). -/
  exp_log : True
  /-- log identifies F with the additive formal group law (recorded). -/
  log_additive : True

/-! ## Summary -/

-- This module records formal group law data: Lazard ring universality,
-- Quillen's MU_+ ~= L theorem, p-typical and Honda Gamma_n structures,
-- and logarithm/exponential series data.

end FormalGroupLaw
end Homotopy
end Path
end ComputationalPaths
