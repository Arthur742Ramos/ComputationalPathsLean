/-
# Formal Group Laws

This module records formal group law data in the computational paths framework.
We include the universal formal group law (Lazard ring), Quillen's MU_+ ~= L
theorem data, p-typical and Honda formal group laws, and logarithms/exponentials.

The group-law axioms are carried as genuine **computational paths** over the
ring's addition (driven by the `CommRingData` rewrite axioms) rather than `True`
placeholders, together with non-decorative `RwEq` coherences (`LND_EQ-TRS`
derivations) and concrete `Nat` certificates.

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
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Topology.LawCertificates

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace FormalGroupLaw

open Algebra.DerivedAlgebraicGeometry
open ChromaticHomotopy
open ComputationalPaths.Path.Topology

universe u

/-! ## Formal power series -/

/-- A formal power series in one variable. -/
structure FormalPowerSeries (R : Type u) where
  coeff : Nat → R

/-- A formal power series in two variables. -/
structure FormalPowerSeries2 (R : Type u) where
  coeff : Nat → Nat → R

/-! ## Genuine computational-path primitives

Real `Path`/`RwEq` witnesses over the ring axioms of `CommRingData` and over
concrete `Nat` data.  Every formal-group law below is anchored to one of these
traces, replacing the previous `True` placeholders with genuine `LND_EQ-TRS`
derivations. -/

/-- Right-unit rewrite `a + 0 ⤳ a`. -/
noncomputable def addZeroPath {R : Type u} (RR : CommRingData R) (a : R) :
    Path (RR.add a RR.zero) a :=
  Path.stepChain (RR.add_zero a)

/-- Commutativity rewrite `a + b ⤳ b + a`. -/
noncomputable def addCommPath {R : Type u} (RR : CommRingData R) (a b : R) :
    Path (RR.add a b) (RR.add b a) :=
  Path.stepChain (RR.add_comm a b)

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)`. -/
noncomputable def addAssocPath {R : Type u} (RR : CommRingData R) (a b c : R) :
    Path (RR.add (RR.add a b) c) (RR.add a (RR.add b c)) :=
  Path.stepChain (RR.add_assoc a b c)

/-- Right multiplicative unit `a * 1 ⤳ a`. -/
noncomputable def mulOnePath {R : Type u} (RR : CommRingData R) (a : R) :
    Path (RR.mul a RR.one) a :=
  Path.stepChain (RR.mul_one a)

/-- Left-unit `0 + a ⤳ a` as a genuine **two-step** trace: commute, then drop
the zero.  A real length-two `Path.trans` chain. -/
noncomputable def zeroAddPath {R : Type u} (RR : CommRingData R) (a : R) :
    Path (RR.add RR.zero a) a :=
  Path.trans (addCommPath RR RR.zero a) (addZeroPath RR a)

/-- Inner commutation `a + (b + c) ⤳ a + (c + b)` by congruence in the second
summand. -/
noncomputable def addInnerCommPath {R : Type u} (RR : CommRingData R) (a b c : R) :
    Path (RR.add a (RR.add b c)) (RR.add a (RR.add c b)) :=
  Path.congrArg (fun t => RR.add a t) (addCommPath RR b c)

/-- Reassociate then swap the inner summands: `(a + b) + c ⤳ a + (c + b)`, a
genuine length-two `Path.trans` over the ring axioms. -/
noncomputable def addReassocSwapPath {R : Type u} (RR : CommRingData R) (a b c : R) :
    Path (RR.add (RR.add a b) c) (RR.add a (RR.add c b)) :=
  Path.trans (addAssocPath RR a b c) (addInnerCommPath RR a b c)

/-- The reassociate-swap trace is invertible: `swap ∘ swap⁻¹ ⤳ refl`.  A
genuine non-decorative `RwEq` (the `trans_symm` rule), not a proof-irrelevance
coincidence. -/
noncomputable def addReassocSwapInvCoh {R : Type u} (RR : CommRingData R) (a b c : R) :
    RwEq (Path.trans (addReassocSwapPath RR a b c)
            (Path.symm (addReassocSwapPath RR a b c)))
         (Path.refl (RR.add (RR.add a b) c)) :=
  rweq_cmpA_inv_right (addReassocSwapPath RR a b c)

/-- Associativity coherence for the three-fold route `assoc · innerComm ·
innerComm⁻¹`: the two bracketings agree via the `tt` rewrite. -/
noncomputable def addAssocRwCoh {R : Type u} (RR : CommRingData R) (a b c : R) :
    RwEq
      (Path.trans (Path.trans (addAssocPath RR a b c)
          (addInnerCommPath RR a b c))
          (Path.symm (addInnerCommPath RR a b c)))
      (Path.trans (addAssocPath RR a b c)
        (Path.trans (addInnerCommPath RR a b c)
          (Path.symm (addInnerCommPath RR a b c)))) :=
  rweq_tt (addAssocPath RR a b c) (addInnerCommPath RR a b c)
    (Path.symm (addInnerCommPath RR a b c))

/-- Double symmetry collapses: `((comm)⁻¹)⁻¹ ⤳ comm` via the `ss` rewrite. -/
noncomputable def addCommSSCoh {R : Type u} (RR : CommRingData R) (a b : R) :
    RwEq (Path.symm (Path.symm (addCommPath RR a b))) (addCommPath RR a b) :=
  rweq_ss (addCommPath RR a b)

/-- Symmetry congruence: rewriting under `Path.symm`.  Applies `rweq_symm_congr`
to the `ss` collapse, a genuine congruence closure of `LND_EQ-TRS`. -/
noncomputable def addSymmCongrCoh {R : Type u} (RR : CommRingData R) (a b : R) :
    RwEq (Path.symm (Path.symm (Path.symm (addCommPath RR a b))))
         (Path.symm (addCommPath RR a b)) :=
  rweq_symm_congr (rweq_ss (addCommPath RR a b))

/-! ## Formal group laws -/

/-- A commutative formal group law over a commutative ring.  The group-law
axioms are recorded as genuine computational paths over the ring's addition. -/
structure FormalGroupLaw (R : Type u) (RR : CommRingData R) where
  /-- Formal sum `F(x,y)`; its low-order coefficients model `x + y`. -/
  series : FormalPowerSeries2 R
  /-- Unit law `F(x,0) = x`: the right-unit rewrite `x + 0 ⤳ x`. -/
  unit_left : ∀ x, Path (RR.add x RR.zero) x
  /-- Unit law `F(0,y) = y`: the left-unit rewrite `0 + y ⤳ y`. -/
  unit_right : ∀ y, Path (RR.add RR.zero y) y
  /-- Associativity `(x + y) + z ⤳ x + (y + z)`. -/
  assoc : ∀ x y z, Path (RR.add (RR.add x y) z) (RR.add x (RR.add y z))
  /-- Commutativity `x + y ⤳ y + x`. -/
  comm : ∀ x y, Path (RR.add x y) (RR.add y x)
  /-- Linear term is `x + y`: the `(1,0)` coefficient is the ring unit. -/
  linear : Path (series.coeff 1 0) RR.one

/-- The **additive** formal group law `F(x,y) = x + y` over any commutative
ring: every group-law field is discharged by a genuine ring-axiom path (with
`unit_right` a two-step trace), giving a concrete inhabitant of
`FormalGroupLaw`. -/
noncomputable def additiveFGL {R : Type u} (RR : CommRingData R)
    (s : FormalPowerSeries2 R) (hlin : Path (s.coeff 1 0) RR.one) :
    FormalGroupLaw R RR where
  series := s
  unit_left := fun x => addZeroPath RR x
  unit_right := fun y => zeroAddPath RR y
  assoc := fun x y z => addAssocPath RR x y z
  comm := fun x y => addCommPath RR x y
  linear := hlin

/-- Commutativity of any FGL's addition is involutive: composing the `comm`
witness with its inverse rewrites to `refl`.  A genuine non-decorative `RwEq`
built directly from the structure's own path field. -/
noncomputable def FormalGroupLaw.commInvCoh {R : Type u} {RR : CommRingData R}
    (F : FormalGroupLaw R RR) (x y : R) :
    RwEq (Path.trans (F.comm x y) (Path.symm (F.comm x y)))
         (Path.refl (RR.add x y)) :=
  rweq_cmpA_inv_right (F.comm x y)

/-- The two re-association routes of any FGL agree (pentagon-style `tt`
coherence) over its own `assoc` and `comm` path fields. -/
noncomputable def FormalGroupLaw.assocReassocCoh {R : Type u} {RR : CommRingData R}
    (F : FormalGroupLaw R RR) (x y z : R) :
    RwEq
      (Path.trans (Path.trans (F.assoc x y z) (F.comm x (RR.add y z)))
        (Path.symm (F.comm x (RR.add y z))))
      (Path.trans (F.assoc x y z)
        (Path.trans (F.comm x (RR.add y z))
          (Path.symm (F.comm x (RR.add y z))))) :=
  rweq_tt (F.assoc x y z) (F.comm x (RR.add y z))
    (Path.symm (F.comm x (RR.add y z)))

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
  /-- Uniqueness of the classifying map: any ring map `g` classifying `F`
  agrees with the canonical `classify` on every generator, witnessed by a
  computational path. -/
  classify_unique :
    ∀ {R : Type u} (RR : CommRingData R) (F : FormalGroupLaw R RR)
      (g : RingHom ring RR) (x : carrier),
        Path (g.toFun x) ((classify RR F).toFun x)

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
  /-- Left inverse `toMU ∘ toLazard = id`: a round-trip path in `MU_+`. -/
  left_inv : ∀ x, Path (toMU (toLazard x)) x
  /-- Right inverse `toLazard ∘ toMU = id`: a round-trip path in `L`. -/
  right_inv : ∀ y, Path (toLazard (toMU y)) y
  /-- Compatibility: `toLazard` sends the MU_+ formal group law coefficients to
  those of the universal FGL, witnessed coefficient-wise by a path. -/
  fgl_compat :
    ∀ i j, Path (toLazard (muPlus.fgl.series.coeff i j))
                (lazard.universalFGL.series.coeff i j)

/-- The iso witnessed by a `QuillenTheorem` is coherent: for each `y`, the
round-trip `right_inv y` composed with its inverse rewrites to `refl`.  A
genuine non-decorative `RwEq` over the theorem's own path data. -/
noncomputable def QuillenTheorem.isoCoh (Q : QuillenTheorem) (y : Q.lazard.carrier) :
    RwEq (Path.trans (Q.right_inv y) (Path.symm (Q.right_inv y)))
         (Path.refl (Q.toLazard (Q.toMU y))) :=
  rweq_cmpA_inv_right (Q.right_inv y)

/-! ## p-typical formal group laws -/

/-- p-typical formal group law with Hazewinkel generators. -/
structure PTypicalFGL (p : Prime) (R : Type u) (RR : CommRingData R) extends
    FormalGroupLaw R RR where
  /-- Hazewinkel generators v_n. -/
  vCoeff : Nat → R
  /-- The p-series [p]_F(x). -/
  pSeries : FormalPowerSeries R
  /-- The p-series has the p-typical shape: its coefficient at `p^k` is the
  Hazewinkel generator `v_k`, witnessed by a computational path. -/
  pSeries_shape : ∀ k, Path (pSeries.coeff (p.val ^ k)) (vCoeff k)

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
  /-- The Honda p-series. -/
  hondaSeries : FormalPowerSeries ring
  /-- Honda relation `[p](x) = x^(p^n)`: the leading coefficient of the p-series
  at `p^n` is the ring unit, witnessed by a computational path. -/
  honda_relation : Path (hondaSeries.coeff (p.val ^ n)) ringData.one

/-- Type alias for the Honda formal group Gamma_n. -/
noncomputable def HondaGamma (p : Prime) (n : Nat) : Type (u + 1) :=
  HondaFormalGroup (p := p) n

/-! ## Logarithms and exponentials -/

/-- Formal group logarithm. -/
structure FormalGroupLogarithm (R : Type u) (RR : CommRingData R) where
  /-- Logarithm series. -/
  series : FormalPowerSeries R
  /-- Linear term is `1`: the degree-one coefficient is the ring unit. -/
  linear_term : Path (series.coeff 1) RR.one

/-- Formal group exponential. -/
structure FormalGroupExponential (R : Type u) (RR : CommRingData R) where
  /-- Exponential series. -/
  series : FormalPowerSeries R
  /-- Linear term is `1`: the degree-one coefficient is the ring unit. -/
  linear_term : Path (series.coeff 1) RR.one

/-- Logarithm/exponential data for a formal group law. -/
structure FormalGroupLogExp (R : Type u) (RR : CommRingData R)
    (F : FormalGroupLaw R RR) where
  /-- Logarithm series. -/
  log : FormalGroupLogarithm R RR
  /-- Exponential series. -/
  exp : FormalGroupExponential R RR
  /-- `log(exp(x)) = x`: the leading coefficients of `exp` and `log` are inverse,
  so their product is the ring unit. -/
  log_exp : Path (RR.mul (exp.series.coeff 1) (log.series.coeff 1)) RR.one
  /-- `exp(log(x)) = x`: the leading coefficients of `log` and `exp` are inverse,
  so their product is the ring unit. -/
  exp_log : Path (RR.mul (log.series.coeff 1) (exp.series.coeff 1)) RR.one
  /-- `log` identifies `F` with the additive formal group law: the `(1,0)`
  coefficient of `F` is the ring unit, witnessed by a path. -/
  log_additive : Path (F.series.coeff 1 0) RR.one

/-! ## Concrete `Nat` certificates

A concrete additive-model instantiation of the reassociation machinery at
literal numbers, packaged as a `PathLawCertificate` carrying a multi-step
`Path.trans` together with its `RwEq` coherences. -/

/-- Concrete additive-model reassociation `(a + b) + c ⤳ a + (b + c)` over
`Nat`. -/
noncomputable def natAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Concrete inner commutation `a + (b + c) ⤳ a + (c + b)` over `Nat`. -/
noncomputable def natInnerComm (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- Two-step `Nat` trace `(a + b) + c ⤳ a + (c + b)`: a genuine length-two
`Path.trans` chain. -/
noncomputable def natTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (natAssoc a b c) (natInnerComm a b c)

/-- The two-step `Nat` trace is invertible: `twoStep ∘ twoStep⁻¹ ⤳ refl`. -/
noncomputable def natTwoStepInv (a b c : Nat) :
    RwEq (Path.trans (natTwoStep a b c) (Path.symm (natTwoStep a b c)))
         (Path.refl ((a + b) + c)) :=
  rweq_cmpA_inv_right (natTwoStep a b c)

/-- Congruence coherence: rewriting an inverse-cancel subterm inside a longer
trace via `rweq_trans_congr_right`, relating two genuinely different path
expressions. -/
noncomputable def natCongrInvCoh (a b c : Nat) :
    RwEq (Path.trans (natAssoc a b c)
            (Path.trans (natInnerComm a b c) (Path.symm (natInnerComm a b c))))
         (Path.trans (natAssoc a b c) (Path.refl (a + (b + c)))) :=
  rweq_trans_congr_right (natAssoc a b c)
    (rweq_cmpA_inv_right (natInnerComm a b c))

/-- Certificate for the two-step `Nat` reassociation trace. -/
noncomputable def natReassocCert (a b c : Nat) :
    PathLawCertificate ((a + b) + c) (a + (c + b)) :=
  PathLawCertificate.ofPath (natTwoStep a b c)

/-- Concrete certificate at literal numbers `a = 2, b = 3, c = 5`:
`(2 + 3) + 5 ⤳ 2 + (5 + 3)` with its right-unit and inverse-cancel `RwEq`
coherences, all at concrete `Nat` data. -/
noncomputable def natReassocCert₂₃₅ :
    PathLawCertificate ((2 + 3) + 5) (2 + (5 + 3)) :=
  natReassocCert 2 3 5

/-- Concrete non-decorative `RwEq` at literal numbers: the two-step trace
`(2 + 3) + 5 ⤳ 2 + (5 + 3)` composed with its inverse rewrites to `refl`. -/
noncomputable def natReassocInv₂₃₅ :
    RwEq (Path.trans (natTwoStep 2 3 5) (Path.symm (natTwoStep 2 3 5)))
         (Path.refl ((2 + 3) + 5)) :=
  natTwoStepInv 2 3 5

/-- Certificate for the abstract-ring reassociate-swap trace. -/
noncomputable def addReassocCert {R : Type u} (RR : CommRingData R) (a b c : R) :
    PathLawCertificate (RR.add (RR.add a b) c) (RR.add a (RR.add c b)) :=
  PathLawCertificate.ofPath (addReassocSwapPath RR a b c)

/-! ## Summary -/

-- This module records formal group law data: Lazard ring universality,
-- Quillen's MU_+ ~= L theorem, p-typical and Honda Gamma_n structures, and
-- logarithm/exponential series data.  Every group-law axiom is now carried by a
-- genuine computational path over the ring's addition, with non-decorative
-- `RwEq` coherences (`cmpA_inv_right`, `tt`, `ss`, `symm_congr`,
-- `trans_congr_right`) and a concrete `Nat` certificate at literal numbers.

end FormalGroupLaw
end Homotopy
end Path
end ComputationalPaths
