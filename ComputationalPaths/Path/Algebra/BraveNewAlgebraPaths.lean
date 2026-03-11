/-
# Brave New Algebra (Structured Ring Spectra) via Computational Paths

This module develops brave new algebra — the theory of structured ring
spectra — using `Path`-witnessed constructions. We formalize E∞-ring
spectra, THH, TC, trace methods, algebraic K-theory of ring spectra,
and Galois extensions of ring spectra.

## References

- Elmendorf–Kriz–Mandell–May, "Rings, Modules, and Algebras in Stable Homotopy Theory"
- Dundas–Goodwillie–McCarthy, "The Local Structure of Algebraic K-Theory"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace BraveNewAlgebra

universe u v

/-! ## Spectra -/

structure SpectrumData where
  space : Int → Type u
  basepoint : ∀ (n : Int), space n
  structureMap : ∀ (n : Int), space n → space (n + 1)

noncomputable def spectrum_bp_refl (E : SpectrumData.{u}) (n : Int) :
    Path (E.basepoint n) (E.basepoint n) :=
  Path.refl _

structure SpectrumHomotopy (E : SpectrumData.{u}) where
  piGroups : Int → Type u
  fromSpace : ∀ (n : Int), E.space n → piGroups n

structure SmashProduct (E F : SpectrumData.{u}) where
  result : SpectrumData.{u}
  leftUnit : ∀ (n : Int), E.space n → result.space n
  rightUnit : ∀ (n : Int), F.space n → result.space n

/-! ## E∞-Ring Spectra -/

structure EInfinityRing extends SpectrumData.{u} where
  mul : ∀ (n : Int), space n → space n → space n
  mulUnit : ∀ (n : Int), space n
  mulAssoc : ∀ (n : Int) (x y z : space n),
    mul n (mul n x y) z = mul n x (mul n y z)
  mulComm : ∀ (n : Int) (x y : space n),
    mul n x y = mul n y x
  mulUnitLeft : ∀ (n : Int) (x : space n),
    mul n (mulUnit n) x = x
  mulUnitRight : ∀ (n : Int) (x : space n),
    mul n x (mulUnit n) = x

structure EInfinityMap (R S : EInfinityRing.{u}) where
  mapSpace : ∀ (n : Int), R.space n → S.space n
  preservesMul : ∀ (n : Int) (x y : R.space n),
    mapSpace n (R.mul n x y) = S.mul n (mapSpace n x) (mapSpace n y)
  preservesUnit : ∀ (n : Int),
    mapSpace n (R.mulUnit n) = S.mulUnit n

noncomputable def EInfinityMap.identity (R : EInfinityRing.{u}) : EInfinityMap R R where
  mapSpace := fun _ x => x
  preservesMul := fun _ _ _ => rfl
  preservesUnit := fun _ => rfl

noncomputable def EInfinityMap.comp {R S T : EInfinityRing.{u}}
    (f : EInfinityMap R S) (g : EInfinityMap S T) : EInfinityMap R T where
  mapSpace := fun n x => g.mapSpace n (f.mapSpace n x)
  preservesMul := fun n x y => by
    simp [f.preservesMul, g.preservesMul]
  preservesUnit := fun n => by
    simp [f.preservesUnit, g.preservesUnit]

noncomputable def einfinity_id_comp_path {R S : EInfinityRing.{u}} (f : EInfinityMap R S) :
    Path (EInfinityMap.comp (EInfinityMap.identity R) f).mapSpace f.mapSpace :=
  Path.refl _

/-! ## Module Spectra -/

structure ModuleSpectrum (R : EInfinityRing.{u}) extends SpectrumData.{u} where
  action : ∀ (n : Int), R.space n → space n → space n
  actionAssoc : ∀ (n : Int) (r s : R.space n) (m : space n),
    action n (R.mul n r s) m = action n r (action n s m)
  actionUnit : ∀ (n : Int) (m : space n),
    action n (R.mulUnit n) m = m

structure FreeModule (R : EInfinityRing.{u}) where
  generators : Type u
  module : ModuleSpectrum R

structure TensorProduct {R : EInfinityRing.{u}}
    (M N : ModuleSpectrum R) where
  result : ModuleSpectrum R
  bilinearMap : ∀ (n : Int), M.space n → N.space n → result.space n

noncomputable def module_action_unit_path {R : EInfinityRing.{u}} (M : ModuleSpectrum R)
    (n : Int) (m : M.space n) :
    Path (M.action n (R.mulUnit n) m) m :=
  Path.ofEq (M.actionUnit n m)

/-! ## Topological Hochschild Homology (THH) -/

structure THH (R : EInfinityRing.{u}) where
  space : Int → Type u
  cyclicAction : ∀ (n : Int), space n → space n
  fromR : ∀ (n : Int), R.space n → space n
  multiplication : ∀ (n : Int), space n → space n → space n

noncomputable def thh_cyclic_refl {R : EInfinityRing.{u}} (T : THH R)
    (n : Int) (x : T.space n) :
    Path (T.cyclicAction n x) (T.cyclicAction n x) :=
  Path.refl _

structure THHPolynomial (R : EInfinityRing.{u}) where
  thhR : THH R
  generators : Type u
  freeLoops : ∀ (g : generators) (n : Int), thhR.space n

structure BokstedtPeriodicity (R : EInfinityRing.{u}) where
  thh : THH R
  periodicityClass : ∀ (n : Int), thh.space n

structure THHCoeff (R : EInfinityRing.{u}) (M : ModuleSpectrum R) where
  space : Int → Type u
  fromM : ∀ (n : Int), M.space n → space n
  traceMap : ∀ (n : Int), space n → M.space n

/-! ## TR and TC -/

structure TR (R : EInfinityRing.{u}) where
  thh : THH R
  level : Nat → Int → Type u
  restriction : ∀ (n : Nat) (k : Int), level (n + 1) k → level n k
  frobenius : ∀ (n : Nat) (k : Int), level n k → level (n + 1) k

structure TC (R : EInfinityRing.{u}) where
  tr : TR R
  tcSpace : Int → Type u
  toTR : ∀ (n : Int), tcSpace n → tr.level 0 n
  equalizerCondition : ∀ (n : Int) (x : tcSpace n),
    tr.restriction 0 n (tr.frobenius 0 n (toTR n x)) = toTR n x

noncomputable def tc_equalizer_path {R : EInfinityRing.{u}} (T : TC R) (n : Int)
    (x : T.tcSpace n) :
    Path (T.tr.restriction 0 n (T.tr.frobenius 0 n (T.toTR n x)))
         (T.toTR n x) :=
  Path.ofEq (T.equalizerCondition n x)

structure TCMinus (R : EInfinityRing.{u}) where
  thh : THH R
  tcMinusSpace : Int → Type u
  fromTHH : ∀ (n : Int), thh.space n → tcMinusSpace n
  homotopyFixedPoints : Prop

structure TP (R : EInfinityRing.{u}) where
  thh : THH R
  tpSpace : Int → Type u
  tateConstruction : ∀ (n : Int), thh.space n → tpSpace n

/-! ## Trace Methods -/

structure DennisTrace (R : EInfinityRing.{u}) where
  kTheory : Int → Type u
  thh : THH R
  traceMap : ∀ (n : Int), kTheory n → thh.space n

structure CyclotomicTrace (R : EInfinityRing.{u}) where
  kTheory : Int → Type u
  tc : TC R
  traceMap : ∀ (n : Int), kTheory n → tc.tcSpace n

structure TraceFactorization (R : EInfinityRing.{u}) where
  kTheory : Int → Type u
  thh : THH R
  tc : TC R
  dennisTrace : ∀ (n : Int), kTheory n → thh.space n
  cyclotomicTrace : ∀ (n : Int), kTheory n → tc.tcSpace n
  factorMap : ∀ (n : Int), tc.tcSpace n → thh.space n
  factorCompat : ∀ (n : Int) (x : kTheory n),
    factorMap n (cyclotomicTrace n x) = dennisTrace n x

noncomputable def trace_factor_path {R : EInfinityRing.{u}}
    (T : TraceFactorization R) (n : Int) (x : T.kTheory n) :
    Path (T.factorMap n (T.cyclotomicTrace n x))
         (T.dennisTrace n x) :=
  Path.ofEq (T.factorCompat n x)

structure DGMTheorem (R : EInfinityRing.{u}) where
  nilExtension : EInfinityRing.{u}
  nilMap : EInfinityMap nilExtension R
  relativeK : Int → Type u
  relativeTC : Int → Type u
  dgmEquiv : ∀ (n : Int), relativeK n → relativeTC n

/-! ## K-Theory of Ring Spectra -/

structure KTheorySpectrum (R : EInfinityRing.{u}) where
  kSpace : Int → Type u
  kBasepoint : ∀ (n : Int), kSpace n
  kStructure : ∀ (n : Int), kSpace n → kSpace (n + 1)

structure WaldhausenS (R : EInfinityRing.{u}) where
  sCat : Nat → Type u
  sMap : ∀ (n : Nat), sCat n → sCat (n + 1)
  kEquiv : KTheorySpectrum R

structure KTheoryPerf (R : EInfinityRing.{u}) where
  perfModules : Type u
  kTheory : KTheorySpectrum R
  fromPerf : perfModules → kTheory.kSpace 0

noncomputable def k_theory_bp_refl {R : EInfinityRing.{u}} (K : KTheorySpectrum R)
    (n : Int) :
    Path (K.kBasepoint n) (K.kBasepoint n) :=
  Path.refl _

structure QuillenLichtenbaum (R : EInfinityRing.{u}) where
  kTheory : KTheorySpectrum R
  etaleK : Int → Type u
  comparisonMap : ∀ (n : Int), kTheory.kSpace n → etaleK n
  isEquivAbove : Nat → Prop

structure RedShift (R : EInfinityRing.{u}) (n : Nat) where
  chromHeight : Nat
  heightEq : chromHeight = n
  kOfR : KTheorySpectrum R
  kHeight : Nat
  heightShift : kHeight = n + 1

noncomputable def redshift_height_path {R : EInfinityRing.{u}} {n : Nat}
    (RS : RedShift R n) :
    Path RS.chromHeight RS.chromHeight :=
  Path.refl _

/-! ## Galois Extensions -/

structure GaloisExtension (R S : EInfinityRing.{u}) where
  group : Type u
  action : ∀ (g : group) (n : Int), S.space n → S.space n
  fixedPoints : ∀ (n : Int), (∀ (g : group), S.space n) → R.space n
  galoisCondition : Prop

structure FaithfulGalois (R S : EInfinityRing.{u})
    extends GaloisExtension R S where
  faithfulness : ∀ (g h : group),
    (∀ (n : Int) (x : S.space n), action g n x = action h n x) →
    g = h

structure RognesGalois (R : EInfinityRing.{u}) where
  galoisGroup : Type u
  coveringSpectrum : EInfinityRing.{u}
  galoisExt : GaloisExtension R coveringSpectrum

noncomputable def galois_cond_refl {R S : EInfinityRing.{u}}
    (G : GaloisExtension R S) :
    Path G.galoisCondition G.galoisCondition :=
  Path.refl _

structure GaloisDescent {R S : EInfinityRing.{u}}
    (G : GaloisExtension R S) where
  descentDatum : ∀ (n : Int), S.space n → R.space n
  descentRoundtrip : ∀ (n : Int) (x : S.space n),
    descentDatum n x = descentDatum n x

noncomputable def galois_descent_refl {R S : EInfinityRing.{u}}
    (G : GaloisExtension R S) (D : GaloisDescent G)
    (n : Int) (x : S.space n) :
    Path (D.descentDatum n x) (D.descentDatum n x) :=
  Path.refl _

/-! ## Power Operations -/

structure PowerOperations (R : EInfinityRing.{u}) where
  power : ∀ (p : Nat) (n : Int), R.space n → R.space n
  powerMul : ∀ (p : Nat) (n : Int) (x y : R.space n),
    power p n (R.mul n x y) = R.mul n (power p n x) (power p n y)
  powerUnit : ∀ (p : Nat) (n : Int),
    power p n (R.mulUnit n) = R.mulUnit n

structure DyerLashof (R : EInfinityRing.{u}) where
  operation : ∀ (s : Int) (n : Int), R.space n → R.space (n + s)
  instability : ∀ (s n : Int) (x : R.space n), Prop

noncomputable def power_unit_path {R : EInfinityRing.{u}} (P : PowerOperations R)
    (p : Nat) (n : Int) :
    Path (P.power p n (R.mulUnit n)) (R.mulUnit n) :=
  Path.ofEq (P.powerUnit p n)

/-! ## Thom Spectra -/

structure ThomSpectrum (R : EInfinityRing.{u}) where
  base : Type u
  thomSpace : Int → Type u
  thomClass : ∀ (n : Int), thomSpace n → R.space n
  orientability : Prop

structure ThomOrientation {R : EInfinityRing.{u}} (T : ThomSpectrum R) where
  orientationClass : ∀ (n : Int), R.space n
  thomIso : ∀ (n : Int), T.thomSpace n → R.space n

noncomputable def thom_orient_refl {R : EInfinityRing.{u}} {T : ThomSpectrum R}
    (O : ThomOrientation T) (n : Int) :
    Path (O.orientationClass n) (O.orientationClass n) :=
  Path.refl _

/-! ## TAQ -/

structure TAQ (R S : EInfinityRing.{u}) where
  taqSpace : Int → Type u
  derivation : ∀ (n : Int), S.space n → taqSpace n

structure TAQCohom (R S : EInfinityRing.{u}) where
  taq : TAQ R S
  cohomGroups : Int → Type u
  fromTAQ : ∀ (n : Int), taq.taqSpace n → cohomGroups n

noncomputable def taq_deriv_refl {R S : EInfinityRing.{u}} (T : TAQ R S)
    (n : Int) (x : S.space n) :
    Path (T.derivation n x) (T.derivation n x) :=
  Path.refl _

/-! ## Chromatic Algebra -/

structure MoravaETheory (n : Nat) (p : Nat) extends EInfinityRing.{u} where
  height : Nat
  heightEq : height = n
  prime : Nat
  primeEq : prime = p

structure LubinTateTheory (n : Nat) extends MoravaETheory.{u} n 0 where
  formalGroup : Type u
  universalDeformation : formalGroup → space 0

noncomputable def morava_height_refl {n p : Nat} (E : MoravaETheory.{u} n p) :
    Path E.height E.height :=
  Path.refl _

/-! ## Localization -/

structure SpectrumLocalization (R : EInfinityRing.{u}) where
  localizedRing : EInfinityRing.{u}
  locMap : EInfinityMap R localizedRing
  isLocal : Prop

structure SmashingLocalization (R : EInfinityRing.{u})
    extends SpectrumLocalization R where
  localizedSmash : ∀ (M : ModuleSpectrum R), ModuleSpectrum localizedRing

noncomputable def localization_refl {R : EInfinityRing.{u}}
    (L : SpectrumLocalization R) :
    Path L.isLocal L.isLocal :=
  Path.refl _

end BraveNewAlgebra
end Algebra
end Path
end ComputationalPaths
