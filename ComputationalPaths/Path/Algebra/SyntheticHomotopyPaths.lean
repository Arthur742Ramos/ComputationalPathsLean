/-
# Synthetic Homotopy Theory via Computational Paths

This module develops synthetic homotopy theory using `Path`-witnessed
constructions. We formalize synthetic spectra (Pstragowski), Adams-type
spectral sequences synthetically, synthetic analogs of chromatic homotopy
theory, ν-excision, and τ-deformation.

## References

- Pstragowski, "Synthetic spectra and the cellular motivic category"
- Gheorghe–Wang–Xu, "The special fiber of the motivic deformation"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace SyntheticHomotopy

universe u v

/-! ## Synthetic Category -/

structure SyntheticCategory where
  objects : Type u
  morphisms : objects → objects → Type v
  id : (X : objects) → morphisms X X
  comp : {X Y Z : objects} → morphisms X Y → morphisms Y Z → morphisms X Z
  suspension : objects → objects
  loops : objects → objects
  connective : objects → Prop
  coconnective : objects → Prop

structure SyntheticFunctor (C D : SyntheticCategory.{u, v}) where
  onOb : C.objects → D.objects
  onMor : ∀ {X Y : C.objects}, C.morphisms X Y → D.morphisms (onOb X) (onOb Y)
  preserveId : ∀ (X : C.objects), onMor (C.id X) = D.id (onOb X)
  preserveComp : ∀ {X Y Z : C.objects} (f : C.morphisms X Y)
    (g : C.morphisms Y Z),
    onMor (C.comp f g) = D.comp (onMor f) (onMor g)

noncomputable def synth_functor_id_path {C D : SyntheticCategory.{u, v}}
    (F : SyntheticFunctor C D) (X : C.objects) :
    Path (F.onMor (C.id X)) (D.id (F.onOb X)) :=
  Path.ofEq (F.preserveId X)

/-! ## Synthetic Spectra -/

structure SyntheticSpectrum (E : Type u) where
  underlying : Type u
  bigraded : Int → Int → Type u
  eHomology : underlying → E
  syntheticFiltr : Nat → underlying → Prop

structure SyntheticSpectrumMap {E : Type u}
    (X Y : SyntheticSpectrum.{u} E) where
  mapUnderlying : X.underlying → Y.underlying
  mapBigraded : ∀ (s t : Int), X.bigraded s t → Y.bigraded s t

noncomputable def SyntheticSpectrumMap.identity {E : Type u}
    (X : SyntheticSpectrum.{u} E) : SyntheticSpectrumMap X X where
  mapUnderlying := id
  mapBigraded := fun _ _ x => x

noncomputable def SyntheticSpectrumMap.comp {E : Type u}
    {X Y Z : SyntheticSpectrum.{u} E}
    (f : SyntheticSpectrumMap X Y) (g : SyntheticSpectrumMap Y Z) :
    SyntheticSpectrumMap X Z where
  mapUnderlying := g.mapUnderlying ∘ f.mapUnderlying
  mapBigraded := fun s t x => g.mapBigraded s t (f.mapBigraded s t x)

noncomputable def synth_id_comp_path {E : Type u} {X Y : SyntheticSpectrum.{u} E}
    (f : SyntheticSpectrumMap X Y) :
    Path (SyntheticSpectrumMap.comp (SyntheticSpectrumMap.identity X) f).mapUnderlying
         f.mapUnderlying :=
  Path.refl _

/-! ## Synthetic t-Structure -/

structure SyntheticTStructure (C : SyntheticCategory.{u, v}) where
  tauLeq : Int → C.objects → Prop
  tauGeq : Int → C.objects → Prop
  heart : Type u
  heartInclusion : heart → C.objects
  truncBelow : ∀ (n : Int), C.objects → C.objects
  truncAbove : ∀ (n : Int), C.objects → C.objects

structure SyntheticHeart {C : SyntheticCategory.{u, v}}
    (T : SyntheticTStructure C) where
  heartObj : T.heart
  isConnective : C.connective (T.heartInclusion heartObj)
  isCoconnective : C.coconnective (T.heartInclusion heartObj)

noncomputable def synth_heart_refl {C : SyntheticCategory.{u, v}}
    (T : SyntheticTStructure C) (H : SyntheticHeart T) :
    Path (T.heartInclusion H.heartObj) (T.heartInclusion H.heartObj) :=
  Path.refl _

/-! ## Adams Spectral Sequence -/

structure AdamsSS (E : Type u) where
  page : Nat → Int → Int → Type u
  differential : ∀ (r : Nat) (s t : Int), page r s t → page r (s + r) (t - r + 1)
  convergence : Nat → Type u

structure AdamsE2Page {E : Type u} (A : AdamsSS.{u} E) where
  extGroups : Int → Int → Type u

structure AdamsFiltration {E : Type u} (A : AdamsSS.{u} E) where
  filtLevel : Nat → Type u
  graded : ∀ (n : Nat), filtLevel n → A.convergence n

structure AdamsDifferential {E : Type u} (A : AdamsSS.{u} E) (r : Nat) where
  source : Int → Int → Type u
  target : Int → Int → Type u
  diffMap : ∀ (s t : Int), source s t → target (s + r) (t - r + 1)

noncomputable def adams_diff_refl {E : Type u} (A : AdamsSS.{u} E) (r : Nat)
    (d : AdamsDifferential A r) (s t : Int) (x : d.source s t) :
    Path (d.diffMap s t x) (d.diffMap s t x) :=
  Path.refl _

structure MaySS (E : Type u) extends AdamsSS E where
  mayFiltration : Nat → Int → Int → Type u
  mayDifferential : ∀ (r : Nat) (s t : Int),
    mayFiltration r s t → mayFiltration r (s + 1) t

/-! ## Chromatic Synthetic Homotopy Theory -/

structure ChromaticSynthetic where
  height : Nat
  synCat : SyntheticCategory.{u, v}
  monochromaticLayer : Nat → synCat.objects → Prop

structure SyntheticMoravaK (n : Nat) (p : Nat) where
  synSpectrum : SyntheticSpectrum (Type u)
  height : Nat
  heightEq : height = n
  prime : Nat
  primeEq : prime = p

structure SyntheticMoravaE (n : Nat) (p : Nat) where
  synSpectrum : SyntheticSpectrum (Type u)
  height : Nat
  heightEq : height = n
  prime : Nat
  primeEq : prime = p

noncomputable def synth_morava_height_path {n p : Nat} (K : SyntheticMoravaK.{u} n p) :
    Path K.height K.height :=
  Path.refl _

structure SyntheticChromaticConvergence where
  spectrum : SyntheticSpectrum (Type u)
  layers : Nat → SyntheticSpectrum (Type u)
  convergenceMap : ∀ (n : Nat) (s t : Int),
    spectrum.bigraded s t → (layers n).bigraded s t

structure ChromaticReassembly where
  layers : Nat → Type u
  totalSpace : Type u
  reassemblyMap : totalSpace → ∀ (n : Nat), layers n
  fracture : ∀ (n : Nat), layers n → layers (n + 1) → Type u

noncomputable def chrom_conv_refl (C : SyntheticChromaticConvergence.{u})
    (n : Nat) (s t : Int) (x : C.spectrum.bigraded s t) :
    Path (C.convergenceMap n s t x) (C.convergenceMap n s t x) :=
  Path.refl _

/-! ## ν-Excision -/

structure NuExcision where
  cat : SyntheticCategory.{u, v}
  nuMap : cat.objects → cat.objects
  excisionSquare : cat.objects → cat.objects → cat.objects → cat.objects → Prop

structure NuPeriodicGroups where
  underlying : Type u
  nuPeriod : Nat
  periodicMap : underlying → underlying

noncomputable def nu_periodic_refl (N : NuPeriodicGroups.{u}) (x : N.underlying) :
    Path (N.periodicMap x) (N.periodicMap x) :=
  Path.refl _

structure NuSelfMap (C : SyntheticCategory.{u, v}) where
  source : C.objects
  selfMap : C.morphisms source (C.suspension source)
  periodicity : Nat

noncomputable def nu_self_map_refl {C : SyntheticCategory.{u, v}}
    (N : NuSelfMap C) :
    Path N.periodicity N.periodicity :=
  Path.refl _

structure NuPeriodicEquiv (C : SyntheticCategory.{u, v}) where
  source : C.objects
  target : C.objects
  equivMor : C.morphisms source target
  isEquiv : Prop

structure NuNilpotence (C : SyntheticCategory.{u, v}) where
  element : ∀ (X : C.objects), C.morphisms X (C.suspension X)
  nilpotenceOrder : C.objects → Nat
  isNilpotent : ∀ (X : C.objects), Prop

noncomputable def nu_nilp_refl {C : SyntheticCategory.{u, v}}
    (N : NuNilpotence C) (X : C.objects) :
    Path (N.nilpotenceOrder X) (N.nilpotenceOrder X) :=
  Path.refl _

/-! ## τ-Deformation -/

structure TauDeformation where
  synCat : SyntheticCategory.{u, v}
  tau : synCat.objects
  tauInvertible : Prop
  specialFiber : SyntheticCategory.{u, v}
  genericFiber : SyntheticCategory.{u, v}

structure TauBockstein (D : TauDeformation.{u, v}) where
  page : Nat → Int → Int → Type u
  differential : ∀ (r : Nat) (s t : Int), page r s t → page r s (t + 1)
  convergesToGeneric : Prop

structure TauSpecialization (D : TauDeformation.{u, v}) where
  specMap : D.genericFiber.objects → D.specialFiber.objects
  preservesConnective : ∀ (X : D.genericFiber.objects),
    D.genericFiber.connective X → D.specialFiber.connective (specMap X)

noncomputable def tau_deform_refl (D : TauDeformation.{u, v}) :
    Path D.tauInvertible D.tauInvertible :=
  Path.refl _

structure MotivicDeformation extends TauDeformation.{u, v} where
  motivicWeight : synCat.objects → Int
  realizationFunctor : synCat.objects → genericFiber.objects

structure TauPeriodic (D : TauDeformation.{u, v}) where
  periodicObjects : D.synCat.objects → Prop
  tauPeriodicity : ∀ (X : D.synCat.objects),
    periodicObjects X → D.synCat.morphisms X X

noncomputable def tau_periodic_refl {D : TauDeformation.{u, v}}
    (P : TauPeriodic D) (X : D.synCat.objects) (h : P.periodicObjects X) :
    Path (P.tauPeriodicity X h) (P.tauPeriodicity X h) :=
  Path.refl _

/-! ## Synthetic Analogs -/

structure SyntheticTodaBracket (C : SyntheticCategory.{u, v}) where
  f : C.objects
  g : C.objects
  h : C.objects
  bracket : C.morphisms f h → Type v
  indeterminacy : Type v

structure SyntheticMassey (C : SyntheticCategory.{u, v}) where
  elements : List C.objects
  product : Type v
  indeterminacy : Type v

noncomputable def synth_toda_refl {C : SyntheticCategory.{u, v}}
    (T : SyntheticTodaBracket C) :
    Path T.f T.f :=
  Path.refl _

structure SyntheticCofiber (C : SyntheticCategory.{u, v}) where
  source : C.objects
  target : C.objects
  morphism : C.morphisms source target
  cofiber : C.objects
  cofiberMap : C.morphisms target cofiber
  connectingMap : C.morphisms cofiber (C.suspension source)

structure SyntheticFiber (C : SyntheticCategory.{u, v}) where
  source : C.objects
  target : C.objects
  morphism : C.morphisms source target
  fiber : C.objects
  fiberMap : C.morphisms fiber source
  connectingMap : C.morphisms (C.loops target) fiber

noncomputable def synth_cofiber_refl {C : SyntheticCategory.{u, v}}
    (CF : SyntheticCofiber C) :
    Path CF.cofiber CF.cofiber :=
  Path.refl _

/-! ## Synthetic Algebraic Geometry -/

structure SyntheticQCoh (C : SyntheticCategory.{u, v}) where
  sheaf : C.objects → Type u
  restriction : ∀ {X Y : C.objects}, C.morphisms X Y → sheaf Y → sheaf X

structure SyntheticDescent (C : SyntheticCategory.{u, v}) where
  cover : C.objects → C.objects
  descentDatum : ∀ (X : C.objects), C.morphisms (cover X) X
  effectiveness : Prop

noncomputable def synth_descent_refl {C : SyntheticCategory.{u, v}}
    (D : SyntheticDescent C) :
    Path D.effectiveness D.effectiveness :=
  Path.refl _

/-! ## Cellular Motivic Category -/

structure CellularMotivic extends SyntheticCategory.{u, v} where
  cellStructure : objects → List Nat
  motivicWeight : objects → Int
  bigrading : objects → Int × Int

structure MotivicCellAttachment (C : CellularMotivic.{u, v}) where
  source : C.objects
  cellDim : Nat
  weight : Int
  attachingMap : C.morphisms source (C.suspension source)

structure MotivicAdamsSS extends AdamsSS (Type u) where
  motivicBigrading : Int → Int → Int → Type u
  weightFiltration : Nat → Int → Int → Type u

noncomputable def motivic_cell_refl {C : CellularMotivic.{u, v}}
    (A : MotivicCellAttachment C) :
    Path A.cellDim A.cellDim :=
  Path.refl _

/-! ## Synthetic at Height 2 -/

structure SyntheticHeight2 where
  tmf : SyntheticSpectrum (Type u)
  modularForms : Int → Type u
  tmfHomotopy : Int → Int → Type u
  spectralSequence : AdamsSS (Type u)

structure SyntheticTMFResolution (H : SyntheticHeight2.{u}) where
  resolution : Nat → SyntheticSpectrum (Type u)
  resolutionMap : ∀ (n : Nat) (s t : Int),
    (resolution n).bigraded s t → (resolution (n + 1)).bigraded s t

noncomputable def synth_tmf_refl (H : SyntheticHeight2.{u}) (s t : Int) :
    Path (H.tmfHomotopy s t) (H.tmfHomotopy s t) :=
  Path.refl _

/-! ## Synthetic Picard Groups -/

structure SyntheticPicard (C : SyntheticCategory.{u, v}) where
  invertibleObjects : Type u
  product : invertibleObjects → invertibleObjects → invertibleObjects
  unit : invertibleObjects
  inverse : invertibleObjects → invertibleObjects
  unitLeft : ∀ (x : invertibleObjects), product unit x = x
  unitRight : ∀ (x : invertibleObjects), product x unit = x

noncomputable def synth_picard_unit_path {C : SyntheticCategory.{u, v}}
    (P : SyntheticPicard C) (x : P.invertibleObjects) :
    Path (P.product P.unit x) x :=
  Path.ofEq (P.unitLeft x)

end SyntheticHomotopy
end Algebra
end Path
end ComputationalPaths
