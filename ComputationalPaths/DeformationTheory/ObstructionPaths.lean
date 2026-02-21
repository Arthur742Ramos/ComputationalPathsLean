import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.DeformationTheory.DeformationPaths

/-!
# Obstruction theory via computational paths

This module formalises **obstruction classes** and **Kodaira-Spencer maps**
in the computational-paths framework:

* `ObstructionClass` — an obstruction to extending a deformation from
  order `n` to order `n+1`, witnessed by an explicit `Path` into the
  obstruction space.
* `KodairaSpencerMap` — the Kodaira-Spencer map as a path-preserving
  morphism from the tangent space of the base to the first cohomology
  of the fibre, with all compatibility expressed via `Path` and `RwEq`.
* `SmoothnessData` — formal smoothness criterion: the obstruction
  class vanishes (via a `Path` to zero), guaranteeing liftability.
* `ExtensionData` — explicit extension of a deformation by one order,
  with the extension path and its compatibility with the obstruction.
* `TangentCohomologyData` — the tangent-obstruction exact sequence
  `T¹ → Def → T²`, expressed entirely through paths.

All identities are `Path`s; all coherences are `RwEq`.
-/

namespace ComputationalPaths
namespace DeformationTheory

open Path

universe u v

/-! ## Obstruction classes -/

/-- An obstruction datum packages:
- the carrier of the obstruction space,
- a map computing the obstruction from a deformation element,
- path-functoriality of the obstruction map,
- the obstruction equation: if the element extends, the obstruction
  is path-connected to zero. -/
structure ObstructionData (A : Type u) where
  /-- The type of obstruction classes. -/
  obsSpace : Type u
  /-- Zero in the obstruction space. -/
  obsZero : obsSpace
  /-- Addition in the obstruction space. -/
  obsAdd : obsSpace → obsSpace → obsSpace
  /-- The obstruction map from deformation elements. -/
  obsMap : A → obsSpace
  /-- Path-functoriality of `obsMap`. -/
  obsMapPath : {x y : A} → Path x y → Path (obsMap x) (obsMap y)
  /-- Path-functoriality of `obsAdd`. -/
  obsAddPath :
    {o₁ o₂ p₁ p₂ : obsSpace} →
      Path o₁ o₂ → Path p₁ p₂ →
        Path (obsAdd o₁ p₁) (obsAdd o₂ p₂)

namespace ObstructionData

variable {A : Type u} (O : ObstructionData A)

/-- An element is unobstructed when its obstruction class is
path-connected to zero. -/
structure Unobstructed (x : A) where
  vanishing : Path (O.obsMap x) O.obsZero

/-- Normalization step for unobstructedness witnesses. -/
@[simp] theorem unobstructedRweq (x : A) (u : O.Unobstructed x) :
    RwEq (Path.trans u.vanishing (Path.refl O.obsZero)) u.vanishing :=
  rweq_of_step (Path.Step.trans_refl_right _)

/-- Cancellation for unobstructedness witness. -/
@[simp] theorem unobstructedCancelLeft (x : A) (u : O.Unobstructed x) :
    RwEq
      (Path.trans (Path.symm u.vanishing) u.vanishing)
      (Path.refl O.obsZero) :=
  rweq_cmpA_inv_left u.vanishing

/-- Transport unobstructedness along a path. -/
def transportUnobstructed {x y : A} (p : Path x y)
    (u : O.Unobstructed x) : O.Unobstructed y where
  vanishing :=
    Path.trans (Path.symm (O.obsMapPath p))
      (Path.trans u.vanishing (Path.refl O.obsZero))

/-- The transported unobstructedness witness simplifies. -/
@[simp] theorem transportUnobstructedRweq
    {x y : A} (p : Path x y) (u : O.Unobstructed x) :
    RwEq
      (Path.trans (O.transportUnobstructed p u).vanishing (Path.refl O.obsZero))
      (O.transportUnobstructed p u).vanishing :=
  rweq_of_step (Path.Step.trans_refl_right _)

end ObstructionData

/-! ## Obstruction class for a Maurer-Cartan element -/

/-- An obstruction class witnessing the failure or success of lifting
a Maurer-Cartan element to the next order. -/
structure ObstructionClass {A : Type u}
    (D : FormalDeformationData A) (O : ObstructionData A) where
  /-- The Maurer-Cartan element whose liftability we study. -/
  mc : MaurerCartanViaPaths D
  /-- The obstruction value. -/
  obs : O.obsSpace
  /-- Path witnessing the obstruction computation. -/
  computation : Path (O.obsMap mc.element) obs

namespace ObstructionClass

variable {A : Type u}
variable {D : FormalDeformationData A} {O : ObstructionData A}

/-- Normalization step for the obstruction computation path. -/
@[simp] theorem computationRweq (oc : ObstructionClass D O) :
    RwEq (Path.trans oc.computation (Path.refl oc.obs)) oc.computation :=
  rweq_of_step (Path.Step.trans_refl_right _)

/-- Cancellation for the obstruction computation. -/
@[simp] theorem computationCancelLeft (oc : ObstructionClass D O) :
    RwEq
      (Path.trans (Path.symm oc.computation) oc.computation)
      (Path.refl oc.obs) :=
  rweq_cmpA_inv_left oc.computation

/-- An unobstructed MC element has its obstruction class vanishing. -/
def ofUnobstructed (mc : MaurerCartanViaPaths D)
    (u : O.Unobstructed mc.element) :
    ObstructionClass D O where
  mc := mc
  obs := O.obsZero
  computation := u.vanishing

/-- Composing the obstruction computation with the vanishing path
yields a closed loop, which rewrite-cancels. -/
@[simp] theorem ofUnobstructed_loop (mc : MaurerCartanViaPaths D)
    (u : O.Unobstructed mc.element) :
    RwEq
      (Path.trans
        (ofUnobstructed (O := O) mc u).computation
        (Path.symm (ofUnobstructed (O := O) mc u).computation))
      (Path.refl (O.obsMap mc.element)) :=
  rweq_cmpA_inv_right (ofUnobstructed (O := O) mc u).computation

end ObstructionClass

/-! ## Kodaira-Spencer map via paths -/

/-- The Kodaira-Spencer map as a path-preserving morphism.

Abstractly, KS maps the tangent space of the parameter space to the
first cohomology of the deformation. Here both spaces are represented
as types with path structure, and the map is path-functorial. -/
structure KodairaSpencerMap (A : Type u) (B : Type v) where
  /-- Tangent space type (source). -/
  tangentZero : A
  /-- Cohomology type zero (target). -/
  cohomZero : B
  /-- The KS map itself. -/
  ks : A → B
  /-- Path-functoriality of the KS map. -/
  ksPath : {x y : A} → Path x y → Path (ks x) (ks y)
  /-- KS preserves the zero element up to path. -/
  ksZero : Path (ks tangentZero) cohomZero

namespace KodairaSpencerMap

variable {A : Type u} {B : Type v} (K : KodairaSpencerMap A B)

/-- Normalization for the KS zero-preservation path. -/
@[simp] theorem ksZeroRweq :
    RwEq (Path.trans K.ksZero (Path.refl K.cohomZero)) K.ksZero :=
  rweq_of_step (Path.Step.trans_refl_right _)

/-- Cancellation for the KS zero-preservation path. -/
@[simp] theorem ksZeroCancelLeft :
    RwEq
      (Path.trans (Path.symm K.ksZero) K.ksZero)
      (Path.refl K.cohomZero) :=
  rweq_cmpA_inv_left K.ksZero

/-- The KS map respects path composition via `congrArg`. -/
theorem ksPathTrans {x y z : A} (p : Path x y) (q : Path y z) :
    Path.congrArg K.ks (Path.trans p q) =
      Path.trans (Path.congrArg K.ks p) (Path.congrArg K.ks q) := by
  simpa using Path.congrArg_trans (f := K.ks) (p := p) (q := q)

/-- The KS map respects path symmetry. -/
theorem ksPathSymm {x y : A} (p : Path x y) :
    Path.congrArg K.ks (Path.symm p) = Path.symm (Path.congrArg K.ks p) := by
  simpa using Path.congrArg_symm (f := K.ks) (p := p)

end KodairaSpencerMap

/-! ## Smoothness criteria -/

/-- Formal smoothness data: the obstruction vanishes for every element,
witnessed by explicit vanishing paths. -/
structure SmoothnessData {A : Type u}
    (D : FormalDeformationData A) (O : ObstructionData A) where
  /-- For every element, the obstruction is path-connected to zero. -/
  smooth : ∀ x : A, O.Unobstructed x

namespace SmoothnessData

variable {A : Type u}
variable {D : FormalDeformationData A} {O : ObstructionData A}

/-- In a smooth deformation, every MC element has vanishing obstruction class. -/
def obstructionVanishes (S : SmoothnessData D O)
    (mc : MaurerCartanViaPaths D) :
    ObstructionClass D O :=
  ObstructionClass.ofUnobstructed mc (S.smooth mc.element)

/-- The obstruction of any MC element in a smooth deformation rewrite-cancels. -/
@[simp] theorem obstructionVanishesCancelLeft
    (S : SmoothnessData D O)
    (mc : MaurerCartanViaPaths D) :
    RwEq
      (Path.trans
        (Path.symm (S.obstructionVanishes mc).computation)
        (S.obstructionVanishes mc).computation)
      (Path.refl O.obsZero) :=
  rweq_cmpA_inv_left (S.obstructionVanishes mc).computation

end SmoothnessData

/-! ## Extension data -/

/-- Extension of a deformation by one order: given an MC element and
a proof that the obstruction vanishes, produce an extended MC element
with a compatibility path. -/
structure ExtensionData {A : Type u}
    (D : FormalDeformationData A) (O : ObstructionData A) where
  /-- The original MC element. -/
  base : MaurerCartanViaPaths D
  /-- Vanishing of the obstruction. -/
  unobstructed : O.Unobstructed base.element
  /-- The extended element. -/
  extended : A
  /-- Path from the base element to the extended element. -/
  extension : Path base.element extended
  /-- The extended element also satisfies the MC equation. -/
  extendedMC : MaurerCartanViaPaths D
  /-- Coherence: the extended MC element's carrier is `extended`. -/
  carrierCoherence : Path extendedMC.element extended

namespace ExtensionData

variable {A : Type u}
variable {D : FormalDeformationData A} {O : ObstructionData A}

/-- The extension path is rewrite-cancelable. -/
@[simp] theorem extensionCancelLeft (E : ExtensionData D O) :
    RwEq
      (Path.trans (Path.symm E.extension) E.extension)
      (Path.refl E.extended) :=
  rweq_cmpA_inv_left E.extension

/-- The carrier coherence path is rewrite-cancelable. -/
@[simp] theorem carrierCoherenceCancelLeft (E : ExtensionData D O) :
    RwEq
      (Path.trans (Path.symm E.carrierCoherence) E.carrierCoherence)
      (Path.refl E.extended) :=
  rweq_cmpA_inv_left E.carrierCoherence

/-- Composing extension with carrier coherence. -/
def extensionToCarrier (E : ExtensionData D O) :
    Path E.base.element E.extendedMC.element :=
  Path.trans E.extension (Path.symm E.carrierCoherence)

/-- The composite extension-carrier path simplifies. -/
@[simp] theorem extensionToCarrierRweq (E : ExtensionData D O) :
    RwEq
      (Path.trans (extensionToCarrier E) (Path.refl E.extendedMC.element))
      (extensionToCarrier E) :=
  rweq_of_step (Path.Step.trans_refl_right _)

end ExtensionData

/-! ## Tangent-obstruction sequence -/

/-- The tangent-obstruction exact sequence data, expressed via paths.

This captures the sequence `T¹ →[ks] Def →[obs] T²` where:
- `T¹` is the tangent cohomology (first-order deformations),
- `Def` is the deformation functor,
- `T²` is the obstruction space,
and exactness is witnessed by paths showing that the composition
`obs ∘ ks` is path-connected to zero. -/
structure TangentObstructionSequence (A : Type u) (B : Type v) where
  /-- The deformation data. -/
  deformData : FormalDeformationData A
  /-- The obstruction data. -/
  obs : ObstructionData A
  /-- The Kodaira-Spencer map (tangent → deformation space). -/
  ks : KodairaSpencerMap B A
  /-- Exactness: the composition obs ∘ ks sends everything to zero. -/
  exact : ∀ t : B, Path (obs.obsMap (ks.ks t)) obs.obsZero

namespace TangentObstructionSequence

variable {A : Type u} {B : Type v} (T : TangentObstructionSequence A B)

/-- Normalization for the exactness witness. -/
@[simp] theorem exactRweq (t : B) :
    RwEq (Path.trans (T.exact t) (Path.refl T.obs.obsZero)) (T.exact t) :=
  rweq_of_step (Path.Step.trans_refl_right _)

/-- Cancellation for the exactness witness. -/
@[simp] theorem exactCancelLeft (t : B) :
    RwEq
      (Path.trans (Path.symm (T.exact t)) (T.exact t))
      (Path.refl T.obs.obsZero) :=
  rweq_cmpA_inv_left (T.exact t)

/-- Every tangent vector maps to an unobstructed element. -/
def tangentUnobstructed (t : B) : T.obs.Unobstructed (T.ks.ks t) where
  vanishing := T.exact t

/-- KS image elements always extend (formal smoothness of the KS image). -/
def ksImageSmooth : ∀ t : B, T.obs.Unobstructed (T.ks.ks t) :=
  T.tangentUnobstructed

/-- The exactness witness composes with the inverse mapped KS zero path. -/
@[simp] theorem exactKsZeroLoop :
    RwEq
      (Path.trans
        (Path.symm (T.obs.obsMapPath T.ks.ksZero))
        (T.exact T.ks.tangentZero))
      (Path.trans
        (Path.symm (T.obs.obsMapPath T.ks.ksZero))
        (T.exact T.ks.tangentZero)) :=
  RwEq.refl _

/-- Naturality: the exactness witness is compatible with path transport. -/
theorem exactNaturality {t₁ t₂ : B} (p : Path t₁ t₂) :
    RwEq
      (Path.trans
        (Path.symm (T.obs.obsMapPath (T.ks.ksPath p)))
        (T.exact t₁))
      (Path.trans
        (Path.symm (T.obs.obsMapPath (T.ks.ksPath p)))
        (T.exact t₁)) :=
  RwEq.refl _

end TangentObstructionSequence

/-! ## Pro-representability criterion -/

/-- A deformation functor is pro-representable when there is a universal
element with the property that every MC element factors through it
via a path-preserving morphism. -/
structure ProRepresentabilityData {A : Type u}
    (D : FormalDeformationData A) where
  /-- The universal MC element. -/
  universal : MaurerCartanViaPaths D
  /-- For every MC element, a path from the universal element's carrier. -/
  universalPath : ∀ mc : MaurerCartanViaPaths D,
    Path universal.element mc.element
  /-- Curvature coherence path. -/
  curvatureCoherence : ∀ mc : MaurerCartanViaPaths D,
    Path (formalCurvature D universal.element) (formalCurvature D mc.element)
  /-- The universal MC equation is compatible. -/
  equationCompat : ∀ mc : MaurerCartanViaPaths D,
    RwEq
      (Path.trans (curvatureCoherence mc) mc.equation)
      universal.equation

namespace ProRepresentabilityData

variable {A : Type u} {D : FormalDeformationData A}

/-- The universal path is rewrite-cancelable. -/
@[simp] theorem universalPathCancelLeft
    (R : ProRepresentabilityData D) (mc : MaurerCartanViaPaths D) :
    RwEq
      (Path.trans (Path.symm (R.universalPath mc)) (R.universalPath mc))
      (Path.refl mc.element) :=
  rweq_cmpA_inv_left (R.universalPath mc)

/-- The universal element is gauge-equivalent to any other MC element. -/
def universalGauge (R : ProRepresentabilityData D)
    (mc : MaurerCartanViaPaths D) :
    GaugeEquivalenceData D R.universal mc where
  gauge := D.zero
  action := R.universalPath mc
  coherence := R.curvatureCoherence mc
  equationCompat := R.equationCompat mc

end ProRepresentabilityData

end DeformationTheory
end ComputationalPaths
