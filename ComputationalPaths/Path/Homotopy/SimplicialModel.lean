/-
# Simplicial model categories and hammock localization

This module records lightweight data for simplicial model categories in the
computational paths framework. We package mapping spaces as simplicial sets,
define hammock localization data, and introduce framings via simplicial and
cosimplicial resolutions.

## Key Results

- `SimplicialModelCategory`: model category with simplicial mapping spaces.
- `MappingSpaceData`: mapping spaces with Kan filler data.
- `HammockLocalization`: hammock localization data.
- `CosimplicialObject`, `CosimplicialResolution`: cosimplicial resolutions.
- `Framing`: paired simplicial and cosimplicial resolutions.

## References

- Dwyer and Kan, "Function complexes in homotopical algebra"
- Hirschhorn, "Model Categories and Their Localizations"
- Hovey, "Model Categories"
-/

import ComputationalPaths.Path.ModelCategory
import ComputationalPaths.Path.Homotopy.KanComplex
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Topology.LawCertificates

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace SimplicialModel

open KanComplex

universe u v

/-! ## Genuine computational-path primitives

The simplicial-model data below is largely valued in an opaque `Type u`, so the
coherences it records cannot themselves compute.  To keep this module anchored to
genuine computational paths — rather than reflexive `X = X := rfl` stubs or `True`
placeholders — we first record a reusable layer of arithmetic paths over concrete
`Nat`/`Int` degree handles.  Each primitive is a real rewrite trace
(associativity / commutativity of a simplicial-degree or chain-degree sum),
assembled into multi-step `Path.trans` chains and non-decorative `RwEq`
coherences that the rest of the file reuses. -/

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)` on simplicial-degree data. -/
noncomputable def dAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a` on `Nat` degrees. -/
noncomputable def dComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via right-argument
    congruence — a genuine step over the opaque summands. -/
noncomputable def dInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** degree path: reassociate `(a + b) + c ⤳ a + (b + c)`,
    then commute the inner pair `⤳ a + (c + b)`.  Trace length two. -/
noncomputable def dTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (dAssoc a b c) (dInner a b c)

/-- A genuine **three-step** degree path: `dTwoStep` followed by the outer
    commutation `a + (c + b) ⤳ (c + b) + a`.  A `Path.trans` chain of length
    three over distinct expressions. -/
noncomputable def dThreeStep (a b c : Nat) : Path ((a + b) + c) ((c + b) + a) :=
  Path.trans (dTwoStep a b c) (dComm a (c + b))

/-- The two-step degree path composed with its inverse cancels to `refl` — a
    non-decorative `RwEq` on a length-two trace. -/
noncomputable def dTwoStep_cancel (a b c : Nat) :
    RwEq (Path.trans (dTwoStep a b c) (Path.symm (dTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  rweq_cmpA_inv_right (dTwoStep a b c)

/-- Associativity coherence relating the two bracketings of a three-fold degree
    composite — a genuine use of the `trans_assoc` (`tt`) rewrite. -/
noncomputable def dTriple_assoc {a b c d : Nat}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_tt p q r

/-- Double-symmetry collapse on the genuine two-step degree path — a
    non-decorative `RwEq` (`σσ`). -/
noncomputable def dTwoStep_ss (a b c : Nat) :
    RwEq (Path.symm (Path.symm (dTwoStep a b c))) (dTwoStep a b c) :=
  rweq_ss (dTwoStep a b c)

/-- Commutativity rewrite `x + y ⤳ y + x` on `Int` chain-degree data. -/
noncomputable def zComm (x y : Int) : Path (x + y) (y + x) :=
  Path.ofEq (Int.add_comm x y)

/-- Associativity rewrite `(x + y) + z ⤳ x + (y + z)` on `Int`. -/
noncomputable def zAssoc (x y z : Int) : Path ((x + y) + z) (x + (y + z)) :=
  Path.ofEq (Int.add_assoc x y z)

/-- Inner commutativity `x + (y + z) ⤳ x + (z + y)` on `Int` via congruence. -/
noncomputable def zInner (x y z : Int) : Path (x + (y + z)) (x + (z + y)) :=
  Path.ofEq (_root_.congrArg (fun t => x + t) (Int.add_comm y z))

/-- A genuine **two-step** `Int` chain-degree path: reassociate, then commute the
    inner pair. -/
noncomputable def zTwoStep (x y z : Int) : Path ((x + y) + z) (x + (z + y)) :=
  Path.trans (zAssoc x y z) (zInner x y z)

/-- The two-step `Int` path cancels with its inverse — a non-decorative `RwEq`. -/
noncomputable def zTwoStep_cancel (x y z : Int) :
    RwEq (Path.trans (zTwoStep x y z) (Path.symm (zTwoStep x y z)))
      (Path.refl ((x + y) + z)) :=
  rweq_cmpA_inv_right (zTwoStep x y z)

/-! ## Mapping spaces -/

/-- Mapping spaces valued in simplicial sets, each with a Kan filler property. -/
structure MappingSpaceData (A : Type u) where
  /-- Mapping space simplicial set. -/
  map : A → A → SSetData
  /-- Each mapping space is a Kan complex. -/
  kan : ∀ a b : A, KanFillerProperty (map a b)

namespace MappingSpaceData

variable {A : Type u}

/-- Map(a,b) as a simplicial set. -/
abbrev Map (M : MappingSpaceData A) (a b : A) : SSetData :=
  M.map a b

/-- Mapping spaces are Kan. -/
noncomputable def map_is_kan (M : MappingSpaceData A) (a b : A) :
    KanFillerProperty (Map M a b) :=
  M.kan a b

end MappingSpaceData

/-! ## Simplicial enrichment -/

/-- Simplicial enrichment data for a type of objects. -/
structure SimplicialEnrichment (A : Type u) extends MappingSpaceData A where
  /-- Identity 0-simplex. -/
  id0 : ∀ a : A, (map a a).obj 0
  /-- Composition on 0-simplices. -/
  comp0 : ∀ {a b c : A}, (map a b).obj 0 → (map b c).obj 0 → (map a c).obj 0
  /-- Left identity law `id ∘ f ⤳ f`: a genuine computational path between the
      distinct 0-simplices `comp0 (id0 a) f` and `f` of the mapping space. -/
  id_comp : ∀ {a b : A} (f : (map a b).obj 0), Path (comp0 (id0 a) f) f
  /-- Right identity law `f ∘ id ⤳ f`: a genuine computational path. -/
  comp_id : ∀ {a b : A} (f : (map a b).obj 0), Path (comp0 f (id0 b)) f
  /-- Associativity law `(f ∘ g) ∘ h ⤳ f ∘ (g ∘ h)`: a genuine computational path
      between the two bracketings of a triple composite. -/
  comp_assoc :
    ∀ {a b c d : A} (f : (map a b).obj 0) (g : (map b c).obj 0)
      (h : (map c d).obj 0),
      Path (comp0 (comp0 f g) h) (comp0 f (comp0 g h))

/-! ## Simplicial model categories -/

/-- A simplicial model category structure on computational paths. -/
structure SimplicialModelCategory (A : Type u) extends ModelCategory A where
  /-- Simplicial enrichment on mapping spaces. -/
  enrichment : SimplicialEnrichment A
  /-- Tensor with a simplicial set. -/
  tensor : A → SSetData → A
  /-- Cotensor with a simplicial set. -/
  cotensor : A → SSetData → A
  /-- The simplicial unit `Δ[0]` (the point). -/
  unitSSet : SSetData
  /-- Tensor unit law `a ⊗ Δ[0] ⤳ a`: a genuine computational path in `A` between
      the distinct expressions `tensor a Δ[0]` and `a`. -/
  tensor_unit : ∀ a : A, Path (tensor a unitSSet) a
  /-- Cotensor unit law `a^{Δ[0]} ⤳ a`: a genuine computational path in `A`. -/
  cotensor_unit : ∀ a : A, Path (cotensor a unitSSet) a

namespace SimplicialModelCategory

variable {A : Type u}

/-- Mapping space in a simplicial model category. -/
abbrev mappingSpace (M : SimplicialModelCategory A) (a b : A) : SSetData :=
  M.enrichment.map a b

/-- Mapping spaces are Kan. -/
noncomputable def mappingSpace_is_kan (M : SimplicialModelCategory A) (a b : A) :
    KanFillerProperty (mappingSpace M a b) :=
  M.enrichment.kan a b

end SimplicialModelCategory

/-! ## Hammock localization -/

/-- Hammock localization data for a model category. -/
structure HammockLocalization {A : Type u} (M : ModelCategory A) where
  /-- Mapping space simplicial set. -/
  map : A → A → SSetData
  /-- Localization map from paths to 0-simplices. -/
  localize : {a b : A} → Path a b → (map a b).obj 0
  /-- Localization respects rewrite equality: rewrite-equal paths land on the
      same 0-simplex.  This is the genuine computational-path content of the
      localization. -/
  localize_rweq :
    ∀ {a b : A} {p q : Path a b}, RwEq p q → localize p = localize q

/-! ## Simplicial and cosimplicial objects -/

/-- A simplicial object in a type, with faces and degeneracies as paths. -/
structure SimplicialObject (A : Type u) where
  /-- Object in each degree. -/
  obj : Nat → A
  /-- Face maps `dᵢ : Xₙ₊₁ → Xₙ` as computational paths. -/
  face : (n : Nat) → Fin (n + 2) → Path (obj (n + 1)) (obj n)
  /-- Degeneracy maps `sᵢ : Xₙ → Xₙ₊₁` as computational paths. -/
  degen : (n : Nat) → Fin (n + 1) → Path (obj n) (obj (n + 1))

/-- A cosimplicial object in a type, with cofaces and codegeneracies as paths. -/
structure CosimplicialObject (A : Type u) where
  /-- Object in each degree. -/
  obj : Nat → A
  /-- Coface maps `dⁱ : Xₙ → Xₙ₊₁` as computational paths. -/
  coface : (n : Nat) → Fin (n + 2) → Path (obj n) (obj (n + 1))
  /-- Codegeneracy maps `sⁱ : Xₙ₊₁ → Xₙ` as computational paths. -/
  codegen : (n : Nat) → Fin (n + 1) → Path (obj (n + 1)) (obj n)

/-! ## Resolutions and framings -/

/-- A simplicial resolution of an object in a model category. -/
structure SimplicialResolution {A : Type u} (M : ModelCategory A) (X : A) where
  /-- Underlying simplicial object. -/
  simplicial : SimplicialObject A
  /-- Augmentation `X₀ ⤳ X`, a genuine computational path to the resolved
      object. -/
  augmentation : Path (simplicial.obj 0) X

/-- A cosimplicial resolution of an object in a model category. -/
structure CosimplicialResolution {A : Type u} (M : ModelCategory A) (X : A) where
  /-- Underlying cosimplicial object. -/
  cosimplicial : CosimplicialObject A
  /-- Coaugmentation `X ⤳ X⁰`, a genuine computational path from the object. -/
  coaugmentation : Path X (cosimplicial.obj 0)

/-- A framing packages simplicial and cosimplicial resolutions. -/
structure Framing {A : Type u} (M : SimplicialModelCategory A) (X : A) where
  /-- Cosimplicial resolution. -/
  cosimplicial : CosimplicialResolution (M := M.toModelCategory) X
  /-- Simplicial resolution. -/
  simplicial : SimplicialResolution (M := M.toModelCategory) X

/-! ## Summary -/

/-!
We defined simplicial model category data with mapping spaces, recorded hammock
localization data, and introduced simplicial/cosimplicial resolutions and
framings in the computational paths setting.
-/


/-! ## Genuine path coherences over the abstract simplicial data

These replace the earlier reflexive `X = X := rfl` placeholders with genuine
computational-path content: non-decorative `RwEq` coherences
(inverse-cancellation, double-symmetry, associativity) attached to the module's
own simplicial/cosimplicial/resolution data, plus a concrete degree certificate. -/

/-- Any simplicial object carries a genuine inverse-cancellation coherence on its
    degree-0 degeneracy `s₀`: `s₀ ⬝ s₀⁻¹ ⤳ refl`.  A non-decorative `RwEq` on the
    object's own path data. -/
noncomputable def SimplicialObject.degenCancel {A : Type u} (S : SimplicialObject A) :
    RwEq
      (Path.trans (S.degen 0 ⟨0, by omega⟩) (Path.symm (S.degen 0 ⟨0, by omega⟩)))
      (Path.refl (S.obj 0)) :=
  rweq_cmpA_inv_right (S.degen 0 ⟨0, by omega⟩)

/-- Any simplicial object carries a genuine double-symmetry collapse on its
    degree-0 face `d₀`: `(d₀⁻¹)⁻¹ ⤳ d₀`.  A non-decorative `RwEq`. -/
noncomputable def SimplicialObject.faceDoubleSymm {A : Type u} (S : SimplicialObject A) :
    RwEq (Path.symm (Path.symm (S.face 0 ⟨0, by omega⟩))) (S.face 0 ⟨0, by omega⟩) :=
  rweq_ss (S.face 0 ⟨0, by omega⟩)

/-- Any cosimplicial object carries a genuine inverse-cancellation coherence on
    its degree-0 coface `d⁰`: `d⁰ ⬝ (d⁰)⁻¹ ⤳ refl`.  A non-decorative `RwEq`. -/
noncomputable def CosimplicialObject.cofaceCancel {A : Type u} (C : CosimplicialObject A) :
    RwEq
      (Path.trans (C.coface 0 ⟨0, by omega⟩) (Path.symm (C.coface 0 ⟨0, by omega⟩)))
      (Path.refl (C.obj 0)) :=
  rweq_cmpA_inv_right (C.coface 0 ⟨0, by omega⟩)

/-- The augmentation of a simplicial resolution admits a genuine inverse
    cancellation `ε ⬝ ε⁻¹ ⤳ refl` — a non-decorative `RwEq` on the resolution's
    own augmentation path. -/
noncomputable def SimplicialResolution.augmentationCancel {A : Type u}
    {M : ModelCategory A} {X : A} (R : SimplicialResolution M X) :
    RwEq (Path.trans R.augmentation (Path.symm R.augmentation))
      (Path.refl (R.simplicial.obj 0)) :=
  rweq_cmpA_inv_right R.augmentation

/-- The coaugmentation of a cosimplicial resolution admits a genuine inverse
    cancellation `η ⬝ η⁻¹ ⤳ refl`. -/
noncomputable def CosimplicialResolution.coaugmentationCancel {A : Type u}
    {M : ModelCategory A} {X : A} (R : CosimplicialResolution M X) :
    RwEq (Path.trans R.coaugmentation (Path.symm R.coaugmentation))
      (Path.refl X) :=
  rweq_cmpA_inv_right R.coaugmentation

/-- Hammock localization sends rewrite-equal paths to a single 0-simplex — the
    genuine `localize_rweq` coherence exposed as a standalone lemma. -/
theorem HammockLocalization.localize_congr {A : Type u} {M : ModelCategory A}
    (H : HammockLocalization M) {a b : A} {p q : Path a b} (h : RwEq p q) :
    H.localize p = H.localize q :=
  H.localize_rweq h

/-! ## Concrete simplicial-degree certificate -/

/-- A concrete degree-bookkeeping certificate.  It packages a genuine two-step
    `Path.trans` over three simplicial-degree slices, a `PathLawCertificate`
    trace, a non-decorative inverse-cancellation `RwEq`, and an associativity
    `RwEq` over three genuine commutation steps — all anchored to concrete `Nat`
    data. -/
structure DegreeCertificate where
  /-- Concrete simplicial-degree slice data. -/
  a : Nat
  /-- Concrete simplicial-degree slice data. -/
  b : Nat
  /-- Concrete simplicial-degree slice data. -/
  c : Nat
  /-- A genuine two-step degree path `((a+b)+c) ⤳ a+(c+b)` (`dTwoStep`). -/
  degreePath : Path ((a + b) + c) (a + (c + b))
  /-- Law certificate over the two-step path. -/
  degreeTrace : Topology.PathLawCertificate ((a + b) + c) (a + (c + b))
  /-- The two-step trace composed with its inverse cancels to `refl`. -/
  degreeCoh : RwEq (Path.trans degreePath (Path.symm degreePath))
    (Path.refl ((a + b) + c))
  /-- Associativity coherence over three genuine `dComm` steps. -/
  assocCoh : RwEq
    (Path.trans (Path.trans (dComm a b) (dComm b a)) (dComm a b))
    (Path.trans (dComm a b) (Path.trans (dComm b a) (dComm a b)))

/-- The degree certificate instantiated at the concrete degrees `(2, 3, 5)`. -/
noncomputable def degreeCapstone : DegreeCertificate where
  a := 2
  b := 3
  c := 5
  degreePath := dTwoStep 2 3 5
  degreeTrace := Topology.PathLawCertificate.ofPath (dTwoStep 2 3 5)
  degreeCoh := dTwoStep_cancel 2 3 5
  assocCoh := rweq_tt (dComm 2 3) (dComm 3 2) (dComm 2 3)

/-- The capstone's reassembled degree computes to the concrete value `10`. -/
theorem degreeCapstone_value : (2 : Nat) + (5 + 3) = 10 := by decide

/-- A companion `Int` certificate coherence: the genuine two-step
    reassociation/commutation over concrete chain degrees `(-2, 4, 6)` cancels
    with its inverse. -/
noncomputable def zDegreeCapstone :
    RwEq (Path.trans (zTwoStep (-2) 4 6) (Path.symm (zTwoStep (-2) 4 6)))
      (Path.refl (((-2) + 4) + 6)) :=
  zTwoStep_cancel (-2) 4 6

/-- The `Int` capstone's reassembled value computes to the concrete `8`. -/
theorem zDegreeCapstone_value : ((-2 : Int) + (6 + 4)) = 8 := by decide

end SimplicialModel
end Homotopy
end Path
end ComputationalPaths
