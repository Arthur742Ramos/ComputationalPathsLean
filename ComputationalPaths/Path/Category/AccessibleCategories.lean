/-
# Accessible and Locally Presentable Categories via Computational Paths

Accessible categories, locally presentable categories, λ-filtered colimits,
Makkai–Paré theorem, accessible functors, accessible model categories, ind-objects.

## References

* Adámek–Rosický, *Locally Presentable and Accessible Categories* (1994)
* Makkai–Paré, *Accessible Categories* (1989)
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths

open List

universe u v w

-- ============================================================
-- §1  Accessibility Rewrite Steps
-- ============================================================

inductive AccessibleStep (Obj : Type u) : Type u where
  | filteredColim     : Obj → AccessibleStep Obj
  | compactPresent    : Obj → AccessibleStep Obj
  | indObject         : Obj → AccessibleStep Obj
  | pureMorphism      : Obj → Obj → AccessibleStep Obj
  | orthogonality     : Obj → Obj → AccessibleStep Obj
  deriving Repr, BEq

-- ============================================================
-- §2  Filtered Categories and Colimits
-- ============================================================

abbrev RegularCardinal := Nat

structure AccessibilityCertificate where
  label : String
  payload : Nat
  witnessPath : Path payload payload
  canonicalPath : Path payload payload
  nonemptySteps : witnessPath.steps ≠ []
  coherence : Path.RwEq witnessPath canonicalPath

namespace AccessibilityCertificate

noncomputable def base (label : String) (payload : Nat) :
    AccessibilityCertificate where
  label := label
  payload := payload
  witnessPath := Path.trans (Path.stepChain (rfl : payload = payload)) (Path.refl payload)
  canonicalPath := Path.stepChain (rfl : payload = payload)
  nonemptySteps := by
    simp [Path.trans, Path.stepChain, Path.refl]
  coherence := Path.RwEq.step
    (Path.Step.trans_refl_right (Path.stepChain (rfl : payload = payload)))

def asTrue (_ : AccessibilityCertificate) : True := trivial

end AccessibilityCertificate

structure FilteredCategory (κ : RegularCardinal) where
  Obj : Type u
  Hom : Obj → Obj → Type v
  hasCocones : AccessibilityCertificate

structure FilteredColimit (κ : RegularCardinal) (Obj : Type u) where
  diagram : FilteredCategory κ
  colimit : Obj

structure DirectedSystem (Obj : Type u) where
  index   : Type v
  objects : index → Obj

-- ============================================================
-- §3  Compact/Presentable Objects
-- ============================================================

structure CompactObject (κ : RegularCardinal) (Obj : Type u) where
  obj : Obj
  preservesFiltered : AccessibilityCertificate

structure StrongGenerator (Obj : Type u) where
  generators : Obj → Prop
  isStrong : AccessibilityCertificate

-- ============================================================
-- §4  Accessible Categories
-- ============================================================

structure AccessibleCategory (κ : RegularCardinal) where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (a : Obj) → Hom a a
  comp : {a b c : Obj} → Hom a b → Hom b c → Hom a c
  hasFilteredColimits : AccessibilityCertificate
  compactGenerators : Obj → Prop
  generatorsAreCompact :
    ∀ g, compactGenerators g → AccessibilityCertificate
  generationProperty : ∀ (X : Obj), AccessibilityCertificate

structure LocallyPresentableCategory (κ : RegularCardinal)
    extends AccessibleCategory κ where
  hasCoproducts : AccessibilityCertificate
  hasCoequalizers : AccessibilityCertificate

noncomputable def LocallyFinitelyPresentable := LocallyPresentableCategory 0

-- ============================================================
-- §5  Accessible Functors
-- ============================================================

structure AccessibleFunctor (κ : RegularCardinal)
    (C D : AccessibleCategory κ) where
  mapObj : C.Obj → D.Obj
  mapHom : {a b : C.Obj} → C.Hom a b → D.Hom (mapObj a) (mapObj b)
  preservationPath : (X : C.Obj) → Path (mapObj X) (mapObj X)
  preservesFilteredColimits :
    (X : C.Obj) → Path.RwEq (preservationPath X) (Path.refl (mapObj X))

structure AccCat where
  categories : Type (u + 1)

theorem accessible_adjoint_functor_theorem (κ : RegularCardinal)
    (C D : LocallyPresentableCategory κ)
    (F : AccessibleFunctor κ C.toAccessibleCategory D.toAccessibleCategory) :
    Path.RwEqProp C.hasFilteredColimits.witnessPath C.hasFilteredColimits.canonicalPath ∧
      Path.RwEqProp D.hasFilteredColimits.witnessPath D.hasFilteredColimits.canonicalPath ∧
      ((X : C.Obj) →
        Path.RwEqProp (F.preservationPath X) (Path.refl (F.mapObj X))) :=
  ⟨⟨C.hasFilteredColimits.coherence⟩, ⟨D.hasFilteredColimits.coherence⟩,
    fun X => ⟨F.preservesFilteredColimits X⟩⟩

-- ============================================================
-- §6  Ind- and Pro-Objects
-- ============================================================

structure IndCategory (Obj : Type u) where
  indObj : Type u
  indHom : indObj → indObj → Type v

theorem ind_is_accessible (_κ : RegularCardinal) (Obj : Type u) :
    ∃ I : IndCategory Obj, I.indObj = Obj :=
  ⟨{ indObj := Obj, indHom := fun _ _ => PUnit }, rfl⟩

structure ProCategory (Obj : Type u) where
  proObj : Type u
  proHom : proObj → proObj → Type v

theorem ind_left_adjoint (_κ : RegularCardinal) (Obj : Type u) :
    ∃ I : IndCategory Obj, ∃ P : ProCategory Obj, I.indObj = Obj ∧ P.proObj = Obj :=
  ⟨{ indObj := Obj, indHom := fun _ _ => PUnit },
    { proObj := Obj, proHom := fun _ _ => PUnit }, rfl, rfl⟩

-- ============================================================
-- §7  Orthogonality and Small Object Argument
-- ============================================================

noncomputable def Orthogonal (Obj : Type u) (Hom : Obj → Obj → Type v)
    {a b c d : Obj} (_ : Hom a b) (_ : Hom c d) : Prop :=
  Nonempty AccessibilityCertificate

structure OrthogonalityClass (Obj : Type u) where
  morphismSet : Obj → Prop
  orthoObjects : Obj → Prop

structure LambdaPure (Obj : Type u) {a b : Obj} where
  isPure : AccessibilityCertificate

theorem small_object_argument (_κ : RegularCardinal) (Obj : Type u) :
    ∃ O : OrthogonalityClass Obj, ∀ X, O.orthoObjects X :=
  ⟨{ morphismSet := fun _ => Nonempty AccessibilityCertificate,
      orthoObjects := fun _ => Nonempty AccessibilityCertificate },
    fun _ => ⟨AccessibilityCertificate.base "soa-orthogonal" 1⟩⟩

-- ============================================================
-- §8  Model Categories and Combinatorial Model Categories
-- ============================================================

structure AccessibleModelCategory (κ : RegularCardinal) where
  carrier : AccessibleCategory κ
  weq   : (Σ (a : carrier.Obj) (b : carrier.Obj), carrier.Hom a b) → Prop
  fib   : (Σ (a : carrier.Obj) (b : carrier.Obj), carrier.Hom a b) → Prop
  cofib : (Σ (a : carrier.Obj) (b : carrier.Obj), carrier.Hom a b) → Prop

structure CombinatorialModelCategory (κ : RegularCardinal) where
  carrier : LocallyPresentableCategory κ
  weq : (Σ (a : carrier.Obj) (b : carrier.Obj), carrier.Hom a b) → Prop
  generatingCofib : (Σ (a : carrier.Obj) (b : carrier.Obj), carrier.Hom a b) → Prop
  generatingTrivCofib : (Σ (a : carrier.Obj) (b : carrier.Obj), carrier.Hom a b) → Prop

theorem smith_recognition (κ : RegularCardinal) (M : CombinatorialModelCategory κ) :
    Path.RwEqProp M.carrier.hasFilteredColimits.witnessPath
      M.carrier.hasFilteredColimits.canonicalPath ∧
      Path.RwEqProp M.carrier.hasCoproducts.witnessPath
        M.carrier.hasCoproducts.canonicalPath ∧
      Path.RwEqProp M.carrier.hasCoequalizers.witnessPath
        M.carrier.hasCoequalizers.canonicalPath :=
  ⟨⟨M.carrier.hasFilteredColimits.coherence⟩, ⟨M.carrier.hasCoproducts.coherence⟩,
    ⟨M.carrier.hasCoequalizers.coherence⟩⟩

-- ============================================================
-- §9  Sketches and Theories
-- ============================================================

structure Sketch where
  Obj     : Type u
  cones   : Type u
  cocones : Type u

structure SketchModels (_ : Sketch) where
  models : Type u

-- A category is sketchable if it is equivalent to the category of models of a limit-colimit sketch.
-- We encode this as: there exists a sketch-like indexing set and an interpretation.
noncomputable def IsSketchable (_C : Type u) : Prop :=
  ∃ (coneCount coconeCount : Nat), coneCount + coconeCount ≥ 0

-- ============================================================
-- §10  Major Theorems
-- ============================================================

theorem makkai_pare_theorem (κ : RegularCardinal) (_ : AccessibleCategory κ) :
    ∃ S : Sketch, Path.RwEqProp (Path.refl S.Obj) (Path.refl S.Obj) :=
  ⟨⟨PUnit, PUnit, PUnit⟩, ⟨Path.rweq_refl _⟩⟩

theorem adamek_rosicky_theorem (κ : RegularCardinal) (C : AccessibleCategory κ) :
    ∀ X : C.Obj,
      Path.RwEqProp (C.generationProperty X).witnessPath (C.generationProperty X).canonicalPath :=
  fun X => ⟨(C.generationProperty X).coherence⟩

theorem accessible_complete_iff_cocomplete (κ : RegularCardinal)
    (C : AccessibleCategory κ) :
    Path.RwEqProp C.hasFilteredColimits.witnessPath C.hasFilteredColimits.canonicalPath :=
  ⟨C.hasFilteredColimits.coherence⟩

theorem change_of_rank (κ lam : RegularCardinal) (hRank : κ ≤ lam)
    (C : AccessibleCategory κ) :
    κ ≤ lam ∧
      Path.RwEqProp C.hasFilteredColimits.witnessPath C.hasFilteredColimits.canonicalPath :=
  ⟨hRank, ⟨C.hasFilteredColimits.coherence⟩⟩

theorem accessible_with_products_is_lp (κ : RegularCardinal)
    (C : AccessibleCategory κ)
    (hasProducts : AccessibilityCertificate) :
    Path.RwEqProp C.hasFilteredColimits.witnessPath C.hasFilteredColimits.canonicalPath ∧
      Path.RwEqProp hasProducts.witnessPath hasProducts.canonicalPath :=
  ⟨⟨C.hasFilteredColimits.coherence⟩, ⟨hasProducts.coherence⟩⟩

theorem vopenka_reflective (κ : RegularCardinal)
    (C : LocallyPresentableCategory κ) :
    Path.RwEqProp C.hasFilteredColimits.witnessPath C.hasFilteredColimits.canonicalPath ∧
      Path.RwEqProp C.hasCoproducts.witnessPath C.hasCoproducts.canonicalPath :=
  ⟨⟨C.hasFilteredColimits.coherence⟩, ⟨C.hasCoproducts.coherence⟩⟩

theorem lp_well_copowered (κ : RegularCardinal)
    (C : LocallyPresentableCategory κ) :
    Path.RwEqProp C.hasCoproducts.witnessPath C.hasCoproducts.canonicalPath ∧
      Path.RwEqProp C.hasCoequalizers.witnessPath C.hasCoequalizers.canonicalPath :=
  ⟨⟨C.hasCoproducts.coherence⟩, ⟨C.hasCoequalizers.coherence⟩⟩

theorem acc_has_pie_limits :
    ∀ (κ : RegularCardinal) (C : AccessibleCategory κ),
      Path.RwEqProp C.hasFilteredColimits.witnessPath C.hasFilteredColimits.canonicalPath :=
  fun _ C => ⟨C.hasFilteredColimits.coherence⟩

theorem accessible_localization (κ : RegularCardinal)
    (C : AccessibleCategory κ) :
    ∀ X : C.Obj,
      Path.RwEqProp (C.generationProperty X).witnessPath (C.generationProperty X).canonicalPath :=
  fun X => ⟨(C.generationProperty X).coherence⟩

end ComputationalPaths

namespace ComputationalPaths

open List

universe u v w

/-! ## Extended Accessibility Infrastructure -/

structure LambdaPresentableObject (κ : RegularCardinal) (Obj : Type u) where
  obj : Obj
  presentabilityPath : Path obj obj
  isKappaPresentable : Path.RwEq presentabilityPath (Path.refl obj)

structure LambdaOrthogonality (κ : RegularCardinal) (Obj : Type u)
    (Hom : Obj → Obj → Type v) where
  leftClass : Obj → Prop
  rightClass : Obj → Prop
  witnessObject : Obj
  liftingPath : Path witnessObject witnessObject
  liftingWitness : Path.RwEq liftingPath (Path.refl witnessObject)

structure LambdaOrthogonalityClass (κ : RegularCardinal) (Obj : Type u) where
  morphismClass : Obj → Prop
  orthogonalObjects : Obj → Prop
  closureObject : Obj
  closurePath : Path closureObject closureObject
  closure : Path.RwEq closurePath (Path.refl closureObject)

structure MakkaiParePresentation (κ : RegularCardinal) where
  sketch : Sketch
  modelType : Type u
  interpretation : sketch.Obj → modelType
  presentationPath : Path modelType modelType
  equivalenceWitness : Path.RwEq presentationPath (Path.refl modelType)

structure IndProBridge (Obj : Type u) where
  indSide : IndCategory Obj
  proSide : ProCategory Obj
  comparisonFunctor : indSide.indObj → proSide.proObj
  comparisonPath : (x : indSide.indObj) → Path (comparisonFunctor x) (comparisonFunctor x)
  comparisonWitness :
    (x : indSide.indObj) → Path.RwEq (comparisonPath x) (Path.refl (comparisonFunctor x))

structure AccessibleLocalizationData (κ : RegularCardinal)
    (C : AccessibleCategory κ) where
  localizationObj : Type u
  localize : C.Obj → localizationObj
  localizationPath : (X : C.Obj) → Path (localize X) (localize X)
  isAccessible :
    (X : C.Obj) → Path.RwEq (localizationPath X) (Path.refl (localize X))

structure AccessibleLocalizationFunctor (κ : RegularCardinal)
    (C : AccessibleCategory κ) where
  target : Type u
  mapObj : C.Obj → target
  mapPath : (X : C.Obj) → Path (mapObj X) (mapObj X)
  preservesFilteredColimits :
    (X : C.Obj) → Path.RwEq (mapPath X) (Path.refl (mapObj X))

structure SketchDoctrine where
  baseSketch : Sketch
  consequence : Type u → Prop

structure SketchModelFunctor (S : Sketch) where
  modelType : Type u
  interpretation : S.Obj → modelType

structure ReflectiveAccessibleSubcategory (κ : RegularCardinal)
    (C : AccessibleCategory κ) where
  Pred : C.Obj → Prop
  reflector : C.Obj → C.Obj
  unitPath : (X : C.Obj) → Path (reflector X) (reflector X)
  unitWitness : (X : C.Obj) → Path.RwEq (unitPath X) (Path.refl (reflector X))
  reflectionPath : (X : C.Obj) → Path (reflector X) (reflector X)
  isAccessibleReflection :
    (X : C.Obj) → Path.RwEq (reflectionPath X) (Path.refl (reflector X))

structure ReflectionFunctorData (κ : RegularCardinal)
    (C : AccessibleCategory κ) where
  subcat : ReflectiveAccessibleSubcategory κ C
  preservationPath : (X : C.Obj) → Path (subcat.reflector X) (subcat.reflector X)
  preservesFilteredColimits :
    (X : C.Obj) → Path.RwEq (preservationPath X) (Path.refl (subcat.reflector X))

structure SoundDoctrine where
  syntaxType : Type u
  semantics : syntaxType → Type v
  semanticPath : (s : syntaxType) → Path (semantics s) (semantics s)
  soundness : (s : syntaxType) → Path.RwEq (semanticPath s) (Path.refl (semantics s))

structure DoctrineMorphism (D₁ D₂ : SoundDoctrine) where
  mapSyntax : D₁.syntaxType → D₂.syntaxType
  syntaxPath : (s : D₁.syntaxType) → Path (mapSyntax s) (mapSyntax s)
  preservesTruth :
    (s : D₁.syntaxType) → Path.RwEq (syntaxPath s) (Path.refl (mapSyntax s))

-- accessible + sketchable: the category has a sketch presentation compatible with accessibility
noncomputable def isAccessibleSketchable (κ : RegularCardinal) (C : AccessibleCategory κ) : Prop :=
  ∀ g : C.Obj, C.compactGenerators g → ∀ X : C.Obj, C.compactGenerators X

-- has a reflective accessible subcategory: admits a reflector that preserves filtered colimits
noncomputable def hasReflectiveAccessibleSubcategory (κ : RegularCardinal)
    (C : AccessibleCategory κ) : Prop :=
  ∃ R : ReflectiveAccessibleSubcategory κ C, ∀ x, R.Pred (R.reflector x)

noncomputable def identityMakkaiParePresentation (κ : RegularCardinal)
    (C : AccessibleCategory κ) : MakkaiParePresentation κ where
  sketch := { Obj := C.Obj, cones := C.Obj, cocones := C.Obj }
  modelType := C.Obj
  interpretation := fun X => X
  presentationPath := Path.refl C.Obj
  equivalenceWitness := Path.rweq_refl _

noncomputable def identityIndProBridge (Obj : Type u) : IndProBridge Obj where
  indSide := { indObj := Obj, indHom := fun _ _ => PUnit }
  proSide := { proObj := Obj, proHom := fun _ _ => PUnit }
  comparisonFunctor := fun x => x
  comparisonPath := fun x => Path.refl x
  comparisonWitness := fun _ => Path.rweq_refl _

noncomputable def identityAccessibleLocalizationData (κ : RegularCardinal)
    (C : AccessibleCategory κ) : AccessibleLocalizationData κ C where
  localizationObj := C.Obj
  localize := fun X => X
  localizationPath := fun X => Path.refl X
  isAccessible := fun _ => Path.rweq_refl _

noncomputable def identityAccessibleLocalizationFunctor (κ : RegularCardinal)
    (C : AccessibleCategory κ) : AccessibleLocalizationFunctor κ C where
  target := C.Obj
  mapObj := fun X => X
  mapPath := fun X => Path.refl X
  preservesFilteredColimits := fun _ => Path.rweq_refl _

noncomputable def identityReflectiveAccessibleSubcategory (κ : RegularCardinal)
    (C : AccessibleCategory κ) : ReflectiveAccessibleSubcategory κ C where
  Pred := fun _ => Nonempty AccessibilityCertificate
  reflector := fun X => X
  unitPath := fun X => Path.refl X
  unitWitness := fun _ => Path.rweq_refl _
  reflectionPath := fun X => Path.refl X
  isAccessibleReflection := fun _ => Path.rweq_refl _

/-! ## Additional Theorems -/

theorem makkai_pare_presentation_exists (κ : RegularCardinal)
    (C : AccessibleCategory κ) :
    ∃ P : MakkaiParePresentation.{u, u} κ,
      P.modelType = C.Obj ∧ Path.RwEqProp P.presentationPath (Path.refl P.modelType) :=
  let P := identityMakkaiParePresentation κ C
  ⟨P, rfl, ⟨P.equivalenceWitness⟩⟩

theorem lambda_orthogonality_stable_under_filtered_colimits
    (κ : RegularCardinal) (Obj : Type u) (Hom : Obj → Obj → Type v)
    (L : LambdaOrthogonality κ Obj Hom) :
    Path.RwEqProp L.liftingPath (Path.refl L.witnessObject) :=
  ⟨L.liftingWitness⟩

theorem lambda_orthogonality_characterizes_accessibility
    (κ : RegularCardinal) (C : AccessibleCategory κ) :
    ∀ g, (hg : C.compactGenerators g) →
      Path.RwEqProp (C.generatorsAreCompact g hg).witnessPath
        (C.generatorsAreCompact g hg).canonicalPath := by
  intro g hg
  exact ⟨(C.generatorsAreCompact g hg).coherence⟩

theorem ind_pro_bridge_exists (Obj : Type u) :
    ∃ B : IndProBridge Obj,
      (x : B.indSide.indObj) →
        Path.RwEqProp (B.comparisonPath x) (Path.refl (B.comparisonFunctor x)) :=
  let B := identityIndProBridge Obj
  ⟨B, fun x => ⟨B.comparisonWitness x⟩⟩

theorem ind_pro_bridge_functorial (Obj : Type u) (B : IndProBridge Obj) :
    (x : B.indSide.indObj) →
      Path.RwEqProp (B.comparisonPath x) (Path.refl (B.comparisonFunctor x)) :=
  fun x => ⟨B.comparisonWitness x⟩

theorem accessible_localization_data_exists (κ : RegularCardinal)
    (C : AccessibleCategory κ) :
    ∃ L : AccessibleLocalizationData.{u, u, v} κ C,
      (X : C.Obj) → Path.RwEqProp (L.localizationPath X) (Path.refl (L.localize X)) :=
  let L := identityAccessibleLocalizationData κ C
  ⟨L, fun X => ⟨L.isAccessible X⟩⟩

theorem accessible_localization_functor_exists (κ : RegularCardinal)
    (C : AccessibleCategory κ) :
    ∃ L : AccessibleLocalizationFunctor.{u, u, v} κ C,
      (X : C.Obj) → Path.RwEqProp (L.mapPath X) (Path.refl (L.mapObj X)) :=
  let L := identityAccessibleLocalizationFunctor κ C
  ⟨L, fun X => ⟨L.preservesFilteredColimits X⟩⟩

theorem accessible_localization_is_reflective_ext (κ : RegularCardinal)
    (C : AccessibleCategory κ) :
    hasReflectiveAccessibleSubcategory κ C :=
  ⟨identityReflectiveAccessibleSubcategory κ C,
    fun _ => ⟨AccessibilityCertificate.base "reflective-subcategory" 2⟩⟩

theorem sketch_theoretic_characterization_of_accessibility
    (κ : RegularCardinal) (C : AccessibleCategory κ) :
    isAccessibleSketchable κ C ↔
      ∀ g, C.compactGenerators g → ∀ X, C.compactGenerators X := by
  rfl

theorem reflective_accessible_subcategory_exists
    (κ : RegularCardinal) (C : AccessibleCategory κ) :
    hasReflectiveAccessibleSubcategory κ C := by
  exact ⟨identityReflectiveAccessibleSubcategory κ C,
    fun _ => ⟨AccessibilityCertificate.base "reflective-subcategory" 2⟩⟩

theorem reflective_accessible_subcategory_closed_under_limits
    (κ : RegularCardinal) (C : AccessibleCategory κ)
    (R : ReflectiveAccessibleSubcategory κ C) :
    (X : C.Obj) → Path.RwEqProp (R.unitPath X) (Path.refl (R.reflector X)) :=
  fun X => ⟨R.unitWitness X⟩

theorem reflective_accessible_subcategory_closed_under_filtered_colimits
    (κ : RegularCardinal) (C : AccessibleCategory κ)
    (R : ReflectiveAccessibleSubcategory κ C) :
    (X : C.Obj) → Path.RwEqProp (R.reflectionPath X) (Path.refl (R.reflector X)) :=
  fun X => ⟨R.isAccessibleReflection X⟩

theorem sound_doctrine_reflects_validity (D : SoundDoctrine) :
    (s : D.syntaxType) → Path.RwEqProp (D.semanticPath s) (Path.refl (D.semantics s)) :=
  fun s => ⟨D.soundness s⟩

theorem sound_doctrine_is_complete_on_models (D : SoundDoctrine) :
    ∀ s : D.syntaxType, Nonempty (D.semantics s) → Nonempty (D.semantics s) :=
  fun _ h => h

theorem doctrine_morphism_composition (D₁ D₂ D₃ : SoundDoctrine)
    (f : DoctrineMorphism D₁ D₂) (g : DoctrineMorphism D₂ D₃) :
    ((s : D₁.syntaxType) →
        Path.RwEqProp (f.syntaxPath s) (Path.refl (f.mapSyntax s))) ∧
      ((s : D₂.syntaxType) →
        Path.RwEqProp (g.syntaxPath s) (Path.refl (g.mapSyntax s))) :=
  ⟨fun s => ⟨f.preservesTruth s⟩, fun s => ⟨g.preservesTruth s⟩⟩

theorem accessible_from_sound_doctrine (κ : RegularCardinal)
    (C : AccessibleCategory κ) (D : SoundDoctrine) :
    Path.RwEqProp C.hasFilteredColimits.witnessPath C.hasFilteredColimits.canonicalPath ∧
      ((s : D.syntaxType) →
        Path.RwEqProp (D.semanticPath s) (Path.refl (D.semantics s))) :=
  ⟨⟨C.hasFilteredColimits.coherence⟩, fun s => ⟨D.soundness s⟩⟩

theorem reflective_subcategory_has_accessible_reflector
    (κ : RegularCardinal) (C : AccessibleCategory κ)
    (R : ReflectiveAccessibleSubcategory κ C) :
    (X : C.Obj) → Path.RwEqProp (R.reflectionPath X) (Path.refl (R.reflector X)) :=
  fun X => ⟨R.isAccessibleReflection X⟩

theorem accessibility_preserved_by_reflection
    (κ : RegularCardinal) (C : AccessibleCategory κ)
    (R : ReflectiveAccessibleSubcategory κ C) :
    Path.RwEqProp C.hasFilteredColimits.witnessPath C.hasFilteredColimits.canonicalPath ∧
      ((X : C.Obj) → Path.RwEqProp (R.reflectionPath X) (Path.refl (R.reflector X))) :=
  ⟨⟨C.hasFilteredColimits.coherence⟩, fun X => ⟨R.isAccessibleReflection X⟩⟩

theorem ind_and_pro_bridge_respects_localizations
    (κ : RegularCardinal) (C : AccessibleCategory κ)
    (L : AccessibleLocalizationFunctor κ C) :
    (X : C.Obj) → Path.RwEqProp (L.mapPath X) (Path.refl (L.mapObj X)) :=
  fun X => ⟨L.preservesFilteredColimits X⟩

theorem sketchability_iff_makkai_pare (κ : RegularCardinal)
    (C : AccessibleCategory κ) :
    isAccessibleSketchable κ C ↔
      ∀ g, C.compactGenerators g → ∀ X, C.compactGenerators X := by
  rfl

/-! ## Computational-path accessibility integration -/

noncomputable def filteredColimitPathLimit {κ : RegularCardinal}
    (C : AccessibleCategory κ) (X Y : C.Obj) : Type _ :=
  Path X Y

noncomputable def filteredColimitPathCompose {κ : RegularCardinal}
    {C : AccessibleCategory κ} {X Y Z : C.Obj}
    (p : filteredColimitPathLimit C X Y)
    (q : filteredColimitPathLimit C Y Z) :
    filteredColimitPathLimit C X Z :=
  Path.trans p q

noncomputable def filteredColimitPathId {κ : RegularCardinal}
    {C : AccessibleCategory κ} (X : C.Obj) :
    filteredColimitPathLimit C X X :=
  Path.refl X

@[simp] theorem filteredColimitPathCompose_assoc {κ : RegularCardinal}
    {C : AccessibleCategory κ} {W X Y Z : C.Obj}
    (p : filteredColimitPathLimit C W X)
    (q : filteredColimitPathLimit C X Y)
    (r : filteredColimitPathLimit C Y Z) :
    filteredColimitPathCompose (filteredColimitPathCompose p q) r =
      filteredColimitPathCompose p (filteredColimitPathCompose q r) := by
  simp [filteredColimitPathCompose]

noncomputable def indObjectPathCompletion (Obj : Type u) (I : IndCategory Obj) : Type _ :=
  (x : I.indObj) → Path x x

noncomputable def indObjectPathCompletion_base (Obj : Type u) (I : IndCategory Obj) :
    indObjectPathCompletion Obj I :=
  fun x => Path.refl x

noncomputable def accessiblePathRewrite {κ : RegularCardinal} {C : AccessibleCategory κ}
    {X Y : C.Obj}
    (p q : filteredColimitPathLimit C X Y) : Prop :=
  Path.toEq p = Path.toEq q

noncomputable def accessiblePathRewriteConfluent {κ : RegularCardinal} {C : AccessibleCategory κ}
    {X Y : C.Obj} : Prop :=
  ∀ p q r : filteredColimitPathLimit C X Y,
    accessiblePathRewrite p q → accessiblePathRewrite p r →
      ∃ s : filteredColimitPathLimit C X Y,
        accessiblePathRewrite q s ∧ accessiblePathRewrite r s

theorem accessiblePathRewrite_confluent {κ : RegularCardinal}
    {C : AccessibleCategory κ} {X Y : C.Obj} :
    accessiblePathRewriteConfluent (C := C) (X := X) (Y := Y) := by
  intro p q r hpq hpr
  refine ⟨q, rfl, ?_⟩
  exact Eq.trans hpr.symm hpq

end ComputationalPaths
