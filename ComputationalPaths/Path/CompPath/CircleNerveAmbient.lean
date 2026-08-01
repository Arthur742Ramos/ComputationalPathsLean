import ComputationalPaths.Path.CompPath.CircleAmbientRealization
import ComputationalPaths.Path.Homotopy.TopologicalNerve
import ComputationalPaths.Path.Homotopy.TopologicalRealizationOpen
import Mathlib.Data.NNReal.Basic
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Topology.Homotopy.Equiv

open CategoryTheory Simplicial Opposite
open CategoryTheory.Limits
open scoped ContinuousMap

namespace ComputationalPaths
namespace Path
namespace CompPath
namespace CircleNerveAmbient

open CirclePresented
open CircleTopologicalRealization
open CircleAmbientRealization
open Presented
open TopologicalNerve

abbrev CircleObject :=
  Presented.Realization.Object CirclePresented.presentation

noncomputable abbrev CircleNerve : SSet :=
  CategoryTheory.nerve CircleObject

noncomputable abbrev CircleNerveRealization : TopCat :=
  Presented.Realization.topologicalRealization CirclePresented.presentation

/-! ## Winding coordinates on nerve simplices -/

/-- The integer winding carried by a morphism of the presented circle groupoid. -/
noncomputable def arrowWinding {X Y : CircleObject} (f : X ⟶ Y) : ℤ :=
  topologicalWinding (comparisonFunctor.map f)

theorem arrowWinding_comp {X Y Z : CircleObject}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    arrowWinding (f ≫ g) = arrowWinding f + arrowWinding g := by
  simpa [arrowWinding, comparisonFunctor] using
    (topologicalWinding_comp (comparisonFunctor.map f)
      (comparisonFunctor.map g))

theorem arrowWinding_id (X : CircleObject) :
    arrowWinding (𝟙 X) = 0 := by
  cases X with
  | mk x =>
      cases x
      change topologicalWinding
        (classToAmbient (Presented.PiOne.id : PresentedClass)) = 0
      rw [classToAmbient_id]
      exact windingPath_refl

/-- The cumulative integer attached to a vertex of a composable nerve simplex. -/
noncomputable def simplexHeight {n : ℕ}
    (σ : ComposableArrows CircleObject n) (i : Fin (n + 1)) : ℤ :=
  arrowWinding (σ.map' 0 i.1)

theorem simplexHeight_zero {n : ℕ}
    (σ : ComposableArrows CircleObject n) :
    simplexHeight σ 0 = 0 := by
  simpa [simplexHeight] using arrowWinding_id (σ.obj' 0)

theorem simplexHeight_whisker_add {m n : ℕ}
    (σ : ComposableArrows CircleObject m)
    (Φ : Fin (n + 1) ⥤ Fin (m + 1))
    (i : Fin (n + 1)) :
    simplexHeight (σ.whiskerLeft Φ) i +
        simplexHeight σ (Φ.obj 0) =
      simplexHeight σ (Φ.obj i) := by
  unfold simplexHeight
  have h0i : (Φ.obj 0).1 ≤ (Φ.obj i).1 :=
    Functor.monotone Φ (Fin.zero_le i)
  change
    arrowWinding ((σ.whiskerLeft Φ).map' 0 i.1
      (by omega) (by omega)) +
        arrowWinding (σ.map' 0 (Φ.obj 0).1
          (by omega) (by omega)) =
      arrowWinding (σ.map' 0 (Φ.obj i).1
        (by omega) (by omega))
  have hnew :
      (σ.whiskerLeft Φ).map' 0 i.1
          (by omega) (by omega) =
        σ.map' (Φ.obj 0).1 (Φ.obj i).1 h0i
          (by omega) := by
    rfl
  have hcomp := σ.map'_comp 0 (Φ.obj 0).1 (Φ.obj i).1
    (hij := by omega) (hjk := by omega) (hk := by omega)
  rw [hnew, hcomp, arrowWinding_comp]
  exact Int.add_comm _ _

/-- The affine lift of a nerve simplex to the universal cover `ℝ`. -/
noncomputable def affineHeight {n : ℕ}
    (σ : ComposableArrows CircleObject n) :
    C(SimplexCategory.toTopObj ⦋n⦌, ℝ) where
  toFun p := ∑ i : Fin (n + 1), (p i : ℝ) * (simplexHeight σ i : ℝ)
  continuous_toFun := by
    exact continuous_finset_sum _ (fun i _ =>
      (NNReal.continuous_coe.comp
        ((continuous_apply i).comp continuous_subtype_val)).mul
        continuous_const)

/-- The simplex map obtained by projecting the affine winding lift to the circle. -/
noncomputable def circleSimplex {n : ℕ}
    (σ : ComposableArrows CircleObject n) :
    C(SimplexCategory.toTopObj ⦋n⦌, TopologicalCircle) where
  toFun p := circleCover (affineHeight σ p)
  continuous_toFun := continuous_circleCover.comp (affineHeight σ).continuous

theorem affineHeight_whisker {m n : SimplexCategory}
    (σ : ComposableArrows CircleObject n.len)
    (f : m ⟶ n)
    (p : SimplexCategory.toTopObj m) :
    affineHeight
        (σ.whiskerLeft (SimplexCategory.toCat.map f)) p +
        (simplexHeight σ
          ((SimplexCategory.toCat.map f).obj (0 : Fin (m.len + 1))) : ℝ) =
      affineHeight σ (SimplexCategory.toTopMap f p) := by
  classical
  let Φ : Fin (m.len + 1) ⥤ Fin (n.len + 1) :=
    SimplexCategory.toCat.map f
  have hp : ∑ i : Fin (m.len + 1), (p i : ℝ) = 1 := by
    have hcoe :
        ((∑ i : Fin (m.len + 1), p i : NNReal) : ℝ) =
          ∑ i : Fin (m.len + 1), (p i : ℝ) := by
      exact NNReal.coe_sum (Finset.univ : Finset (Fin (m.len + 1)))
        (fun i : Fin (m.len + 1) => p i)
    calc
      _ = ((∑ i : Fin (m.len + 1), p i : NNReal) : ℝ) := hcoe.symm
      _ = (1 : NNReal) := _root_.congrArg (fun x : NNReal => (x : ℝ)) p.2
      _ = 1 := rfl
  have hheight (i : Fin (m.len + 1)) :
      (simplexHeight (σ.whiskerLeft Φ) i : ℝ) +
          (simplexHeight σ (Φ.obj 0) : ℝ) =
        (simplexHeight σ (Φ.obj i) : ℝ) := by
    exact_mod_cast simplexHeight_whisker_add σ Φ i
  change
    (∑ i : Fin (m.len + 1), (p i : ℝ) *
        (simplexHeight (σ.whiskerLeft Φ) i : ℝ)) +
        (simplexHeight σ (Φ.obj 0) : ℝ) =
      ∑ j : Fin (n.len + 1),
        ((SimplexCategory.toTopMap f p j : ℝ) *
          (simplexHeight σ j : ℝ))
  have hleft :
      (∑ i : Fin (m.len + 1), (p i : ℝ) *
        (simplexHeight (σ.whiskerLeft Φ) i : ℝ)) +
        (simplexHeight σ (Φ.obj 0) : ℝ) =
      ∑ i : Fin (m.len + 1), (p i : ℝ) *
        (simplexHeight σ (Φ.obj i) : ℝ) := by
    calc
      _ = ∑ i : Fin (m.len + 1),
          ((p i : ℝ) *
            (simplexHeight (σ.whiskerLeft Φ) i : ℝ) +
            (p i : ℝ) * (simplexHeight σ (Φ.obj 0) : ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp]
          ring
      _ = ∑ i : Fin (m.len + 1), (p i : ℝ) *
          ((simplexHeight (σ.whiskerLeft Φ) i : ℝ) +
            (simplexHeight σ (Φ.obj 0) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
      _ = ∑ i : Fin (m.len + 1), (p i : ℝ) *
          (simplexHeight σ (Φ.obj i) : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hheight]
  rw [hleft]
  simp only [SimplexCategory.coe_toTopMap]
  simp_rw [NNReal.coe_sum]
  simp_rw [Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp [eq_comm]
  apply Finset.sum_congr rfl
  intro x hx
  congr 2

theorem circleSimplex_naturality {m n : SimplexCategory}
    (σ : ComposableArrows CircleObject n.len)
    (f : m ⟶ n) :
    circleSimplex (σ.whiskerLeft (SimplexCategory.toCat.map f)) =
      (circleSimplex σ).comp
        { toFun := SimplexCategory.toTopMap f
          continuous_toFun := SimplexCategory.continuous_toTopMap f } := by
  ext p
  change
    circleCover
        (affineHeight
          (σ.whiskerLeft (SimplexCategory.toCat.map f)) p) =
      circleCover (affineHeight σ (SimplexCategory.toTopMap f p))
  let Φ : Fin (m.len + 1) ⥤ Fin (n.len + 1) :=
    SimplexCategory.toCat.map f
  have h := affineHeight_whisker σ f p
  have hc := circleCover_add_intCast
    (affineHeight (σ.whiskerLeft Φ) p)
    (simplexHeight σ (Φ.obj 0))
  calc
    circleCover (affineHeight (σ.whiskerLeft Φ) p) =
        circleCover
          (affineHeight (σ.whiskerLeft Φ) p +
            (simplexHeight σ (Φ.obj 0) : ℝ)) := hc.symm
    _ = circleCover (affineHeight σ (SimplexCategory.toTopMap f p)) := by
      exact _root_.congrArg circleCover h

noncomputable def circleSimplexFamily :
    SimplexFamily CircleNerve (TopCat.of TopologicalCircle) where
  app n σ :=
    TopCat.ofHom
      { toFun := fun p => circleSimplex σ p.down
        continuous_toFun :=
          (circleSimplex σ).continuous.comp continuous_uliftDown }
  naturality := by
    intro m n f σ
    apply TopCat.hom_ext
    ext p
    change
      circleSimplex
          (σ.whiskerLeft (SimplexCategory.toCat.map f)) p.down =
        circleSimplex σ
          ((SimplexCategory.toTop.map f).hom p).down
    rw [show ((SimplexCategory.toTop.map f).hom p).down =
        SimplexCategory.toTopMap f p.down by rfl]
    exact _root_.congrArg (fun g => g p.down)
      (circleSimplex_naturality σ f)

/-! ## The two ambient maps -/

/-- The continuous map obtained by descending the compatible affine simplex maps. -/
noncomputable def circleNerveToAmbient :
    C(CircleNerveRealization, TopologicalCircle) :=
  (circleSimplexFamily.desc).hom

theorem circleNerveToAmbient_realizeSimplex
    {n : SimplexCategory} (σ : CircleNerve.obj (op n))
    (p : SimplexCategory.toTop.obj n) :
    circleNerveToAmbient (realizeSimplex σ p) =
      circleSimplex σ p.down := by
  exact circleSimplexFamily.desc_realizeSimplex σ p

/-- The unique vertex of the presented circle groupoid. -/
noncomputable def circleBaseObject : CircleObject :=
  Presented.Realization.Object.ofPoint
    (P := CirclePresented.presentation) circleCompPathBase

/-- The positive generator edge of the presented circle groupoid. -/
noncomputable def circleGenerator : circleBaseObject ⟶ circleBaseObject :=
  Presented.PiOne.ofRaw
    (P := CirclePresented.presentation) (CirclePresented.rawEdge 1)

theorem arrowWinding_circleGenerator : arrowWinding circleGenerator = 1 := by
  change topologicalWinding (comparisonFunctor.map circleGenerator) = 1
  change topologicalWinding
    (classToAmbient
      (Presented.PiOne.ofRaw
        (P := CirclePresented.presentation) (CirclePresented.rawEdge 1))) = 1
  rw [classToAmbient_winding]
  rfl

/-- Clamp a real number to the unit interval. It is used only to extend the
generator edge off the interval; `AddCircle.liftIco` only reads the resulting
map on one closed period. -/
def clampUnit (x : ℝ) : unitInterval :=
  ⟨max 0 (min x 1), by
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_right _ _)
  ⟩

theorem clampUnit_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    clampUnit x = ⟨x, hx⟩ := by
  apply Subtype.ext
  simp [clampUnit, hx.1, hx.2]

theorem continuous_clampUnit : Continuous clampUnit := by
  exact (continuous_const.max (continuous_id.min continuous_const)).subtype_mk
    (fun x => by
      constructor
      · exact le_max_left _ _
      · exact max_le (by norm_num) (min_le_right _ _))

/-- A globally defined continuous representative of the generator edge. -/
noncomputable def generatorLine :
    C(ℝ, CircleNerveRealization) where
  toFun x := nerveEdge circleGenerator (clampUnit x)
  continuous_toFun :=
    (nerveEdge circleGenerator).continuous.comp continuous_clampUnit

theorem generatorLine_zero_one : generatorLine 0 = generatorLine 1 := by
  change nerveEdge circleGenerator (clampUnit 0) =
    nerveEdge circleGenerator (clampUnit 1)
  rw [show clampUnit 0 = (0 : unitInterval) by
      apply Subtype.ext
      simp [clampUnit],
    show clampUnit 1 = (1 : unitInterval) by
      apply Subtype.ext
      simp [clampUnit]]
  exact (nerveEdge circleGenerator).source.trans
    (nerveEdge circleGenerator).target.symm

/-- The reverse map is the periodic quotient of the generator edge. -/
noncomputable def circleAmbientToNerve :
    C(TopologicalCircle, CircleNerveRealization) where
  toFun := AddCircle.liftIco 1 0 generatorLine
  continuous_toFun := AddCircle.liftIco_zero_continuous
    generatorLine_zero_one generatorLine.continuous.continuousOn

theorem circleAmbientToNerve_coe {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    circleAmbientToNerve (x : TopologicalCircle) = generatorLine x := by
  change AddCircle.liftIco 1 0 generatorLine (x : TopologicalCircle) =
    generatorLine x
  exact AddCircle.liftIco_zero_coe_apply hx

/-! ## Pointwise realization paths -/

/-- The generator edge extended periodically along the universal cover. -/
noncomputable def periodicGenerator :
    C(ℝ, CircleNerveRealization) :=
  circleAmbientToNerve.comp
    { toFun := circleCover
      continuous_toFun := continuous_circleCover }

theorem periodicGenerator_apply (a : ℝ) :
    periodicGenerator a = circleAmbientToNerve (circleCover a) :=
  rfl

theorem periodicGenerator_zero :
    periodicGenerator 0 = nerveVertex circleBaseObject := by
  change circleAmbientToNerve (circleCover 0) = nerveVertex circleBaseObject
  rw [show circleCover 0 = (0 : TopologicalCircle) by
    simp [circleCover]]
  change circleAmbientToNerve ((0 : ℝ) : TopologicalCircle) =
    nerveVertex circleBaseObject
  rw [circleAmbientToNerve_coe (x := 0) (by constructor <;> norm_num)]
  change nerveEdge circleGenerator (clampUnit 0) =
    nerveVertex circleBaseObject
  rw [show clampUnit 0 = (0 : unitInterval) by
    apply Subtype.ext
    simp [clampUnit]]
  exact (nerveEdge circleGenerator).source

/-- A continuous path from a periodically parametrized generator point to the
base vertex.  This is a path certificate for one chosen lift in `ℝ`; it is
not yet a globally compatible homotopy on the realization. -/
noncomputable def periodicGeneratorPathToBase (a : ℝ) :
    _root_.Path (periodicGenerator a) (periodicGenerator 0) where
  toFun t := periodicGenerator ((1 - (t : ℝ)) * a)
  continuous_toFun := periodicGenerator.continuous.comp
    ((continuous_const.sub continuous_subtype_val).mul continuous_const)
  source' := by simp
  target' := by simp

theorem circleObject_eq_base (X : CircleObject) :
    X = circleBaseObject := by
  cases X with
  | mk x =>
      cases x
      rfl

/-- The simplexwise path from the common vertex to a point represented in a
nerve simplex. -/
noncomputable def circleSimplexVertexPath
    {n : SimplexCategory} (σ : CircleNerve.obj (op n))
    (p : SimplexCategory.toTop.obj n)
    (x : CircleNerveRealization)
    (hp : realizeSimplex σ p = x) :
    _root_.Path (nerveVertex circleBaseObject)
      x := by
  let q := (pathToSimplexZeroVertex p).map
    (realizeSimplex σ).continuous
  have hvertex : realizeSimplex σ (simplexZeroVertex n) =
      nerveVertex circleBaseObject := by
    rw [realize_nerve_simplex_zero_vertex σ]
    exact _root_.congrArg nerveVertex (circleObject_eq_base (σ.obj 0))
  exact q.symm.cast hvertex.symm hp.symm

/-- Every point of the nerve realization admits a (chosen) path from the
roundtrip image `circleAmbientToNerve ∘ circleNerveToAmbient` to that point.
The choice is made through a simplex representative, so this theorem is a
pointwise path certificate and deliberately does not assert continuity in the
base point. -/
noncomputable def circleRoundtripPath (x : CircleNerveRealization) :
    _root_.Path
      (circleAmbientToNerve (circleNerveToAmbient x)) x := by
  let rep := realizationPointRepresentation CircleNerve x
  let r := affineHeight rep.simplex rep.point.down
  have hambient : circleNerveToAmbient x = circleCover r := by
    rw [← rep.realize_eq]
    exact circleNerveToAmbient_realizeSimplex rep.simplex rep.point
  have hround :
      circleAmbientToNerve (circleNerveToAmbient x) = periodicGenerator r := by
    rw [hambient, periodicGenerator_apply]
  have hvertex : periodicGenerator 0 = nerveVertex circleBaseObject :=
    periodicGenerator_zero
  let first := (periodicGeneratorPathToBase r).cast
    hround hvertex.symm
  let second := circleSimplexVertexPath rep.simplex rep.point x rep.realize_eq
  exact first.trans second

noncomputable def edgeParameter0 (t : unitInterval) :
    SimplexCategory.toTop.{0}.obj ⦋1⦌ :=
  edgeParameter t

theorem affineHeight_circleGenerator_edge (t : unitInterval) :
    affineHeight (ComposableArrows.mk₁ circleGenerator)
        (edgeParameter0 t).down = (t : ℝ) := by
  classical
  let p : SimplexCategory.toTopObj ⦋1⦌ := (edgeParameter0 t).down
  change affineHeight (ComposableArrows.mk₁ circleGenerator) p = (t : ℝ)
  have h0 : ((p.1 0 : ℝ)) =
      1 - (t : ℝ) := by
    change
      ((SimplexCategory.toTopObjOneHomeo.symm
          (unitInterval.symm t)) 0 : ℝ) = 1 - (t : ℝ)
    simp [SimplexCategory.toTopObjOneHomeo, unitInterval.symm]
  have h1 : ((p.1 1 : ℝ)) =
      (t : ℝ) := by
    change
      ((SimplexCategory.toTopObjOneHomeo.symm
          (unitInterval.symm t)) 1 : ℝ) = (t : ℝ)
    simp [SimplexCategory.toTopObjOneHomeo, unitInterval.symm]
  change
    (∑ x : Fin 2,
      (p.1 x : ℝ) *
        (simplexHeight (ComposableArrows.mk₁ circleGenerator) x : ℝ)) =
      (t : ℝ)
  rw [Fin.sum_univ_two, h0, h1]
  simp [simplexHeight, arrowWinding_circleGenerator, arrowWinding_id]

theorem circleNerveToAmbient_nerveEdge (t : unitInterval) :
    circleNerveToAmbient (nerveEdge circleGenerator t) =
      circleCover (t : ℝ) := by
  change
    circleNerveToAmbient
        (realizeSimplex (ComposableArrows.mk₁ circleGenerator)
          (edgeParameter0 t)) = circleCover (t : ℝ)
  calc
    _ = circleSimplex (ComposableArrows.mk₁ circleGenerator)
          (edgeParameter0 t).down :=
      circleNerveToAmbient_realizeSimplex
        (n := ⦋1⦌)
        (show CircleNerve.obj (op ⦋1⦌) from
          ComposableArrows.mk₁ circleGenerator) (edgeParameter0 t)
    _ = circleCover (t : ℝ) := by
      change
        circleCover
            (affineHeight (ComposableArrows.mk₁ circleGenerator)
              (edgeParameter0 t).down) = circleCover (t : ℝ)
      rw [affineHeight_circleGenerator_edge]

theorem circleNerveToAmbient_comp_circleAmbientToNerve :
    circleNerveToAmbient.comp circleAmbientToNerve =
      ContinuousMap.id TopologicalCircle := by
  ext q
  obtain ⟨x, hx, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) q
  have hclamp : clampUnit x =
      ⟨x, ⟨hx.1, hx.2.le⟩⟩ :=
    clampUnit_of_mem_Icc ⟨hx.1, hx.2.le⟩
  change circleNerveToAmbient
      (circleAmbientToNerve (x : TopologicalCircle)) = circleCover x
  rw [circleAmbientToNerve_coe hx]
  change circleNerveToAmbient (nerveEdge circleGenerator (clampUnit x)) =
    circleCover x
  rw [hclamp]
  exact circleNerveToAmbient_nerveEdge ⟨x, hx.1, hx.2.le⟩

theorem circleNerveToAmbient_right_homotopy :
    (circleNerveToAmbient.comp circleAmbientToNerve).Homotopic
      (ContinuousMap.id TopologicalCircle) := by
  rw [circleNerveToAmbient_comp_circleAmbientToNerve]

/-- The exact classifying-space obligation left by the explicit maps. -/
def CircleAmbientClassifyingSpaceStep : Prop :=
  (circleAmbientToNerve.comp circleNerveToAmbient).Homotopic
    (ContinuousMap.id CircleNerveRealization)

/-- Once the realization-side homotopy is supplied, the explicit maps above
package the literal ambient homotopy equivalence. The separate argument is
intentional: the circle-side inverse is proved here, while the realization
side homotopy is the classifying-space step. -/
noncomputable def circleAmbientHomotopyEquiv_of_left_homotopy
    (hleft : CircleAmbientClassifyingSpaceStep) :
    CircleNerveRealization ≃ₕ TopologicalCircle where
  toFun := circleNerveToAmbient
  invFun := circleAmbientToNerve
  left_inv := hleft
  right_inv := circleNerveToAmbient_right_homotopy

/-! ## Computational-path certificate -/

/-- The winding computation for the chosen generator is also recorded as an
explicit computational path.  This is separate from the topological
homotopy-equivalence data above: the former is a rewrite trace, while the
latter is a statement about continuous maps of ambient spaces. -/
noncomputable def circleGeneratorWindingPath :
    ComputationalPaths.Path (arrowWinding circleGenerator) 1 :=
  ComputationalPaths.Path.stepChain arrowWinding_circleGenerator

/-- The winding certificate is stable under a trailing reflexive rewrite. -/
noncomputable def circleGeneratorWindingCoherence :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans circleGeneratorWindingPath
        (ComputationalPaths.Path.refl 1))
      circleGeneratorWindingPath :=
  ComputationalPaths.Path.rweq_cmpA_refl_right circleGeneratorWindingPath

end CircleNerveAmbient
end CompPath
end Path
end ComputationalPaths
