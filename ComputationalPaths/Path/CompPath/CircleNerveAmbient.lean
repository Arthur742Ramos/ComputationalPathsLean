import ComputationalPaths.Path.CompPath.CircleAmbientRealization
import ComputationalPaths.Path.Homotopy.TopologicalNerve
import ComputationalPaths.Path.Homotopy.TopologicalRealizationOpen
import Mathlib.Data.NNReal.Basic
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Topology.Homotopy.Equiv

open CategoryTheory Simplicial Opposite
open CategoryTheory.Limits
open scoped ContinuousMap Topology

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

open CirclePresented CircleTopologicalRealization CircleAmbientRealization Presented TopologicalNerve

noncomputable def circleBridge {n : ℕ} (σ : ComposableArrows CircleObject n) :
    circleBaseObject ⟶ σ.left :=
  eqToHom (circleObject_eq_base σ.left).symm

noncomputable def joinedSimplex {n : ℕ} (σ : ComposableArrows CircleObject n) :
    ComposableArrows CircleObject (n + 2) := by
  simpa [Nat.add_assoc] using
    ((σ.precomp (circleBridge σ)).precomp circleGenerator)

def backJoinMap (n : ℕ) : SimplexCategory.Hom ⦋n⦌ ⦋n + 2⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨i.1 + 2, by
          have hi : i.1 < n + 1 := by simpa using i.isLt
          simpa using (show i.1 + 2 < n + 3 by omega)⟩
      monotone' := by
        intro i j hij
        exact Fin.mk_le_mk.mpr (Nat.add_le_add_right hij 2) }

def frontJoinMap (n : ℕ) : SimplexCategory.Hom ⦋1⦌ ⦋n + 2⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨i.1, by
          have hi : i.1 < 2 := by simpa using i.isLt
          simpa using (show i.1 < n + 3 by omega)⟩
      monotone' := by
        intro i j hij
        exact Fin.mk_le_mk.mpr hij }

theorem backJoinMap_obj (n : ℕ) (i : Fin (n + 1)) :
    (SimplexCategory.toCat.map (backJoinMap n)).obj i =
      (⟨i.1 + 2, by
        have hi : i.1 < n + 1 := i.isLt
        simpa using (show i.1 + 2 < n + 3 by omega)⟩ : Fin (n + 3)) := by
  rfl

theorem frontJoinMap_obj (n : ℕ) (i : Fin 2) :
    (SimplexCategory.toCat.map (frontJoinMap n)).obj i =
      (⟨i.1, by
        have hi : i.1 < 2 := i.isLt
        simpa using (show i.1 < n + 3 by omega)⟩ : Fin (n + 3)) := by
  rfl

theorem backJoinMap_apply (n : ℕ) (i : Fin (n + 1)) :
    (ConcreteCategory.hom (C := SimplexCategory) (backJoinMap n)) i =
      (⟨i.1 + 2, by
        have hi : i.1 < n + 1 := i.isLt
        simpa using (show i.1 + 2 < n + 3 by omega)⟩ : Fin (n + 3)) := by
  rfl

theorem frontJoinMap_apply (n : ℕ) (i : Fin 2) :
    (ConcreteCategory.hom (C := SimplexCategory) (frontJoinMap n)) i =
      (⟨i.1, by
        have hi : i.1 < 2 := i.isLt
        simpa using (show i.1 < n + 3 by omega)⟩ : Fin (n + 3)) := by
  rfl

theorem joinedSimplex_back_map {n : ℕ} (σ : ComposableArrows CircleObject n) :
    (CircleNerve.map (Opposite.op (backJoinMap n))) (joinedSimplex σ) = σ := by
  refine ComposableArrows.ext (h := ?_) (w := ?_)
  · intro i
    rfl
  · intro i hi
    dsimp [CircleNerve, joinedSimplex]
    have hi' : i < n := by simpa using hi
    have hobji := backJoinMap_obj n (⟨i, Nat.lt_succ_of_lt hi'⟩ : Fin (n + 1))
    have hobjj := backJoinMap_obj n (⟨i + 1, by omega⟩ : Fin (n + 1))
    dsimp at hobji hobjj
    change ComposableArrows.Precomp.map
        (σ.precomp (circleBridge σ)) circleGenerator
        (⟨i + 2, by omega⟩ : Fin (n + 3))
        (⟨i + 3, by omega⟩ : Fin (n + 3)) _ = _
    simp [circleBridge, backJoinMap,
      SimplexCategory.toCat, ComposableArrows.Precomp.map]

theorem joinedSimplex_front_map {n : ℕ} (σ : ComposableArrows CircleObject n) :
    (CircleNerve.map (Opposite.op (frontJoinMap n))) (joinedSimplex σ) =
      ComposableArrows.mk₁ circleGenerator := by
  refine ComposableArrows.ext (h := ?_) (w := ?_)
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have hi' : i < 1 := by simpa only [SimplexCategory.len_mk] using hi
    have hi0 : i = 0 := by omega
    subst i
    dsimp [CircleNerve, joinedSimplex]
    change ComposableArrows.Precomp.map
        (σ.precomp (circleBridge σ)) circleGenerator
        (0 : Fin (n + 3)) (1 : Fin (n + 3)) _ = _
    simp [joinedSimplex, circleBridge, frontJoinMap, frontJoinMap_obj,
      SimplexCategory.toCat]
    rfl

noncomputable def joinTopPoint {n : ℕ}
    (t : unitInterval)
    (p : SimplexCategory.toTopObj ⦋n⦌)
    (q : SimplexCategory.toTopObj ⦋1⦌) :
    SimplexCategory.toTopObj ⦋n + 2⦌ :=
  ⟨fun i : Fin (n + 3) =>
      (Fin.cases
        (unitInterval.toNNReal t * q 0)
        (fun j =>
          Fin.cases
            (unitInterval.toNNReal t * q 1)
            (fun k => unitInterval.toNNReal (unitInterval.symm t) * p k)
            j)
        i : NNReal),
    by
      change ∑ i : Fin (n + 3),
          (Fin.cases
            (unitInterval.toNNReal t * q 0)
            (fun j =>
              Fin.cases
                (unitInterval.toNNReal t * q 1)
                (fun k => unitInterval.toNNReal (unitInterval.symm t) * p k)
                j)
            i : NNReal) = 1
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ]
      rw [← Finset.mul_sum]
      have hp : ∑ i : Fin (n + 1), p i = 1 := p.2
      have hq : q 0 + q 1 = 1 :=
        SimplexCategory.toTopObj_one_add_eq_one q
      have ht : unitInterval.toNNReal t +
          unitInterval.toNNReal (unitInterval.symm t) = 1 := by
        apply NNReal.eq
        simp [unitInterval.toNNReal, unitInterval.symm]
      rw [hp]
      calc
        unitInterval.toNNReal t * q 0 +
              (unitInterval.toNNReal t * q 1 +
                unitInterval.toNNReal (unitInterval.symm t) * 1) =
            unitInterval.toNNReal t * (q 0 + q 1) +
              unitInterval.toNNReal (unitInterval.symm t) := by
                simp [mul_add, add_assoc]
        _ = unitInterval.toNNReal t +
              unitInterval.toNNReal (unitInterval.symm t) := by rw [hq]; simp
        _ = 1 := ht
  ⟩

noncomputable def joinParameter {n : ℕ}
    (t : unitInterval)
    (p : SimplexCategory.toTop.{0}.obj ⦋n⦌)
    (q : SimplexCategory.toTop.{0}.obj ⦋1⦌) :
    SimplexCategory.toTop.{0}.obj ⦋n + 2⦌ :=
  ULift.up (joinTopPoint t p.down q.down)

theorem continuous_joinParameter {n : ℕ} :
    Continuous (fun tp : unitInterval ×
        SimplexCategory.toTop.{0}.obj ⦋n⦌ ×
        SimplexCategory.toTop.{0}.obj ⦋1⦌ =>
      joinParameter tp.1 tp.2.1 tp.2.2) := by
  unfold joinParameter
  apply continuous_uliftUp.comp
  unfold joinTopPoint
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cases_zero]
    change Continuous (fun a : unitInterval ×
        SimplexCategory.toTop.{0}.obj ⦋n⦌ ×
        SimplexCategory.toTop.{0}.obj ⦋1⦌ =>
      unitInterval.toNNReal a.1 *
        ((a.2.2.down : SimplexCategory.toTopObj ⦋1⦌).1 0))
    exact
      (unitInterval.toNNReal_continuous.comp continuous_fst).mul
        ((continuous_apply 0).comp
          (continuous_subtype_val.comp
            (continuous_uliftDown.comp
              (continuous_snd.comp continuous_snd))))
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp only [Fin.cases_zero]
      change Continuous (fun a : unitInterval ×
          SimplexCategory.toTop.{0}.obj ⦋n⦌ ×
          SimplexCategory.toTop.{0}.obj ⦋1⦌ =>
        unitInterval.toNNReal a.1 *
          ((a.2.2.down : SimplexCategory.toTopObj ⦋1⦌).1 1))
      exact
        (unitInterval.toNNReal_continuous.comp continuous_fst).mul
          ((continuous_apply 1).comp
            (continuous_subtype_val.comp
              (continuous_uliftDown.comp
                (continuous_snd.comp continuous_snd))))
    · simp only [Fin.cases_succ]
      change Continuous (fun a : unitInterval ×
          SimplexCategory.toTop.{0}.obj ⦋n⦌ ×
          SimplexCategory.toTop.{0}.obj ⦋1⦌ =>
        unitInterval.toNNReal (unitInterval.symm a.1) *
          ((a.2.1.down : SimplexCategory.toTopObj ⦋n⦌).1 k))
      exact
        (unitInterval.toNNReal_continuous.comp
            (unitInterval.continuous_symm.comp continuous_fst)).mul
          ((continuous_apply k).comp
            (continuous_subtype_val.comp
              (continuous_uliftDown.comp
                (continuous_fst.comp continuous_snd))))

theorem joinParameter_zero {n : ℕ}
    (p : SimplexCategory.toTop.{0}.obj ⦋n⦌)
    (q : SimplexCategory.toTop.{0}.obj ⦋1⦌) :
    joinParameter (0 : unitInterval) p q =
      SimplexCategory.toTop.map (backJoinMap n) p := by
  apply ULift.ext
  change joinTopPoint (0 : unitInterval) p.down q.down =
    SimplexCategory.toTopMap (backJoinMap n) p.down
  apply SimplexCategory.toTopObj.ext
  funext i
  rw [SimplexCategory.coe_toTopMap]
  rcases i with ⟨_ | j, hi⟩
  · simp [joinTopPoint, unitInterval.toNNReal, unitInterval.symm]
    change 0 =
      ∑ k ∈ Finset.univ.filter
        (fun k : Fin (n + 1) =>
          (backJoinMap n).toOrderHom k = (0 : Fin (n + 3))),
        p.down.1 k
    simp [backJoinMap]
  · cases j with
    | zero =>
      simp [joinTopPoint, unitInterval.toNNReal, unitInterval.symm]
      change 0 =
        ∑ k ∈ Finset.univ.filter
          (fun k : Fin (n + 1) =>
            (backJoinMap n).toOrderHom k = (1 : Fin (n + 3))),
          p.down.1 k
      simp [backJoinMap]
    | succ k =>
      simp [joinTopPoint, unitInterval.toNNReal, unitInterval.symm]
      have hk : k < n + 1 := by
        have hk' : k + 2 < n + 3 := by
          simpa only [SimplexCategory.len_mk] using hi
        omega
      let kt : Fin (n + 1) := ⟨k, hk⟩
      have hf : Finset.univ.filter
          (fun j : Fin (n + 1) =>
            (ConcreteCategory.hom (C := SimplexCategory) (backJoinMap n)) j =
              (⟨k + 1 + 1, hi⟩ : Fin (⦋n + 2⦌.len + 1))) = {kt} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        change
          (⟨j.1 + 2, by
            have hj := j.isLt
            simpa only [SimplexCategory.len_mk] using
              (show j.1 + 2 < n + 3 by omega)⟩ :
            Fin (⦋n + 2⦌.len + 1)) =
            (⟨k + 1 + 1, hi⟩ : Fin (⦋n + 2⦌.len + 1)) ↔
              j = kt
        simp [kt, Fin.ext_iff]
      have hsum :
          (∑ j with
            (ConcreteCategory.hom (C := SimplexCategory) (backJoinMap n)) j =
              (⟨k + 1 + 1, hi⟩ : Fin (⦋n + 2⦌.len + 1)),
            p.down.1 j) = p.down.1 kt := by
        apply Finset.sum_eq_single kt
        · intro b hb hne
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
          have hb' : b.1 + 2 = k + 2 := by
            exact _root_.congrArg Fin.val hb
          have hbt : b = kt := by
            apply Fin.ext
            simp [kt] at hb'
            omega
          exact (hne hbt).elim
        · intro hnot
          apply (hnot ?_).elim
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          change
            (⟨kt.1 + 2, by
              have hkt := kt.isLt
              simpa only [SimplexCategory.len_mk] using
                (show kt.1 + 2 < n + 3 by omega)⟩ :
              Fin (⦋n + 2⦌.len + 1)) =
              (⟨k + 1 + 1, hi⟩ : Fin (⦋n + 2⦌.len + 1))
          apply Fin.ext
          simp [kt]
      exact hsum.symm

theorem joinParameter_one {n : ℕ}
    (p : SimplexCategory.toTop.{0}.obj ⦋n⦌)
    (q : SimplexCategory.toTop.{0}.obj ⦋1⦌) :
    joinParameter (1 : unitInterval) p q =
      SimplexCategory.toTop.map (frontJoinMap n) q := by
  apply ULift.ext
  change joinTopPoint (1 : unitInterval) p.down q.down =
    SimplexCategory.toTopMap (frontJoinMap n) q.down
  apply SimplexCategory.toTopObj.ext
  funext i
  rw [SimplexCategory.coe_toTopMap]
  rcases i with ⟨_ | j, hi⟩
  · simp [joinTopPoint, unitInterval.toNNReal, unitInterval.symm]
    change q.down.1 0 =
      ∑ x ∈ Finset.univ.filter
        (fun x : Fin 2 =>
          (frontJoinMap n).toOrderHom x = (0 : Fin (n + 3))),
        q.down.1 x
    simp [frontJoinMap]
    have hf : Finset.univ.filter (fun x : Fin 2 => x = 0) = {0} := by
      ext x
      simp
    rw [hf]
    simp
  · cases j with
    | zero =>
      simp [joinTopPoint, unitInterval.toNNReal, unitInterval.symm]
      change q.down.1 1 =
        ∑ x ∈ Finset.univ.filter
          (fun x : Fin 2 =>
            (frontJoinMap n).toOrderHom x = (1 : Fin (n + 3))),
          q.down.1 x
      simp [frontJoinMap]
      have hf : Finset.univ.filter (fun x : Fin 2 => (x : ℕ) = 1) = {1} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · intro h
          exact Fin.ext h
        · intro h
          simpa [h]
      rw [hf]
      simp
    | succ k =>
      simp [joinTopPoint, unitInterval.toNNReal, unitInterval.symm]
      simp [frontJoinMap]
      symm
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hx' : x.1 = k + 2 := _root_.congrArg Fin.val hx
      have hi' : k + 2 < n + 3 := by
        simpa only [SimplexCategory.len_mk, Nat.add_assoc] using hi
      omega

open CirclePresented CircleTopologicalRealization CircleAmbientRealization Presented TopologicalNerve

noncomputable def circleDecodeArrow (z : ℤ) :
    circleBaseObject ⟶ circleBaseObject :=
  CirclePresented.decode z

theorem arrowWinding_circleDecodeArrow (z : ℤ) :
    arrowWinding (circleDecodeArrow z) = z := by
  simpa [circleDecodeArrow, arrowWinding] using
    (classToAmbient_winding (CirclePresented.decode z))

theorem circleArrow_eq_of_winding {X Y : CircleObject}
    (f g : X ⟶ Y) (h : arrowWinding f = arrowWinding g) : f = g := by
  cases X
  cases Y
  have hf : arrowWinding f = CirclePresented.encode f := by
    simpa [arrowWinding, comparisonFunctor] using
      (classToAmbient_winding f)
  have hg : arrowWinding g = CirclePresented.encode g := by
    simpa [arrowWinding, comparisonFunctor] using
      (classToAmbient_winding g)
  have hencode : CirclePresented.encode f = CirclePresented.encode g :=
    hf.symm.trans (h.trans hg)
  calc
    f = CirclePresented.piOneEquivInt.invFun
        (CirclePresented.piOneEquivInt.toFun f) :=
      (CirclePresented.piOneEquivInt.left_inv f).symm
    _ = CirclePresented.piOneEquivInt.invFun
        (CirclePresented.piOneEquivInt.toFun g) :=
      _root_.congrArg CirclePresented.piOneEquivInt.invFun hencode
    _ = g := CirclePresented.piOneEquivInt.left_inv g

noncomputable def circleBridgeInt {n : ℕ}
    (z : ℤ) (σ : ComposableArrows CircleObject n) :
    circleBaseObject ⟶ σ.left :=
  circleDecodeArrow (-(z + 1)) ≫
    eqToHom (circleObject_eq_base σ.left)

theorem arrowWinding_eqToHom_base {X : CircleObject}
    (h : X = circleBaseObject) :
    arrowWinding (eqToHom h) = 0 := by
  subst X
  exact arrowWinding_id circleBaseObject

theorem arrowWinding_circleBridgeInt {n : ℕ}
    (z : ℤ) (σ : ComposableArrows CircleObject n) :
    arrowWinding (circleBridgeInt z σ) = -(z + 1) := by
  rw [circleBridgeInt, arrowWinding_comp,
    arrowWinding_circleDecodeArrow, arrowWinding_eqToHom_base]
  simp

noncomputable def joinedSimplexAt {n : ℕ} (z : ℤ)
    (σ : ComposableArrows CircleObject n) :
    ComposableArrows CircleObject (n + 2) := by
  simpa [Nat.add_assoc] using
    ((σ.precomp (circleBridgeInt z σ)).precomp circleGenerator)

theorem joinedSimplexAt_back_map {n : ℕ} (z : ℤ)
    (σ : ComposableArrows CircleObject n) :
    (CircleNerve.map (Opposite.op (backJoinMap n)))
        (joinedSimplexAt z σ) = σ := by
  refine ComposableArrows.ext (h := ?_) (w := ?_)
  · intro i
    rfl
  · intro i hi
    dsimp [CircleNerve, joinedSimplexAt]
    have hi' : i < n := by simpa using hi
    have hobji := backJoinMap_obj n (⟨i, Nat.lt_succ_of_lt hi'⟩ : Fin (n + 1))
    have hobjj := backJoinMap_obj n (⟨i + 1, by omega⟩ : Fin (n + 1))
    dsimp at hobji hobjj
    change ComposableArrows.Precomp.map
        (σ.precomp (circleBridgeInt z σ)) circleGenerator
        (⟨i + 2, by omega⟩ : Fin (n + 3))
        (⟨i + 3, by omega⟩ : Fin (n + 3)) _ = _
    simp [circleBridgeInt, circleDecodeArrow, backJoinMap,
      SimplexCategory.toCat, ComposableArrows.Precomp.map]

theorem joinedSimplexAt_front_map {n : ℕ} (z : ℤ)
    (σ : ComposableArrows CircleObject n) :
    (CircleNerve.map (Opposite.op (frontJoinMap n)))
        (joinedSimplexAt z σ) =
      ComposableArrows.mk₁ circleGenerator := by
  refine ComposableArrows.ext (h := ?_) (w := ?_)
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have hi' : i < 1 := by simpa only [SimplexCategory.len_mk] using hi
    have hi0 : i = 0 := by omega
    subst i
    dsimp [CircleNerve, joinedSimplexAt]
    change ComposableArrows.Precomp.map
        (σ.precomp (circleBridgeInt z σ)) circleGenerator
        (0 : Fin (n + 3)) (1 : Fin (n + 3)) _ = _
    simp [joinedSimplexAt, circleBridgeInt, circleDecodeArrow, frontJoinMap,
      frontJoinMap_obj, SimplexCategory.toCat]
    rfl

open CirclePresented CircleTopologicalRealization CircleAmbientRealization Presented TopologicalNerve

def boundaryZeroMap (n : ℕ) : SimplexCategory.Hom ⦋n + 1⦌ ⦋n + 2⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨i.1 + 1, by
          have hi := i.isLt
          change i.1 < n + 2 at hi
          have htarget : i.1 + 1 < n + 3 := by omega
          simpa only [SimplexCategory.len_mk] using htarget⟩
      monotone' := by
        intro i j hij
        exact Fin.mk_le_mk.mpr (Nat.add_le_add_right hij 1) }

def boundaryOneMap (n : ℕ) : SimplexCategory.Hom ⦋n + 1⦌ ⦋n + 2⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => if hi : i.1 = 0 then ⟨0, by
          simpa only [SimplexCategory.len_mk] using (show 0 < n + 3 by omega)⟩ else ⟨i.1 + 1, by
          have hi' := i.isLt
          change i.1 < n + 2 at hi'
          have htarget : i.1 + 1 < n + 3 := by omega
          simpa only [SimplexCategory.len_mk] using htarget⟩
      monotone' := by
        dsimp
        intro i j hij
        by_cases hi : i.1 = 0
        · by_cases hj : j.1 = 0
          · simp [hi, hj]
          · simp [hi, hj]
        · by_cases hj : j.1 = 0
          · exfalso
            apply hi
            omega
          · simp [hi, hj]
            omega }

theorem boundaryZeroMap_obj (n : ℕ) (i : Fin (n + 2)) :
    (SimplexCategory.toCat.map (boundaryZeroMap n)).obj i =
      (⟨i.1 + 1, by
        have hi := i.isLt
        change i.1 < n + 2 at hi
        have htarget : i.1 + 1 < n + 3 := by omega
        simpa only [SimplexCategory.len_mk] using htarget⟩ : Fin (n + 3)) := by
  rfl

theorem boundaryOneMap_obj (n : ℕ) (i : Fin (n + 2)) :
    (SimplexCategory.toCat.map (boundaryOneMap n)).obj i =
      (if hi : i.1 = 0 then
        (⟨0, by omega⟩ : Fin (n + 3)) else
        ⟨i.1 + 1, by omega⟩) := by
  by_cases hi : i.1 = 0
  · have hi' : i = 0 := Fin.ext hi
    subst i
    rfl
  · rfl

theorem boundaryZeroMap_eq_delta (n : ℕ) :
    boundaryZeroMap n = SimplexCategory.δ (0 : Fin (n + 3)) := by
  apply SimplexCategory.Hom.ext
  rfl

theorem boundaryOneMap_eq_delta (n : ℕ) :
    boundaryOneMap n = SimplexCategory.δ (1 : Fin (n + 3)) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  dsimp [boundaryOneMap, SimplexCategory.δ]
  split_ifs with hi
  · have hi' : i = 0 := Fin.ext hi
    simp [Fin.succAbove, hi, hi']
  · have hi' : i ≠ 0 := by
      intro h
      apply hi
      exact _root_.congrArg Fin.val h
    simp [Fin.succAbove, hi, hi']
    apply Fin.ext
    rfl

theorem joinedSimplex_boundary {n : ℕ} (z : ℤ)
    (σ : ComposableArrows CircleObject n) :
    CircleNerve.map (Opposite.op (boundaryZeroMap n)) (joinedSimplexAt z σ) =
      CircleNerve.map (Opposite.op (boundaryOneMap n))
        (joinedSimplexAt (z + 1) σ) := by
  refine ComposableArrows.ext (h := ?_) (w := ?_)
  · intro i
    rcases i with ⟨_ | i, hi⟩
    · rfl
    · rfl
  · intro i hi
    rcases i with ⟨j | k, hi⟩
    · dsimp [CircleNerve, joinedSimplexAt]
      have hz0 := boundaryZeroMap_obj n (0 : Fin (n + 2))
      have hz1 := boundaryZeroMap_obj n (1 : Fin (n + 2))
      have ho0 := boundaryOneMap_obj n (0 : Fin (n + 2))
      have ho1 := boundaryOneMap_obj n (1 : Fin (n + 2))
      dsimp at hz0 hz1 ho0 ho1
      change
        ComposableArrows.Precomp.map
            (σ.precomp (circleBridgeInt z σ)) circleGenerator
            (⟨1, by omega⟩ : Fin (n + 3))
            (⟨2, by omega⟩ : Fin (n + 3)) _ =
          𝟙 _ ≫
            ComposableArrows.Precomp.map
              (σ.precomp (circleBridgeInt (z + 1) σ)) circleGenerator
              (0 : Fin (n + 3))
              (⟨2, by omega⟩ : Fin (n + 3)) _ ≫ 𝟙 _
      simp only [ComposableArrows.Precomp.map_succ_succ,
        ComposableArrows.Precomp.map_zero_succ_succ,
        Category.id_comp, Category.comp_id]
      change circleBridgeInt z σ =
        circleGenerator ≫ circleBridgeInt (z + 1) σ
      apply circleArrow_eq_of_winding
      rw [arrowWinding_circleBridgeInt, arrowWinding_comp,
        arrowWinding_circleGenerator, arrowWinding_circleBridgeInt]
      ring
    · rename_i k
      have hi' : k < n := by
        have hi'' : k + 1 < n + 1 := by
          simpa only [SimplexCategory.len_mk] using hi
        omega
      have hz0 := boundaryZeroMap_obj n (⟨k + 1, by omega⟩ : Fin (n + 2))
      have hz1 := boundaryZeroMap_obj n (⟨k + 2, by omega⟩ : Fin (n + 2))
      have ho0 := boundaryOneMap_obj n (⟨k + 1, by omega⟩ : Fin (n + 2))
      have ho1 := boundaryOneMap_obj n (⟨k + 2, by omega⟩ : Fin (n + 2))
      dsimp at hz0 hz1 ho0 ho1
      dsimp [CircleNerve, joinedSimplexAt]
      change
        ComposableArrows.Precomp.map
            (σ.precomp (circleBridgeInt z σ)) circleGenerator
            (⟨k + 2, by omega⟩ : Fin (n + 3))
            (⟨k + 3, by omega⟩ : Fin (n + 3)) _ =
          eqToHom (by rfl) ≫
            ComposableArrows.Precomp.map
              (σ.precomp (circleBridgeInt (z + 1) σ)) circleGenerator
              (⟨k + 2, by omega⟩ : Fin (n + 3))
              (⟨k + 3, by omega⟩ : Fin (n + 3)) _ ≫ eqToHom (by rfl)
      simp [circleBridgeInt, circleDecodeArrow, boundaryZeroMap,
        boundaryOneMap, boundaryZeroMap_obj, boundaryOneMap_obj,
        SimplexCategory.toCat,
      ComposableArrows.Precomp.map]

open CirclePresented CircleTopologicalRealization CircleAmbientRealization Presented TopologicalNerve

noncomputable def circleLocalJoin {n : ℕ} (z : ℤ)
    (σ : ComposableArrows CircleObject n) :
    C(unitInterval × SimplexCategory.toTop.{0}.obj ⦋n⦌,
      CircleNerveRealization) where
  toFun := fun hp =>
    realizeSimplex (X := CircleNerve) (n := ⦋n + 2⦌)
      (joinedSimplexAt z σ)
      (joinParameter (unitInterval.symm hp.1) hp.2
        (edgeParameter0
          (clampUnit (affineHeight σ hp.2.down - (z : ℝ)))))
  continuous_toFun := by
    have hinput : Continuous (fun hp : unitInterval ×
        SimplexCategory.toTop.{0}.obj ⦋n⦌ =>
      (unitInterval.symm hp.1, hp.2,
        edgeParameter0
          (clampUnit (affineHeight σ hp.2.down - (z : ℝ))))) := by
      apply (unitInterval.continuous_symm.comp continuous_fst).prodMk
      apply continuous_snd.prodMk
      have hdown : Continuous (fun hp : unitInterval ×
          SimplexCategory.toTop.{0}.obj ⦋n⦌ => hp.2.down) :=
        continuous_uliftDown.comp continuous_snd
      have hheight : Continuous (fun hp : unitInterval ×
          SimplexCategory.toTop.{0}.obj ⦋n⦌ =>
        affineHeight σ hp.2.down - (z : ℝ)) := by
        have hconst : Continuous (fun _ : unitInterval ×
            SimplexCategory.toTop.{0}.obj ⦋n⦌ => (z : ℝ)) :=
          continuous_const
        exact
          ((affineHeight σ).continuous.comp hdown).sub hconst
      exact continuous_edgeParameter.comp
        (continuous_clampUnit.comp hheight)
    have hj : Continuous (fun hp : unitInterval ×
        SimplexCategory.toTop.{0}.obj ⦋n⦌ =>
      joinParameter (unitInterval.symm hp.1) hp.2
        (edgeParameter0
          (clampUnit (affineHeight σ hp.2.down - (z : ℝ))))) := by
      simpa [Function.comp_def] using continuous_joinParameter.comp hinput
    simpa [Function.comp_def] using
      (realizeSimplex (X := CircleNerve) (n := ⦋n + 2⦌)
        (joinedSimplexAt z σ)).continuous.comp hj

theorem circleLocalJoin_zero {n : ℕ} (z : ℤ)
    (σ : ComposableArrows CircleObject n)
    (h : unitInterval × SimplexCategory.toTop.{0}.obj ⦋n⦌) :
    circleLocalJoin z σ (0, h.2) =
      nerveEdge circleGenerator
        (clampUnit (affineHeight σ h.2.down - (z : ℝ))) := by
  change
    realizeSimplex (X := CircleNerve) (n := ⦋n + 2⦌)
      (joinedSimplexAt z σ)
        (joinParameter (unitInterval.symm (0 : unitInterval)) h.2
          (edgeParameter0
            (clampUnit (affineHeight σ h.2.down - (z : ℝ))))) = _
  rw [show unitInterval.symm (0 : unitInterval) = (1 : unitInterval) by
    apply Subtype.ext
    simp [unitInterval.symm]]
  rw [joinParameter_one]
  have hfront :
      CircleNerve.map (Quiver.Hom.op (frontJoinMap n))
          (joinedSimplexAt z σ) =
        ComposableArrows.mk₁ circleGenerator := by
    exact joinedSimplexAt_front_map z σ
  have hn := _root_.congrArg
      (fun k : SimplexCategory.toTop.{0}.obj ⦋1⦌ ⟶ CircleNerveRealization =>
        k (edgeParameter0
          (clampUnit (affineHeight σ h.2.down - (z : ℝ)))))
      (realizeSimplexHom_naturality
        (X := CircleNerve) (frontJoinMap n) (joinedSimplexAt z σ))
  rw [hfront] at hn
  simpa [nerveEdge, edgeParameter0] using hn

theorem circleLocalJoin_one {n : ℕ} (z : ℤ)
    (σ : ComposableArrows CircleObject n)
    (h : unitInterval × SimplexCategory.toTop.{0}.obj ⦋n⦌) :
    circleLocalJoin z σ (1, h.2) = realizeSimplex σ h.2 := by
  change
    realizeSimplex (X := CircleNerve) (n := ⦋n + 2⦌)
      (joinedSimplexAt z σ)
        (joinParameter (unitInterval.symm (1 : unitInterval)) h.2
          (edgeParameter0
            (clampUnit (affineHeight σ h.2.down - (z : ℝ))))) = _
  rw [show unitInterval.symm (1 : unitInterval) = (0 : unitInterval) by
    apply Subtype.ext
    simp [unitInterval.symm]]
  rw [joinParameter_zero]
  have hback :
      CircleNerve.map (Quiver.Hom.op (backJoinMap n))
          (joinedSimplexAt z σ) = σ := by
    exact joinedSimplexAt_back_map z σ
  have hn := _root_.congrArg
      (fun k : SimplexCategory.toTop.{0}.obj ⦋n⦌ ⟶ CircleNerveRealization =>
        k h.2)
      (realizeSimplexHom_naturality
        (X := CircleNerve) (backJoinMap n) (joinedSimplexAt z σ))
  rw [hback] at hn
  simpa using hn

noncomputable def boundaryParameter {n : ℕ}
    (t : unitInterval)
    (p : SimplexCategory.toTop.{0}.obj ⦋n⦌) :
    SimplexCategory.toTop.{0}.obj ⦋n + 1⦌ :=
  ULift.up
    ⟨fun i : Fin (n + 2) =>
        Fin.cases
          (unitInterval.toNNReal t)
          (fun j => unitInterval.toNNReal (unitInterval.symm t) * p.down.1 j)
          i,
      by
        change ∑ i : Fin (n + 2),
            (Fin.cases
              (unitInterval.toNNReal t)
              (fun j => unitInterval.toNNReal (unitInterval.symm t) * p.down.1 j)
              i : NNReal) = 1
        rw [Fin.sum_univ_succ]
        simp only [Fin.cases_zero, Fin.cases_succ]
        rw [← Finset.mul_sum]
        have hp : ∑ j : Fin (n + 1), p.down.1 j = 1 := p.down.2
        have ht : unitInterval.toNNReal t +
            unitInterval.toNNReal (unitInterval.symm t) = 1 := by
          apply NNReal.eq
          simp [unitInterval.toNNReal, unitInterval.symm]
        rw [hp]
        calc
          unitInterval.toNNReal t +
                unitInterval.toNNReal (unitInterval.symm t) * 1 =
              unitInterval.toNNReal t +
                unitInterval.toNNReal (unitInterval.symm t) := by simp
          _ = 1 := ht⟩

theorem edgeParameter0_one_coord_zero :
    (edgeParameter0 (1 : unitInterval)).down.1 (0 : Fin 2) = 0 := by
  change (SimplexCategory.toTopObjOneHomeo.symm
      (unitInterval.symm (1 : unitInterval))) 0 = 0
  simp [SimplexCategory.toTopObjOneHomeo, unitInterval.toNNReal,
    unitInterval.symm]

theorem edgeParameter0_one_coord_one :
    (edgeParameter0 (1 : unitInterval)).down.1 (1 : Fin 2) = 1 := by
  change (SimplexCategory.toTopObjOneHomeo.symm
      (unitInterval.symm (1 : unitInterval))) 1 = 1
  simp [SimplexCategory.toTopObjOneHomeo, unitInterval.toNNReal,
    unitInterval.symm]

theorem edgeParameter0_zero_coord_zero :
    (edgeParameter0 (0 : unitInterval)).down.1 (0 : Fin 2) = 1 := by
  change (SimplexCategory.toTopObjOneHomeo.symm
      (unitInterval.symm (0 : unitInterval))) 0 = 1
  simp [SimplexCategory.toTopObjOneHomeo, unitInterval.toNNReal,
    unitInterval.symm]

theorem edgeParameter0_zero_coord_one :
    (edgeParameter0 (0 : unitInterval)).down.1 (1 : Fin 2) = 0 := by
  change (SimplexCategory.toTopObjOneHomeo.symm
      (unitInterval.symm (0 : unitInterval))) 1 = 0
  simp [SimplexCategory.toTopObjOneHomeo, unitInterval.toNNReal,
    unitInterval.symm]

theorem boundaryZeroMap_apply (n : ℕ) (x : Fin (n + 2)) :
    (ConcreteCategory.hom (C := SimplexCategory) (boundaryZeroMap n)) x =
      (⟨x.1 + 1, by
        have hx := x.isLt
        change x.1 < n + 2 at hx
        have htarget : x.1 + 1 < n + 3 := by omega
        simpa only [SimplexCategory.len_mk] using htarget⟩ :
        Fin (⦋n + 2⦌.len + 1)) := by
  rfl

theorem boundaryOneMap_apply (n : ℕ) (x : Fin (n + 2)) :
    (ConcreteCategory.hom (C := SimplexCategory) (boundaryOneMap n)) x =
      (if h : x.1 = 0 then
        (⟨0, by simp only [SimplexCategory.len_mk]; omega⟩ :
          Fin (⦋n + 2⦌.len + 1)) else
        (⟨x.1 + 1, by
          have hx := x.isLt
          change x.1 < n + 2 at hx
          have htarget : x.1 + 1 < n + 3 := by omega
          simpa only [SimplexCategory.len_mk] using htarget⟩ :
          Fin (⦋n + 2⦌.len + 1))) := by
  by_cases hx : x.1 = 0
  · have hx' : x = 0 := Fin.ext hx
    subst x
    rfl
  · rfl

theorem boundaryZeroMap_filter_zero (n : ℕ) :
    Finset.univ.filter
        (fun x : Fin (n + 2) =>
          (ConcreteCategory.hom (C := SimplexCategory) (boundaryZeroMap n)) x =
            (0 : Fin (⦋n + 2⦌.len + 1))) = ∅ := by
  apply Finset.filter_eq_empty_iff.mpr
  intro x _ hx
  have hx' := _root_.congrArg Fin.val hx
  rw [boundaryZeroMap_apply] at hx'
  have hx'' : x.1 + 1 = 0 := by
    simpa only [SimplexCategory.len_mk] using hx'
  omega

theorem boundaryZeroMap_filter_one (n : ℕ) :
    Finset.univ.filter
        (fun x : Fin (n + 2) =>
          (ConcreteCategory.hom (C := SimplexCategory) (boundaryZeroMap n)) x =
            (1 : Fin (⦋n + 2⦌.len + 1))) = {0} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  rw [boundaryZeroMap_apply]
  constructor
  · intro h
    have hval := _root_.congrArg Fin.val h
    have hval' : x.1 + 1 = 1 := by
      simpa only [SimplexCategory.len_mk] using hval
    have hx0 : x.1 = 0 := by omega
    exact Fin.ext hx0
  · intro h
    subst x
    rfl

theorem boundaryOneMap_filter_zero (n : ℕ) :
    Finset.univ.filter
        (fun x : Fin (n + 2) =>
          (ConcreteCategory.hom (C := SimplexCategory) (boundaryOneMap n)) x =
            (0 : Fin (⦋n + 2⦌.len + 1))) = {0} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  rw [boundaryOneMap_apply]
  constructor
  · intro h
    by_cases hx : x.1 = 0
    · exact Fin.ext hx
    · simp [hx] at h
  · intro h
    subst x
    simp

theorem boundaryOneMap_filter_one (n : ℕ) :
    Finset.univ.filter
        (fun x : Fin (n + 2) =>
          (ConcreteCategory.hom (C := SimplexCategory) (boundaryOneMap n)) x =
            (1 : Fin (⦋n + 2⦌.len + 1))) = ∅ := by
  apply Finset.filter_eq_empty_iff.mpr
  intro x _ hx
  have hx' := _root_.congrArg Fin.val hx
  rw [boundaryOneMap_apply] at hx'
  by_cases hzero : x.1 = 0
  · simp [hzero] at hx'
  · have hx'' : x.1 + 1 = 1 := by
      simpa only [hzero, if_neg, SimplexCategory.len_mk] using hx'
    omega

theorem boundaryZeroMap_filter_succ (n k : ℕ)
    (hk : k + 1 + 1 < ⦋n + 2⦌.len + 1) :
    Finset.univ.filter
        (fun x : Fin (n + 2) =>
          (ConcreteCategory.hom (C := SimplexCategory) (boundaryZeroMap n)) x =
            (⟨k + 1 + 1, hk⟩ : Fin (⦋n + 2⦌.len + 1))) =
      {(⟨k + 1, by
          have hk' : k + 1 + 1 < n + 3 := by
            simpa only [SimplexCategory.len_mk] using hk
          omega⟩ : Fin (n + 2))} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  rw [boundaryZeroMap_apply]
  constructor
  · intro h
    have hval := _root_.congrArg Fin.val h
    have hval' : x.1 + 1 = k + 1 + 1 := by
      simpa only [SimplexCategory.len_mk] using hval
    have hxval : x.1 = k + 1 := by omega
    exact Fin.ext hxval
  · intro h
    subst x
    rfl

theorem boundaryOneMap_filter_succ (n k : ℕ)
    (hk : k + 1 + 1 < ⦋n + 2⦌.len + 1) :
    Finset.univ.filter
        (fun x : Fin (n + 2) =>
          (ConcreteCategory.hom (C := SimplexCategory) (boundaryOneMap n)) x =
            (⟨k + 1 + 1, hk⟩ : Fin (⦋n + 2⦌.len + 1))) =
      {(⟨k + 1, by
          have hk' : k + 1 + 1 < n + 3 := by
            simpa only [SimplexCategory.len_mk] using hk
          omega⟩ : Fin (n + 2))} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  rw [boundaryOneMap_apply]
  constructor
  · intro h
    by_cases hx : x.1 = 0
    · simp [hx] at h
    · have hval := _root_.congrArg Fin.val h
      have hval' : x.1 + 1 = k + 1 + 1 := by
        simpa only [hx, if_neg, SimplexCategory.len_mk] using hval
      have hxval : x.1 = k + 1 := by omega
      exact Fin.ext hxval
  · intro h
    subst x
    simp

theorem joinParameter_one_edge_eq_boundaryParameter {n : ℕ}
    (t : unitInterval)
    (p : SimplexCategory.toTop.{0}.obj ⦋n⦌) :
    joinParameter t p (edgeParameter0 (1 : unitInterval)) =
      SimplexCategory.toTop.map (boundaryZeroMap n) (boundaryParameter t p) := by
  apply ULift.ext
  change joinTopPoint t p.down (edgeParameter0 (1 : unitInterval)).down =
    SimplexCategory.toTopMap (boundaryZeroMap n) (boundaryParameter t p).down
  apply SimplexCategory.toTopObj.ext
  funext i
  rw [SimplexCategory.coe_toTopMap]
  rcases i with ⟨_ | j, hi⟩
  · have hfilter :
        Finset.univ.filter
            (fun x : Fin (n + 2) =>
              (ConcreteCategory.hom (C := SimplexCategory) (boundaryZeroMap n)) x =
                (⟨0, hi⟩ : Fin (⦋n + 2⦌.len + 1))) = ∅ := by
      simpa only [Fin.ext_iff] using boundaryZeroMap_filter_zero n
    change _ =
      ∑ j ∈ Finset.univ.filter
        (fun j : Fin (n + 2) =>
          (ConcreteCategory.hom (C := SimplexCategory) (boundaryZeroMap n)) j =
            (⟨0, hi⟩ : Fin (⦋n + 2⦌.len + 1))),
        (boundaryParameter t p).down.1 j
    rw [hfilter]
    simp only [Finset.sum_empty]
    change unitInterval.toNNReal t *
        (edgeParameter0 (1 : unitInterval)).down.1 (0 : Fin 2) = 0
    rw [edgeParameter0_one_coord_zero]
    simp [unitInterval.toNNReal, unitInterval.symm]
  · cases j with
    | zero =>
      have hfilter :
          Finset.univ.filter
              (fun x : Fin (n + 2) =>
                (ConcreteCategory.hom (C := SimplexCategory) (boundaryZeroMap n)) x =
                  (⟨0 + 1, hi⟩ : Fin (⦋n + 2⦌.len + 1))) = {0} := by
        simpa only [Fin.ext_iff] using boundaryZeroMap_filter_one n
      change _ =
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin (n + 2) =>
            (ConcreteCategory.hom (C := SimplexCategory) (boundaryZeroMap n)) j =
              (⟨0 + 1, hi⟩ : Fin (⦋n + 2⦌.len + 1))),
          (boundaryParameter t p).down.1 j
      rw [hfilter]
      simp only [Finset.sum_singleton]
      change unitInterval.toNNReal t *
          (edgeParameter0 (1 : unitInterval)).down.1 (1 : Fin 2) =
        (boundaryParameter t p).down.1 (0 : Fin (n + 2))
      rw [edgeParameter0_one_coord_one]
      simp [boundaryParameter, unitInterval.toNNReal, unitInterval.symm]
    | succ k =>
      have hfilter := boundaryZeroMap_filter_succ n k hi
      have hk : k < n + 1 := by
        have hi' : k + 2 < n + 3 := by
          simpa only [SimplexCategory.len_mk] using hi
        omega
      let kt : Fin (n + 1) := ⟨k, hk⟩
      change _ =
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin (n + 2) =>
            (ConcreteCategory.hom (C := SimplexCategory) (boundaryZeroMap n)) j =
              (⟨k + 1 + 1, hi⟩ : Fin (⦋n + 2⦌.len + 1))),
          (boundaryParameter t p).down.1 j
      rw [hfilter]
      simp only [Finset.sum_singleton]
      change unitInterval.toNNReal (unitInterval.symm t) * p.down.1 kt =
        (boundaryParameter t p).down.1
          (⟨k + 1, by
            have hk' : k + 1 < n + 2 := by omega
            exact hk'⟩ : Fin (n + 2))
      simp [kt, boundaryParameter, unitInterval.toNNReal, unitInterval.symm]

theorem joinParameter_zero_edge_eq_boundaryParameter {n : ℕ}
    (t : unitInterval)
    (p : SimplexCategory.toTop.{0}.obj ⦋n⦌) :
    joinParameter t p (edgeParameter0 (0 : unitInterval)) =
      SimplexCategory.toTop.map (boundaryOneMap n) (boundaryParameter t p) := by
  apply ULift.ext
  change joinTopPoint t p.down (edgeParameter0 (0 : unitInterval)).down =
    SimplexCategory.toTopMap (boundaryOneMap n) (boundaryParameter t p).down
  apply SimplexCategory.toTopObj.ext
  funext i
  rw [SimplexCategory.coe_toTopMap]
  rcases i with ⟨_ | j, hi⟩
  · have hfilter :
        Finset.univ.filter
            (fun x : Fin (n + 2) =>
              (ConcreteCategory.hom (C := SimplexCategory) (boundaryOneMap n)) x =
                (⟨0, hi⟩ : Fin (⦋n + 2⦌.len + 1))) = {0} := by
      simpa only [Fin.ext_iff] using boundaryOneMap_filter_zero n
    change _ =
      ∑ j ∈ Finset.univ.filter
        (fun j : Fin (n + 2) =>
          (ConcreteCategory.hom (C := SimplexCategory) (boundaryOneMap n)) j =
            (⟨0, hi⟩ : Fin (⦋n + 2⦌.len + 1))),
        (boundaryParameter t p).down.1 j
    rw [hfilter]
    simp only [Finset.sum_singleton]
    change unitInterval.toNNReal t *
        (edgeParameter0 (0 : unitInterval)).down.1 (0 : Fin 2) =
      (boundaryParameter t p).down.1 (0 : Fin (n + 2))
    rw [edgeParameter0_zero_coord_zero]
    simp [boundaryParameter, unitInterval.toNNReal, unitInterval.symm]
  · cases j with
    | zero =>
      have hfilter :
          Finset.univ.filter
              (fun x : Fin (n + 2) =>
                (ConcreteCategory.hom (C := SimplexCategory) (boundaryOneMap n)) x =
                  (⟨1, hi⟩ : Fin (⦋n + 2⦌.len + 1))) = ∅ := by
        simpa only [Fin.ext_iff] using boundaryOneMap_filter_one n
      change _ =
        ∑ k ∈ Finset.univ.filter
          (fun k : Fin (n + 2) =>
            (ConcreteCategory.hom (C := SimplexCategory) (boundaryOneMap n)) k =
              (⟨1, hi⟩ : Fin (⦋n + 2⦌.len + 1))),
          (boundaryParameter t p).down.1 k
      rw [hfilter]
      simp only [Finset.sum_empty]
      change unitInterval.toNNReal t *
          (edgeParameter0 (0 : unitInterval)).down.1 (1 : Fin 2) = 0
      rw [edgeParameter0_zero_coord_one]
      simp [unitInterval.toNNReal, unitInterval.symm]
    | succ k =>
      have hfilter := boundaryOneMap_filter_succ n k hi
      have hk : k < n + 1 := by
        have hi' : k + 2 < n + 3 := by
          simpa only [SimplexCategory.len_mk] using hi
        omega
      let kt : Fin (n + 1) := ⟨k, hk⟩
      change _ =
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin (n + 2) =>
            (ConcreteCategory.hom (C := SimplexCategory) (boundaryOneMap n)) j =
              (⟨k + 1 + 1, hi⟩ : Fin (⦋n + 2⦌.len + 1))),
          (boundaryParameter t p).down.1 j
      rw [hfilter]
      simp only [Finset.sum_singleton]
      change unitInterval.toNNReal (unitInterval.symm t) * p.down.1 kt =
        (boundaryParameter t p).down.1
          (⟨k + 1, by
            have hk' : k + 1 < n + 2 := by omega
            exact hk'⟩ : Fin (n + 2))
      simp [kt, boundaryParameter, unitInterval.toNNReal, unitInterval.symm]

theorem circleLocalJoin_seam {n : ℕ} (z : ℤ)
    (σ : ComposableArrows CircleObject n)
    (t : unitInterval)
    (p : SimplexCategory.toTop.{0}.obj ⦋n⦌)
    (h : affineHeight σ p.down = (z + 1 : ℝ)) :
    circleLocalJoin z σ (t, p) = circleLocalJoin (z + 1) σ (t, p) := by
  have hleft :
      clampUnit (affineHeight σ p.down - (z : ℝ)) = (1 : unitInterval) := by
    have hz : affineHeight σ p.down - (z : ℝ) = 1 := by
      rw [h]
      norm_num
    rw [hz]
    exact clampUnit_of_mem_Icc ⟨by norm_num, by norm_num⟩
  have hright :
      clampUnit (affineHeight σ p.down - ((z + 1 : ℤ) : ℝ)) =
        (0 : unitInterval) := by
    have hz : affineHeight σ p.down - ((z + 1 : ℤ) : ℝ) = 0 := by
      rw [h]
      push_cast
      ring
    rw [hz]
    exact clampUnit_of_mem_Icc ⟨by norm_num, by norm_num⟩
  change
    realizeSimplex (X := CircleNerve) (n := ⦋n + 2⦌)
        (joinedSimplexAt z σ)
        (joinParameter (unitInterval.symm t) p
          (edgeParameter0
            (clampUnit (affineHeight σ p.down - (z : ℝ))))) =
      realizeSimplex (X := CircleNerve) (n := ⦋n + 2⦌)
        (joinedSimplexAt (z + 1) σ)
        (joinParameter (unitInterval.symm t) p
          (edgeParameter0
            (clampUnit (affineHeight σ p.down - ((z + 1 : ℤ) : ℝ)))))
  rw [hleft, hright]
  rw [joinParameter_one_edge_eq_boundaryParameter,
    joinParameter_zero_edge_eq_boundaryParameter]
  have h0 := _root_.congrArg
      (fun k : SimplexCategory.toTop.{0}.obj ⦋n + 1⦌ ⟶ CircleNerveRealization =>
        k (boundaryParameter (unitInterval.symm t) p))
      (realizeSimplexHom_naturality
        (X := CircleNerve) (boundaryZeroMap n) (joinedSimplexAt z σ))
  have h1 := _root_.congrArg
      (fun k : SimplexCategory.toTop.{0}.obj ⦋n + 1⦌ ⟶ CircleNerveRealization =>
        k (boundaryParameter (unitInterval.symm t) p))
      (realizeSimplexHom_naturality
        (X := CircleNerve) (boundaryOneMap n) (joinedSimplexAt (z + 1) σ))
  have hseam :
      CircleNerve.map (Quiver.Hom.op (boundaryZeroMap n))
          (joinedSimplexAt z σ) =
        CircleNerve.map (Quiver.Hom.op (boundaryOneMap n))
          (joinedSimplexAt (z + 1) σ) := by
    simpa using joinedSimplex_boundary z σ
  rw [← hseam] at h1
  simpa [realizeSimplex] using h0.trans h1.symm

noncomputable def circleHomotopyValue {n : ℕ}
    (σ : ComposableArrows CircleObject n)
    (tp : unitInterval × SimplexCategory.toTop.{0}.obj ⦋n⦌) :
    CircleNerveRealization :=
  circleLocalJoin (Int.floor (affineHeight σ tp.2.down)) σ tp

theorem continuous_circleHomotopyValue {n : ℕ}
    (σ : ComposableArrows CircleObject n) :
    Continuous (circleHomotopyValue σ) := by
  classical
  let A := unitInterval × SimplexCategory.toTop.{0}.obj ⦋n⦌
  let r : A → ℝ := fun tp => affineHeight σ tp.2.down
  have hr : Continuous r := by
    exact (affineHeight σ).continuous.comp
      (continuous_uliftDown.comp continuous_snd)
  change Continuous (fun x : A => circleHomotopyValue σ x)
  rw [continuous_iff_continuousAt]
  intro x
  let z : ℤ := Int.floor (r x)
  let s : Set A := r ⁻¹' Set.Ici (z : ℝ)
  let fz : A → CircleNerveRealization := circleLocalJoin z σ
  let fm : A → CircleNerveRealization := circleLocalJoin (z - 1) σ
  have hfront : ∀ y ∈ frontier s, fz y = fm y := by
    intro y hy
    have hy' : r y ∈ frontier (Set.Ici (z : ℝ)) := by
      exact hr.frontier_preimage_subset (Set.Ici (z : ℝ)) hy
    have hy'' : r y ∈ ({(z : ℝ)} : Set ℝ) :=
      (frontier_Ici_subset (z : ℝ)) hy'
    have hyr : r y = (z : ℝ) := by simpa using hy''
    have hseam :
        circleLocalJoin (z - 1) σ (y.1, y.2) =
          circleLocalJoin z σ (y.1, y.2) := by
      have hseam' := circleLocalJoin_seam (z - 1) σ y.1 y.2 (by
        dsimp [r] at hyr ⊢
        rw [hyr]
        push_cast
        ring)
      simpa only [sub_add_cancel] using hseam'
    exact hseam.symm
  have hfz : Continuous fz := by
    simpa only [fz] using (circleLocalJoin z σ).continuous
  have hfm : Continuous fm := by
    simpa only [fm] using (circleLocalJoin (z - 1) σ).continuous
  have hpiece :
      Continuous (Set.piecewise s fz fm) := by
    exact hfz.piecewise hfront hfm
  have hxlo : (z : ℝ) - 1 < r x := by
    have hzle : (z : ℝ) ≤ r x := Int.floor_le _
    linarith
  have hxhi : r x < (z : ℝ) + 1 := by
    exact Int.lt_floor_add_one _
  have hnhds : r ⁻¹' Set.Ioo ((z : ℝ) - 1) ((z : ℝ) + 1) ∈ 𝓝 x := by
    apply (isOpen_Ioo.preimage hr).mem_nhds
    exact ⟨hxlo, hxhi⟩
  have heq :
      (fun y : A => circleHomotopyValue σ y) =ᶠ[𝓝 x]
        Set.piecewise s fz fm := by
    filter_upwards [hnhds] with y hy
    by_cases hyz : (z : ℝ) ≤ r y
    · have hfloor : Int.floor (r y) = z := by
        apply Int.floor_eq_iff.mpr
        constructor
        · exact hyz
        · linarith [hy.2]
      simp [circleHomotopyValue, r, s, fz, fm, hfloor, hyz]
    · have hyz' : r y < (z : ℝ) := lt_of_not_ge hyz
      have hfloor : Int.floor (r y) = z - 1 := by
        apply Int.floor_eq_iff.mpr
        constructor
        · have hylo : ((z - 1 : ℤ) : ℝ) ≤ r y := by
            push_cast
            linarith [hy.1]
          exact hylo
        · push_cast
          linarith
      simp [circleHomotopyValue, r, s, fz, fm, hfloor, hyz]
  exact (continuousAt_congr heq).2 (hpiece.continuousAt)

noncomputable def circleHomotopyPath {n : ℕ}
    (σ : ComposableArrows CircleObject n)
    (p : SimplexCategory.toTop.{0}.obj ⦋n⦌) :
    C(unitInterval, CircleNerveRealization) where
  toFun t := circleHomotopyValue σ (t, p)
  continuous_toFun := by
    exact continuous_circleHomotopyValue σ |>.comp
      (continuous_id.prodMk continuous_const)

theorem circleHomotopyPath_apply {n : ℕ}
    (σ : ComposableArrows CircleObject n)
    (p : SimplexCategory.toTop.{0}.obj ⦋n⦌)
    (t : unitInterval) :
    circleHomotopyPath σ p t =
      circleLocalJoin (Int.floor (affineHeight σ p.down)) σ (t, p) :=
  rfl

def joinedWhiskerMap {m n : SimplexCategory} (f : m ⟶ n) :
    SimplexCategory.Hom ⦋m.len + 2⦌ ⦋n.len + 2⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i =>
        Fin.cases (0 : Fin (n.len + 3))
          (fun j =>
            Fin.cases (1 : Fin (n.len + 3))
              (fun k => (f.toOrderHom k).succ.succ) j)
          i,
      monotone' := by
        intro i j hij
        rcases i with ⟨i, hi⟩
        rcases j with ⟨j, hj⟩
        simp only [Fin.mk_le_mk] at hij ⊢
        rcases i with _ | i <;> rcases j with _ | j
        · exact le_rfl
        · exact Nat.zero_le _
        · omega
        · rcases i with _ | i <;> rcases j with _ | j
          · exact le_rfl
          · simpa only [Fin.cases_zero, Fin.cases_succ] using
              (Fin.succ_le_succ_iff.mpr
                (Fin.zero_le
                  ((f.toOrderHom (⟨j, by
                    have hj' := hj
                    simp only [SimplexCategory.len_mk] at hj'
                    omega⟩ :
                    Fin (m.len + 1))).succ)))
          · omega
          · simpa only [Fin.cases_succ] using
              (Fin.succ_le_succ_iff.mpr
                (Fin.succ_le_succ_iff.mpr
                  (f.toOrderHom.monotone (by
                    have hi' : i < m.len + 1 := by
                      have hi'' := hi
                      simp only [SimplexCategory.len_mk] at hi''
                      omega
                    have hj' : j < m.len + 1 := by
                      have hj'' := hj
                      simp only [SimplexCategory.len_mk] at hj''
                      omega
                    apply Fin.mk_le_mk.mpr
                    omega)))) }

theorem joinedWhiskerMap_apply {m n : SimplexCategory} (f : m ⟶ n)
    (i : Fin (m.len + 3)) :
    (ConcreteCategory.hom (C := SimplexCategory) (joinedWhiskerMap f)) i =
      Fin.cases (0 : Fin (n.len + 3))
        (fun j =>
          Fin.cases (1 : Fin (n.len + 3))
            (fun k => (f.toOrderHom k).succ.succ) j)
        i := by
  rfl

theorem joinedWhiskerMap_obj {m n : SimplexCategory} (f : m ⟶ n)
    (i : Fin (m.len + 3)) :
    (SimplexCategory.toCat.map (joinedWhiskerMap f)).obj i =
      Fin.cases (0 : Fin (n.len + 3))
        (fun j =>
          Fin.cases (1 : Fin (n.len + 3))
            (fun k => (f.toOrderHom k).succ.succ) j)
        i := by
  rfl

universe u

theorem precomp_map_succ_zero {C : Type u} [Category C] {n : ℕ}
    (F : ComposableArrows C n) {X : C} (g : X ⟶ F.left)
    (u : Fin (n + 1)) :
    (F.precomp g).map' 0 (u.1 + 1) (by omega) (by omega) =
      g ≫ F.map' 0 u.1 (by omega) (by omega) := by
  rcases u with ⟨u, hu⟩
  cases u with
  | zero =>
      change ComposableArrows.Precomp.map F g
          (⟨0, by omega⟩ : Fin (n + 2))
          (⟨1, by omega⟩ : Fin (n + 2)) (Fin.zero_le _) = _
      simp [ComposableArrows.Precomp.map]
      change g = g ≫ 𝟙 F.left
      exact (Category.comp_id g).symm
  | succ u =>
      change ComposableArrows.Precomp.map F g
          (0 : Fin (n + 2))
          (⟨u + 2, by omega⟩ : Fin (n + 2)) (Fin.zero_le _) = _
      rw [ComposableArrows.Precomp.map_zero_succ_succ]

theorem joinParameter_whisker_naturality {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌)
    (t : unitInterval)
    (p : SimplexCategory.toTop.{0}.obj ⦋m⦌)
    (q : SimplexCategory.toTop.{0}.obj ⦋1⦌) :
    SimplexCategory.toTop.map (joinedWhiskerMap f) (joinParameter t p q) =
      joinParameter t (SimplexCategory.toTop.map f p) q := by
  classical
  apply ULift.ext
  change SimplexCategory.toTopMap (joinedWhiskerMap f)
      (joinTopPoint t p.down q.down) =
    joinTopPoint t (SimplexCategory.toTopMap f p.down) q.down
  apply SimplexCategory.toTopObj.ext
  funext i
  rw [SimplexCategory.coe_toTopMap]
  rcases i with ⟨_ | j, hi⟩
  · have hf :
        Finset.univ.filter
            (fun x : Fin (m + 3) =>
              (ConcreteCategory.hom (C := SimplexCategory)
                (joinedWhiskerMap f)) x =
                (0 : Fin (⦋n + 2⦌.len + 1))) = {0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      rw [joinedWhiskerMap_apply]
      rcases x with ⟨x, hx⟩
      cases x with
      | zero =>
          have hx0 : (⟨0, hx⟩ : Fin (m + 3)) = 0 := by
            apply Fin.ext
            rfl
          rw [hx0]
          simp only [Fin.cases_zero]
      | succ x =>
          cases x with
          | zero =>
              let y0 : Fin (m + 2) := ⟨0, by omega⟩
              have hy0 : y0 = 0 := by
                apply Fin.ext
                rfl
              have hx1 :
                  (⟨1, hx⟩ : Fin (m + 3)) =
                    y0.succ := by
                apply Fin.ext
                rfl
              rw [hx1, Fin.cases_succ, hy0, Fin.cases_zero]
              simp
          | succ x =>
              have hxi :
                  (⟨x + 1 + 1, hx⟩ : Fin (m + 3)) =
                    Fin.succ (Fin.succ (⟨x, by omega⟩ : Fin (m + 1))) := by
                apply Fin.ext
                rfl
              rw [hxi, Fin.cases_succ, Fin.cases_succ]
              simp
    change
      ∑ x ∈ Finset.univ.filter
          (fun x : Fin (m + 3) =>
            (ConcreteCategory.hom (C := SimplexCategory)
              (joinedWhiskerMap f)) x =
              (0 : Fin (⦋n + 2⦌.len + 1))),
          (joinTopPoint t p.down q.down) x = _
    rw [hf]
    simp only [Finset.sum_singleton]
    have hi0 : (⟨0, hi⟩ : Fin (⦋n + 2⦌.len + 1)) = 0 := by
      apply Fin.ext
      rfl
    rw [hi0]
    simp [joinTopPoint]
  · cases j with
    | zero =>
        simp only [SimplexCategory.len_mk] at hi ⊢
        have hf :
            Finset.univ.filter
                (fun x : Fin (m + 3) =>
                  (ConcreteCategory.hom (C := SimplexCategory)
                    (joinedWhiskerMap f)) x =
                    (1 : Fin (⦋n + 2⦌.len + 1))) = {1} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton]
          rw [joinedWhiskerMap_apply]
          rcases x with ⟨x, hx⟩
          cases x with
          | zero =>
              have hx0 : (⟨0, hx⟩ : Fin (m + 3)) = 0 := by
                apply Fin.ext
                rfl
              rw [hx0]
              simp only [Fin.cases_zero]
              simp
          | succ x =>
              cases x with
              | zero =>
                  let y0 : Fin (m + 2) := ⟨0, by omega⟩
                  have hy0 : y0 = 0 := by
                    apply Fin.ext
                    rfl
                  have hx1 :
                      (⟨1, hx⟩ : Fin (m + 3)) =
                        y0.succ := by
                    apply Fin.ext
                    rfl
                  rw [hx1, Fin.cases_succ, hy0, Fin.cases_zero]
                  simp
              | succ x =>
                  have hxi :
                      (⟨x + 1 + 1, hx⟩ : Fin (m + 3)) =
                        Fin.succ (Fin.succ (⟨x, by omega⟩ : Fin (m + 1))) := by
                    apply Fin.ext
                    rfl
                  rw [hxi, Fin.cases_succ, Fin.cases_succ]
                  constructor <;> intro h
                  · have hv := _root_.congrArg Fin.val h
                    simp at hv
                  · have hv := _root_.congrArg Fin.val h
                    simp at hv
        change
          ∑ x ∈ Finset.univ.filter
              (fun x : Fin (m + 3) =>
                (ConcreteCategory.hom (C := SimplexCategory)
                  (joinedWhiskerMap f)) x =
                  (1 : Fin (⦋n + 2⦌.len + 1))),
              (joinTopPoint t p.down q.down) x = _
        rw [hf]
        simp only [Finset.sum_singleton]
        let z : Fin (n + 2) := ⟨0, by omega⟩
        have hi1 : (⟨1, hi⟩ : Fin (n + 3)) = z.succ := by
          apply Fin.ext
          rfl
        rw [hi1]
        have hz : z = 0 := by
          dsimp [z]
        rw [hz]
        have hs : (1 : Fin (m + 3)) = Fin.succ (0 : Fin (m + 2)) := by
          apply Fin.ext
          rfl
        rw [hs]
        simp only [joinTopPoint]
        simp only [Fin.cases_succ, Fin.cases_zero]
    | succ k =>
        simp only [SimplexCategory.len_mk] at hi ⊢
        let K : Fin (n + 1) := ⟨k, by omega⟩
        have hK : (⟨k + 1 + 1, hi⟩ : Fin (n + 3)) = K.succ.succ := by
          apply Fin.ext
          rfl
        rw [hK]
        rw [Finset.sum_filter]
        rw [Fin.sum_univ_succ]
        conv_lhs =>
          congr
          · skip
          · rw [Fin.sum_univ_succ]
        have hmap0 :
            (ConcreteCategory.hom (C := SimplexCategory)
              (joinedWhiskerMap f)) 0 = (0 : Fin (n + 3)) := by
          rw [joinedWhiskerMap_apply]
          simp only [Fin.cases_zero]
        have hs : (1 : Fin (m + 3)) = Fin.succ (0 : Fin (m + 2)) := by
          apply Fin.ext
          rfl
        have hmap1 :
            (ConcreteCategory.hom (C := SimplexCategory)
              (joinedWhiskerMap f)) 1 = (1 : Fin (n + 3)) := by
          rw [hs, joinedWhiskerMap_apply, Fin.cases_succ, Fin.cases_zero]
        have hK0 : (0 : Fin (n + 3)) ≠ K.succ.succ := by
          intro h
          have hv := _root_.congrArg Fin.val h
          simp at hv
        have hK1 : (1 : Fin (n + 3)) ≠ K.succ.succ := by
          intro h
          have hv := _root_.congrArg Fin.val h
          simp at hv
        have hmap_tail (x : Fin (m + 1)) :
            (ConcreteCategory.hom (C := SimplexCategory)
                (joinedWhiskerMap f)) x.succ.succ = K.succ.succ ↔
              (ConcreteCategory.hom (C := SimplexCategory) f) x = K := by
          rw [joinedWhiskerMap_apply, Fin.cases_succ, Fin.cases_succ]
          change ((f.toOrderHom x).succ.succ = K.succ.succ ↔
            f.toOrderHom x = K)
          constructor
          · intro h
            exact Fin.succ_inj.mp (Fin.succ_inj.mp h)
          · intro h
            exact Fin.succ_inj.mpr (Fin.succ_inj.mpr h)
        simp only [SimplexCategory.len_mk] at *
        simp [joinedWhiskerMap_apply, joinTopPoint, hmap0, hmap1,
          hmap_tail, hK0, hK1]
        rw [Finset.sum_filter]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : (ConcreteCategory.hom (C := SimplexCategory) f) x = K <;>
          simp [hx]

theorem joinedSimplexAt_whisker_naturality {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌)
    (z : ℤ)
    (σ : ComposableArrows CircleObject n) :
    CircleNerve.map (Opposite.op (joinedWhiskerMap f))
        (joinedSimplexAt
          (z + simplexHeight σ
            ((SimplexCategory.toCat.map f).obj (0 : Fin (m + 1)))) σ) =
      joinedSimplexAt z (σ.whiskerLeft (SimplexCategory.toCat.map f)) := by
  refine ComposableArrows.ext (h := ?_) (w := ?_)
  · intro i
    dsimp [CircleNerve, joinedSimplexAt]
    rcases i with ⟨j, hj⟩
    cases j with
    | zero => rfl
    | succ j =>
        cases j with
        | zero => rfl
        | succ j => rfl
  · intro i hi
    cases i with
    | zero =>
        dsimp [CircleNerve, joinedSimplexAt]
        change
          ComposableArrows.Precomp.map
              (σ.precomp
                (circleBridgeInt
                  (z + simplexHeight σ
                    ((SimplexCategory.toCat.map f).obj (0 : Fin (m + 1)))) σ))
              circleGenerator (0 : Fin (n + 3)) (1 : Fin (n + 3)) _ = _
        simp [circleBridgeInt, circleDecodeArrow, SimplexCategory.toCat,
          ComposableArrows.Precomp.map]
        rfl
    | succ i =>
        cases i with
        | zero =>
            dsimp [CircleNerve, joinedSimplexAt]
            let A : ℤ := z + simplexHeight σ
              ((SimplexCategory.toCat.map f).obj (0 : Fin (m + 1)))
            have hu :
                (f.toOrderHom (0 : Fin (m + 1))).1 < n + 1 := by
              simpa only [SimplexCategory.len_mk] using
                (f.toOrderHom (0 : Fin (m + 1))).isLt
            change
              ComposableArrows.Precomp.map
                  (σ.precomp (circleBridgeInt A σ)) circleGenerator
                  (⟨1, by omega⟩ : Fin (n + 3))
                  (⟨(f.toOrderHom (0 : Fin (m + 1))).1 + 2, by omega⟩ :
                    Fin (n + 3))
                  (by
                    apply Fin.mk_le_mk.mpr
                    omega) = _
            rw [ComposableArrows.Precomp.map_succ_succ]
            calc
              _ = circleBridgeInt A σ ≫
                    σ.map' 0 (f.toOrderHom (0 : Fin (m + 1))).1
                      (by omega) (by omega) := by
                exact precomp_map_succ_zero (C := CircleObject) (n := n)
                  σ (circleBridgeInt A σ)
                  (f.toOrderHom (0 : Fin (m + 1)))
              _ = circleBridgeInt z
                    (σ.whiskerLeft (SimplexCategory.toCat.map f)) := by
                apply circleArrow_eq_of_winding
                rw [arrowWinding_comp, arrowWinding_circleBridgeInt,
                  arrowWinding_circleBridgeInt]
                change
                  -(A + 1) + simplexHeight σ
                      ((SimplexCategory.toCat.map f).obj
                        (0 : Fin (m + 1))) = -(z + 1)
                dsimp [A]
                ring
              _ = _ := by
                simp only [Category.id_comp, Category.comp_id]
                rfl
        | succ k =>
            dsimp [CircleNerve, joinedSimplexAt]
            have hk : k + 2 < m + 2 := by
              simpa only [SimplexCategory.len_mk] using hi
            let u0 : Fin (m + 1) := ⟨k, by omega⟩
            let u1 : Fin (m + 1) := ⟨k + 1, by omega⟩
            let v0 : Fin (n + 1) := f.toOrderHom u0
            let v1 : Fin (n + 1) := f.toOrderHom u1
            have hv0 : v0.1 + 2 < n + 3 := by
              have h := v0.isLt
              omega
            have hv1 : v1.1 + 2 < n + 3 := by
              have h := v1.isLt
              omega
            have hvle : v0.1 + 2 ≤ v1.1 + 2 := by
              have hle : u0 ≤ u1 := by
                apply Fin.mk_le_mk.mpr
                dsimp [u0, u1]
                omega
              have hmap := f.toOrderHom.monotone hle
              omega
            change
              ComposableArrows.Precomp.map
                  (σ.precomp
                    (circleBridgeInt
                      (z + simplexHeight σ
                        ((SimplexCategory.toCat.map f).obj
                          (0 : Fin (m + 1)))) σ)) circleGenerator
                  (⟨v0.1 + 2, hv0⟩ : Fin (n + 3))
                  (⟨v1.1 + 2, hv1⟩ : Fin (n + 3))
                  (Fin.mk_le_mk.mpr hvle) = _
            simp [circleBridgeInt, circleDecodeArrow, SimplexCategory.toCat,
              ComposableArrows.Precomp.map]
            congr 1

theorem circleHomotopyPath_naturality {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows CircleObject n)
    (p : SimplexCategory.toTop.{0}.obj ⦋m⦌) :
    circleHomotopyPath σ (SimplexCategory.toTop.map f p) =
      circleHomotopyPath
        (σ.whiskerLeft (SimplexCategory.toCat.map f)) p := by
  classical
  apply ContinuousMap.ext
  intro t
  rw [circleHomotopyPath_apply, circleHomotopyPath_apply]
  let Φ : Fin (m + 1) ⥤ Fin (n + 1) :=
    SimplexCategory.toCat.map f
  let τ : ComposableArrows CircleObject m := σ.whiskerLeft Φ
  let a : ℤ := simplexHeight σ (Φ.obj (0 : Fin (m + 1)))
  let z : ℤ := Int.floor (affineHeight τ p.down)
  have hheight :
      affineHeight τ p.down + (a : ℝ) =
        affineHeight σ (SimplexCategory.toTopMap f p.down) := by
    exact affineHeight_whisker (m := ⦋m⦌) (n := ⦋n⦌) σ f p.down
  have hfloor :
      Int.floor (affineHeight σ (SimplexCategory.toTopMap f p.down)) =
        z + a := by
    rw [← hheight]
    dsimp [z]
    rw [Int.floor_add_intCast]
  have hshift :
      affineHeight σ (SimplexCategory.toTopMap f p.down) -
          ((z + a : ℤ) : ℝ) =
        affineHeight τ p.down - (z : ℝ) := by
    rw [← hheight]
    push_cast
    ring
  have hparam := joinParameter_whisker_naturality f
    (unitInterval.symm t) p
    (edgeParameter0 (clampUnit (affineHeight τ p.down - (z : ℝ))))
  change
    circleLocalJoin
        (Int.floor (affineHeight σ (SimplexCategory.toTopMap f p.down))) σ
        (t, SimplexCategory.toTop.map f p) =
      circleLocalJoin (Int.floor (affineHeight τ p.down)) τ (t, p)
  rw [hfloor]
  change
    realizeSimplex (X := CircleNerve) (n := ⦋n + 2⦌)
        (joinedSimplexAt (z + a) σ)
        (joinParameter (unitInterval.symm t)
          (SimplexCategory.toTop.map f p)
          (edgeParameter0
            (clampUnit
              (affineHeight σ (SimplexCategory.toTopMap f p.down) -
                ((z + a : ℤ) : ℝ))))) =
      realizeSimplex (X := CircleNerve) (n := ⦋m + 2⦌)
        (joinedSimplexAt z τ)
        (joinParameter (unitInterval.symm t) p
          (edgeParameter0
            (clampUnit (affineHeight τ p.down - (z : ℝ)))))
  rw [hshift]
  have hparam' :
      joinParameter (unitInterval.symm t)
          (SimplexCategory.toTop.map f p)
          (edgeParameter0 (clampUnit (affineHeight τ p.down - (z : ℝ)))) =
        SimplexCategory.toTop.map (joinedWhiskerMap f)
          (joinParameter (unitInterval.symm t) p
            (edgeParameter0 (clampUnit (affineHeight τ p.down - (z : ℝ))))) := by
    simpa using hparam.symm
  have hsimplex := joinedSimplexAt_whisker_naturality f z σ
  have hsimplex' :
      CircleNerve.map (Opposite.op (joinedWhiskerMap f))
          (joinedSimplexAt (z + a) σ) = joinedSimplexAt z τ := by
    simpa [a, τ, Φ] using hsimplex
  have hsimplex'' :
      CircleNerve.map (Quiver.Hom.op (joinedWhiskerMap f))
          (joinedSimplexAt (z + a) σ) = joinedSimplexAt z τ := by
    simpa using hsimplex'
  have hreal := _root_.congrArg
      (fun k : SimplexCategory.toTop.{0}.obj ⦋m + 2⦌ ⟶ CircleNerveRealization =>
        k (joinParameter (unitInterval.symm t) p
          (edgeParameter0 (clampUnit (affineHeight τ p.down - (z : ℝ))))))
      (realizeSimplexHom_naturality
        (X := CircleNerve) (joinedWhiskerMap f)
        (joinedSimplexAt (z + a) σ))
  rw [hsimplex''] at hreal
  calc
    realizeSimplex (X := CircleNerve) (n := ⦋n + 2⦌)
          (joinedSimplexAt (z + a) σ)
          (joinParameter (unitInterval.symm t)
            (SimplexCategory.toTop.map f p)
            (edgeParameter0
              (clampUnit (affineHeight τ p.down - (z : ℝ))))) =
        realizeSimplex (X := CircleNerve) (n := ⦋n + 2⦌)
          (joinedSimplexAt (z + a) σ)
          (SimplexCategory.toTop.map (joinedWhiskerMap f)
            (joinParameter (unitInterval.symm t) p
              (edgeParameter0
                (clampUnit (affineHeight τ p.down - (z : ℝ)))))) := by
      rw [hparam']
    _ = realizeSimplex (X := CircleNerve) (n := ⦋m + 2⦌)
          (joinedSimplexAt z τ)
          (joinParameter (unitInterval.symm t) p
            (edgeParameter0
              (clampUnit (affineHeight τ p.down - (z : ℝ))))) := by
      simpa [realizeSimplex, Function.comp_def, τ, Φ] using hreal

theorem circleHomotopyPath_naturality' {m n : SimplexCategory}
    (f : m ⟶ n)
    (σ : ComposableArrows CircleObject n.len)
    (p : SimplexCategory.toTop.{0}.obj m) :
    circleHomotopyPath σ (SimplexCategory.toTop.map f p) =
      circleHomotopyPath
        (σ.whiskerLeft (SimplexCategory.toCat.map f)) p := by
  induction m using SimplexCategory.rec with
  | _ m =>
      induction n using SimplexCategory.rec with
      | _ n =>
          exact circleHomotopyPath_naturality f σ p

theorem circleHomotopyPath_apply' {n : SimplexCategory}
    (σ : ComposableArrows CircleObject n.len)
    (p : SimplexCategory.toTop.{0}.obj n)
    (t : unitInterval) :
    circleHomotopyPath σ p t =
      circleLocalJoin (Int.floor (affineHeight σ p.down)) σ (t, p) := by
  induction n using SimplexCategory.rec with
  | _ n =>
      exact circleHomotopyPath_apply σ p t

theorem circleLocalJoin_zero' {n : SimplexCategory} (z : ℤ)
    (σ : ComposableArrows CircleObject n.len)
    (h : unitInterval × SimplexCategory.toTop.{0}.obj n) :
    circleLocalJoin z σ (0, h.2) =
      nerveEdge circleGenerator
        (clampUnit (affineHeight σ h.2.down - (z : ℝ))) := by
  induction n using SimplexCategory.rec with
  | _ n =>
      exact circleLocalJoin_zero z σ h

theorem circleLocalJoin_one' {n : SimplexCategory} (z : ℤ)
    (σ : ComposableArrows CircleObject n.len)
    (h : unitInterval × SimplexCategory.toTop.{0}.obj n) :
    circleLocalJoin z σ (1, h.2) = realizeSimplex σ h.2 := by
  induction n using SimplexCategory.rec with
  | _ n =>
      exact circleLocalJoin_one z σ h

noncomputable def circleHomotopyCocone :
    Cocone
      (CostructuredArrow.proj SSet.stdSimplex CircleNerve ⋙
        SimplexCategory.toTop.{0}) where
  pt := TopCat.of C(unitInterval, CircleNerveRealization)
  ι :=
    { app := fun j =>
        TopCat.ofHom
          ⟨fun p =>
              circleHomotopyPath (SSet.yonedaEquiv j.hom) p,
            by
              apply ContinuousMap.continuous_of_continuous_uncurry
              exact
                (continuous_circleHomotopyValue (SSet.yonedaEquiv j.hom)).comp
                  (continuous_snd.prodMk continuous_fst)⟩
      naturality := by
        intro A B f
        ext p
        apply ContinuousMap.ext
        intro t
        let sB : CircleNerve.obj (op B.left) :=
          SSet.yonedaEquiv B.hom
        change
          circleHomotopyPath sB
              (SimplexCategory.toTop.map f.left p) t =
            circleHomotopyPath (SSet.yonedaEquiv A.hom) p t
        have hs :
            SSet.yonedaEquiv A.hom =
              CircleNerve.map f.left.op sB :=
          costructured_simplex_naturality f
        rw [hs]
        simpa using
          _root_.congrArg (fun k : C(unitInterval, CircleNerveRealization) => k t)
            (circleHomotopyPath_naturality' f.left sB p) }

theorem periodicGenerator_floor (r : ℝ) :
    periodicGenerator r =
      nerveEdge circleGenerator
        (clampUnit (r - (Int.floor r : ℝ))) := by
  let z : ℤ := Int.floor r
  have hzle : (z : ℝ) ≤ r := by
    dsimp [z]
    exact Int.floor_le r
  have hzlt : r < (z : ℝ) + 1 := by
    dsimp [z]
    exact Int.lt_floor_add_one r
  have hmem : r - (z : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr hzle
    ·
      linarith
  have hcover : circleCover r = circleCover (r - (z : ℝ)) := by
    calc
      circleCover r = circleCover ((r - (z : ℝ)) + (z : ℝ)) := by
        congr 1
        ring
      _ = circleCover (r - (z : ℝ)) := by
        exact circleCover_add_intCast (r - (z : ℝ)) z
  rw [periodicGenerator_apply, hcover]
  simpa [circleCover, generatorLine, z] using
    (circleAmbientToNerve_coe hmem)

noncomputable def circleAmbientHomotopyCurried :
    CircleNerveRealization ⟶ TopCat.of
      C(unitInterval, CircleNerveRealization) :=
  (realizationCoconeIsColimit CircleNerve).desc circleHomotopyCocone

theorem circleAmbientHomotopyCurried_realizeSimplex
    (j : RealizationIndex CircleNerve)
    (p : SimplexCategory.toTop.{0}.obj j.left) :
    circleAmbientHomotopyCurried
        (realizeSimplex (SSet.yonedaEquiv j.hom) p) =
      circleHomotopyPath (SSet.yonedaEquiv j.hom) p := by
  have hf :=
    (realizationCoconeIsColimit CircleNerve).fac circleHomotopyCocone j
  have hp := _root_.congrArg (fun k => k p) hf
  simpa [circleAmbientHomotopyCurried, circleHomotopyCocone,
    realizationCocone, realizationExtension,
    Functor.LeftExtension.coconeAt, realizeSimplex,
    realizeSimplexHom] using hp

noncomputable def circleAmbientClassifyingSpaceHomotopy :
    (circleAmbientToNerve.comp circleNerveToAmbient).Homotopy
      (ContinuousMap.id CircleNerveRealization) where
  toContinuousMap :=
    { toFun := fun tx => circleAmbientHomotopyCurried tx.2 tx.1
      continuous_toFun := by
        exact
          (ContinuousMap.continuous_uncurry_of_continuous
              circleAmbientHomotopyCurried.hom).comp
            (continuous_snd.prodMk continuous_fst) }
  map_zero_left := by
    intro x
    let rep := realizationPointRepresentation CircleNerve x
    let j := realizationIndexOfSimplex rep.simplex
    have hs : SSet.yonedaEquiv j.hom = rep.simplex := by
      change SSet.yonedaEquiv (SSet.yonedaEquiv.symm rep.simplex) = _
      exact Equiv.apply_symm_apply SSet.yonedaEquiv rep.simplex
    have hrep :
        realizeSimplex (SSet.yonedaEquiv j.hom) rep.point = x := by
      simpa [hs] using rep.realize_eq
    have hcur := _root_.congrArg
        (fun k : C(unitInterval, CircleNerveRealization) => k 0)
        (circleAmbientHomotopyCurried_realizeSimplex j rep.point)
    rw [hrep] at hcur
    have hpath0 :
        circleAmbientHomotopyCurried x 0 =
          nerveEdge circleGenerator
            (clampUnit
              (affineHeight rep.simplex rep.point.down -
                (Int.floor (affineHeight rep.simplex rep.point.down) : ℝ))) := by
      calc
        circleAmbientHomotopyCurried x 0 =
            circleHomotopyPath (SSet.yonedaEquiv j.hom) rep.point 0 := hcur
        _ = circleLocalJoin
              (Int.floor (affineHeight rep.simplex rep.point.down))
              rep.simplex (0, rep.point) := by
          rw [hs]
          exact circleHomotopyPath_apply' (n := rep.n)
            (SSet.yonedaEquiv j.hom) rep.point 0
        _ = _ := circleLocalJoin_zero' (n := rep.n)
          (Int.floor (affineHeight rep.simplex rep.point.down))
          rep.simplex (0, rep.point)
    have hambient :
        circleNerveToAmbient x =
          circleCover (affineHeight rep.simplex rep.point.down) := by
      have hambient_rep :
          circleNerveToAmbient
              (realizeSimplex (SSet.yonedaEquiv j.hom) rep.point) =
            circleCover (affineHeight rep.simplex rep.point.down) := by
        rw [hs]
        exact circleNerveToAmbient_realizeSimplex
          (n := rep.n) rep.simplex rep.point
      calc
        circleNerveToAmbient x =
            circleNerveToAmbient
              (realizeSimplex (SSet.yonedaEquiv j.hom) rep.point) :=
          _root_.congrArg circleNerveToAmbient hrep.symm
        _ = _ := hambient_rep
    change circleAmbientHomotopyCurried x 0 =
      (circleAmbientToNerve.comp circleNerveToAmbient) x
    calc
      _ = nerveEdge circleGenerator
            (clampUnit
              (affineHeight rep.simplex rep.point.down -
                (Int.floor (affineHeight rep.simplex rep.point.down) : ℝ))) :=
        hpath0
      _ = periodicGenerator (affineHeight rep.simplex rep.point.down) := by
        symm
        exact periodicGenerator_floor _
      _ = circleAmbientToNerve
            (circleCover (affineHeight rep.simplex rep.point.down)) := by
        rw [periodicGenerator_apply]
      _ = circleAmbientToNerve (circleNerveToAmbient x) := by
        exact _root_.congrArg circleAmbientToNerve hambient.symm
  map_one_left := by
    intro x
    let rep := realizationPointRepresentation CircleNerve x
    let j := realizationIndexOfSimplex rep.simplex
    have hs : SSet.yonedaEquiv j.hom = rep.simplex := by
      change SSet.yonedaEquiv (SSet.yonedaEquiv.symm rep.simplex) = _
      exact Equiv.apply_symm_apply SSet.yonedaEquiv rep.simplex
    have hrep :
        realizeSimplex (SSet.yonedaEquiv j.hom) rep.point = x := by
      simpa [hs] using rep.realize_eq
    have hcur := _root_.congrArg
        (fun k : C(unitInterval, CircleNerveRealization) => k 1)
        (circleAmbientHomotopyCurried_realizeSimplex j rep.point)
    rw [hrep] at hcur
    calc
      circleAmbientHomotopyCurried x 1 =
          circleHomotopyPath (SSet.yonedaEquiv j.hom) rep.point 1 := hcur
      _ = circleLocalJoin
            (Int.floor (affineHeight rep.simplex rep.point.down))
            rep.simplex (1, rep.point) := by
        rw [hs]
        exact (circleHomotopyPath_apply' (n := rep.n)
          (SSet.yonedaEquiv j.hom) rep.point 1).symm
      _ = realizeSimplex rep.simplex rep.point :=
        circleLocalJoin_one' (n := rep.n)
          (Int.floor (affineHeight rep.simplex rep.point.down))
          rep.simplex (1, rep.point)
      _ = x := rep.realize_eq

/- The realization-side classifying-space step is now proved by the
   descended simplexwise homotopy above. -/
noncomputable def circleAmbientClassifyingSpaceStep :
    CircleAmbientClassifyingSpaceStep :=
  ⟨circleAmbientClassifyingSpaceHomotopy⟩

/- The unconditional ambient homotopy equivalence for the presented circle. -/
noncomputable def circleAmbientHomotopyEquiv :
    CircleNerveRealization ≃ₕ TopologicalCircle where
  toFun := circleNerveToAmbient
  invFun := circleAmbientToNerve
  left_inv := circleAmbientClassifyingSpaceStep
  right_inv := circleNerveToAmbient_right_homotopy

noncomputable def circlePresented_topologicalRealization_homotopyEquiv :
    CircleNerveRealization.{0} ≃ₕ TopologicalCircle :=
  circleAmbientHomotopyEquiv


end CircleNerveAmbient
end CompPath
end Path
end ComputationalPaths
