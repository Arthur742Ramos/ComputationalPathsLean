import ComputationalPaths.Path.CompPath.CircleTopologicalRealization
import ComputationalPaths.Path.Homotopy.PresentedGroupoidRealization

/-!
# Concrete ambient realization for the presented circle

The paper's concrete ambient space is the unit additive circle
`AddCircle (1 : ℝ)`.  The presented circle already has an integer winding
normal form, and the topological circle has the matching standard loops.  This
file turns that common winding coordinate into an explicit ambient path map
and a functor between the corresponding fundamental groupoids.

This is deliberately a fundamental-groupoid comparison.  It does not claim a
whole-space homotopy equivalence between the nerve realization and
`AddCircle 1`; that stronger statement requires a separate classifying-space
argument.
-/

namespace ComputationalPaths
namespace Path
namespace CompPath
namespace CircleAmbientRealization

open CategoryTheory
open CirclePresented
open CircleTopologicalRealization
open Presented
open scoped FundamentalGroupoid

attribute [local instance] _root_.Path.Homotopic.setoid

/-! ## Raw presented paths as ambient loops -/

abbrev RawPath :=
  Presented.RawPath CirclePresented.graph
    circleCompPathBase circleCompPathBase

abbrev PresentedClass := CirclePresented.PiOne

abbrev AmbientLoop := CircleTopologicalRealization.TopologicalLoopQuot

/-- The standard topological loop carrying a presented path's winding. -/
noncomputable def ambientPath (p : RawPath) :
    _root_.Path (0 : TopologicalCircle) 0 :=
  standardLoop (CirclePresented.winding p)

/-- The ambient loop class carried by a raw presented path. -/
noncomputable def ambientArrow (p : RawPath) : AmbientLoop :=
  Quotient.mk' (ambientPath p)

theorem ambientArrow_respects_homotopy
    {p q : RawPath}
    (h : Presented.Homotopy CirclePresented.presentation p q) :
    ambientArrow p = ambientArrow q := by
  change Quotient.mk'
      (standardLoop (CirclePresented.winding p)) =
    Quotient.mk'
      (standardLoop (CirclePresented.winding q))
  rw [CirclePresented.homotopy_winding h]

/-- Descend the raw ambient loop map to presented path classes. -/
noncomputable def classToAmbient : PresentedClass → AmbientLoop :=
  Quot.lift ambientArrow (by
    intro p q h
    exact ambientArrow_respects_homotopy h)

theorem classToAmbient_ofRaw (p : RawPath) :
    classToAmbient
        (Presented.PiOne.ofRaw
          (P := CirclePresented.presentation) p) =
      ambientArrow p := by
  rfl

theorem classToAmbient_winding (x : PresentedClass) :
    topologicalWinding (classToAmbient x) =
      CirclePresented.encode x := by
  induction x using Quot.ind with
  | _ p =>
      change windingPath (standardLoop (CirclePresented.winding p)) =
        CirclePresented.winding p
      exact windingPath_standardLoop _

/-! ## Multiplication and the explicit path composition witness -/

theorem ambientPath_trans_homotopic
    (p q : RawPath) :
    (ambientPath (Presented.RawPath.trans p q)).Homotopic
      ((ambientPath p).trans (ambientPath q)) := by
  simpa [ambientPath, CirclePresented.winding,
    windingPath_trans, windingPath_standardLoop] using
    (standardLoop_homotopic
      ((standardLoop (CirclePresented.winding p)).trans
        (standardLoop (CirclePresented.winding q))))

theorem classToAmbient_id :
    classToAmbient (Presented.PiOne.id : PresentedClass) =
      Quotient.mk' (_root_.Path.refl (0 : TopologicalCircle)) := by
  change Quotient.mk' (standardLoop 0) =
    Quotient.mk' (_root_.Path.refl (0 : TopologicalCircle))
  have hzero : standardLoop 0 =
      _root_.Path.refl (0 : TopologicalCircle) := by
    ext t
    simp [standardLoop, circleCover]
  rw [hzero]

theorem classToAmbient_mul (x y : PresentedClass) :
    classToAmbient (Presented.PiOne.mul x y) =
      _root_.Path.Homotopic.Quotient.comp
        (classToAmbient x) (classToAmbient y) := by
  induction x using Quot.ind with
  | _ p =>
      induction y using Quot.ind with
      | _ q =>
          change Quotient.mk' (ambientPath (Presented.RawPath.trans p q)) =
            Quotient.mk'
              ((ambientPath p).trans (ambientPath q))
          exact Quotient.sound (ambientPath_trans_homotopic p q)

/-! ## A concrete ambient comparison functor -/

/-- Every presented circle object is sent to the additive-circle basepoint. -/
noncomputable def comparisonFunctor :
    Presented.Realization.Object CirclePresented.presentation ⥤
      _root_.FundamentalGroupoid TopologicalCircle where
  obj _ := { as := (0 : TopologicalCircle) }
  map := by
    intro X Y f
    cases X
    cases Y
    exact classToAmbient f
  map_id := by
    intro X
    cases X
    exact classToAmbient_id
  map_comp := by
    intro X Y Z f g
    cases X
    cases Y
    cases Z
    exact classToAmbient_mul f g

/-- The ambient circle has a path from the basepoint to every point. -/
noncomputable def pathToPoint (a : ℝ) :
    _root_.Path (0 : TopologicalCircle) (circleCover a) where
  toFun t := circleCover ((t : ℝ) * a)
  continuous_toFun :=
    continuous_circleCover.comp
      (continuous_subtype_val.mul continuous_const)
  source' := by simp [circleCover]
  target' := by simp [circleCover]

noncomputable instance comparisonFunctor_full :
    comparisonFunctor.Full where
  map_surjective := by
    intro X Y q
    cases X
    cases Y
    let q' : AmbientLoop := by
      simpa [comparisonFunctor] using q
    refine ⟨CirclePresented.decode (topologicalWinding q'), ?_⟩
    have hq : comparisonFunctor.map
          (CirclePresented.decode (topologicalWinding q')) = q' := by
      simpa [comparisonFunctor, CirclePresented.decode, classToAmbient,
        ambientArrow, ambientPath] using decode_topologicalWinding q'
    simpa [q', comparisonFunctor] using hq

noncomputable instance comparisonFunctor_faithful :
    comparisonFunctor.Faithful where
  map_injective := by
    intro X Y f g h
    cases X
    cases Y
    have h' : classToAmbient f = classToAmbient g := by
      simpa [comparisonFunctor] using h
    have hencode : CirclePresented.encode f = CirclePresented.encode g := by
      calc
        CirclePresented.encode f = topologicalWinding (classToAmbient f) :=
          (classToAmbient_winding f).symm
        _ = topologicalWinding (classToAmbient g) :=
          _root_.congrArg topologicalWinding h'
        _ = CirclePresented.encode g := classToAmbient_winding g
    calc
      f = CirclePresented.piOneEquivInt.invFun
          (CirclePresented.piOneEquivInt.toFun f) :=
        (CirclePresented.piOneEquivInt.left_inv f).symm
      _ = CirclePresented.piOneEquivInt.invFun
          (CirclePresented.piOneEquivInt.toFun g) :=
        _root_.congrArg CirclePresented.piOneEquivInt.invFun hencode
      _ = g := CirclePresented.piOneEquivInt.left_inv g

noncomputable instance comparisonFunctor_essSurj :
    comparisonFunctor.EssSurj where
  mem_essImage Y := by
    cases Y with
    | mk y =>
        obtain ⟨a, _, rfl⟩ :=
          AddCircle.eq_coe_Ico (p := (1 : ℝ)) y
        refine ⟨
          Presented.Realization.Object.ofPoint
            (P := CirclePresented.presentation) circleCompPathBase,
          ⟨?_⟩⟩
        simpa [comparisonFunctor] using
          (asIso (Quotient.mk' (pathToPoint a)))

noncomputable instance comparisonFunctor_isEquivalence :
    comparisonFunctor.IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

/-- Fundamental-groupoid equivalence between the presented circle and
`AddCircle 1`. -/
noncomputable def circleAmbientGroupoidEquivalence :
    Presented.Realization.Object CirclePresented.presentation ≌
      _root_.FundamentalGroupoid TopologicalCircle :=
  comparisonFunctor.asEquivalence

/-! ## A compact concrete certificate -/

/-- The data connecting the presented circle to its actual ambient circle. -/
structure Certificate where
  rawPath {p : RawPath} :
    _root_.Path (0 : TopologicalCircle) 0
  rawArrow {p : RawPath} : AmbientLoop
  groupoidEquivalence :
    Presented.Realization.Object CirclePresented.presentation ≌
      _root_.FundamentalGroupoid TopologicalCircle

noncomputable def certificate : Certificate where
  rawPath := fun {p} => ambientPath p
  rawArrow := fun {p} => ambientArrow p
  groupoidEquivalence := circleAmbientGroupoidEquivalence

end CircleAmbientRealization
end CompPath
end Path
end ComputationalPaths
