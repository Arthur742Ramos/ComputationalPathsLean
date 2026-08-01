import ComputationalPaths.Path.Homotopy.AmbientPathComparison
import ComputationalPaths.Path.Homotopy.PresentedGeometricAdapter

/-!
# Ambient geometric adapter for presented computational paths

The presented geometric adapter lands in the nerve realization of the
presented path groupoid.  This file transports the same computational traces
through an explicit homotopy equivalence

```
  topologicalRealization P ≃ₕ X
```

to an ambient topological space `X`.  The equivalence is an input: the
presentation alone does not determine an arbitrary ambient space.
-/

namespace ComputationalPaths
namespace Path
namespace Presented
namespace Realization
namespace AmbientAdapter

open CategoryTheory
open scoped ContinuousMap
open scoped FundamentalGroupoid
open GeometricTopology

attribute [local instance] _root_.Path.Homotopic.setoid

universe u v

variable {G : Graph.{u, v}} (P : Presentation G)

/-! ## Transporting the primitive geometric system -/

/-- The presented edge system transported to the ambient space. -/
noncomputable def ambientStepSystem
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X) :
    GeometricTopology.GeometricStepSystem X
      (GeometricAdapter.EdgeStep G) where
  src s := h.toFun ((GeometricAdapter.presentedStepSystem P).src s)
  tgt s := h.toFun ((GeometricAdapter.presentedStepSystem P).tgt s)
  realize s :=
    (GeometricAdapter.presentedStepSystem P).realize s |>.map h.toFun.continuous

/-! ## Mapping traces and coherent open paths -/

/-- Map a presented geometric trace through the ambient homotopy equivalence. -/
noncomputable def mapTrace
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X)
    {a b : topologicalRealization P}
    (t : GeometricTrace (GeometricAdapter.presentedStepSystem P) a b) :
    GeometricTrace (ambientStepSystem P h) (h.toFun a) (h.toFun b) :=
  match t with
  | GeometricTrace.refl a => GeometricTrace.refl (h.toFun a)
  | GeometricTrace.single s =>
      by simpa [ambientStepSystem] using
        (GeometricTrace.single (S := ambientStepSystem P h) s)
  | GeometricTrace.trans p q =>
      GeometricTrace.trans (mapTrace h p) (mapTrace h q)
  | GeometricTrace.symm p => GeometricTrace.symm (mapTrace h p)

theorem mapTrace_realize
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X)
    {a b : topologicalRealization P}
    (t : GeometricTrace (GeometricAdapter.presentedStepSystem P) a b) :
    GeometricTrace.realize (mapTrace P h t) =
      (GeometricTrace.realize t).map h.toFun.continuous := by
  induction t with
  | refl a =>
      ext t
      rfl
  | single s =>
      simp [mapTrace, GeometricTrace.realize, ambientStepSystem]
  | trans p q ihp ihq =>
      simp [mapTrace, GeometricTrace.realize, ambientStepSystem, ihp, ihq]
  | symm p ih =>
      simp [mapTrace, GeometricTrace.realize, ambientStepSystem, ih]

/-- Map an open geometric computational path, preserving its coherence witness. -/
noncomputable def mapOpenPath
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X)
    {a b : topologicalRealization P}
    (p : OpenGeometricCompPath
      (GeometricAdapter.presentedStepSystem P) a b) :
    OpenGeometricCompPath (ambientStepSystem P h) (h.toFun a) (h.toFun b) where
  trace := mapTrace P h p.trace
  geometric := p.geometric.map h.toFun.continuous
  coherent := by
    rw [mapTrace_realize P h p.trace]
    exact p.coherent.map h.toFun

/-! ## Raw presented paths in the ambient space -/

/-- The coherent ambient path associated to a raw presented path. -/
noncomputable def rawPathToAmbientGeometric
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X)
    {x y : G.Point} (p : RawPath G x y) :
    OpenGeometricCompPath (ambientStepSystem P h)
      (h.toFun
        (TopologicalNerve.nerveVertex
          (Object.ofPoint (P := P) x)))
      (h.toFun
        (TopologicalNerve.nerveVertex
          (Object.ofPoint (P := P) y)) : X) :=
  mapOpenPath P h (GeometricAdapter.rawPathToGeometric P p)

/-- The ambient geometric path associated to a primitive presentation edge. -/
noncomputable def ambientGeometricPath
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X)
    {x y : G.Point} (e : G.Edge x y) :
    _root_.Path
      (h.toFun
        (TopologicalNerve.nerveVertex
          (Object.ofPoint (P := P) x)))
      (h.toFun
        (TopologicalNerve.nerveVertex
          (Object.ofPoint (P := P) y)) : X) :=
  (rawPathToAmbientGeometric P h (RawPath.edge e)).geometric

theorem ambientGeometricPath_is_map
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X)
    {x y : G.Point} (e : G.Edge x y) :
    ambientGeometricPath P h e =
      (GeometricAdapter.edgeGeometricPath P e).map h.toFun.continuous := by
  rfl

/-! This explicit composition keeps the multi-step computational path visible. -/

/-- The ambient path obtained by composing two transported raw paths. -/
noncomputable def ambientRawPathTransPath
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X)
    {x y z : G.Point} (p : RawPath G x y) (q : RawPath G y z) :
    _root_.Path
      (h.toFun
        (TopologicalNerve.nerveVertex
          (Object.ofPoint (P := P) x)))
      (h.toFun
        (TopologicalNerve.nerveVertex
          (Object.ofPoint (P := P) z)) : X) :=
  (rawPathToAmbientGeometric P h p).geometric.trans
    (rawPathToAmbientGeometric P h q).geometric

theorem rawPathToAmbientGeometric_trans
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X)
    {x y z : G.Point} (p : RawPath G x y) (q : RawPath G y z) :
    (rawPathToAmbientGeometric P h (RawPath.trans p q)).geometric =
      ambientRawPathTransPath P h p q := by
  simp [rawPathToAmbientGeometric, mapOpenPath,
    GeometricAdapter.rawPathToGeometric, GeometricTopology.openTrans,
    ambientRawPathTransPath]

/-! ## Ambient fundamental-groupoid arrows -/

/-- The ambient fundamental-groupoid arrow carried by a transported path. -/
noncomputable def ambientGeometricArrow
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X)
    {x y : G.Point} (p : RawPath G x y) :
    FundamentalGroupoid.fromTop
        (h.toFun
          (TopologicalNerve.nerveVertex
            (Object.ofPoint (P := P) x))) ⟶
      FundamentalGroupoid.fromTop
        (h.toFun
          (TopologicalNerve.nerveVertex
            (Object.ofPoint (P := P) y)) : X) :=
  (πₘ (TopCat.ofHom h.toFun)).map
    (GeometricAdapter.geometricArrow P p)

/-- The transported arrow is the quotient of the explicitly mapped ambient path. -/
theorem ambientGeometricArrow_is_path_map
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X)
    {x y : G.Point} (p : RawPath G x y) :
    ambientGeometricArrow P h p =
      Quotient.mk' (rawPathToAmbientGeometric P h p).geometric := by
  rfl

/-- The geometric adapter agrees with the paper's ambient comparison functor. -/
theorem rawPathAmbientGeometricArrow_is_comparison
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X)
    {x y : G.Point} (p : RawPath G x y) :
    ambientGeometricArrow P h p =
      (ambientComparisonFunctor P h).map
        (PathClass.ofRaw (P := P) p) := by
  change
    (πₘ (TopCat.ofHom h.toFun)).map
        (GeometricAdapter.geometricArrow P p) =
      (πₘ (TopCat.ofHom h.toFun)).map
        ((topologicalComparisonFunctor P).map
          (PathClass.ofRaw (P := P) p))
  rw [GeometricAdapter.rawPathGeometricArrow_is_comparison P p]

/-! ## A reusable ambient certificate -/

/-- The full ambient data attached to a presented path space and its witness. -/
structure Certificate
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X) where
  stepSystem : GeometricTopology.GeometricStepSystem X
    (GeometricAdapter.EdgeStep G)
  rawPath {x y : G.Point} (p : RawPath G x y) :
    OpenGeometricCompPath (ambientStepSystem P h)
      (h.toFun
        (TopologicalNerve.nerveVertex
          (Object.ofPoint (P := P) x)))
      (h.toFun
        (TopologicalNerve.nerveVertex
          (Object.ofPoint (P := P) y)) : X)
  rawPathArrow {x y : G.Point} (p : RawPath G x y) :
    ambientGeometricArrow P h p =
      (ambientComparisonFunctor P h).map
        (PathClass.ofRaw (P := P) p)
  fundamentalGroupoidEquivalence :
    Object P ≌ FundamentalGroupoid X

noncomputable def certificate
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X) : Certificate P h where
  stepSystem := ambientStepSystem P h
  rawPath := rawPathToAmbientGeometric P h
  rawPathArrow := rawPathAmbientGeometricArrow_is_comparison P h
  fundamentalGroupoidEquivalence := ambientComparisonEquivalence P h

end AmbientAdapter
end Realization
end Presented
end Path
end ComputationalPaths
