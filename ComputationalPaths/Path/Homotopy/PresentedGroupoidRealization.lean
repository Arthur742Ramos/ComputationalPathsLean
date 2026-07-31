/-
# Simplicial and topological realization of presented path groupoids

Every presented computational path space determines a strict groupoid.  This
module turns that groupoid into a Mathlib groupoid, takes its simplicial nerve,
and then takes Mathlib's geometric realization.

The nerve is fully faithful: its Mathlib homotopy category is isomorphic to the
original presented path groupoid.  This is the general combinatorial
realization theorem available in Mathlib.

The canonical forward functor

```
P ⥤ FundamentalGroupoid (SSet.toTop.obj (nerve P))
```

is constructed explicitly from realized vertices and edges. Degenerate edges
prove the identity law, while realized 2-simplices prove the composition law.
The topological edge-path theorem gives

```
FundamentalGroupoid (SSet.toTop.obj (nerve P)) ≌ P
```

unconditionally. Full faithfulness follows by realizing the under-category
projection as a covering map, lifting paths and homotopies, and using the
contractibility of its total realization. Essential surjectivity follows from
the colimit presentation and path-connectedness of every topological simplex.
-/

import ComputationalPaths.Path.Homotopy.PresentedFundamentalGroup
import ComputationalPaths.Path.Homotopy.TopologicalNerveComparison
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.CategoryTheory.Category.Grpd

namespace ComputationalPaths
namespace Path
namespace Presented
namespace Realization

open CategoryTheory

universe u v

variable {G : Graph.{u, v}} (P : Presentation G)

/-- Universe-lifted objects of the presented path groupoid. -/
structure Object (P : Presentation G) : Type (max u v) where
  as : G.Point

namespace Object

/-- Include a point of the presentation as an object of its Mathlib groupoid. -/
def ofPoint (a : G.Point) : Object P :=
  ⟨a⟩

end Object

noncomputable instance objectCategory :
    Category.{max u v} (Object P) where
  Hom X Y := PathClass P X.as Y.as
  id X := PathClass.id X.as
  comp f g := PathClass.comp f g
  id_comp := PathClass.comp_id_left
  comp_id := PathClass.comp_id_right
  assoc := PathClass.comp_assoc

noncomputable instance objectGroupoid :
    CategoryTheory.Groupoid.{max u v} (Object P) where
  inv f := PathClass.inv f
  inv_comp := PathClass.inv_comp
  comp_inv := PathClass.comp_inv

/-- The presented path groupoid as an object of Mathlib's category of
groupoids. -/
noncomputable def mathlibGroupoid :
    Grpd.{max u v, max u v} :=
  Grpd.of (Object P)

/-- Simplicial nerve of a presented path groupoid. -/
noncomputable def nerve : SSet.{max u v} :=
  CategoryTheory.nerve (Object P)

/-- Mathlib geometric realization of the presented path groupoid's nerve. -/
noncomputable def topologicalRealization : TopCat.{max u v} :=
  SSet.toTop.obj (nerve P)

/-- The canonical functor from the presented path groupoid to the topological
fundamental groupoid of its geometric realization. It is essentially
surjective by `topologicalComparisonFunctor_essSurj`. -/
noncomputable def topologicalComparisonFunctor :
    Object P ⥤ FundamentalGroupoid (topologicalRealization P) :=
  TopologicalNerve.nerveRealizationFunctor

noncomputable instance topologicalComparisonFunctor_essSurj :
    (topologicalComparisonFunctor P).EssSurj := by
  change
    (TopologicalNerve.nerveRealizationFunctor
      (C := Object P)).EssSurj
  infer_instance

noncomputable instance topologicalComparisonFunctor_full :
    (topologicalComparisonFunctor P).Full := by
  change
    (TopologicalNerve.nerveRealizationFunctor
      (C := Object P)).Full
  infer_instance

noncomputable instance topologicalComparisonFunctor_faithful :
    (topologicalComparisonFunctor P).Faithful := by
  change
    (TopologicalNerve.nerveRealizationFunctor
      (C := Object P)).Faithful
  infer_instance

noncomputable instance topologicalComparisonFunctor_isEquivalence :
    (topologicalComparisonFunctor P).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

/-- **General nerve recovery.**  The homotopy category of the nerve is
isomorphic to the presented path groupoid. -/
noncomputable def hoNerveIso :
    SSet.hoFunctor.obj (nerve P) ≅ Cat.of (Object P) :=
  CategoryTheory.nerveFunctorCompHoFunctorIso.app (Cat.of (Object P))

/-- Named proposition recording the general topological comparison. -/
def TopologicalComparisonStatement : Prop :=
  Nonempty
    (FundamentalGroupoid (topologicalRealization P) ≌ Object P)

/-- Constructor from an available equivalence instance. -/
theorem topologicalComparisonStatement_of_isEquivalence
    [(topologicalComparisonFunctor P).IsEquivalence] :
    TopologicalComparisonStatement P :=
  ⟨(topologicalComparisonFunctor P).asEquivalence.symm⟩

/-- Constructor from full and faithful instances together with essential
surjectivity. -/
theorem topologicalComparisonStatement_of_full_faithful
    [(topologicalComparisonFunctor P).Full]
    [(topologicalComparisonFunctor P).Faithful] :
    TopologicalComparisonStatement P := by
  letI : (topologicalComparisonFunctor P).IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }
  exact topologicalComparisonStatement_of_isEquivalence P

/-- **Topological realization theorem.** The fundamental groupoid of the
genuine geometric realization of a presented path groupoid is equivalent to
the original presented groupoid. -/
noncomputable def topologicalFundamentalGroupoidEquivalence :
    FundamentalGroupoid (topologicalRealization P) ≌ Object P :=
  (topologicalComparisonFunctor P).asEquivalence.symm

/-- Unconditional public proof of the topological comparison statement. -/
theorem topologicalComparisonStatement :
    TopologicalComparisonStatement P :=
  ⟨topologicalFundamentalGroupoidEquivalence P⟩

/-- Computational-path associativity certificate inherited by the realized
presentation's vertex group. -/
noncomputable def vertexAssociativityPath
    {a : G.Point} (x y z : PiOne P a) :
    Path
      (PiOne.mul (PiOne.mul x y) z)
      (PiOne.mul x (PiOne.mul y z)) :=
  PiOne.mul_assoc_path x y z

/-- The associativity certificate is coherent under the core global rewrite
calculus. -/
noncomputable def vertexAssociativityCoherence
    {a : G.Point} (x y z : PiOne P a) :
    RwEq
      (Path.trans (vertexAssociativityPath P x y z)
        (Path.refl (PiOne.mul x (PiOne.mul y z))))
      (vertexAssociativityPath P x y z) :=
  rweq_cmpA_refl_right (vertexAssociativityPath P x y z)

end Realization
end Presented
end Path
end ComputationalPaths
