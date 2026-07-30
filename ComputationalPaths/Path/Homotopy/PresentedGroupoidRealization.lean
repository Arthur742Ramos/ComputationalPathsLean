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
The further topological statement

```
FundamentalGroupoid (SSet.toTop.obj (nerve P)) ≌ P
```

requires proving that this canonical functor is full and faithful: the
topological edge-path theorem for geometric realizations. Essential
surjectivity is proved here from the colimit presentation and path-connectedness
of every topological simplex. Mathlib v4.24 does not yet provide the remaining
edge-path theorem. The circle comparison is
proved directly by covering-space methods in
`CircleTopologicalRealization.lean`.
-/

import ComputationalPaths.Path.Homotopy.PresentedFundamentalGroup
import ComputationalPaths.Path.Homotopy.TopologicalNerve
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

/-- **General nerve recovery.**  The homotopy category of the nerve is
isomorphic to the presented path groupoid. -/
noncomputable def hoNerveIso :
    SSet.hoFunctor.obj (nerve P) ≅ Cat.of (Object P) :=
  CategoryTheory.nerveFunctorCompHoFunctorIso.app (Cat.of (Object P))

/-- Named statement of the remaining general topological comparison.  It is
kept as a proposition rather than an axiom or typeclass instance. The explicit
candidate equivalence is `topologicalComparisonFunctor`. -/
def TopologicalComparisonStatement : Prop :=
  Nonempty
    (FundamentalGroupoid (topologicalRealization P) ≌ Object P)

/-- The edge-path theorem would close the comparison by proving that the
canonical realization functor is an equivalence. -/
theorem topologicalComparisonStatement_of_isEquivalence
    [(topologicalComparisonFunctor P).IsEquivalence] :
    TopologicalComparisonStatement P :=
  ⟨(topologicalComparisonFunctor P).asEquivalence.symm⟩

/-- Since essential surjectivity is proved, the full topological comparison is
reduced exactly to the edge-path functor being full and faithful. -/
theorem topologicalComparisonStatement_of_full_faithful
    [(topologicalComparisonFunctor P).Full]
    [(topologicalComparisonFunctor P).Faithful] :
    TopologicalComparisonStatement P := by
  letI : (topologicalComparisonFunctor P).IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }
  exact topologicalComparisonStatement_of_isEquivalence P

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
