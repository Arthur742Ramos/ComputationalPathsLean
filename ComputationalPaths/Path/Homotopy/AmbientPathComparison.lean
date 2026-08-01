import ComputationalPaths.Path.Homotopy.PresentedGroupoidRealization
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Ambient comparison for presented computational paths

The realization theorem for a presented path groupoid compares the
presentation with the fundamental groupoid of its geometric realization.
This file adds the missing ambient-space interface: an arbitrary topological
space `X` can be compared with the realization only after supplying an
explicit homotopy equivalence

```
  topologicalRealization P ≃ₕ X.
```

Under that hypothesis the presented groupoid is transported to the
fundamental groupoid of `X`.  Thus the formalization does not silently claim
that every presentation reconstructs every ambient space.
-/

namespace ComputationalPaths
namespace Path
namespace Presented
namespace Realization

open CategoryTheory
open scoped ContinuousMap
open scoped FundamentalGroupoid

universe u v

variable {G : Graph.{u, v}} (P : Presentation G)

/-! ## The ambient comparison functor -/

/-- Transport the canonical realization comparison along a supplied ambient
homotopy equivalence. -/
noncomputable def ambientComparisonFunctor
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X) :
    Object P ⥤ FundamentalGroupoid X :=
  topologicalComparisonFunctor P ⋙
    πₘ (TopCat.ofHom h.toFun)

/-- The two ingredients of the ambient comparison are equivalences: the first
comes from realization of the presented groupoid and the second from
homotopy invariance of the fundamental groupoid. -/
noncomputable def ambientComparisonEquivalence
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X) :
    Object P ≌ FundamentalGroupoid X :=
  (topologicalComparisonFunctor P).asEquivalence.trans
    (FundamentalGroupoidFunctor.equivOfHomotopyEquiv h)

/-- The functor underlying `ambientComparisonEquivalence` is the explicitly
defined comparison functor. -/
@[simp]
theorem ambientComparisonEquivalence_functor
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X) :
    (ambientComparisonEquivalence P h).functor = ambientComparisonFunctor P h :=
  rfl

/-! ## Explicit reconstruction data -/

/-- Data required to reconstruct an ambient space from a presented path
groupoid.  The homotopy equivalence is intentionally an explicit hypothesis;
it is not inferred from the presentation alone. -/
structure AmbientPathComparison (X : TopCat.{max u v}) where
  realizationEquiv : topologicalRealization P ≃ₕ X

/-- The presentation-to-ambient fundamental-groupoid equivalence carried by
explicit reconstruction data. -/
noncomputable def AmbientPathComparison.fundamentalGroupoidEquivalence
    {X : TopCat.{max u v}} (data : AmbientPathComparison P X) :
    Object P ≌ FundamentalGroupoid X :=
  ambientComparisonEquivalence P data.realizationEquiv

/-- A proposition-level interface when the reconstruction witness is
available only existentially. -/
def AmbientPathComparisonStatement (X : TopCat.{max u v}) : Prop :=
  Nonempty (topologicalRealization P ≃ₕ X)

/-- An explicit reconstruction witness produces the corresponding ambient
fundamental-groupoid equivalence. -/
theorem ambientComparisonStatement
    {X : TopCat.{max u v}}
    (h : AmbientPathComparisonStatement P X) :
    Nonempty (Object P ≌ FundamentalGroupoid X) := by
  let reconstruction : topologicalRealization P ≃ₕ X := Classical.choice h
  exact ⟨ambientComparisonEquivalence P reconstruction⟩

/-! ## Computational-path coherence retained by the interface -/

/-- The ambient comparison does not discard the computational associativity
certificate at a presentation vertex. -/
noncomputable def ambientVertexAssociativityCoherence
    {a : G.Point} (x y z : PiOne P a) :
    RwEq
      (Path.trans (vertexAssociativityPath P x y z)
        (Path.refl (PiOne.mul x (PiOne.mul y z))))
      (vertexAssociativityPath P x y z) :=
  vertexAssociativityCoherence P x y z

end Realization
end Presented
end Path
end ComputationalPaths
