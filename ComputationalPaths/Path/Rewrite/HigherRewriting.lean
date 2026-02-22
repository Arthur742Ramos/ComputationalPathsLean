/-
# Higher-dimensional rewriting via polygraphs

This module packages lightweight data structures for 2- and 3-polygraphs and
their coherence data.  The definitions are intentionally small so that the
computational-path rewrite system can instantiate them without adding axioms.

## Key Results

- `TwoPolygraph`, `ThreePolygraph`: basic polygraph data.
- `homotopicalCompletion`: 3-cells given by proof equality.
- `CoherentPresentation`: a coherent 3-polygraph package.
- `squier_theorem`: coherence of the canonical completion.

## References

- Craig Squier, "Word problems and a homological finiteness condition for monoids"
- Yves Guiraud & Philippe Malbos, "Higher-dimensional rewriting"
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace HigherRewriting

universe u v

/-! ## 2-polygraphs -/

/-- A 2-polygraph: objects, 1-cells, and generating 2-cells (rewrite steps). -/
structure TwoPolygraph where
  /-- The 0-cells of the polygraph. -/
  Obj : Type u
  /-- The generating 1-cells between objects. -/
  OneCell : Obj → Obj → Type v
  /-- The generating 2-cells (one-step rewrites) between parallel 1-cells. -/
  TwoCell : {a b : Obj} → OneCell a b → OneCell a b → Prop

namespace TwoPolygraph

/-- Multi-step rewrite closure for a 2-polygraph. -/
inductive Rw {P : TwoPolygraph} {a b : P.Obj} :
    P.OneCell a b → P.OneCell a b → Prop
  | refl (p : P.OneCell a b) : Rw p p
  | tail {p q r : P.OneCell a b} : Rw p q → P.TwoCell q r → Rw p r

/-- Reflexive closure for polygraph rewrites. -/
@[simp] noncomputable def rw_refl {P : TwoPolygraph} {a b : P.Obj} (p : P.OneCell a b) :
    Rw p p :=
  Rw.refl p

/-- Lift a single step into the multi-step closure. -/
@[simp] noncomputable def rw_of_step {P : TwoPolygraph} {a b : P.Obj}
    {p q : P.OneCell a b} (h : P.TwoCell p q) :
    Rw p q :=
  Rw.tail (Rw.refl p) h

/-- Local confluence for a 2-polygraph. -/
noncomputable def LocallyConfluent (P : TwoPolygraph) : Prop :=
  ∀ {a b} {p q r : P.OneCell a b},
    P.TwoCell p q → P.TwoCell p r →
      ∃ s, Rw (P := P) q s ∧ Rw (P := P) r s

/-- Confluence for the multi-step rewrite closure. -/
noncomputable def Confluent (P : TwoPolygraph) : Prop :=
  ∀ {a b} {p q r : P.OneCell a b},
    Rw (P := P) p q → Rw (P := P) p r →
      ∃ s, Rw (P := P) q s ∧ Rw (P := P) r s

/-- Termination: every hom-set has a well-founded step relation. -/
noncomputable def Terminating (P : TwoPolygraph) : Prop :=
  ∀ {a b}, WellFounded (fun p q : P.OneCell a b => P.TwoCell q p)

/-- A 2-polygraph is convergent when it is terminating and confluent. -/
noncomputable def Convergent (P : TwoPolygraph) : Prop :=
  Terminating P ∧ Confluent P

end TwoPolygraph

/-! ## 3-polygraphs and coherence -/

/-- A 3-polygraph extends a 2-polygraph with 3-cells between parallel 2-cells. -/
structure ThreePolygraph extends TwoPolygraph where
  /-- The generating 3-cells between parallel 2-cells. -/
  ThreeCell :
    (a b : Obj) → (p q : OneCell a b) →
      TwoCell p q → TwoCell p q → Prop

/-- A 3-polygraph is coherent if every pair of parallel 2-cells is connected. -/
noncomputable def Coherent (P : ThreePolygraph) : Prop :=
  ∀ {a b} {p q : P.OneCell a b} (α β : P.TwoCell p q),
    P.ThreeCell a b p q α β

/-- A coherent presentation packages a 3-polygraph with its coherence proof. -/
structure CoherentPresentation where
  /-- The underlying 3-polygraph. -/
  polygraph : ThreePolygraph
  /-- Coherence witness. -/
  coherent : Coherent polygraph

/-! ## Homotopical completion -/

/-- The homotopical completion adds 3-cells given by proof equality. -/
noncomputable def homotopicalCompletion (P : TwoPolygraph) : ThreePolygraph :=
  { Obj := P.Obj
    OneCell := P.OneCell
    TwoCell := P.TwoCell
    ThreeCell := fun a b (p q : P.OneCell a b) (α β : P.TwoCell p q) => α = β }

/-- The homotopical completion is coherent by proof irrelevance. -/
theorem homotopicalCompletion_coherent (P : TwoPolygraph) :
    Coherent (homotopicalCompletion P) := by
  intro _ _ _ _ α β
  apply Subsingleton.elim

/-- The canonical coherent presentation obtained from homotopical completion. -/
noncomputable def homotopicalCompletionPresentation (P : TwoPolygraph) : CoherentPresentation :=
  { polygraph := homotopicalCompletion P
    coherent := homotopicalCompletion_coherent P }

/-! ## Squier theorem -/

/-- Squier-style statement: a convergent 2-polygraph has a coherent completion. -/
theorem squier_theorem (P : TwoPolygraph) (h : TwoPolygraph.Convergent P) :
    Coherent (homotopicalCompletion P) := by
  rcases h with ⟨_, _⟩
  exact homotopicalCompletion_coherent P

/-! ## Path rewriting instance -/

/-- The computational-path rewrite system as a 2-polygraph. -/
noncomputable def pathTwoPolygraph (A : Type u) : TwoPolygraph :=
  { Obj := A
    OneCell := fun a b => Path a b
    TwoCell := fun {a b} p q =>
      Nonempty (RwEq (A := A) (a := a) (b := b) p q) }

/-- The path 3-polygraph obtained via homotopical completion. -/
noncomputable def pathThreePolygraph (A : Type u) : ThreePolygraph :=
  homotopicalCompletion (pathTwoPolygraph A)

/-- The path rewrite system as a coherent presentation. -/
noncomputable def pathCoherentPresentation (A : Type u) : CoherentPresentation :=
  homotopicalCompletionPresentation (pathTwoPolygraph A)

/-! ## Summary -/

/-!
We introduced polygraph data for higher rewriting, defined homotopical
completion and coherent presentations, and recorded a Squier-style coherence
statement for convergent systems. The computational-path rewrite system
instantiates these definitions directly.
-/

end HigherRewriting
end Rewrite
end Path
end ComputationalPaths
