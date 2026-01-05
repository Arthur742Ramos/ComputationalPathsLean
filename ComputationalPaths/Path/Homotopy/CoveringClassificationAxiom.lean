/-
# Covering Space Classification (assumption-free, opt-in)

The core development keeps the Galois correspondence theorem *parametric* in
the typeclass `HasCoveringEquivSubgroup` (see `CoveringClassification.lean`) so
the assumption stays explicit and discharge-friendly.

If you want to *use* the classification results without threading that typeclass
hypothesis everywhere, import this file. It:

1. Adds a global instance `HasCoveringEquivSubgroup` as a **kernel axiom**, and
2. Exports a wrapper `galois_correspondence'` with no extra parameters.

This is intentionally **not** imported by `ComputationalPaths` by default.

## Mathematical Background

The Galois correspondence between covering spaces and subgroups of π₁ is a deep
result from algebraic topology, requiring:
- Path lifting properties
- Homotopy lifting properties
- Local path-connectivity and semi-local simple connectivity

A full constructive proof would require significant infrastructure for
covering space functoriality.
-/

import ComputationalPaths.Path.Homotopy.CoveringClassification

namespace ComputationalPaths
namespace Path
namespace CoveringClassification

universe u

/-- Global covering classification instance (kernel axiom, opt-in). -/
axiom instHasCoveringEquivSubgroupAxiom : HasCoveringEquivSubgroup.{u}

attribute [instance] instHasCoveringEquivSubgroupAxiom

/-- Assumption-free wrapper: Galois correspondence. -/
noncomputable def galois_correspondence' {A : Type u} (a : A) :
    SimpleEquiv (CoveringOf A a) (Subgroup A a) :=
  galois_correspondence a

end CoveringClassification
end Path
end ComputationalPaths
