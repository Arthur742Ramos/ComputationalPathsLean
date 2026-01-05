/-
# Confluence Axioms (opt-in)

The core development keeps confluence properties *parametric* in
typeclass assumptions (`HasLocalConfluenceProp`, `HasStepStripProp`)
so the assumptions stay explicit and discharge-friendly.

If you want to *use* confluence-dependent results without threading
typeclass hypotheses everywhere, import this file. It:

1. Adds global instances of `HasLocalConfluenceProp` and `HasStepStripProp`
   as **kernel axioms**, and
2. Provides the derived instances `HasLocalConfluence` and `HasStepStrip`.

This is intentionally **not** imported by `ComputationalPaths` by default.

## Mathematical Background

The confluence axioms are justified by metatheoretic analysis:

### Local Confluence (`HasLocalConfluenceProp`)

For any two single-step rewrites `Step p q` and `Step p r` from the same
source path, there exists a common descendant reachable from both.

**Justification**: All critical pairs have explicit join proofs in
`ConfluenceProof.lean`. Non-overlapping steps commute via congruence.

### Strip Lemma (`HasStepStripProp`)

For a single-step rewrite `Step p q` and a multi-step rewrite `Rw p r`,
there exists a common descendant reachable from both.

**Justification**: Newman's lemma: local confluence + termination implies
confluence (and hence the strip lemma). Termination is established via
RPO ordering in `Termination.lean`.
-/

import ComputationalPaths.Path.Rewrite.ConfluenceConstructive

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace ConfluenceConstructive

universe u

/-- Global local confluence axiom (kernel axiom, opt-in). -/
axiom instHasLocalConfluencePropAxiom : HasLocalConfluenceProp.{u}

attribute [instance] instHasLocalConfluencePropAxiom

/-- Global strip lemma axiom (kernel axiom, opt-in). -/
axiom instHasStepStripPropAxiom : HasStepStripProp.{u}

attribute [instance] instHasStepStripPropAxiom

end ConfluenceConstructive
end Rewrite
end Path
end ComputationalPaths
