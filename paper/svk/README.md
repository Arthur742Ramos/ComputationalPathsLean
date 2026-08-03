# SVK revision package

This directory contains the revised manuscript and point-by-point response to
Reviewer 1.

## Build

```bash
cd paper/svk
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error response_to_reviewer.tex
```

Generated deliverables:

- `main.pdf` — revised manuscript
- `response_to_reviewer.pdf` — response letter

## Reproduce source claims

```bash
python3 paper/svk/check_stats.py
python3 scripts/check_invariants.py

lake build ComputationalPaths.Path.CompPath.PushoutCompPath
lake build ComputationalPaths.Path.CompPath.PushoutSVKInstances
lake build ComputationalPaths.Path.CompPath.ScopedSeifertVanKampen
lake build ComputationalPaths.Path.CompPath.ClassicalPresentationsScoped
lake build ComputationalPaths.Path.Homotopy.PresentedFundamentalGroup
lake build ComputationalPaths.Path.Homotopy.TopologicalNerve
lake build ComputationalPaths.Path.Homotopy.TopologicalNerveContractible
lake build ComputationalPaths.Path.Homotopy.TopologicalRealizationOpen
lake build ComputationalPaths.Path.Homotopy.TopologicalSimplexStar
lake build ComputationalPaths.Path.Homotopy.TopologicalNerveCover
lake build ComputationalPaths.Path.Homotopy.TopologicalNerveComparison
lake build ComputationalPaths.Path.Homotopy.PresentedGroupoidRealization
lake build ComputationalPaths.Path.Topology.TopologicalCompPathGroupoidLaws
lake build ComputationalPaths.Path.Homotopy.PresentedContinuousGeometricAdapter
lake build ComputationalPaths.Path.Homotopy.PresentedAmbientContinuousGeometricAdapter
lake build ComputationalPaths.Path.CompPath.CirclePresented
lake build ComputationalPaths.Path.CompPath.CircleTopologicalRealization
lake build ComputationalPaths.Path.CompPath.CircleNerveAmbient
lake build ComputationalPaths.Path.CompPath.PresentedSeifertVanKampen
lake build ComputationalPaths.Path.Homotopy.Fibration
lake build ComputationalPaths.Path.CompPath.SuspensionDeep
```

The manuscript distinguishes presented computational fundamental groups,
global-rule `PathRwQuot` loop fibers, and completed expression quotients.  The
headline theorem is the proved presented SVK equivalence; the global-rule SVK
schema remains separately conditional.  The circle presentation is additionally
identified with Mathlib's topological fundamental group of `AddCircle 1`.
Every presented path groupoid also has a checked nerve/geometric realization
and homotopy-category recovery theorem. The canonical functor to the
topological fundamental groupoid is constructed and proved essentially
surjective, full, and faithful, yielding a public equivalence with the original
presented groupoid.  The proof descends degeneracy-aware open stars through the
realization quotient, partitions their preimages into disjoint lifted sheets,
constructs sheet homeomorphisms, proves the under-category projection is a
Mathlib covering map, and applies path and homotopy lifting.
The circle instance additionally proves an unconditional homotopy equivalence
between the nerve realization of the presented circle and `TopologicalCircle`.
The total endpoint-varying computational-path quotient now also has a complete
unconditional topological groupoid certificate: source, target, identity,
inverse, and composition are continuous, and the endpoint, unit, inverse, and
associativity laws are proved. Composition uses the quotient-compatible final
topology on composable classes. The inherited product/subspace topology remains
the separate conditional interface because products of quotient maps need not
be quotient maps in arbitrary topological spaces. The certificate is
specialized both to every presented realization and to every ambient homotopy
equivalence supplied by the user.

## Build the archival artifact

From a clean commit, build the standalone archive for a new Zenodo version:

```bash
python3 paper/svk/build_artifact.py --version 0.4.2
```

The archive is written under `paper/svk/dist/`.  Its explicit import manifest
contains the same 31 entry modules audited by `check_stats.py`, including the
circle ambient-realization theorem, the modules that prove the general
topological comparison, and the unconditional quotient-compatible topological
groupoid package.
