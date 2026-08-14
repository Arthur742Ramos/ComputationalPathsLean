# Topological computational-paths artifact

This directory contains the mathematical design contract for the standalone
paper.  The checked Lean implementation is in
`ComputationalPaths/Path/Topology/ScopedGeometricRewrite*.lean`, together with
the weighted-realization bridge in
`ComputationalPaths/Path/Topology/WeightedConcatenation.lean` and the
finite-generator presentation data in
`ComputationalPaths/Path/Topology/FiniteCircleTorusPresentation.lean`, and the
Hawaiian-earring transfer module
`ComputationalPaths/Path/Topology/ScopedGeometricRewriteHawaiianEarring.lean`,
the trace-sensitive topology module
`ComputationalPaths/Path/Topology/TraceSensitiveTopologicalCompPath.lean`, and
the universal-topology collapse module
`ComputationalPaths/Path/Topology/TraceSensitiveUniversalCollapse.lean`, and
the finite topology-separation certificate
`ComputationalPaths/Path/Topology/TraceSensitiveSeparation.lean`.  The
modules are imported by `ComputationalPaths.lean`.

The implementation has two explicit levels of composition:

- `ScopedStrongComposablePair` is the unconditional final-domain on which
  composition is continuous and all groupoid laws are proved.
- `ScopedComposablePair` is the ordinary pullback domain.  Its agreement with
  the final topology is characterized by
  `scopedProductCompatibility_iff_topology_agreement`, with an open-map
  sufficient condition in `scopedProductCompatibility_of_open_pair_map`.

The circle artifact uses the actual unit additive circle and the explicit
zero, integer-addition, and reversal rewrite rules.  It proves generator
soundness, trace normalization, the continuous scoped-arrow map, and the
integer winding equivalence.  The realized fundamental-groupoid bridge also
proves carrier closure for identities, reversal, and composition.

The artifact also checks:

- `scopedProductCompatibility_of_compact_final_t2` and the discrete positive
  ordinary-pullback theorem;
- `ScopedGeometricNormalFormCertificate` and its completeness theorem;
- the based circle normal-form certificate; and
- the finite one-generator/two-generator trace-code completion certificates
  and the sound torus commuting square;
- the genuine product-torus winding equivalence and the
  simultaneous/sequential representative bridge in
  `TopologicalTorusScoped.lean`; and
- the quotient-obstruction transfer from an externally supplied Fabel-style
  non-quotient product theorem to failure of ordinary-pullback compatibility
  and discontinuity of ordinary multiplication.

The manuscript's main mathematical example uses finite oriented circle and
torus generators.  The finite-generator module now records those alphabets,
their integer or integer-pair trace codes, the torus commuting-square
soundness, and explicit completion certificates.  The integer-indexed circle
module remains a separate completed presentation, and the ordinary torus
module remains a quotient classification of genuine continuous loops.  The
minimal cancellation-only circle derivation and the commutation-generated
torus normalizer are still mathematical presentation-level arguments rather
than claims that the completed modules reproduce the entire scoped derivation.

## Reproduce

From the repository root:

```text
lake build
```

The focused checks are:

```text
lake build ComputationalPaths.Path.Topology.ScopedGeometricRewrite
lake build ComputationalPaths.Path.Topology.WeightedConcatenation
lake build ComputationalPaths.Path.Topology.ScopedGeometricRewriteQuotient
lake build ComputationalPaths.Path.Topology.ScopedGeometricRewriteGroupoid
lake build ComputationalPaths.Path.Topology.ScopedGeometricRewriteComparison
lake build ComputationalPaths.Path.Topology.ScopedGeometricRewriteFunctor
lake build ComputationalPaths.Path.Topology.ScopedGeometricRewriteFundamental
lake build ComputationalPaths.Path.Topology.ScopedGeometricRewriteHawaiianEarring
lake build ComputationalPaths.Path.Topology.ScopedGeometricRewriteCircle
lake build ComputationalPaths.Path.Topology.TopologicalTorusScoped
lake build ComputationalPaths.Path.Topology.FiniteCircleTorusPresentation
lake build ComputationalPaths.Path.Topology.TraceSensitiveTopologicalCompPath
lake build ComputationalPaths.Path.Topology.TraceSensitiveUniversalCollapse
lake build ComputationalPaths.Path.Topology.TraceSensitiveSeparation
```

Declaration-level audits for these implementation modules are:

```text
rg -n '^[[:space:]]*(sorry|admit|axiom)' \
  ComputationalPaths/Path/Topology/ScopedGeometricRewrite*.lean \
  ComputationalPaths/Path/Topology/WeightedConcatenation.lean \
  ComputationalPaths/Path/Topology/FiniteCircleTorusPresentation.lean \
  ComputationalPaths/Path/Topology/TraceSensitiveTopologicalCompPath.lean \
  ComputationalPaths/Path/Topology/TraceSensitiveUniversalCollapse.lean \
  ComputationalPaths/Path/Topology/TraceSensitiveSeparation.lean
git diff --check
```

The paper’s mathematical claims and the Lean declaration map are recorded in
[`design.md`](design.md).  This artifact does not claim a discrete topology
for the circle’s integer normal form, and it does not identify the ordinary
and final composable-pair topologies without the proved compatibility
criterion.  The Hawaiian-earring module checks the transfer argument from
external non-quotient and discontinuity facts; it does not reprove Fabel's
classical Hawaiian-earring theorem.

The standalone manuscript is [`main.tex`](main.tex). Reproduce the PDF from
this directory with:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The checked output is published at
`output/pdf/topological-computational-paths-v17.pdf`.

The exact source snapshot for this paper artifact is the tag
`topological-paper-v10` in the public repository.  The accompanying Lean-only
artifact is version `0.6.1+lean-only-v3` at
[`10.5281/zenodo.21938980`](https://doi.org/10.5281/zenodo.21938980); the
permanent concept DOI is
[`10.5281/zenodo.21817207`](https://doi.org/10.5281/zenodo.21817207).  The
paper source is available in the repository at
`https://github.com/Arthur742Ramos/ComputationalPathsLean`.
