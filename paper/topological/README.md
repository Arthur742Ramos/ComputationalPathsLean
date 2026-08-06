# Topological computational-paths artifact

This directory contains the mathematical design contract for the standalone
paper.  The checked Lean implementation is in
`ComputationalPaths/Path/Topology/ScopedGeometricRewrite*.lean`, together with
the weighted-realization bridge in
`ComputationalPaths/Path/Topology/WeightedConcatenation.lean` and the
Hawaiian-earring transfer module
`ComputationalPaths/Path/Topology/ScopedGeometricRewriteHawaiianEarring.lean`,
and is imported by `ComputationalPaths.lean`.

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

The strengthened artifact additionally checks:

- `scopedProductCompatibility_of_compact_final_t2` and the discrete positive
  ordinary-pullback theorem;
- `ScopedGeometricNormalFormCertificate` and its completeness theorem;
- the based circle normal-form certificate; and
- the genuine product-torus winding equivalence in
  `TopologicalTorusScoped.lean`.
- the quotient-obstruction transfer from an externally supplied Fabel-style
  non-quotient product theorem to failure of ordinary-pullback compatibility
  and discontinuity of ordinary multiplication.

The manuscript's main mathematical example uses finite oriented circle and
torus generators.  The integer-indexed circle module is the completed normal
form presentation used for compact formal certificates; it does not replace
the finite-generator argument in the main text.

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
```

Declaration-level audits for the new implementation are:

```text
rg -n '^[[:space:]]*(sorry|admit|axiom)' \
  ComputationalPaths/Path/Topology/ScopedGeometricRewrite*.lean \
  ComputationalPaths/Path/Topology/WeightedConcatenation.lean
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
`output/pdf/topological-computational-paths.pdf`.

The exact source snapshot for the released Lean artifact is the immutable tag
`topological-paper-v2` in
`https://github.com/Arthur742Ramos/ComputationalPathsLean`. The archived
artifact has DOI [`10.5281/zenodo.21797011`](https://doi.org/10.5281/zenodo.21797011).
