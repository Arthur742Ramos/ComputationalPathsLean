# Diagnosis and universal metadata-repair paper

- `main.tex` is the focused 25-page article, *Equality with Observable
  Metadata: Diagnosis, Universal Quotient Repair, and the PathRwQuot Boundary*.
- `companion/main.tex` is the distinct 37-page raw scoped-calculus manuscript.
- Each directory has its own `refs.bib` and builds independently with
  `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`.

The Lean counterparts are
`ComputationalPaths/Path/TypeTheory/MetadataJ.lean` for the metadata-fiber
diagnosis and `ComputationalPaths/Path/TypeTheory/MetadataRepair.lean` for
setoid repair, projection/kernel, `PathRwQuot`/K, trace, and no-bridge results.
