# Metadata-fiber paper

- `main.tex` is the focused 15–20 page theory article.
- `companion/main.tex` preserves the complete raw scoped-calculus manuscript.
- Each directory has its own `refs.bib` and builds independently with
  `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`.

The Lean counterpart of the headline results is
`ComputationalPaths/Path/TypeTheory/MetadataJ.lean`.
