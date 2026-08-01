# Metadata-fiber paper

- `main.tex` is the focused 15–20 page theory article.
- `companion/main.tex` preserves the complete raw scoped-calculus manuscript.
- Each directory has its own `refs.bib` and builds independently with
  `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`.

The Lean counterpart of the headline results is
`ComputationalPaths/Path/TypeTheory/MetadataJ.lean`.

Reviewer claim map:

| Earlier combined-draft claim | Stable Lean declaration |
| --- | --- |
| Based identity total-space contractibility | `based_identity_total_space_contractible` |
| Unrestricted based eliminator with propositional beta iff contractible | `unrestricted_based_elimination_iff_contractible` |
| General equality-metadata fiber criterion | `metadata_fiber_criterion` |

The explicit beta field is part of `UnrestrictedBasedEliminator`; the
factor-through-equality result is `factorized_motive_eliminator`.
