# Paper directory

This directory contains paper and book-companion material for
`ComputationalPathsLean`. It is reader-facing only where noted below; several
Markdown files are preserved as historical development notes from earlier
formalization campaigns.

## Contents

| Path | Role |
|---|---|
| `main.tex` | LaTeX source for the computational-path paper draft. |
| `refs.bib` | Bibliography used by `main.tex`. |
| `main.pdf` | Checked-in PDF artifact for reference. Do not edit it by hand. |
| `CHANGELOG.md` | Short paper-source change log. |
| `campaign_inventory.md`, `wave*.md` | Historical campaign and wave notes. They are useful for provenance, but they are not the polished source map for the Lean library. |

For the maintained repository documentation, start with
[`../README.md`](../README.md), [`../docs/README.md`](../docs/README.md), and
[`../docs/book-companion.md`](../docs/book-companion.md).

## Relationship to the Lean companion repository

The Lean source is the authoritative formalization surface in this repository.
Use the paper files as companion context for the mathematical narrative, then use
the documentation under `../docs/` to find maintained module entrypoints,
architecture notes, and axiom inventories.

In particular:

- `../docs/modules.md` maps stable Lean entrypoints and representative modules.
- `../docs/ARCHITECTURE.md` describes the current source layers.
- `../docs/axioms.md` tracks axiom declarations and assumption-sensitive files.
- `../docs/archive/` holds historical audits and generated run outputs.

## Inspecting or building the LaTeX source

There is no Lake target for the paper. The source can be inspected directly from
`main.tex` and `refs.bib`.

Building the paper requires a local TeX installation plus the external
`BSLstyle` document class and `BSLbibstyle` bibliography style referenced by
`main.tex`. Those style files are not vendored in this repository, so LaTeX
build commands are intentionally not part of the standard repository workflow.
If you build the PDF locally, keep generated LaTeX artifacts out of commits
unless a PR is specifically updating the checked-in `main.pdf`.
