# Book and paper companion guide

This repository is a Lean 4 companion for the book
[_The Calculus of Computational Paths_](https://www.amazon.com/dp/1848905157/).
It is not a chapter-by-chapter mirror of the book. Use this guide as a practical
route from the mathematical themes to maintained repository entrypoints.

## Reader path

| Need | Start here |
|---|---|
| Build and project scope | [`../README.md`](../README.md) |
| Stable documentation order | [`README.md`](README.md) |
| Source and import map | [`modules.md`](modules.md) |
| Architecture overview | [`ARCHITECTURE.md`](ARCHITECTURE.md) |
| Axiom and assumption inventory | [`axioms.md`](axioms.md) |
| Paper source and historical wave notes | [`../paper/README.md`](../paper/README.md) |
| Archived audits and generated run outputs | [`archive/README.md`](archive/README.md) |

## Lean source landmarks

| Theme | Lean entrypoints | Notes |
|---|---|---|
| Core computational paths | `ComputationalPaths.Basic`, `ComputationalPaths/Path/Basic/Core.lean` | `Path a b` packages trace metadata with Lean equality evidence. |
| Rewrite equality | `ComputationalPaths/Path/Rewrite/Step.lean`, `Rw.lean`, `RwEq.lean`, `Quot.lean` | Central rewrite, equivalence, and quotient infrastructure. |
| Loop and fundamental-group APIs | `ComputationalPaths/Path/Homotopy/Loops.lean`, `FundamentalGroup.lean` | Shared loop-space interfaces used by space examples. |
| Space examples | `ComputationalPaths/Path/CompPath/CircleStep.lean`, `TorusStep.lean`, `SphereCompPath.lean`, `FigureEight.lean` | Representative encode/decode-style companion modules. Check file comments and `axioms.md` before generalizing results. |
| Higher structure | `ComputationalPaths/Path/OmegaGroupoid.lean` and `ComputationalPaths/Path/OmegaGroupoid/` | Weak higher-groupoid-style structures and coherence-oriented files. |
| Broad companion material | `ComputationalPaths/Path/Algebra/`, `Topology/`, `Category/`, `Logic/`, plus top-level domain directories | Exploratory or domain-specific material unless a file documents a stronger status. |

For imports, prefer the smallest module that exposes what you need. The compact
core entrypoint is:

```lean
import ComputationalPaths.Basic
```

Use `import ComputationalPaths.Path` for the broader computational-path subtree,
and `import ComputationalPaths` only when you intentionally need the full
package surface.

## Paper and historical notes

The `paper/` directory contains the LaTeX source, bibliography, checked-in PDF,
and campaign/wave Markdown notes. Treat the wave documents as historical
development notes, not as the canonical module navigation layer. The maintained
navigation surfaces are this file, `modules.md`, `ARCHITECTURE.md`, and
`axioms.md`.

This guide deliberately avoids reproducing book text. It only points to
repository-owned files and concise summaries of how the companion materials are
organized.
