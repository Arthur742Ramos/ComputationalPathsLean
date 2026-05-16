# ComputationalPaths source map

This directory is the Lean library root. It contains the compact core export
`Basic.lean`, the large computational-path subtree `Path/`, and many broad
domain companion directories.

## Recommended entrypoints

| Need | Import |
|---|---|
| Core computational paths and rewrite quotients | `ComputationalPaths.Basic` |
| Large computational-path umbrella | `ComputationalPaths.Path` |
| Full package root, including broad domain modules | `ComputationalPaths` |

`ComputationalPaths.lean` at the repository root imports this library root and
the broad top-level module set. Prefer narrower imports in examples unless you
need the full package surface.

## Directory orientation

- `Basic.lean` re-exports the central `Path.Basic`, rewrite, quotient, and
  groupoid surfaces, and defines `libraryVersion`.
- `Path/` contains the core computational-path implementation plus homotopy,
  `CompPath`, omega-groupoid, algebra, topology, category, logic, and related
  companion modules.
- Other top-level directories such as `Arithmetic/`, `Motivic/`, `Topos/`,
  `SpectralSequence/`, and `OperadicAlgebra/` are broad companion domains.
  Many have matching umbrella files like `Arithmetic.lean` or `Motivic.lean`.

For a reader-facing map with representative file names, see
[`docs/modules.md`](../docs/modules.md). For assumption status, see
[`docs/axioms.md`](../docs/axioms.md).
