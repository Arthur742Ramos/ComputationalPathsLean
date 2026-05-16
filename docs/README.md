# Documentation

This directory contains the stable reader-facing documentation for `ComputationalPathsLean`, the Lean 4 companion repository for [_The Calculus of Computational Paths_](https://www.amazon.com/dp/1848905157/).

## Reading order

1. Start with the repository `README.md` for the project purpose, build commands, and high-level scope.
2. Read `ARCHITECTURE.md` for the current module layers, core types, and representative theorem landmarks.
3. Read `axioms.md` before making claims about constructivity, assumptions, or axiom use.
4. Use `archive/README.md` to understand historical audits and generated run outputs kept for provenance.

## Status notes

- The core computational-path infrastructure lives under `ComputationalPaths/Path/Basic` and `ComputationalPaths/Path/Rewrite`.
- Space-specific examples and fundamental-group interfaces are primarily under `ComputationalPaths/Path/CompPath`.
- The many broader mathematical subdirectories are companion and exploratory material unless a file or the architecture guide documents a stronger status.
- Historical audits belong in `docs/archive/`; active documentation should stay in this directory.
