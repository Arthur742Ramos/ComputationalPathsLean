# ComputationalPaths.Path map

`ComputationalPaths/Path/` is the main computational-path subtree. It combines
the stable path and rewrite core with homotopy examples and broad companion
developments.

## Core path stack

| Segment | Start here | Purpose |
|---|---|---|
| `Basic/` | `Basic/Core.lean` | Defines `Step` and `Path`, plus basic path operations. |
| `Rewrite/` | `Rewrite/Step.lean`, `Rw.lean`, `RwEq.lean`, `Quot.lean` | Rewrite rules, closures, equivalence, normalization, tactics, and quotients. |
| root files | `Groupoid.lean`, `PathAlgebraDerived.lean`, `TransportDerived.lean` | Shared structures and derived path operations. |

For most users, `import ComputationalPaths.Basic` is the smallest stable import
surface for this layer.

## Homotopy and examples

| Segment | Representative files |
|---|---|
| `Homotopy/` | `Loops.lean`, `FundamentalGroup.lean`, `FundamentalGroupoid.lean` |
| `CompPath/` | `CircleStep.lean`, `TorusStep.lean`, `SphereCompPath.lean`, `PushoutPaths.lean`, `FigureEight.lean`, `KleinBottleStep.lean` |
| `OmegaGroupoid/` | `Derived.lean`, `StepToCanonical.lean`, `WeakGroupoidPaths.lean`, `TwoCategoryStructure.lean` |

## Extended companion areas

Directories such as `Algebra/`, `Topology/`, `Category/`, `Logic/`,
`TypeTheory/`, `Foundations/`, `HoTT/`, `Computation/`, and `Rewriting/`
contain larger developments built around the same path infrastructure. Treat
them as broader companion material unless a specific file documents a stronger
status.

Check [`docs/modules.md`](../../docs/modules.md) for the longer source map and
[`docs/axioms.md`](../../docs/axioms.md) before making axiom-freeness or
constructivity claims about extended files.
