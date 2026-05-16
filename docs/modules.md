# Source and module map

This guide is a reader-facing map for the Lean source tree. It is intentionally
selective: use it to choose an import or starting directory, not as a generated
index of every file.

## Entrypoints

| Entrypoint | Defined in | Use it for | Notes |
|---|---|---|---|
| `ComputationalPaths.Basic` | `ComputationalPaths/Basic.lean` | Compact core imports | Re-exports `Path.Basic`, the rewrite core (`SimpleEquiv`, `Step`, `Rw`, `RwEq`, `Quot`), and `Path.Groupoid`; also defines `libraryVersion`. |
| `ComputationalPaths.Path` | `ComputationalPaths/Path.lean` | Broad computational-path umbrella | Pulls in the path core, rewrite infrastructure, homotopy interfaces, `CompPath` examples, omega-groupoid files, and many extended domain modules. |
| `ComputationalPaths` | `ComputationalPaths.lean` | Full library root | Imports `ComputationalPaths.Basic`, `ComputationalPaths.Path`, and many top-level domain umbrellas. This is comprehensive, not minimal. |
| `computational_paths` | `Main.lean` / `lakefile.lean` | Executable smoke entrypoint | Imports `ComputationalPaths` and prints `libraryVersion`. |

For examples, prefer a narrow import first:

```lean
import ComputationalPaths.Basic
```

Use `import ComputationalPaths.Path` when you want the larger computational-path
stack, and use `import ComputationalPaths` when you explicitly want the full
package root.

## Stable core surface

These files are the best starting points for the central computational-path
definitions.

| Area | Start here | What to look for |
|---|---|---|
| Path records | `ComputationalPaths/Path/Basic/Core.lean` | `Step` and `Path`, with trace metadata plus Lean equality evidence. |
| Basic path combinators | `ComputationalPaths/Path/Basic.lean` | Umbrella for core, context, congruence, globular paths, UIP, path algebra, path induction, higher paths, and path equivalence. |
| Rewrite relation | `ComputationalPaths/Path/Rewrite/Step.lean` | Single-step LND_EQ-style rewrite rules over paths. |
| Multi-step rewriting | `ComputationalPaths/Path/Rewrite/Rw.lean` | Reflexive-transitive closure of the rewrite relation. |
| Rewrite equivalence | `ComputationalPaths/Path/Rewrite/RwEq.lean` | Symmetric rewrite equivalence used throughout the path quotient APIs. |
| Quotients | `ComputationalPaths/Path/Rewrite/Quot.lean` | `PathRwQuot` and quotient-level path operations. |
| Groupoid interface | `ComputationalPaths/Path/Groupoid.lean` | Groupoid-style structure built from computational paths. |

The compact import for this layer is `ComputationalPaths.Basic`.

## Homotopy and space computations

The homotopy and space examples sit on top of the core rewrite quotient layer.
Representative files:

| Area | Representative modules |
|---|---|
| Loops and quotient loops | `ComputationalPaths/Path/Homotopy/Loops.lean`, `LoopSpace.lean`, `LoopSpaceAlgebra.lean` |
| Fundamental group API | `ComputationalPaths/Path/Homotopy/FundamentalGroup.lean`, `FundamentalGroupPresentation.lean`, `FundamentalGroupoid.lean` |
| Circle and winding examples | `ComputationalPaths/Path/CompPath/CircleStep.lean`, `CircleCompPath.lean`, `WindingNumberProperties.lean` |
| Torus examples | `ComputationalPaths/Path/CompPath/Torus.lean`, `TorusStep.lean` |
| Sphere and suspension examples | `ComputationalPaths/Path/CompPath/SphereCompPath.lean`, `SuspensionSpace.lean`, `SuspensionCircle.lean` |
| Pushouts and wedges | `ComputationalPaths/Path/CompPath/PushoutCompPath.lean`, `PushoutPaths.lean`, `FigureEight.lean`, `BouquetN.lean` |
| Klein bottle and related spaces | `ComputationalPaths/Path/CompPath/KleinBottle.lean`, `KleinBottleStep.lean`, `LensSpaceStep.lean`, `ProjectivePlaneStep.lean` |

Some generalized Seifert-van Kampen and HIT-style modules expose assumptions or
open encode/decode directions. Check `docs/axioms.md` and file-level comments
before treating a result as assumption-free.

## Higher structure

Omega-groupoid and higher-cell developments are centered around:

| Area | Representative modules |
|---|---|
| Main omega-groupoid API | `ComputationalPaths/Path/OmegaGroupoid.lean` |
| Derived and canonical forms | `ComputationalPaths/Path/OmegaGroupoid/Derived.lean`, `StepToCanonical.lean`, `TruncationProof.lean` |
| Coherence and weak groupoid files | `ComputationalPaths/Path/OmegaGroupoid/CoherencePaths.lean`, `WeakGroupoidPaths.lean`, `OmegaWeakGroupoid.lean` |
| 2-category style structure | `ComputationalPaths/Path/OmegaGroupoid/TwoCategoryStructure.lean`, `ComputationalPaths/TwoCategoryInstances.lean` |

## Book and paper companion material

For a short reader path from book and paper themes to repository entrypoints, see
[`book-companion.md`](book-companion.md). The `paper/` directory contains LaTeX
source, bibliography data, a checked-in PDF artifact, and campaign/wave notes
preserved for historical provenance. See
[`../paper/README.md`](../paper/README.md) before treating those Markdown notes
as active documentation.

## Exploratory and assumption-sensitive surfaces

The repository intentionally contains broader companion material. The following
areas should be read with extra attention to file comments and the axiom
inventory:

| Surface | Why to check carefully |
|---|---|
| `ComputationalPaths/Path/HoTT/` | Contains HoTT-flavored modules, including univalence-oriented files tracked in `docs/axioms.md`. |
| `ComputationalPaths/Path/Logic/` and `ComputationalPaths/Path/Foundations/` | Connects computational paths to logic and type-theoretic variants; status varies by file. |
| `ComputationalPaths/Path/Homotopy/` deep or HIT-related files | Includes large homotopy-theoretic developments; some truncation/HIT assumptions are documented in `docs/axioms.md`. |
| `ComputationalPaths/Path/Algebra/*Deep.lean` and other `*Deep.lean` files | Companion/deepening modules that may be more exploratory than the core path and rewrite surface. |
| `ComputationalPaths/Path/Rewriting/CombinatorReductionDeep.lean` | Listed in the axiom inventory for SKI combinator equations. |

Do not infer that a whole directory is axiom-free or fully canonical from its
name alone. The maintained inventory is `docs/axioms.md`.

## Broad source tree

Most top-level domain directories have matching umbrella modules, for example
`ComputationalPaths/Arithmetic/` and `ComputationalPaths/Arithmetic.lean`.
They are imported by the full root `ComputationalPaths.lean`, while the core
navigation path remains:

```text
ComputationalPaths.Basic
  -> ComputationalPaths.Path.Basic
  -> ComputationalPaths.Path.Rewrite.{Step,Rw,RwEq,Quot}
  -> ComputationalPaths.Path.Groupoid
```

The largest source subtree is `ComputationalPaths/Path/`. Its main segments are:

| Segment | Role |
|---|---|
| `Basic/` | Core `Step`/`Path` representation and elementary operations. |
| `Rewrite/` | LND_EQ-style rewrite rules, closures, normalization, confluence, tactics, and quotient support. |
| `Homotopy/` | Loop spaces, fundamental groups, fibration/covering-space interfaces, and broader homotopy modules. |
| `CompPath/` | Concrete computational-path spaces and encode/decode-style examples. |
| `OmegaGroupoid/` | Higher-cell and omega-groupoid-style structure. |
| `Algebra/`, `Topology/`, `Category/`, `Logic/`, `TypeTheory/`, `Foundations/` | Extended companion developments using the path infrastructure. |
| `Polygraph/`, `Computation/`, `Rewriting/`, `Groupoid/`, `HoTT/` | Specialized support and exploratory surfaces around rewriting, computation, groupoids, and HoTT connections. |

## What not to expect from this map

- It does not list every Lean file.
- It does not change import order or module boundaries.
- It does not replace `docs/ARCHITECTURE.md`; use that document for the layered
  architecture narrative and theorem landmarks.
- It does not replace `docs/axioms.md`; use that document for assumption and
  axiom status.
