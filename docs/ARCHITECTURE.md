# ComputationalPathsLean Architecture

This document summarizes the current architecture of the `ComputationalPathsLean` codebase, with emphasis on `ComputationalPaths/Path/` and the core exports in `ComputationalPaths/Basic.lean`.

## 1. Entry points and import hubs

- `ComputationalPaths.lean` is the library root import hub.
  - It imports `ComputationalPaths.Basic`, `ComputationalPaths.Path`, and many domain infrastructure modules (Motivic, Topos, Arithmetic, TFT, etc.).
- `ComputationalPaths/Basic.lean` provides the compact "core exports" surface:
  - `Path.Basic`, rewrite core (`Step`, `Rw`, `RwEq`, `Quot`), and `Path.Groupoid`.
- `ComputationalPaths/Path.lean` is the large umbrella for the computational-path stack.
  - It imports foundational modules, rewrite infrastructure, homotopy/fundamental-group developments, computational space modules (`CompPath`), omega-groupoid modules, and large Algebra/Topology/Category/Logic ecosystems.

## 2. Layered architecture inside `ComputationalPaths/Path`

### Layer A: Core path representation (`Path/Basic`)

Primary file: `ComputationalPaths/Path/Basic/Core.lean`.

- `Step (A)` is an elementary equality witness with fields `src`, `tgt`, `proof`.
- `Path a b` is a structure:
  - `steps : List (Step A)` (trace metadata),
  - `proof : a = b` (semantic equality witness).
- Core operations:
  - `Path.refl`, `Path.trans`, `Path.symm`,
  - congruence/transport combinators (`congrArg`, `cast`, product/sigma maps in related files).

Supporting umbrellas:
- `Path/Basic.lean` re-exports core/context/congruence/globular/UIP/path algebra/path induction/higher paths.

### Layer B: Rewrite system (`Path/Rewrite`)

Key modules:
- `Rewrite/Step.lean`: single-step rewrite relation with categorized rules (basic path algebra, products, sigma, sums, functions, transport, contexts, structural completion rules).
- `Rewrite/Rw.lean`: reflexive-transitive closure.
- `Rewrite/RwEq.lean`: symmetric reflexive-transitive closure (`RwEq`).
- `Rewrite/Quot.lean`: quotient machinery:
  - `rwEqSetoid`,
  - `PathRwQuot A a b`,
  - quotient-level composition/inverse laws.
- `Rewrite/LNDEQ.lean`: rule tags and soundness/completeness packaging for named LND_EQ rules.
- `Rewrite/PathTactic.lean`: automation (`path_rfl`, `path_simp`, `path_trans`, congruence helpers).

### Layer C: Homotopy/groupoid interfaces

Key modules:
- `Path/Groupoid.lean`: weak category/groupoid structures from computational paths.
- `Path/Homotopy/Loops.lean`: `LoopSpace`, `LoopQuot`, loop algebra on quotients.
- `Path/Homotopy/FundamentalGroup.lean`: notation and API for `π₁(A, a)`.
- `Path/Homotopy/FundamentalGroupoid.lean`: explicit `FundamentalGroupoid` and links to `π₁`.
- `Path/OmegaGroupoid.lean`: weak omega-groupoid tower and coherences.

### Layer D: Computational space constructions (`Path/CompPath`)

Representative modules:
- `CompPath/CircleCompPath.lean` and `CompPath/CircleStep.lean`
- `CompPath/Torus.lean` and `CompPath/TorusStep.lean`
- `CompPath/SphereCompPath.lean`
- `CompPath/PushoutCompPath.lean`, `CompPath/PushoutPaths.lean`
- `CompPath/FigureEight.lean`, `CompPath/BouquetN.lean`

These modules package encode/decode style computations and concrete `π₁` equivalences.

### Layer E: Extended domain ecosystems

Beyond the core and CompPath layers, `Path.lean` imports broad developments across:
- `Algebra`, `Topology`, `Homotopy`, `Category`, `Logic`, `TypeTheory`, `Rewriting`, and related foundational namespaces.

## 3. Module organization snapshot (`ComputationalPaths/Path`)

Counts from current tree scan (`*.lean`):

| Segment | File count |
|---|---:|
| Root files in `Path/` | 51 |
| Algebra | 331 |
| Homotopy | 204 |
| Topology | 104 |
| Category | 67 |
| CompPath | 54 |
| Rewrite | 35 |
| Rewriting | 33 |
| Logic | 28 |
| HoTT | 13 |
| Basic | 9 |
| Groupoid | 9 |
| Foundations | 9 |
| TypeTheory | 6 |
| OmegaGroupoid | 5 |
| Geometry | 4 |
| Graph | 4 |
| Computation | 35 |
| Other small segments (`Analysis`, `NumberTheory`, etc.) | 3+ |
| **Total** | **1004** |

## 4. Core architectural types

| Type / structure | Role | Primary module |
|---|---|---|
| `Step` | Elementary rewrite/equality witness | `Path/Basic/Core.lean` |
| `Path a b` | Equality + explicit trace | `Path/Basic/Core.lean` |
| `Rw` | Multi-step rewrite closure | `Path/Rewrite/Rw.lean` |
| `RwEq` | Symmetric rewrite equivalence | `Path/Rewrite/RwEq.lean` |
| `PathRwQuot A a b` | Paths modulo `RwEq` | `Path/Rewrite/Quot.lean` |
| `LoopSpace A a` / `LoopQuot A a` | Raw loops and quotient loops | `Path/Homotopy/Loops.lean` |
| `π₁(A, a)` | Fundamental group notation/API | `Path/Homotopy/FundamentalGroup.lean` |
| `FundamentalGroupoid A` | Multi-basepoint quotient groupoid | `Path/Homotopy/FundamentalGroupoid.lean` |
| `WeakOmegaGroupoid A` | Higher-cell coherence tower | `Path/OmegaGroupoid.lean` |

## 5. Theorem and equivalence landmarks

Representative named results:

| Result | Statement (informal) | Module |
|---|---|---|
| `circlePiOneEquivInt` | `π₁(S¹) ≃ ℤ` | `CompPath/CircleStep.lean` (and alias in `CircleCompPath.lean`) |
| `torusPiOneEquivIntProd` | `π₁(T²) ≃ ℤ × ℤ` | `CompPath/TorusStep.lean` |
| `sphere2CompPath_pi1_equiv_unit` | `π₁(S²) ≃ Unit` | `CompPath/SphereCompPath.lean` |
| `figureEightPiOneEquiv` | figure-eight `π₁` as free-product words (under required decode-bijectivity assumption) | `CompPath/FigureEight.lean` |
| `seifertVanKampenEquiv` | pushout `π₁` to amalgamated free product equivalence | `CompPath/PushoutPaths.lean` |
| `piOne_eq_hom` | `π₁(A,a)` identified with endomorphisms in `FundamentalGroupoid A` | `Homotopy/FundamentalGroupoid.lean` |
| `compPathOmegaGroupoid` | computational paths instantiate `WeakOmegaGroupoid` | `OmegaGroupoid.lean` |

## 6. Design summary

- The architectural core is: **`Path` traces + rewrite closure (`RwEq`) + quotient (`PathRwQuot`)**.
- Homotopy-level objects (`LoopQuot`, `π₁`, fundamental groupoid) are defined on top of that quotient.
- Space-specific computations (circle/torus/sphere/pushouts/figure-eight) are layered in `CompPath`, while large domain expansions (Algebra/Topology/Category/Logic/Homotopy) reuse the same core interfaces.
