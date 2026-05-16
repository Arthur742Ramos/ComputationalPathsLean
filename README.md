# ComputationalPathsLean

[![CI](https://github.com/Arthur742Ramos/ComputationalPathsLean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Arthur742Ramos/ComputationalPathsLean/actions/workflows/lean_action_ci.yml)
[![Lean](https://img.shields.io/badge/Lean-4.24.0-orange)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.24.0-blue)](https://github.com/leanprover-community/mathlib4)

A Lean 4 companion repository for the book [_The Calculus of Computational Paths_](https://www.amazon.com/dp/1848905157/). It collects formal definitions, examples, and exploratory developments around **computational paths**: explicit, trace-carrying witnesses of equality built on top of Lean's `Eq`.

The most stable part of the repository is the computational-path core under `ComputationalPaths/Path/Basic` and `ComputationalPaths/Path/Rewrite`. Many larger mathematical subdirectories are companion and exploratory material; use the architecture and axiom inventory docs below to distinguish core infrastructure from broader experiments.

At the core, a path records both an equality proof and a rewrite trace:

```lean
structure Path {A : Type u} (a b : A) where
  steps : List (Step A)
  proof : a = b
```

This repository develops:

- the computational-path rewrite system (`Step`, `Rw`, `RwEq`, normalization),
- quotient and loop-space interfaces used by fundamental-group examples,
- selected encode/decode-style space computations, including circle, torus, sphere, pushout, figure-eight, and Klein bottle modules,
- weak higher-groupoid-style interfaces (`OmegaGroupoid`),
- and broad companion developments under `ComputationalPaths/`.

## Project scope

Representative landmarks include:

| Area | Where to start | Notes |
|---|---|---|
| Core path representation | `ComputationalPaths/Path/Basic/Core.lean` | `Path a b` packages trace metadata plus an equality proof. |
| Rewrite equality | `ComputationalPaths/Path/Rewrite/Step.lean`, `Rw.lean`, `RwEq.lean`, `Quot.lean` | Main rewrite and quotient infrastructure. |
| Fundamental-group examples | `ComputationalPaths/Path/CompPath/CircleStep.lean`, `TorusStep.lean`, `SphereCompPath.lean` | Representative encode/decode-style interfaces. |
| Pushouts and wedges | `ComputationalPaths/Path/CompPath/PushoutPaths.lean`, `FigureEight.lean` | Includes documented assumptions and open encode-direction work. |
| Higher structure | `ComputationalPaths/Path/OmegaGroupoid.lean` | Weak omega-groupoid-style hierarchy over computational paths. |

The broader arithmetic, geometric, motivic, topos-theoretic, representation-theoretic, and category-theoretic modules should be read as companion material unless a specific file documents a stronger status.

See `docs/axioms.md` before making axiom-related claims: the project tracks existing axiom declarations and typeclass assumptions explicitly rather than treating the whole tree as axiom-free.

## Repository structure overview

Top-level layout:

```text
ComputationalPathsLean/
├── ComputationalPaths.lean           # Root import hub
├── Main.lean                         # CLI entry (prints libraryVersion)
├── lakefile.lean                     # Lake package configuration
├── lake-manifest.json                # Lake dependency manifest
├── lean-toolchain                    # Pinned Lean toolchain
├── ComputationalPaths/
│   ├── Basic.lean                    # Core exports + libraryVersion
│   ├── Path/                         # Computational paths core ecosystem
│   │   ├── Basic/                    # Path/Step core definitions
│   │   ├── Rewrite/                  # Step, Rw, RwEq, normalization, tactics
│   │   ├── Homotopy/                 # Loop spaces, π₁, πₙ, fibrations, etc.
│   │   ├── CompPath/                 # Circle/Torus/Sphere/Pushout constructions
│   │   ├── OmegaGroupoid/            # Higher coherence and derived omega-groupoid APIs
│   │   ├── Algebra/                  # Algebraic constructions over paths
│   │   ├── Topology/                 # Topological applications
│   │   ├── Category/                 # Category-theoretic path developments
│   │   └── Logic/                    # Logic/type-theoretic path modules
│   ├── Arithmetic/
│   ├── Birational/
│   ├── Chromatic/
│   ├── Cobordism/
│   ├── Condensed/
│   ├── Crystalline/
│   ├── Etale/
│   ├── Floer/
│   ├── Hodge/
│   ├── KacMoody/
│   ├── Langlands/
│   ├── Motivic/
│   ├── OperadicAlgebra/
│   ├── Perfectoid/
│   ├── Prismatic/
│   ├── Quantum/
│   ├── SymplecticDuality/
│   ├── Topos/
│   ├── Tropical/
│   └── VertexAlgebra/
├── docs/
│   ├── README.md                     # Documentation entrypoint
│   ├── ARCHITECTURE.md               # Canonical architecture overview
│   ├── axioms.md                     # Canonical axiom/typeclass inventory
│   └── archive/                      # Historical audits and run outputs
├── paper/                            # Paper/book source material
└── scripts/
    └── legacy/                       # Archived maintenance scripts
```

## Documentation map

- `docs/README.md` - documentation entrypoint and reading order.
- `docs/ARCHITECTURE.md` - current architecture, layers, and representative theorem landmarks.
- `docs/axioms.md` - current axiom and typeclass inventory.
- `docs/archive/README.md` - provenance for historical audits and generated run outputs.

## Getting started

### Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean toolchain manager)
- `git`

This project is pinned to:
- Lean `v4.24.0` (`lean-toolchain`)
- Mathlib `v4.24.0` (`lakefile.lean`)

### Build

```bash
# Clone
git clone https://github.com/Arthur742Ramos/ComputationalPathsLean.git
cd ComputationalPathsLean

# Build all modules
lake build
```

Optional (faster first build when available):

```bash
lake exe cache get
```

### Run executable

```bash
lake exe computational_paths
```

### Build specific modules

```bash
lake build ComputationalPaths.Basic
lake build ComputationalPaths.Path.CompPath.CircleStep
lake build ComputationalPaths.Path.CompPath.TorusStep
lake build ComputationalPaths.Path.CompPath.KleinBottleStep
lake build ComputationalPaths.Path.OmegaGroupoid
```

### Useful maintenance checks

```bash
# Confirm the pinned Lean toolchain used by Lake
lake -R --no-ansi env lean --version

# Find placeholders
rg "sorry" --glob "*.lean" ComputationalPaths

# Find custom axiom declarations
rg "^axiom " --glob "*.lean" ComputationalPaths
```

## CI status

GitHub Actions workflow: **Lean Action CI**
- Workflow file: `.github/workflows/lean_action_ci.yml`
- Triggers: pushes to `main`, pull requests, manual dispatch
- Runner: `ubuntu-latest`
- Main step: `leanprover/lean-action@v1` runs `lake build` from the repository root with GitHub and Mathlib caches enabled
- Action updates: `.github/dependabot.yml` checks GitHub Actions weekly

Use the badge at the top of this README to check live build status.

## Contributing

- Keep new proofs `sorry`-free and avoid new global axioms.
- If a development must rely on an axiom or assumption, document it and keep `docs/axioms.md` current.
- Prefer `Path`/`RwEq`-based reasoning for equality developments.
- Run `lake build` before opening a PR.
- Keep canonical documentation under `docs/`; move historical audits or generated run logs to `docs/archive/` rather than leaving them in the repository root.

## License

MIT License — see [LICENSE](LICENSE).

## References

- de Queiroz, de Oliveira & Ramos, *Propositional equality, identity types, and direct computational paths* (SAJL, 2016)
- Ramos, de Queiroz & de Oliveira, *On the Identity Type as the Type of Computational Paths* (IGPL, 2017)
- de Veras, Ramos, de Queiroz & de Oliveira, *On the Calculation of Fundamental Groups in HoTT by Means of Computational Paths* (arXiv:1804.01413)
- Lumsdaine, *Weak ω-categories from intensional type theory* (TLCA, 2009)
- van den Berg & Garner, *Types are weak ω-groupoids* (PLMS, 2011)
