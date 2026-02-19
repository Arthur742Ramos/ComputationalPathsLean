# ComputationalPathsLean

[![CI](https://github.com/Arthur742Ramos/ComputationalPathsLean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Arthur742Ramos/ComputationalPathsLean/actions/workflows/lean_action_ci.yml)
[![Lean](https://img.shields.io/badge/Lean-4.24.0-orange)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.24.0-blue)](https://github.com/leanprover-community/mathlib4)

A large Lean 4 formalization of **computational paths**: explicit, trace-carrying witnesses of equality built on top of Lean's `Eq`.

At the core, a path records both an equality proof and its rewrite trace:

```lean
structure Path {A : Type u} (a b : A) where
  steps : List (Step A)
  proof : a = b
```

This library develops:
- the computational-path rewrite system (`Step`, `Rw`, `RwEq`, normalization),
- fundamental group computations via encode/decode (including circle and torus),
- weak higher-groupoid structure (`OmegaGroupoid`),
- and a broad collection of mathematical modules under `ComputationalPaths/`.

## Project scope

Representative results and modules include:
- `ComputationalPaths/Path/CompPath/CircleStep.lean` (`π₁(S¹) ≃ ℤ` interface)
- `ComputationalPaths/Path/CompPath/TorusStep.lean` (`π₁(T²) ≃ ℤ × ℤ` interface)
- `ComputationalPaths/Path/OmegaGroupoid.lean` (weak ω-groupoid-style hierarchy)
- `ComputationalPaths/Path/Rewrite/Step.lean` (primitive rewrite-step relation)

Beyond `Path/`, the repository also includes large domain trees such as arithmetic, geometric, motivic, topos-theoretic, and representation-theoretic developments.

## Repository structure overview

Top-level layout:

```text
ComputationalPathsLean/
├── ComputationalPaths.lean           # Root import hub
├── Main.lean                         # CLI entry (prints libraryVersion)
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
├── docbuild/
├── paper/
└── Scripts/
```

## Getting started

### Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean toolchain manager)
- `git`

This project is pinned to:
- Lean `v4.24.0` (`lean-toolchain`)
- Mathlib `v4.24.0` (`lakefile.toml`)

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
lake build ComputationalPaths.Path.CompPath.CircleStep
lake build ComputationalPaths.Path.CompPath.TorusStep
lake build ComputationalPaths.Path.OmegaGroupoid
```

### Useful maintenance checks

```bash
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
- Main step: `leanprover/lean-action@v1` with Mathlib cache enabled

Use the badge at the top of this README to check live build status.

## Contributing

- Keep proofs `sorry`-free and avoid new global axioms.
- Prefer `Path`/`RwEq`-based reasoning for equality developments.
- Run `lake build` before opening a PR.

## License

MIT License — see [LICENSE](LICENSE).

## References

- de Queiroz, de Oliveira & Ramos, *Propositional equality, identity types, and direct computational paths* (SAJL, 2016)
- Ramos, de Queiroz & de Oliveira, *On the Identity Type as the Type of Computational Paths* (IGPL, 2017)
- de Veras, Ramos, de Queiroz & de Oliveira, *On the Calculation of Fundamental Groups in HoTT by Means of Computational Paths* (arXiv:1804.01413)
- Lumsdaine, *Weak ω-categories from intensional type theory* (TLCA, 2009)
- van den Berg & Garner, *Types are weak ω-groupoids* (PLMS, 2011)
