# Computational Paths

Lean formalisation of *Propositional Equality, Identity Types, and Computational Paths*.

## Current status
- Core path operations (`ComputationalPaths/Path/Basic.lean`) are fully implemented via explicit rewrite-step lists, giving transport, symmetry, and congruence lemmas without placeholders.
- The rewrite system (`ComputationalPaths/Path/Rewrite.lean`) now covers the reflexive/transitive/symmetric closures together with additional `mapLeft`/`mapRight` congruence reductions, bringing the development closer to the full LNDEQ suite.  The new `rwEqSetoid`/`PathRwQuot` constructions package rewrite equality as a `Setoid` and quotient, and provide `refl`/`symm`/`trans` operations directly on the quotient.
- Dependent pairs are supported via `sigmaMk`/`sigmaFst`/`sigmaSnd`, and the rewrite system exposes the corresponding β/η behaviour (e.g. `sigma_fst_beta`, `rweq_sigma_eta`) so LNDEQ’s Σ-fragment reduces canonically.
- A weak groupoid structure (`ComputationalPaths/Path/Groupoid.lean`) packages composition, inverses, and identities up to rewrite, serving as a foundation for later algebraic structure.

## Using the library from another project
Add this repository as a Lake dependency (Lean 4.24+):

```toml
[package]
name = "your_project"
version = "0.1.0"

[[require]]
name = "computational_paths"
git = "https://github.com/Arthur742Ramos/ComputationalPathsLean.git"
rev = "main" # or a tagged release once available
```

Then run:

```bash
lake update computational_paths
lake build
```

Downstream modules can import the umbrella entry point:

```lean
import ComputationalPaths
```

The convenience constant `ComputationalPaths.libraryVersion` (currently `"0.1.0"`) tracks API releases; bump it when cutting new tags so dependants can guard against breaking changes.

## Project structure
- `ComputationalPaths/Path/Basic.lean` - inductive definition of computational paths, equivalence with Lean equality, symmetry/transitivity operations, transport, and congruence lemmas.
- `ComputationalPaths/Path/Rewrite.lean` - basic rewrite steps (including the associativity rule) together with their reflexive/transitive closure `Rw` and the symmetric closure `RwEq`; includes β/η rules for products, sums, functions, and dependent pairs.
- `ComputationalPaths/Path/Groupoid.lean` - weak groupoid structure coming from computational paths, using the rewrite relation.
- `ComputationalPaths/Basic.lean` - convenience entry point re-exporting the core modules.
- `ComputationalPaths/Path.lean` – umbrella import for path-specific modules.
- `agents.md` – overview of the automated agents and guidance on when to invoke them.

## Getting started
1. Install Lean 4 via [`elan`](https://github.com/leanprover/elan):
   ```powershell
   elan toolchain install leanprover/lean4:v4.24.0
   elan default leanprover/lean4:v4.24.0
   ```
   The repository contains a small `lake.cmd` shim that forwards to the tool
   installed by `elan`, so `lake` commands can be invoked as `.\lake …` even if
   the `.elan\bin` directory is not on your `PATH`.
2. Clone the repository and move into it:
   ```powershell
   git clone https://github.com/<your-org>/computational-paths.git
   cd computational-paths/computational_paths
   ```
3. Build the project:
   ```powershell
   .\lake build
   ```
4. Run the demo executable:
   ```powershell
   .\lake exe computational_paths
   ```

If `lake build` completes without errors, all Lean proofs have been checked by the
kernel.

## Roadmap
- Extend the rewrite system with the full LNDEQ rules (substitution, products, sums, ...).
- Prove normalisation / confluence for the extended system.
- Connect computational paths with Lean's identity type tooling (UIP counterexamples, rewriting tactics).
- Develop illustrative formal proofs using the new infrastructure.
