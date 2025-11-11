# Computational Paths

Lean formalisation of *Propositional Equality, Identity Types, and Computational Paths*.

## Project structure
- `ComputationalPaths/Path/Basic.lean` – inductive definition of computational paths, equivalence with Lean equality, symmetry/transitivity operations, transport, and congruence lemmas.
- `ComputationalPaths/Path/Rewrite.lean` – basic rewrite steps (including the associativity rule) together with their reflexive/transitive closure `Rw` and the symmetric closure `RwEq`.
- `ComputationalPaths/Path/Groupoid.lean` – weak groupoid structure coming from computational paths, using the rewrite relation.
- `ComputationalPaths/Basic.lean` – convenience entry point re-exporting the core modules.
- `ComputationalPaths/Path.lean` – umbrella import for path-specific modules.

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
- Connect computational paths with Lean''s identity type tooling (UIP counterexamples, rewriting tactics).
- Develop illustrative formal proofs using the new infrastructure.
