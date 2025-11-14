# Computational Paths

Lean formalisation of *Propositional Equality, Identity Types, and Computational Paths*.

## Current status
- Core path operations (`ComputationalPaths/Path/Basic.lean`) are fully implemented via explicit rewrite-step lists, giving transport, symmetry, and congruence lemmas without placeholders.
- The rewrite system (now split across `ComputationalPaths/Path/Rewrite/SimpleEquiv.lean`, `Step.lean`, `Rw.lean`, `RwEq.lean`, and `Quot.lean`) covers the reflexive/transitive/symmetric closures together with `mapLeft`/`mapRight` congruence reductions, bringing the development closer to the full LNDEQ suite.  `SimpleEquiv` factors out reusable equivalence helpers, `Step` records the primitive reductions, while `Rw` and `RwEq` provide the closures and expose the `RewriteLift` transport lemmas for both relations.  The new `rwEqSetoid`/`PathRwQuot` constructions (now housed in `Rewrite/Quot.lean`) package rewrite equality as a `Setoid` and quotient so `refl`/`symm`/`trans` work directly on equivalence classes.  Dependent substitution is still handled via the `Path.apd` combinator together with `rw_apd_refl`/`rweq_apd_refl`, and fresh `sigma`-specific β-rules (`rw_sigma_snd_beta`, `rweq_sigmaFst_sigmaMk`, `rweq_sigmaSnd_sigmaMk`) plus the canonical reflexivity lemma `rweq_sigmaMk_refl` ensure dependent pairs reduce componentwise down to the reflexive witness.
- Canonical normal forms are now unique: every path rewrites to `ofEq (toEq p)` via the `normalize` function, and the rewrite relation is confluent so any two reductions from the same origin meet again at that canonical witness.  The new `IsNormal` predicate, `normalizeForm` constructor, uniqueness lemmas (`normalize_eq_of_rw`, `rw_isNormal_eq`, `normalizeForm_unique`), and the quotient-level helpers `PathRwQuot.normalPath`/`PathRwQuot.normalForm` make the paper's normal-form arguments directly usable inside Lean and on the `PathRwQuot` quotient; fresh compatibility lemmas (`rweq_normalPath_trans`, `rweq_normalPath_symm`, etc.) ensure these canonical witnesses line up with the strict groupoid operations on quotients.
- Definition 3.5's contextual substitution rules (`sub L`/`sub R`) are available through the new `Context`/`BiContext` abstractions (`ComputationalPaths/Path/Basic/Context.lean`).  These package unary and binary holes so that plugging a computational path through any context automatically produces the induced path, together with proofs that the operation respects `refl`, `symm`, and `trans`.  At the rewrite level the `Step.context_congr`/`Step.biContext_*` constructors plus the closure lemmas (`rw_context_map_of_rw`, `rw_biContext_mapLeft_of_rw`, `rw_biContext_mapRight_of_rw`, `rw_biContext_map2_of_rw`, `rw_map2_of_rw`, …) ensure any `Rw` reduction can be lifted through arbitrary contexts—and their new symmetric counterparts (`rweq_context_map_of_rweq`, `rweq_biContext_mapLeft_of_rweq`, `rweq_biContext_mapRight_of_rweq`, `rweq_biContext_map2_of_rweq`, `rweq_map2_of_rweq`) provide the same closure guarantees for `RwEq`.  The brand new `DepContext` hierarchy extends this machinery to dependent codomains, and its just-added binary refinement `DepBiContext` now exposes two-hole dependent substitution together with rewrite rules (`Step.depBiContext_*`) so that transports, `apd`, and other fibre-sensitive terms can participate in contextual substitution just as smoothly as their non-dependent counterparts.  These upgrades also unlock fresh transport β-rules (`Step.transport_trans_beta`, `Step.transport_symm_left_beta`, `Step.transport_symm_right_beta`) so sequential and inverse transports reduce canonically inside the rewrite system.
- Iterating equality is now encoded by the `GlobularLevel` tower (`ComputationalPaths/Path/Basic/Globular.lean`), producing explicit higher-dimensional cells with reflexive, symmetric, and transitive structure at every stage of the path hierarchy.  The `GlobularLevel.toPath` API exposes the underlying computational path and is compatible with `refl`/`symm`/`trans`, and fresh `[simp]` lemmas describe how `symm` and `trans` rewrite their boundary endpoints so higher-dimensional manipulations can be related back to the base rewrite system.
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
- `ComputationalPaths/Path/Basic/Globular.lean` - iterated identity tower yielding the globular set generated by computational paths, closing it under `refl`/`symm`/`trans` dimension-wise, equipping it with the functorial `GlobularLevel.map` action induced by any base function, and providing `toPath` to recover the underlying computational witness.
- `ComputationalPaths/Path/Basic/Context.lean` - Definition 3.5 contexts with unary/binary substitution operators, capturing the labelled deduction `sub L`/`sub R` rules together with the `BiContext.map2` combinator for simultaneous two-hole substitution and the freezing helpers (`fixLeft`/`fixRight`) that recover unary contexts from a binary one; the rewrite layer now exposes the reusable `RewriteLift` abstraction together with `rw_context_map_of_rw`, `rw_biContext_mapLeft_of_rw`, `rw_biContext_mapRight_of_rw`, `rw_biContext_map2_of_rw`, and the specialized `rw_map2_of_rw` so every hole-filling context or binary substitution preserves `Rw` reductions out of the box.  Dependent users now have both `DepContext` and `DepBiContext` variants, mirroring the unary/binary split for fibre-valued codomains.
- `ComputationalPaths/Path/Rewrite/` - modular rewrite layer:
   - `SimpleEquiv.lean` collects the reusable equivalence gadgets used by quotients and other symmetry arguments.
   - `Step.lean` enumerates the primitive rewrite steps (β/η rules, associativity, contextual substitution) and proves they respect propositional equality.
   - `Rw.lean` builds the reflexive/transitive closure, normalization routines, and context-lifting lemmas for `Rw`.
   - `RwEq.lean` extends the closure to symmetry, packages the `RewriteLift` helpers for `RwEq`, and exposes congruence lemmas for every constructor.
   - `Quot.lean` defines `rwEqSetoid`, the quotient `PathRwQuot`, normal forms on the quotient, and the equivalence with propositional equality.
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
- Finish the LNDEQ rewrite suite by adding the outstanding β/η rules beyond the current context/bi-context coverage (notably the dependent eliminators for transports, `apd`, and quotient-facing operations) so that every construct from the paper has an explicit `Step` witness.
- Extend the new normalization theorems to those remaining LNDEQ rules and push them deeper into downstream constructions (transport, functors, higher coherences) so that every operation on `PathRwQuot` automatically exposes its canonical witness.
- Connect computational paths with Lean's identity type tooling (UIP counterexamples, rewriting tactics).
- Develop illustrative formal proofs using the new infrastructure.
