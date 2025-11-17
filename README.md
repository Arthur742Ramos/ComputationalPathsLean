# Computational Paths (Lean 4)

Lean 4 formalisation of propositional equality via explicit computational paths and rewrite equality. It provides a practical kernel for transport, symmetry, congruence, rewrite quotients, and normalisation — and uses this machinery to formalise the fundamental group of the circle.

Highlights
- Loop quotients and π₁(A, a) as rewrite classes with strict group laws.
- Higher-inductive circle interface + code family into ℤ (via univalence axioms).
- Completed proof π₁(S¹) ≃ ℤ using an encode–decode argument with quotient→equality reduction (no local placeholders).

Quick Start
- Build: `./lake.cmd build`
- Run demo: `./lake.cmd exe computational_paths` (prints version)
- Open in VS Code: install Lean 4 extension, open the folder, and build.

Project Layout (selected)
- `ComputationalPaths/Path/Basic/*` — core path definitions (transport, congruence, symmetry) and helpers.
- `ComputationalPaths/Path/Rewrite/*` — rewrite steps, closures (`Rw`, `RwEq`), and the quotient `PathRwQuot`.
- `ComputationalPaths/Path/Groupoid.lean` — weak and strict categorical packages for computational paths; groupoids extend the corresponding categories so composition/identities are shared.
- `ComputationalPaths/Path/Homotopy/*` — loop spaces, rewrite monoids (`LoopMonoid`), loop groups (`LoopGroup`), and π₁ interfaces.
- `ComputationalPaths/Path/HIT/Circle.lean` — circle HIT interface, code family into ℤ, encode/transport lemmas, z-powers.
- `ComputationalPaths/Path/HIT/CircleStep.lean` — step laws, encode∘decode=id on ℤ, decode∘encode=id on π₁, and decode-add/sub/group lemmas.

Circle π₁(S¹) ≃ ℤ (what to read)
- Encoding: `circleEncode : π₁(S¹) → ℤ` via quotient-lift of `circleEncodePath`.
- Decoding: `circleDecode : ℤ → π₁(S¹)` by z-powers of the fundamental loop.
- Step laws: `circleEncode (x ⋆ loop) = circleEncode x + 1` and the inverse step.
- Identities:
  - Right-inverse on ℤ: `circleEncode (circleDecode z) = z` (by integer induction).
  - Left-inverse on π₁: `circleDecode (circleEncode x) = x` (reduce to equality with `toEq` and use equality induction).
- Homomorphism (circle-specific): decode respects addition, subtraction, and group multiplication — proved from the step laws and encode injectivity.

Assumptions (axioms)
- Circle HIT interface (constructors + β-rules) and a lightweight univalence axiom (`ua`, `ua_beta`).
- No other placeholders remain; everything else is constructed inside Lean.

Contributing
- Build after non-trivial edits: `./lake.cmd build`.
- Keep docstrings in sync, prefer small, focused lemmas with `@[simp]` where useful.
- The simplifier linter flags unused simp arguments; please trim them.
- When a structure adds data on top of an existing interface, prefer extending the smaller structure (e.g. `WeakGroupoid` extends `WeakCategory`) to keep identities/composition definitions in one place.

Citation
- Based on the thesis’ Chapter 5 development of computational paths and the fundamental group of the circle. See `docs/thesis` for source materials.
