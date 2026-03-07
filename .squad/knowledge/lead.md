# Lead Knowledge

## 2026-03-06T13:12:14+00:00
- The repository already contains **two parallel coherence stories**: a proof-relevant one in `Path/OmegaGroupoid.lean` and a truncated wrapper layer in `Path/OmegaGroupoid/*.lean`.
- `RwEq` itself is already `Type`-valued; the regression happens when wrapper modules convert it to `Eq` with `rweq_toEq`.
- Pentagon, triangle, and interchange already have **primitive 3-cell constructors** in `MetaStep₃`; the wrapper layer is not using them.
- The current core still has a **residual Prop boundary** via `MetaStep₃.rweq_transport` and `strict_transport₃`, so “removing the wrapper `toEq` fields” alone is probably insufficient.
- `Homotopy/EckmannHilton.lean` is closer to the target design than `OmegaGroupoid/EckmannHiltonProof.lean`, but it still needs auditing because `contractibility₃` may hide the forbidden shortcut.
- Downstream modules already encode truncation in theorem names like `*_toEq`, so this refactor will likely propagate beyond the four headline files.

## 2026-03-06T14:07:32+00:00
- `OmegaGroupoid.lean` already contains the right proof-relevant primitives; the regression is in how some wrappers/truncations use them.
- `pentagonCoherence` and `triangleCoherence` are genuinely primitive 3-cells; they are not the problem.
- `GroupoidProofs.lean` already has good explicit route data; its missing piece is proof-relevant codomains for inverse-style coherences.
- `EckmannHiltonProof.lean` is split: `interchange_unfolded` is strong, but `hcomp_eq_vcomp` still hides behind generic normalization/contractibility.
- Several downstream files still tell the older “proof irrelevance / toEq” story and will likely need compatibility shims or documentation updates.

