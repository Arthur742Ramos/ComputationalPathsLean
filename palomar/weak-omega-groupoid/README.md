# Weak omega-groupoid core for computational paths

This directory is a small, standalone Palomar project extracted from the
accepted manuscript *Computational Paths Form a Weak omega-Groupoid: A
Constructive Proof*. It is intentionally a focused formalization boundary,
not a claim that the paper's applications and full companion repository fit in
one short Comparator challenge.

The checked boundary contains:

- trace-carrying paths and proof-relevant rewrite equivalence;
- explicit level-3 and higher proof-irrelevance contractions;
- path groupoid laws;
- two distinct, step-counted routes around the associativity pentagon; and
- named pentagon, triangle, interchange, and Eckmann-Hilton coherence cells.

`Challenge.lean` is the human-auditable statement surface. `Solution.lean`
repeats that surface independently and supplies every selected proof/value.
The native correspondence is recorded in `formalization.yaml` and
`NATIVE_CORRESPONDENCE.md`; the compact namespace is necessary because Palomar
checks the Challenge import closure and does not allow it to import
repository-local modules.

## Reproduce the local audit

From this directory, with Lean 4.33.0 available through `elan`:

```bash
scripts/check.sh
```

The audit builds both modules, checks the deliberate Challenge holes and the
zero-hole Solution, verifies the narrow source closure, validates the metadata
and Comparator selection, and prints the kernel axiom report.

The project uses only `propext` among the permitted Lean axioms for the
selected declarations. It does not use `Classical.choice`, `Quot.sound`,
`native_decide`, or a custom axiom.
