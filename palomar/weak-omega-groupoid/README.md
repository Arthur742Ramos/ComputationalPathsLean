# Computational-path weak omega-groupoid coherence core

This directory is a small, standalone Palomar project extracted from the
accepted manuscript *Computational Paths Form a Weak omega-Groupoid: A
Constructive Proof*. It is intentionally a focused formalization boundary,
not a claim that the paper's applications and full companion repository fit in
one short Comparator challenge. The accepted manuscript is the source for this
scope; `formalization.yaml` records the distinction from the earlier public
arXiv version.

The checked boundary contains:

- trace-carrying paths and proof-relevant rewrite equivalence;
- a Type-valued `RwEq` derivation layer and its Prop-valued `RwProp` projection;
- explicit level-3, level-4, and indexed higher proof-irrelevance contractions;
- path groupoid laws;
- two distinct, step-counted routes around the associativity pentagon; and
- named pentagon, triangle, full four-2-cell interchange, and Eckmann-Hilton
  coherence cells;
- the `CellType` tower and the selected `WeakOmegaGroupoidBoundary`.

`MetaStep3.rweq_transport` is the sole primitive 3-cell. In particular,
pentagon, triangle, interchange, and Eckmann-Hilton are derived through
`contractibility3`; they are not constructors inserted to make the advertised
coherences hold.

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

There are twelve deliberate holes in the Challenge, including the selected
declaration statements; the Solution has none. The Challenge is 346 lines,
so Palomar's documented auditability warning is reported but its hard 1,000
line/100 KiB limit is respected. This size is the cost of retaining explicit
level-4, higher-tail, and cell-tower boundaries.

The project uses only `propext` among the permitted Lean axioms for the
selected declarations. It does not use `Classical.choice`, `Quot.sound`,
`native_decide`, or a custom axiom.
