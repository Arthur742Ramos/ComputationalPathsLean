# Computational-path weak omega-groupoid coherence core

## Preparation status: semantic repair in progress; not ready for intake

The original Comparator surface below passes its mechanical checks but does
not encode the claimed recursive globular structure. See `RESEARCH_AUDIT.md`.
The new `GlobularCompletion.lean` fixes the dimensional recursion and proves
globularity, identity/inverse boundary laws, parallel-boundary preservation,
and chosen higher fillers. It also supplies higher vertical composition and
its associativity, unit, and inverse comparisons. It is not yet a formalization
of a published operadic weak omega-groupoid definition and is not selected by
the existing Comparator. Do not treat either set of checks as intake readiness.

Run `bash scripts/check-repair.sh` to reproduce the repair and adversarial checks.
The accepted 49-page manuscript has been recovered locally and inspected;
the source version and outstanding claim-alignment issues are recorded in the audit.

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
`contractibility3`. However, the primitive transport premise is automatic for
every parallel pair: this is a chosen universal-filler completion, not an
independent proof that the original rewrite calculus intrinsically has those
coherences. Definition 3.9 of the accepted manuscript explicitly specifies it.

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
