# Diagnosis and universal metadata-repair paper

- `main.tex` is the focused article, *Equality with Observable
  Metadata: Diagnosis, Universal Quotient Repair, and the PathRwQuot Boundary*.
- `companion/main.tex` is a **self-contained** article, *A Scoped Calculus of
  Equality Traces: Structural Metatheory, Contextual Reduction, and Derivation
  Erasure*. It makes no reference to `main.tex` and is intended to be posted
  independently; `main.tex` cites it as `ScopedTraceCalculus2026`. See
  `companion/README.md`.
- Each directory has its own `refs.bib` and builds independently with
  `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`.

The Lean counterparts are
`ComputationalPaths/Path/TypeTheory/MetadataJ.lean` for the metadata-fiber
diagnosis and `ComputationalPaths/Path/TypeTheory/MetadataRepair.lean` for
setoid repair, projection/kernel, `PathRwQuot`/K, the raw-level
`RwEq`-totality criterion, the computed trace fiber, the failing parity
repair, traces, and no-bridge results.

## Review pass (post-merge of #96/#97)

Additions made while reviewing the merged manuscript:

- **Section 6.3, raw-level criterion.** `PathRwQuot` is an ordinary setoid
  quotient of raw paths, so the universal repair criterion of Section 5
  applies to it directly. The result removes the quotient from the statement:
  elimination exists iff `RwEq` relates *every* pair of raw loops at the base
  point. This links the two previously parallel halves of the paper and makes
  local K checkable on representatives.
  Lean: `loop_quotient_contractible_iff_rweq_total`,
  `local_axiomK_iff_rweq_total`, `pathRwQuot_elimination_iff_rweq_total`,
  `elimination_forces_rweq_on_raw_loops`, `pathRwQuot_axiomK_iff_rweq_total`.
- **Section 8, computed trace fiber.** A step is determined by its source, so
  `Step A ≃ A` and `Path a a ≃ List A`. Failure for raw records is therefore
  unconditional on every pointed carrier, in contrast with the conditional
  `PathRwQuot` criterion.
  Lean: `stepEquivPoint`, `traceEquivPointList`, `loopPathEquivPointList`,
  `raw_loop_fiber_not_contractible`.
- **Section 5.4, a nontrivial repair that fails.** Trace-length parity
  collapses infinitely many traces yet leaves two reflexivity classes, so it
  repairs nothing. This gives the necessity direction of the repair criterion
  a worked instance.
  Lean: `traceParitySetoid`, `traceParity_identifies_distinct_traces`,
  `traceParity_not_setoidTotal`, `trace_parity_repair_fails`.
- **Scope.** Whether some carrier violates raw `RwEq`-totality is stated as an
  explicit open question about the primitive rule set, rather than left
  implicit.
