# Proof-relevant associativity coherence certificate

The Palomar comparator selects eight results in the namespace
`ComputationalPaths.Path.PalomarAssociativity`:

1. `assocStep_wellFounded` proves that context-closed, left-to-right
   associativity rotations terminate by a strict natural-number measure.
2. `assoc_normalizes` constructs a proof-relevant reduction from every
   Mathlib `FreeMagma` tree to the canonical fully right-associated tree of
   its `FreeSemigroup` word.
3. `rightComb_irreducible` proves that the constructed canonical right combs
   have no outgoing directed associativity rewrite.
4. `assoc_reduces_confluent` proves global confluence by joining arbitrary
   reductions at that canonical normal form.
5. `assoc_rwEq_iff_freeSemigroup_eq` proves soundness and completeness of the
   symmetric rewrite calculus against equality of nonempty words.
6. `assoc_rwEq_iff_assocQuotient_eq` identifies the same rewrite equality
   with equality in Mathlib's standard `Magma.AssocQuotient`.
7. `pentagon_route_counts` checks that Mac Lane's two pentagon routes contain
   two and three primitive rotations.
8. `pentagon_routes_distinct` uses those counts to prove that the two
   proof-relevant traces are syntactically different despite sharing their
   source and target.

This boundary is intentionally stronger than a bundled existence record.
Each major mathematical property is separately selected and reviewed. The
rewrite relation is connected to two pre-existing Mathlib semantics, so the
conclusions do not arise from a duplicated project-defined closure.

The result concerns the associativity-only fragment of computational paths.
It does not claim unit coherence, inverse coherence, a full monoidal category,
an intensional identity type, or a new mathematical theorem. Its contribution
is a compact, independently auditable Lean formalization joining termination,
normal forms, confluence, quotient completeness, and proof-relevant pentagon
traces in one standard-library-grounded certificate.

## Audit boundary

- `Challenge.lean` is 171 lines and imports only `Mathlib.Algebra.Free`.
- It contains exactly eight deliberate theorem holes, one for every selected
  declaration and no holes in definitions.
- `Solution.lean` repeats the public statement boundary and supplies every
  proof with no `sorry`, `admit`, custom `axiom`, or evaluator escape.
- `comparator.json` selects all eight results and enables NanoDa replay.
- `scripts/check-palomar-associativity.sh` verifies source closure, limits,
  theorem selection, metadata, forbidden markers, axioms, and builds.

## Reproduce

```bash
scripts/check-palomar-associativity.sh
```

The project is pinned by `lean-toolchain` and `lake-manifest.json` to Lean
4.33.0 and the corresponding Mathlib release.
