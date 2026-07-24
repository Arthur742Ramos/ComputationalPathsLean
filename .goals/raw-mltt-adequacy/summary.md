# Raw MLTT computational-path adequacy

## Result

The repository now contains a substantial bounded adequacy development for a
predicative Martin-Lof type-theory fragment. It separates an independent raw
de Bruijn syntax from its computational-path semantics and proves the central
structural and semantic results without identifying trace-carrying `Path` with
the HoTT identity type.

## Acceptance criteria achieved

- The original semantic `MLTTAdequacy` certificate remains publicly imported
  with its explicit `.{u, v}` signature.
- Independent raw syntax covers `Pi`, `Sigma`, level-indexed lifted `Nat`,
  Tarski-style universe codes, identities, and equality-factored J.
- Binder-aware renaming and simultaneous substitution satisfy identity,
  composition, weakening, and instantiation laws.
- Raw typing and computation judgments cover the in-scope formation,
  introduction, elimination, and beta rules.
- `DefEq` is stable under substitution, and quotient-level model substitution
  is well-defined, functorial, and independent of representatives.
- Subject reduction is derived from source typing plus computation for every
  claimed primitive rule; target typing is no longer assumed.
- Raw identity rewrites contain no target `Path.Step`/`RwEq` escape hatch and
  evaluate soundly to the LND_EQ-TRS groupoid rewrites.
- Endpoint adequacy is stated exactly for quoted expressions in the declared
  `DefEq` quotient, avoiding a global completeness or initiality overclaim.
- Equality-factored identity elimination is paired with the formal obstruction
  to ordinary trace-sensitive J over raw `Path`.
- The modules document assumptions, proof architecture, and exclusions for
  univalence, HITs, normalization, canonicity, and full HoTT.
- All targeted and full builds, invariant checks, and whitespace checks pass.

## Iteration history

1. **FAIL:** The first implementation had constructor-mirroring semantic
   typing, assumed target typing in computation preservation, incoherent
   universe levels, and decorative Path evidence.
2. **PASS:** The implementation added genuine quotient semantics, proved
   substitution well-definedness and subject reduction, repaired universe
   levels with lifted naturals, and replaced the decorative certificate with
   computation-level Path/RwEq evidence.

## Inspector issues and resolutions

- **Non-compositional semantics:** resolved with `DefEq` substitution closure,
  quotient lifting, and model-substitution identity/composition/congruence.
- **Vacuous preservation:** resolved by removing target typing from
  `TypedComputation` and deriving it in `subject_reduction`.
- **Universe inconsistency:** resolved by level-indexing natural-number syntax
  and aligning Tarski codes and decoding with the predicative hierarchy.
- **Decorative Path use:** resolved with certificates over actual redex and
  contractum denotations, including cancellation and multi-rule
  reassociation/cancellation `RwEq` evidence.

## Recommendations

- The next paper result should prove normalization or initiality for a smaller
  core before attempting the whole fragment.
- A later extension can investigate a separate higher identity representation
  supporting genuine J; the current no-go theorem shows raw observable traces
  cannot provide it.
- Univalence and higher inductive types should remain separate future work and
  must not be inferred from this bounded adequacy theorem.
