# Self-contained computational-path coherence certificate

The selected result is

```text
ComputationalPaths.Path.PalomarOmegaGroupoid433.main_result
```

It is checked for every carrier type `A` and packages a compact, standalone
statement boundary suitable for Palomar:

1. The 1-cells are trace-carrying `Path` records, retaining both an explicit
   `Step` list and its equality proof.
2. The 2-cells are Type-valued `Derivation₂` witnesses.  Their equivalence
   with the symmetric, reflexive, transitive `RwEq` closure is proved in both
   directions, including both reification round trips.
3. The Mac Lane pentagon is represented by two explicit rewrite routes with
   two and three primitive edges.  The triangle has two and one.  The kernel
   proves those counts and therefore proves that the routes are syntactically
   distinct.
4. The certificate records the extensional boundary coherence of each route
   pair, inverse cancellation, and a concrete nontrivial trace witness.  The
   higher boundary is stated precisely: it does not claim a proof-relevant
   higher syntax theorem in Lean's proof-irrelevant equality setting.

This is a formalized extraction of the trace, rewrite, and coherence ideas in
the larger Calculus of Computational Paths development.  `Challenge.lean` is
intentionally independent of the repository's local implementation modules;
it imports only `Mathlib`, which keeps its transitive source closure within
Palomar's allowlist.  `Solution.lean` repeats the statement boundary and
proves it independently with the Lean kernel.

The result is extensional Lean mathematics, not an intensional HoTT identity
type and not a constructive Squier finite-derivation-type theorem.  It uses
only the standard Lean dependencies permitted by the comparator: `propext`,
`Quot.sound`, and `Classical.choice`.  There are no custom axioms, proof
holes in the solution, evaluator escapes, or external mathematical input.

## Reproduce

The project is pinned to Lean 4.33.0 and Mathlib v4.33.0. Run:

```bash
lake build
lake env lean Challenge.lean
lake env lean Solution.lean
scripts/check-palomar-omega.sh
```

`Challenge.lean` contains the single statement-side `sorry` required by the
Palomar comparison protocol.  `Solution.lean` contains no proof holes or
custom axioms.
