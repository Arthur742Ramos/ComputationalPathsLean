# Proof-relevant omega-groupoid certificate

The selected result is

```text
ComputationalPaths.Path.PalomarOmegaGroupoid.main_result
```

It is checked for every carrier type `A` and packages the repository's native
computational-path developments in one auditable boundary:

1. The 1-cells are trace-carrying `Path` records, so the equality proof and
   the explicit rewrite trace are both retained.
2. The 2-cells are Type-valued `Derivation₂` witnesses.  Their equivalence
   with the symmetric, reflexive, transitive `RwEq` closure is proved in both
   directions, including both reification round trips.
3. The core normalizer has an explicit KBO/redex measure.  Every core rewrite
   step decreases that lexicographic measure, the output carries both a strict
   normal-form witness and a core-strictness witness, and a typed `Derivation₃`
   bridge connects every input derivation to the normal form.
4. The Mac Lane pentagon is represented by two explicit rewrite routes with
   two and three primitive edges.  The triangle has two and one.  The kernel
   proves the counts and therefore proves that the routes are syntactically
   distinct.  Their higher coherence cells are then derived from the
   corresponding explicit local-confluence diamonds, with only administrative
   unit/associativity cells added; they do not invoke the primitive pentagon
   or triangle labels.
5. The package includes a second inverse-cancellation critical pair,
   proof-relevant interchange, and Eckmann--Hilton commutativity for 2-loops.
6. The native stabilized tower supplies the higher-cell contractibility
   boundary: level 4 and above are contractible, while the lower derivation
   and route syntax remains explicit.  The certificate also proves concrete
   nontriviality at the path, 2-cell, and 3-cell syntax levels.

This is a formalized synthesis of the computational-path rewrite calculus and
its weak omega-groupoid coherence.  Its scope is intentionally precise: the
construction is extensional Lean mathematics, not an intensional HoTT
identity type and not a constructive Squier finite-derivation-type theorem.
The selected result uses the repository's standard `propext`, `Quot.sound`,
and `Classical.choice` dependencies; no custom axioms, proof holes, evaluator
escapes, or external mathematical input are used.

## Reproduce

The project is pinned to Lean 4.24.0 and Mathlib v4.24.0. Run:

```bash
lake build
lake build ComputationalPaths.Path.OmegaGroupoid.PalomarStatement
lake env lean Challenge.lean
lake env lean Solution.lean
scripts/check-palomar-omega.sh
```

`Challenge.lean` contains the single statement-side `sorry` required by the
Palomar comparison protocol. `Solution.lean` and the selected statement module
contain no proof holes or custom axioms.
