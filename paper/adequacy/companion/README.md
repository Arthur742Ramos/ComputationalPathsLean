# A Scoped Calculus of Equality Traces

`main.tex` is a self-contained article. It builds independently of any other
manuscript in this repository:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

## What it proves

A raw, scope-indexed dependent-style calculus in de Bruijn form, together with:

- binder-correct renaming and simultaneous substitution, with identity,
  composition, lifting, weakening, and one- and two-variable instantiation
  laws;
- typed substitution for the raw typing judgment, and preservation of typing
  for ten top-level primitive redexes;
- **contextual and multi-step reduction** — the congruence closure of the
  primitive rules and its reflexive-transitive closure, both sound for
  definitional equality and stable under substitution;
- **conditional subject reduction** — contextual subject reduction fails in the
  raw system, and the article identifies exactly why: conversion and context
  conversion. Assuming those two rules as an explicit hypothesis record (never
  an axiom), subject reduction follows for the whole congruence closure. The
  theorem measures the distance to a conversion-closed calculus;
- a syntactic quotient with representative-independent, compositional
  substitution;
- **derivation erasure** — evaluation of source identity programs factors
  through a label-free syntax over the quotient whose atoms carry only
  proof-irrelevant equalities of classes. Erasure preserves program size, and
  at atoms it is inverse to the recovery map from quotient exactness. This
  makes "unlabelled" a theorem rather than a naming convention, and gives the
  precise contrast with label-sensitive computational paths;
- the trace-record elimination obstruction: the quotient trace fiber is a list
  of quotient classes and is never contractible.

## Lean counterparts

| Area | Module |
|---|---|
| Scoped syntax, binder algebra | `ComputationalPaths/Path/TypeTheory/RawSyntax.lean` |
| Typing, computation, primitive preservation | `.../RawJudgments.lean` |
| Contextual & multi-step reduction, conditional subject reduction | `.../RawReduction.lean` |
| Quotient, identity programs, rewrite soundness | `.../RawSemantics.lean` |
| Derivation erasure | `.../RawErasure.lean` |
| Metadata-fiber criterion | `.../MetadataJ.lean` |

The development declares no custom axioms and contains no `sorry`. The
machine-checked theorems depend only on `propext` and `Quot.sound`; no form of
choice is used.
