# Auditing a Scoped Calculus of Equality Traces

`main.tex` is a self-contained article. It builds independently of any other
manuscript in this repository:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

## What kind of paper this is

A machine-checked **audit** of the raw scope-indexed calculus underlying this
development — not a proposal for a new type theory. Its findings are stated as
theorems in both directions: what the calculus proves, and what it demonstrably
fails to prove.

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
- **subject reduction fails, and this is proved** — contextual subject reduction
  is false in the raw system, with an explicit counterexample; neither the
  conversion rule nor its context-wise companion is admissible; and the
  hypothesis record packaging them is therefore *uninhabited*, so the
  conditional subject-reduction theorem derived from it is vacuous as a
  statement about the raw judgment. What that conditional proof does establish
  is an analysis of the induction: repairs of exactly two shapes close every
  case. The conversion-closed extension is defined and admits both rules, but no
  unconditional subject-reduction theorem is claimed for it, because that needs
  generation lemmas and hence confluence;
- a syntactic quotient with representative-independent, compositional
  substitution;
- **derivation erasure** — evaluation of source identity programs factors
  through a label-free syntax over the quotient whose atoms carry only
  proof-irrelevant equalities of classes. Erasure preserves program size, and
  at atoms it is inverse to the recovery map from quotient exactness. This
  makes "unlabelled" a theorem rather than a naming convention;
- **the essential image of erasure** — the label-free grammar admits congruence
  by arbitrary endofunctions, so erasure is *not* surjective onto it. The image
  is characterized exactly: it is the framed fragment, whose atoms are quotient
  soundness applied to a source definitional equality and whose congruences are
  induced by source frames;
- the trace-record elimination obstruction: the quotient trace fiber is a list
  of quotient classes and is never contractible.

## Lean counterparts

| Area | Module |
|---|---|
| Scoped syntax, binder algebra | `ComputationalPaths/Path/TypeTheory/RawSyntax.lean` |
| Typing, computation, primitive preservation | `.../RawJudgments.lean` |
| Contextual & multi-step reduction, conditional subject reduction | `.../RawReduction.lean` |
| Failure of subject reduction, inadmissibility, conversion-closed extension | `.../RawConversionNecessity.lean` |
| Quotient, identity programs, rewrite soundness | `.../RawSemantics.lean` |
| Derivation erasure | `.../RawErasure.lean` |
| Essential image of erasure | `.../RawErasureImage.lean` |
| Metadata-fiber criterion (imported from the companion article) | `.../MetadataJ.lean` |

The development declares no custom axioms and contains no `sorry`. The
machine-checked theorems depend only on `propext` and `Quot.sound`; no form of
choice is used.

## Reproducibility

- Toolchain: Lean 4 `leanprover/lean4:v4.24.0`, pinned in `lean-toolchain`.
- Dependencies: `mathlib4` at tag `v4.24.0`, with the full transitive lock in
  `lake-manifest.json`.
- Build: `lake build`.
- Invariant check: `python3 scripts/check_invariants.py`.
- Axiom audit: `#print axioms` on any theorem named in the article.
