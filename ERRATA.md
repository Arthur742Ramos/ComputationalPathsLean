# Errata and corrections

This file records corrections to earlier public descriptions of this
development. No previously proved theorem is retracted; what changes is naming
and interpretation.

The corrections are stated in full, with proofs, in
`paper/adequacy/main.tex` (*Identity Elimination with Observable Metadata, and
the Collapse of a Computational-Path Rewrite Quotient*), Section
"Which earlier statements are corrected".

## Affected artifacts

| Artifact | Status |
| --- | --- |
| arXiv:2511.19142, *Formalizing Computational Paths and Fundamental Groups in Lean* | Corrected below; a revised version is to be posted alongside the adequacy articles |
| Repository `README.md` and module documentation | Updated |
| `paper/main.tex` (monograph/preprint source) | Updated |

## (C1) The `π₁` aliases

Two names in the development, and the accompanying documentation, presented the
**winding-expression quotients** as fundamental groups of the circle and the
torus computed by the computational-path machinery.

The encode/decode theorems behind `circlePiOneEquivInt` and
`torusPiOneEquivIntProd` are correct, but they are theorems about a separately
introduced syntax of loop expressions. They are **not** statements about
`PathRwQuot`, and they cannot be transported to it
(`MetadataRepair.no_circle_genuine_synthetic_bridge` and its torus analogue).

These objects are now named as *synthetic winding presentations*. The phrase
"genuine fundamental group" is replaced by "genuine `PathRwQuot` loop
quotient".

## (C2) The "drop-in replacement" description

The abstract of arXiv:2511.19142 describes the trace-carrying `Path` record as a
drop-in replacement for propositional equality, and presents the circle and
torus results without the genuine/synthetic distinction. Both descriptions are
withdrawn.

- The raw record is **not** interchangeable with ambient equality: its
  reflexivity fiber is `List A`, so it admits no unrestricted based eliminator
  on any pointed carrier (`MetadataRepair.raw_loop_fiber_not_contractible`).
- Its rewrite quotient **is** interchangeable with ambient equality, but only in
  the degenerate sense that `PathRwQuot A a b ≃ PLift (a = b)` for every carrier
  (`QuotientPathInduction.rweq_total`,
  `QuotientPathInduction.pathRwQuotEquivPLiftEq`). It therefore retains no
  computational-path information, and every invariant on it is constant.

## (C3) The suggested genuine/synthetic bridge

A connection between the genuine and synthetic objects was described as
unformalized future work. It is not future work: no equivalence exists under the
current definitions, and by the collapse theorem no change of carrier can
produce one
(`QuotientPathInduction.no_loop_quotient_equiv_of_not_contractible`).

## (C4) Normalization as a characterization of `RwEq`

Some documentation described the implemented normalization function as
characterizing rewrite equivalence. That function depends only on the ambient
equality, so it is a **sound invariant** of `RwEq`; equality of normal forms is
not by itself a rewrite certificate. A converse requires a separately supplied
complete step system.

## (C5) Unqualified "path induction" claims

`PathRwQuot` does support unrestricted based path induction on every carrier,
with a beta law that is here even judgmental. Stated without its cause, this
invites the reading that a proof-relevant path object has been shown to admit
`J`. It has not. The supported formulation keeps the reason attached:

> the implemented rewrite quotient supports path induction **because** it is
> equivalent to ambient equality.

## Axiom footprint

All results named above depend only on `propext` and `Quot.sound`.
`Classical.choice` is not used, and the development declares no custom axioms.
