# Observable metadata, identity elimination, and the PathRwQuot collapse

- `main.tex` is the focused article, *Observable Metadata and Identity
  Elimination: Contractibility Criteria, Exact Setoid-Quotient Repair, and the
  PathRwQuot Case Study*.
- `companion/main.tex` is the distinct 37-page raw scoped-calculus manuscript.
- Each directory has its own `refs.bib` and builds independently with
  `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`.

The Lean counterparts are

| Module (under `ComputationalPaths/Path/TypeTheory/`) | Content |
| --- | --- |
| `MetadataJ.lean` | metadata-fiber diagnosis, factorized motives |
| `MetadataRepair.lean` | setoid repair, projection/kernel, `PathRwQuot`/K, raw-level `RwEq`-totality criterion, computed trace fiber, failing parity repair, circle/torus no-bridge |
| `QuotientPathInduction.lean` | the collapse theorem, quotient path induction, universal no-bridge, groupoid-fragment sharpness |

## Resolution pass: computational paths do have path induction

The raw-level criterion of Section 6 reduces unrestricted `J` for `PathRwQuot`
to an elementary question about primitive rewrite rules: is `RwEq` total on raw
loops?  That question, previously left open, is now settled affirmatively.

- **Section 7, the collapse theorem.** `Path.lamCongr` records the *empty*
  trace, while `Path.congrArg` maps traces pointwise.  Instantiating
  `Step.fun_app_beta` at `PUnit` therefore yields a primitive rewrite
  `Path.mk [] p.proof ▷ p` for *every* `p : Path a b`.  Hence `RwEq` is total on
  every fiber, `PathRwQuot A a b ≃ PLift (a = b)`, quotient-level axiom K holds
  on every carrier, and `PathRwQuot` supports unrestricted based path induction
  unconditionally — with a beta law that is here even judgmental.
  Lean: `stepEmptyTrace`, `rweqAny`, `rweq_total`, `rwEqTotalOnLoops_always`,
  `pathRwQuot_subsingleton`, `pathRwQuotEquivPLiftEq`,
  `pathRwQuot_loop_contractible`, `pathRwQuot_localAxiomK`,
  `pathRwQuot_axiomK`, `pathRwQuotJ`, `pathRwQuotJ_beta`, `pathRwQuotJ'`,
  `pathRwQuotTransport`, `pathRwQuotEliminator`.
- **The price.** The repair produced is the indiscrete one, exactly as the
  universal repair theorem of Section 5 predicts.  `PathRwQuot` therefore
  retains no rewrite information beyond ambient equality.  The raw-versus-quotient
  dichotomy is recorded as `raw_fails_quotient_succeeds`.
- **Section 7.4, sharpness.** The groupoid fragment of the rewriting system
  (unit, inverse, associativity, congruence, cancellation) preserves
  trace-length parity, so it does *not* identify the empty and singleton
  reflexive traces.  The collapse is caused by the function-space rules
  together with the trace-erasing definition of `lamCongr`, not by path algebra.
  Lean: `GroupoidStep`, `groupoidStepToStep`, `GroupoidRwEq`,
  `groupoidStep_traceParity`, `groupoidRwEq_traceParity`,
  `groupoid_fragment_not_total`, `groupoidSetoid`,
  `groupoidSetoid_not_setoidTotal`,
  `groupoid_quotient_loop_not_contractible`,
  `fragment_fails_full_system_succeeds`.  The last of these puts the two
  rewrite systems side by side: over the same carrier they land on opposite
  sides of the classification, so the criterion of Section 6 does real work in
  both directions.
- **Section 10, universal no-bridge.** The circle/torus no-bridge results now
  hold for every pointed carrier, not only the one-constructor ones: no genuine
  `PathRwQuot` loop quotient is equivalent to a noncontractible type.
  Lean: `no_loop_quotient_equiv_of_not_contractible`,
  `no_loop_quotient_equiv_int`, `no_loop_quotient_equiv_int_prod`.
- **Section 10.5, corrections.** The manuscript now states explicitly which
  earlier public claims are corrected: the `circlePiOne`/`torusPiOne` aliases,
  the suggested genuine/synthetic bridge, the description of the implemented
  normalization function, and the previously conditional local-K statements.
- **Positioning.** Theorem 3.1 is now labelled as the proof-irrelevant,
  propositional-beta specialization of the identity-system characterization
  (HoTT Book Thm. 5.8.2; Awodey–Gambino–Sojakova) and is explicitly not claimed
  as a contribution.

All new results depend only on `propext` and `Quot.sound`; `Classical.choice` is
not used.

## Earlier review pass (post-merge of #96/#97)

- **Section 6.3, raw-level criterion.** `PathRwQuot` is an ordinary setoid
  quotient of raw paths, so the universal repair criterion of Section 5
  applies to it directly. The result removes the quotient from the statement:
  elimination exists iff `RwEq` relates *every* pair of raw loops at the base
  point.
  Lean: `loop_quotient_contractible_iff_rweq_total`,
  `local_axiomK_iff_rweq_total`, `pathRwQuot_elimination_iff_rweq_total`,
  `elimination_forces_rweq_on_raw_loops`, `pathRwQuot_axiomK_iff_rweq_total`.
- **Section 9, computed trace fiber.** A step is determined by its source, so
  `Step A ≃ A` and `Path a a ≃ List A`. Failure for raw records is therefore
  unconditional on every pointed carrier.
  Lean: `stepEquivPoint`, `traceEquivPointList`, `loopPathEquivPointList`,
  `raw_loop_fiber_not_contractible`.
- **Section 5.4, a nontrivial repair that fails.** Trace-length parity
  collapses infinitely many traces yet leaves two reflexivity classes, so it
  repairs nothing.
  Lean: `traceParitySetoid`, `traceParity_identifies_distinct_traces`,
  `traceParity_not_setoidTotal`, `trace_parity_repair_fails`.
