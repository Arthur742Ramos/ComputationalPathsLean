# Inspector Feedback — Iteration 1

## Verdict: FAIL

## Acceptance Criteria Check

- [x] Criterion 1 — verified: `ComputationalPaths.Path` imports the four new raw modules and `ComputationalPaths.lean` imports that public root.  A root-import check reports `computational_path_adequacy.{u, v}` and `RawMLTT.raw_computational_path_adequacy`.
- [x] Criterion 2 — verified: `RawSyntax.Expr` is an independent indexed de Bruijn syntax with explicit `Ren`, `Sub`, contexts, `Pi`, `Sigma`, `Nat`, code, identity, and equality-factored `eqJ` constructors.
- [x] Criterion 3 — verified: `RawSyntax` defines and proves identity/composition laws for `Ren`, identity/composition laws for simultaneous substitution, and explicit `Ren.lift`/`Sub.lift` binder laws, including one- and two-variable instantiation.
- [x] Criterion 4 — verified as representation: `HasType` and `Computation` contain formation, introduction, elimination, and the requested beta/reflexivity/equality-factored-J constructors for the listed fragment.
- [ ] Criterion 5 — FAILED: the claimed semantic typing/computation result is not a non-circular compositional soundness theorem.  `SemHasType` in `RawSemantics.lean` is a second copy of the raw `HasType` rules over `denote` values, and `typing_sound` is a constructor-for-constructor relabeling.  `interpret` remains a function from a raw `Expr` to a quotient; no quotient-level substitution action or theorem that `DefEq` is preserved by substitution is provided.  Moreover, `TypedComputation` takes `targetTyping` as an input, and `typed_computation_sound` merely applies `typing_sound` to that supplied field, so it does not prove computation preserves typing.
- [x] Criterion 6 — verified: raw `IdentityExpr.atom` accepts only source `DefEq`; raw `IdentityStep`/`IdentityRwEq` contain only source constructors and frames.  `Path.Step`/`RwEq` constructors occur in the soundness proof, not in the source rule grammar.  The proof covers units, inverses/cancellation, inverse composition, associativity, and congruence.
- [x] Criterion 7 — verified with the stated restriction: `term_model_endpoint_adequacy` explicitly restricts reflection to quoted raw terms in the `DefEq` quotient.  Its use of `Quotient.exact` is definitionally exact for that restricted syntactic model and does not use a target-rule escape hatch.
- [x] Criterion 8 — verified: `proofInsensitiveJ`/`eqJ_beta_path` and `no_traceSensitiveJ` are both present and packaged together, and the latter separates equality-factored elimination from trace-sensitive `Path.steps` elimination.
- [x] Criterion 9 — verified: `MLTTAdequacy.lean` documents the bounded theorem, proof architecture, assumptions, explicit limitations, and the boundary with future univalence/HIT work.
- [ ] Criterion 10 — FAILED in part: the touched Lean files contain no `sorry`, `admit`, custom `axiom`, or `unsafe`, but the only `Path`/`RwEq` evidence in `RawJudgments.lean` is `JudgmentTraceCertificate`.  It is a reflexive trace over a derivation (`Path.stepChain rfl`, followed by `Path.trans p (Path.refl d)`) and its unit rewrite; it carries no source computation or judgmental content and is the success-shaped certificate excluded by the goal's “nontrivial” requirement.
- [x] Criterion 11 — verified: all required quality gates pass (details below).

## Quality Gate

- Command: targeted `lake build ComputationalPaths.Path.TypeTheory.RawSyntax ComputationalPaths.Path.TypeTheory.RawJudgments ComputationalPaths.Path.TypeTheory.RawSemantics ComputationalPaths.Path.TypeTheory.MLTTAdequacy`
- Result: PASS — `Build completed successfully (21 jobs).`
- Command: `lake build`
- Result: PASS — `Build completed successfully (8699 jobs).`
- Command: `python3 scripts/check_invariants.py`
- Result: PASS — `invariants OK: zero sorry / admit / custom axiom in ComputationalPaths/`.
- Command: `git diff --check`
- Result: PASS — no whitespace errors.

## Issues Found

1. **The semantic typing result is structurally duplicated rather than compositional.**  `SemHasType` mirrors every raw constructor and `typing_sound` maps each constructor directly.  Although `TermModel` is a quotient, `interpret` does not descend from a quotient term and there is no `DefEq`-under-substitution/well-definedness theorem.  Consequently the endpoint reflection theorem is exact by quotient construction, but the advertised semantic substitution/typing model is not established at the quotient level.
2. **The computation-preservation claim is vacuous.**  `TypedComputation` (RawJudgments lines 252–263) requires both `sourceTyping` and `targetTyping`; `TypedComputation.preservation` just returns `d.targetTyping`, and `typed_computation_sound` repeats it.  A central metatheorem should derive the target typing from source typing plus a `Computation` derivation (or explicitly remove the preservation claim and its certificate field).  The current construction cannot detect an ill-typed target.
3. **The raw universe rules are not a coherent predicative hierarchy.**  `sort level` has type `sort (level + 1)`, but `codeNatIntro`, `codePiIntro`, `codeSigmaIntro`, and `codeIdIntro` place a code in `sort level`, while `elForm` keeps the same level.  In particular, `elNatBeta level` relates `el (codeNat level)`, typed by `sort level`, to `.nat`, typed by `sort 0`, for arbitrary `level`.  This is not type-preserving for `level ≠ 0` and contradicts the module's own statement that the universe lives in its successor.  The claimed predicative code fragment needs corrected level rules (and a level-indexed/lifted natural-number interpretation) plus preservation evidence.
4. **`RawJudgments.lean` uses decorative Path integration.**  Its certificate is entirely over `d : HasType Gamma t A` with endpoints `d` and `d`; `Path.stepChain rfl` and a right-unit rewrite are not a nontrivial source certificate.  Replace this with a certificate involving actual source computation/structural data, or do not count this file as satisfying the per-file Path requirement.

## What Must Be Fixed

- Add a genuine quotient-level/compositional interpretation: prove source `DefEq` is stable under simultaneous substitution and define/use the induced semantic substitution, then state typing and computation soundness against that interpretation.
- Prove subject reduction for every claimed typed computation rule (including the universe-code rules), or narrow the public theorem so it does not call the assumed-target-typing structure preservation.
- Correct the universe-code level discipline and provide a coherent interpretation of lifted `Nat` at the claimed levels.
- Replace the reflexive `JudgmentTraceCertificate` with substantive `Path`/`RwEq` evidence tied to raw judgments or computation.
