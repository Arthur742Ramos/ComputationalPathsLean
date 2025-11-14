# LNDEQ rewrite coverage

Definition 3.21 of *Propositional Equality, Identity Types, and Computational Paths*
lists forty rewrite rules (the original paper refers to "39 rules" but the Knuth–Bendix
completion adds two context-sensitive `tt` cases).  The table below matches each of
those rules against the existing constructors in `ComputationalPaths/Path/Rewrite/Step.lean`.
When a rule uses a context `C[–]`, the Lean proof follows from the listed constructor
together with `Step.context_congr` or its dependent variants; similarly, symmetry-only
rules reuse the underlying step via `Step.symm_congr`.

| # | Paper rule (abbr.) | `Step` coverage | Notes |
|---|--------------------|-----------------|-------|
| 1 | `symm (refl)` → `refl` (sr) | `Step.symm_refl` | Direct translation of Definition 1.3. |
| 2 | `symm (symm r)` → `r` (ss) | `Step.symm_symm` | Cancels double symmetry. |
| 3 | `C[ trans r (symm r) ]` → `C[ refl ]` (tr) | `Step.trans_symm` + `context_congr` | Handles `r ⋅ r⁻¹`. |
| 4 | `C[ trans (symm r) r ]` → `C[ refl ]` (tsr) | `Step.symm_trans` + `context_congr` | Handles `r⁻¹ ⋅ r`. |
| 5 | `trans r (refl)` → `r` (rrr) | `Step.trans_refl_right` | Right unit for concatenation. |
| 6 | `trans (refl) r` → `r` (lrr) | `Step.trans_refl_left` | Left unit law. |
| 7 | `subL (C[r], C[refl])` → `C[r]` (slr) | `Step.context_subst_left_refl_left` | Removing useless `sub L` units. |
| 8 | `subR (C[refl], C[r])` → `C[r]` (srr) | `Step.context_subst_right_refl_right` | Right analogue of rule 7. |
| 9 | `subL(subL(s;C[r]); C[symm r])` → `…` (slss) | `Step.context_subst_left_idempotent` + `Step.symm_congr` | Nested left substitutions collapse even when the inner witness is the inverse of `r`. |
| 10 | `subL(subL(s;C[symm r]); C[r])` → `…` (slsss) | Same as rule 9 | Symmetric version obtained via `Step.symm_congr`. |
| 11 | `subR(C[s]; subR(C[symm s]; r))` → … (srsr) | `Step.context_subst_right_cancel_inner` | Deletes the inner reflexive substitution. |
| 12 | `subR(C[symm s]; subR(C[s]; r))` → … (srrrr) | `Step.context_subst_right_cancel_outer` | Deletes the outer reflexive substitution. |
| 13 | `fst (pair r z)` → `r` (mx2l1r) | `Step.prod_fst_beta` | β-rule for `Prod.fst`. |
| 14 | `fst (pair (r,s) …)` → `r` (mx2l2r) | `Step.prod_fst_beta` | Same constructor handles simultaneous rewrites. |
| 15 | `snd (pair (r,s) …)` → `s` (mx2r1s) | `Step.prod_snd_beta` | β-rule for `Prod.snd`. |
| 16 | `snd (pair x s)` → `s` (mx2r2s) | `Step.prod_snd_beta` | Special case with only the right component changing. |
| 17 | `case (inl r)` reduces (mx3ls) | `Step.sum_rec_inl_beta` | Sum-elimination β for the left branch. |
| 18 | `case (inr r)` reduces (mx3ru) | `Step.sum_rec_inr_beta` | Symmetric β-rule. |
| 19 | `(λx. f x) a` → `f a` (mxlr) | `Step.fun_app_beta` | Dependent function β-rule. |
| 20 | `Σ`-elimination β (mxrs/mxls) | `Step.sigma_fst_beta` / `Step.sigma_snd_beta` | Transporting dependent pairs through `Sigma.fst`/`Sigma.snd`. |
| 21 | `⟨fst x, snd x⟩` → `x` (mxr) | `Step.prod_eta` | Pair η-rule. |
| 22 | `case` congruence (mxxt) | `Step.context_congr` for the `Sum.rec` context | Scrutinee/branch reductions are lifted through contexts. |
| 23 | `λx, h x` → `h` (xmrr) | `Step.fun_eta` | Function η-rule. |
| 24 | Dependent pair η (mxlrs) | `Step.sigma_eta` | Rebuild-and-project on Σ collapses. |
| 25 | `symm (trans r s)` → `trans (symm s) (symm r)` (stss) | `Step.symm_trans_congr` | Symmetry distributes over concatenation. |
| 26 | `symm (subL r s)` ↔ … (ssbl) | `Step.context_subst_left_beta` + `Step.symm_congr` | Derived by taking symmetry of rule 35. |
| 27 | `symm (subR r s)` ↔ … (ssbr) | `Step.context_subst_right_beta` + `Step.symm_congr` | Symmetric counterpart of rule 26. |
| 28 | `symm (inl r)` ↔ `inl (symm r)` (sx) | `Step.context_map_symm` | Works for any unary constructor context, here `Sum.inl`. |
| 29 | `symm (pair r s)` ↔ `pair (symm r) (symm s)` (sxss) | `Step.prod_mk_symm` | Dedicated constructor for pair symmetry. |
| 30 | `symm (λx, f x)` ↔ `λx, symm (f x)` (smss) | `Step.lam_congr_symm` | Captures symmetry through `Path.lamCongr`. |
| 31 | `symm (fst r)` ↔ `fst (symm r)` (sm·) | `Step.context_map_symm` | Projection contexts inherit symmetry from their argument. |
| 32 | `symm (snd r)` ↔ `snd (symm r)` | `Step.context_map_symm` | Mirrors rule 31 for the second projection. |
| 33 | `symm (case r …)` ↔ … | `Step.context_map_symm` | Sum eliminator is symmetric via the general context lemma. |
| 34 | `symm (Σ-elim r …)` ↔ … | `Step.depContext_map_symm` | Dependent contexts expose symmetry through `DepContext.symmMap`. |
| 35 | `trans r (subL (refl, s))` → `subL r s` (tsbll) | `Step.context_subst_left_beta` | Promotes contexts into left substitutions. |
| 36 | `trans r (subR (s, refl))` → `subR r s` (tsbrl) | `Step.context_subst_right_beta` | Right analogue of rule 35. |
| 37 | `trans (subL r s) t` → `trans r (subR s t)` (tsblr) | `Step.context_subst_left_assoc` | Associativity between `subL` and `subR`. |
| 38 | `trans (subR s t) u` → `subR s (trans t u)` (tsbrr) | `Step.context_subst_right_assoc` | Right-side associativity. |
| 39 | `trans (trans t r) s` → `trans t (trans r s)` (tt) | `Step.trans_assoc` | Standard associativity of concatenation. |
| 40 | `trans (C[u]) (trans (C[symm u]) v)` etc. (ttsv/tstu) | `Step.context_tt_cancel_left` / `Step.context_tt_cancel_right` | Reassociates context-driven cancellations directly, matching the Knuth–Bendix completions. |

## Outstanding items

- The table groups the dependent Σ β-rules (paper’s `mxrs`/`mxls`) under a single entry.
  If finer granularity is required, we can split rule 20 into separate rows referencing
  `Step.sigma_fst_beta` and `Step.sigma_snd_beta` individually.

With the above caveat, every other LNDEQ rewrite either has a dedicated constructor or
is an instance of the congruence rules (`context_congr`, `symm_congr`, `trans_congr_*`) already
available in `Step.lean`.

## Encoding strategy

The paper gives each rule a mnemonic (`sr`, `mx3ls`, `tsbrr`, …) and reasons about
composite rewrites by manipulating those names.  The Lean development can mirror this
by introducing a thin enumeration that records the “reason” and its instantiated data:

```lean
namespace LNDEQ

inductive Rule
  | sr | ss | tr | tsr | rrr | lrr
  | slr | srr | slss | slsss | srsr | srrrr
  | mx2l1 | mx2l2 | mx2r1 | mx2r2
  | mx3l | mx3r | mxlam | mxsigmaLeft | mxsigmaRight
  | mxetaProd | mxcase | mxetaFun | mxetaSigma
  | stss | ssbl | ssbr | sx | sxss | smss | smfst | smsnd
  | smcase | smsigma
  | tsbll | tsbrl | tsblr | tsbrr | tt | ttsv | tstu

structure Instantiation where
  rule : Rule
  context : Option (Context _ _) := none
  data : Step …

end LNDEQ
```

The exact shape of `Instantiation.data` depends on how much information we want to
store.  A practical compromise is to capture:

1. the `Rule` tag, so we can recover the paper notation;
2. a sigma-type carrying the proof witnesses (e.g. the particular `Path` arguments);
3. a lemma showing the tagged data really produces the `Step` we claim, e.g.

```lean
def eval : Instantiation → Σ A a b, Step (a := a) (b := b)
```

This lets us prove statements such as “every `Step` is generated by some `Rule`” and
“applying two instantiations with compatible sources produces a valid `Step.trans`”.

Implementation outline:

1. **Enumerate rules:** create `ComputationalPaths/Path/Rewrite/LNDEQ.lean` defining
  `Rule` with one constructor per row of the coverage table.  The pair of
  context-sensitive completions (`ttsv`/`tstu`) now map to the dedicated
  `Step.context_tt_cancel_left/right` lemmas.
2. **Instantiation records:** define `Structure Instantiation` with the actual `Path`
  arguments.  For example, the `sr` case would store the type `A` and the point `a`,
  while `mx3ls` would store `A`, `B`, `a`, `b`, the motive(s), and the branch proofs.
3. **Interpreter:** write `def Instantiation.step : Step p q` that pattern matches on
  `rule` and reconstructs the corresponding `Step` constructor.  This factors common
  arguments (e.g., contexts) so composed rewrites can be kept symbolic and compared to
  the paper’s proofs.
4. **Automation hooks:** expose helper tactics that, given a goal `Step p q`, try to
  build an `Instantiation` automatically.  This creates an audit trail in Lean terms
  mirroring the annotated rewrite derivations used in the SAJL article.

By funnelling every primitive reduction through `Instantiation`, we gain a uniform way
to cite rewrite reasons and to reason about termination/confluence on the Lean side.

## Planned rewrite-proof work

To finish aligning the code with §3.3 of the paper we need two major workstreams:

1. **Termination proof:** replicate Dershowitz’s recursive path ordering in Lean by:
  - defining the precedence relation on `Rule` (mirrors the `>` relations in Definition 3.23);
  - proving `Instantiation.step` decreases under that ordering; and
  - wrapping it in a well-founded recursion principle so that `Rw` and `RwEq` inherit
    termination automatically.
  This likely lives in a new module `Rewrite/Termination.lean` that imports the
  `Rule` enumeration and the `Instantiation` interpreter.
2. **Confluence and correspondence:** re-run the Knuth–Bendix superposition inside Lean.
  Rather than duplicating the full completion, we can state the critical pairs obtained
  in the paper and `simp`-prove them using the existing `Step` constructors.  Afterwards,
  we should add lemmas tying rw-equality to `RwEq` (Definition 3.25), e.g.,
  `lemma of_rweq : RwEq p q → PathRwQuot.representative q = …`.  This cements the
  “rw = Step*” bridge and makes the groupoid proofs cite the same normalisation facts as
  the paper.

Deliverables for the next iteration:

- `LNDEQ.Rule` + `Instantiation` data structures.
- A `Termination` module encoding the recursive path ordering and lifting it to `Rw`.
- A `Confluence` module packaging the critical pairs from the Knuth–Bendix completion
  and exporting `rw_confluent : Confluent Step`.

Once these pieces are in place we can formalise the paper’s Theorem 3.22 inside Lean
and reuse it in the globular/groupoid layers without re-proving ad-hoc normalisation
facts.

## Code scaffolding

The Lean side now includes `ComputationalPaths/Path/Rewrite/LNDEQ.lean`, which exports:

- `LNDEQ.Rule`: the enumerated type listing every row from the coverage table, letting us
  cite paper-style rewrite reasons inside Lean proofs.
- `LNDEQ.Instantiation`: a record bundling a `Rule`, the concrete `Path` arguments, and
  the corresponding `Step` witness, plus helpers `Instantiation.toRw` and
  `Instantiation.toRwEq` that inject the tagged step into the `Rw` / `RwEq` closures.

These definitions are the first step toward the “Instantiation interpreter” discussed
above: each `Step` constructor will be wrapped in a smart constructor that produces the
appropriate `Instantiation`, giving us a faithful, machine-checked account of LNDEQ’s
rewrite reasons.

