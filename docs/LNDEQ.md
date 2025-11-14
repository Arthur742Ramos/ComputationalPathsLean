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
| 20a | `Σ`-elimination β on `Sigma.fst` (mxrs) | `Step.sigma_fst_beta` | Transporting dependent pairs through the first projection. |
| 20b | `Σ`-elimination β on `Sigma.snd` (mxls) | `Step.sigma_snd_beta` | Transporting dependent pairs through the second projection. |
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

- Extend the catalog of critical-pair witnesses beyond the currently mechanised
  β/η and unit overlaps so that every Knuth–Bendix row from §3.3 carries a named
  `Confluence.Join` certificate.  In addition to the context-sensitive
  cancellations (`tt` with `ttsv`/`tstu`), the substitution/unit overlaps
  (`tsbll`/`slr`, `tsbrl`/`srr`) and the symmetric cancellation pair
  (`stss`/`ssbl`) now have explicit joins.  The remaining Σ-heavy rows remain on
  the backlog.
- Exploit the quotient-facing lemmas to streamline downstream developments.
  Paper-style notation for quotient composition/inversion (`PathRwQuot.cmpA` and
  `PathRwQuot.invA`) now satisfies the usual unit/inverse laws by definition, and
  the new `Context.mapQuot` bridge shows that those equalities propagate through
  unary contexts.  Dependent/Σ contexts remain to be connected in the same way.

With the above caveats, every other LNDEQ rewrite either has a dedicated constructor or
is an instance of the congruence rules (`context_congr`, `symm_congr`, `trans_congr_*`) already
available in `Step.lean`.

## Termination and confluence witnesses

The follow-up automation lives in two new modules:

- `ComputationalPaths/Path/Rewrite/Termination.lean` packages normalization data.  The
  `Termination.Witness` structure stores a normal form together with a certificate that
  a path rewrites to it, and `Instantiation.sourceWitness`/`Instantiation.targetWitness`
  attach those witnesses directly to every LNDEQ rule instantiation.  Witnesses now ship
  with `RwEq`/`PathRwQuot` bridges, and the recursive-path ordering layer (`RecursivePathOrdering`)
  records the actual source/target path lengths inside the multiset arguments, mirroring the
  data-aware ordering from Definition 3.23.  The fresh `Instantiation.rpoTerm_measure`
  and `derivationMeasure_*` lemmas expose the multiset weight explicitly, showing that
  concatenating a non-empty derivation strictly increases the RPO measure (hence peeling
  steps strictly decreases it).
- `ComputationalPaths/Path/Rewrite/Confluence.lean` restates `rw_confluent` as concrete
  join objects.  The `Confluence.Join` record carries the common reduct and the two `Rw`
  derivations back to it, while `Confluence.of_steps` and `Instantiation.join` provide
  single-step versions for critical-pair checks.  Each join also exposes `RwEq` and
  `PathRwQuot` equalities so quotient-facing developments can cite the same witnesses.

Two auxiliary pieces keep the quotient and termination stories aligned with the paper:

- `Context.mapQuot` lifts unary contexts to the `PathRwQuot` level and satisfies
  `mapQuot (cmpA x y) = cmpA (mapQuot x) (mapQuot y)` together with the analogous
  statements for `invA` and `toEq`.  This lets higher coherences trade `cmpA`/`invA`
  equalities through functorial contexts without dropping back to raw paths.
- `LNDEQ.Derivation` records a tagged list of instantiations between two paths.
  The helper lemmas `Derivation.toRw`, `Derivation.toRwEq`, and
  `Derivation.measure_tail_lt` show that each tagged step witnesses a strict
  decrease of the recursive-path ordering measure `derivationMeasure`, making it
  possible to argue about termination directly on symbolic derivations rather
  than funnelling everything through `normalize`.

## Critical pair table

The first entries from the paper’s Knuth–Bendix table are now encoded as explicit
`Confluence.Join` witnesses.  Each lemma mirrors a row from §3.3 while keeping the
parameters abstract so it applies uniformly across contexts.

| Pair | Source shape | Join lemma |
|------|--------------|------------|
| `mx2l1` / `mx2l2` | `fst (Path.map2 Prod.mk p q)` | `Confluence.CriticalPairs.mx2_fst` |
| `mx2r1` / `mx2r2` | `snd (Path.map2 Prod.mk (refl a) q)` | `Confluence.CriticalPairs.mx2_snd` |
| `tt` / `rrr` | `trans (trans p q) (refl)` | `Confluence.CriticalPairs.tt_rrr` |
| `tt` / `lrr` | `trans (refl) (trans q r)` | `Confluence.CriticalPairs.tt_lrr` |
| `tt` / `ttsv` | `trans (Context.map C p) (trans (Context.map C (symm p)) v)` | `Confluence.CriticalPairs.tt_ttsv` |
| `tt` / `tstu` | `trans (trans v (Context.map C p)) (Context.map C (symm p))` | `Confluence.CriticalPairs.tt_tstu` |
| `tsbll` / `slr` | `trans (refl (C.fill a₁)) (Context.map C p)` | `Confluence.CriticalPairs.tsbll_slr` |
| `tsbrl` / `srr` | `trans (Context.map C p) (refl (C.fill a₂))` | `Confluence.CriticalPairs.tsbrl_srr` |
| `stss` / `ssbl` | `symm (trans r (Context.map C p))` | `Confluence.CriticalPairs.stss_ssbl` |
| `stss` / `ssbr` | `symm (trans (Context.map C p) t)` | `Confluence.CriticalPairs.stss_ssbr` |

The join proof for each entry is obtained by invoking `Instantiation.join` on the two
relevant instantiations (after matching their sources), so the resulting witnesses are
usable both at the `Rw` layer and inside `PathRwQuot` via the automatic bridges.  The
table is intentionally extensible: additional rows can be registered in
`Confluence.CriticalPairs` as more overlaps are audited.

These modules keep the Lean development in lockstep with the SAJL storyline: every
recorded rewrite reason now comes with a bundled normalization witness, and any pair of
instantiations with a shared source can be joined via the canonical representative
`Path.ofEq (toEq …)`.

## Next steps

The remaining work mirrors the “full proof” milestones from §3.3:

1. Expand the catalogue of `Confluence.CriticalPairs` entries until every row from the
  Knuth–Bendix analysis has a matching Lean witness.  Context-sensitive cases like
  `tt`/`ttsv` and `tt`/`tstu` are now covered; the goal is to push the same treatment to
  the Σ- and substitution-heavy overlaps.
2. Use the new `PathRwQuot.cmpA`/`invA` lemmas as the base step for quotient-level higher
  coherences, wiring these equalities through contexts, transports, and functorial maps.
3. Strengthen the recursive-path ordering story beyond the global `derivationMeasure`
  bounds—e.g. reflect the multiset decrease directly in `RwEq` derivations so the
  termination proof can avoid detouring through `normalize`.

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

