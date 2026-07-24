# Goal: Raw MLTT computational-path adequacy

## User Request

Keep developing the computational-path adequacy result until the repository
contains substantial, defensible results suitable for a research paper.

## Refined Goal

Extend the existing bounded semantic certificate with an independent,
well-scoped raw syntax for a predicative Martin-Lof type-theory fragment with
dependent products, dependent sums, lifted natural numbers, universe codes, and
identity types. Prove the central structural and semantic metatheorems needed
for a paper: substitution laws, typing/computation soundness, and a
non-circular interpretation of source identity rewrites into `Path`/`RwEq`.
State the result conservatively: this is a bounded MLTT result, not full HoTT,
and raw trace-sensitive `Path` still does not satisfy ordinary J.

## Acceptance Criteria

- [ ] The existing `MLTTAdequacy` semantic result remains available through the
  public import root and retains its explicit `.{u, v}` theorem signature.
- [ ] One or more new modules under `ComputationalPaths/Path/TypeTheory/`
  define an independent de Bruijn-scoped raw syntax with contexts, types/terms
  (or a unified expression syntax), renaming, and simultaneous substitution for
  `Pi`, `Sigma`, `Nat`, predicative universe codes, and identity expressions.
- [ ] The raw syntax has machine-checked structural laws including renaming
  identity/composition and substitution identity/composition; binder lifting is
  handled explicitly rather than assumed.
- [ ] Formation, introduction, elimination, and computation judgments are
  represented for every in-scope type former. At minimum the development
  includes `Pi` beta, `Sigma` projection beta, `Nat` zero/successor beta,
  identity reflexivity, and the explicitly supported `Eq`-factored identity
  eliminator.
- [ ] A compositional interpretation from the independent source syntax into a
  clearly documented computational-path semantic model is implemented, with
  machine-checked substitution compatibility and typing/computation soundness
  for the fragment actually claimed.
- [ ] Source identity rewrites are defined independently of `Path.Step`: no
  source constructor may accept an arbitrary target `Path.Step` or `RwEq`
  witness. Their evaluation is proved sound in `RwEq`, covering reflexivity,
  inverse, composition, unit, inverse-cancellation, associativity, and
  congruence.
- [ ] The development proves a defensibly named adequacy/conservativity theorem
  connecting source derivability to the interpreted computational-path
  judgment. Any completeness or reflection theorem states its exact restricted
  domain and is not obtained through a target-rule escape hatch.
- [ ] The existing trace-sensitive-J obstruction is preserved and connected to
  the raw-syntax result, so the public theorem explicitly distinguishes
  `Eq`-factored elimination from unavailable path-trace-sensitive J.
- [ ] The main module documentation presents the mathematical theorem,
  assumptions, proof architecture, limitations, and relationship to future
  univalence/HIT work in paper-companion style.
- [ ] All touched Lean files contain no `sorry`, `admit`, custom `axiom`,
  `unsafe`, or success-shaped placeholders; each substantive new file has
  genuine `Path` integration and at least one nontrivial `RwEq` or multi-step
  `Path.trans` certificate.
- [ ] `lake build` succeeds, `python3 scripts/check_invariants.py` succeeds, and
  `git diff --check` reports no whitespace errors.

## Scope Boundaries

**In scope:**
- A bounded predicative MLTT fragment with `Pi`, `Sigma`, lifted `Nat`,
  universe codes, and identity types.
- Independent raw syntax, structural substitution metatheory, semantic
  interpretation, and identity rewrite soundness.
- Precise positive adequacy/conservativity statements and precise negative
  boundary statements.
- Documentation needed to make the formal result understandable and citable.

**Out of scope:**
- Univalence, general higher inductive types, truncations, or a claim that all
  HoTT is modeled.
- Treating trace-carrying `Path` as the HoTT identity type.
- A global normalization, canonicity, decidable type-checking, or initiality
  theorem unless it follows naturally and is fully proved.
- New axioms or placeholder assumptions.
- Rewriting unrelated generated/scaffold-heavy modules.

## Applicable Project Conventions

**Quality gate command:**
- `lake build`
- `python3 scripts/check_invariants.py`
- `git diff --check`
- During development, use the smallest targeted
  `lake build ComputationalPaths.Path.TypeTheory.<Module>` command first.

**Commit convention:**
- Conventional commits are preferred by recent history.
- Builder commits use `feat(paths): [B] ...` and trailer
  `Assisted-by: OpenAI:GPT-5.6-Sol`.
- Inspector commits use `chore(paths): [I] ...` and trailer
  `Assisted-by: OpenAI:GPT-5.6-Luna`.

**Guidelines:**
- `AGENTS.md`
- No additional `.agents/guidelines/`, `.github/guidelines/`, or
  `CONSTITUTION.md` files exist.

**Rules:**
- Maintain zero `sorry` and zero custom `axiom`.
- Use `Path` genuinely and include substantive `RwEq`/multi-step evidence.
- Prefer typed certificate structures over `True`, reflexive stubs, or strings.
- Preserve existing public APIs where possible.
- Keep the result honest about Lean `Eq` proof irrelevance and the observable
  `steps` metadata in `Path`.
