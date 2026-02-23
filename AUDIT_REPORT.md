# Audit Report: `diamond_filler` Implementation

**Auditor**: Automated audit (Copilot CLI)
**Date**: 2026-02-23
**Files examined**: `OmegaGroupoid.lean`, `Normalizer.lean`, `TruncationProof.lean`,
`RWEQ_ELIMINATION.md`, `ANALYSIS_contractibility3_without_rweq_eq.md`, `paper/main.tex`

---

## 1. Executive Summary

**Verdict: `diamond_filler` is mathematically sound but semantically identical to the
removed `rweq_eq`. It is NOT a genuine Squier-style finite derivation type constructor.
The paper must be updated to reflect the actual code.**

The refactoring from `rweq_eq` to `diamond_filler` was intended to replace a blanket
axiom ("any two parallel 2-cells are connected") with a principled Squier-style
constructor ("critical pair diamonds commute"). However, the implementation achieves
no semantic change: `diamond_filler` connects *arbitrary* parallel derivations, not
just those arising from specific critical pairs. The critical-pair arguments (`s₁`,
`s₂`, `j₁`, `j₂`) are decorative — they do not constrain the conclusion type.

---

## 2. Detailed Findings

### 2.1 The `diamond_filler` Constructor (Level 3)

**Location**: `OmegaGroupoid.lean`, lines 228–233

```lean
| diamond_filler {a b : A} {p q : Path a b} {d₁ d₂ : Derivation₂ p q}
    {p₀ q₀ r₀ m₀ : Path a b}
    (s₁ : Step p₀ q₀) (s₂ : Step p₀ r₀)
    (j₁ : StepStar q₀ m₀) (j₂ : StepStar r₀ m₀) :
    MetaStep₃ d₁ d₂
```

**Critical observation**: The implicit parameters `d₁` and `d₂` are **completely
unconstrained** by the explicit arguments `s₁, s₂, j₁, j₂`. The diamond data
(`p₀, q₀, r₀, m₀`) lives in its own implicit universe — there is no type-level
connection requiring that `d₁` or `d₂` traverse the diamond. The constructor
therefore connects *any* two parallel `Derivation₂ p q`, regardless of their
structure.

**Proof of equivalence to `rweq_eq`**: The old constructor was:
```lean
| rweq_eq {a b : A} {p q : Path a b} {d₁ d₂ : Derivation₂ p q} : MetaStep₃ d₁ d₂
```
Both accept arbitrary `d₁, d₂ : Derivation₂ p q` and produce `MetaStep₃ d₁ d₂`.
The only difference is that `diamond_filler` requires the caller to supply *some*
Step/StepStar witnesses, but these witnesses don't narrow the conclusion. Any
invocation of `rweq_eq` can be mechanically replaced by:
```lean
.diamond_filler (Step.trans_refl_right p) (Step.trans_refl_right p)
  (StepStar.refl p) (StepStar.refl p)
```
This is exactly how it is used everywhere in the codebase (see §2.4).

### 2.2 The `diamond_filler` Constructor (Level 4)

**Location**: `OmegaGroupoid.lean`, lines 376–378

```lean
| diamond_filler {a b : A} {p q : Path a b} {d₁ d₂ : Derivation₂ p q}
    {m₁ m₂ : Derivation₃ d₁ d₂} :
    MetaStep₄ m₁ m₂
```

This is a **zero-argument blanket filler** — strictly weaker than even the level-3
version. It takes no critical-pair data at all. It is semantically identical to
the old `rweq_eq` at level 4.

### 2.3 The `diamond_filler` Constructor (Level 5+)

**Location**: `OmegaGroupoid.lean`, lines 488–490

```lean
| diamond_filler {n : Nat} ... {c₁ c₂ : Derivation₄ m₁ m₂} :
    MetaStepHigh n c₁ c₂
```

Also a zero-argument blanket filler, identical in power to the old `rweq_eq`.

### 2.4 Usage Pattern: Always Trivial Arguments

Every call site supplies the same trivial witnesses:

| File | Line(s) | Arguments supplied |
|------|---------|-------------------|
| `OmegaGroupoid.lean` | 321 | `Step.trans_refl_right p`, `Step.trans_refl_right p`, `StepStar.refl p`, `StepStar.refl p` |
| `Normalizer.lean` | 122, 128, 490, 509, 533 | Same trivial pattern |
| `EckmannHilton.lean` | 296, 302 | Same trivial pattern |

No call site uses genuine critical-pair data from `CriticalPairs.lean`. The 33
critical pairs enumerated in `Step.lean` are never referenced by any `diamond_filler`
invocation.

### 2.5 Axiom-Like Dependencies

| Mechanism | Location | Severity |
|-----------|----------|----------|
| `Classical.choice` | `OmegaGroupoid.lean:169` (`derivation₂_of_stepstar`) | Moderate — needed to extract `Type`-valued `Derivation₂` from `Prop`-valued `StepStar` |
| `Subsingleton.elim` | `OmegaGroupoid.lean:435,723,729,979,984` | Low — used only for `Prop`-level equality proofs (`rweq_toEq` witnesses) |
| `sorry` | None | ✅ Clean |
| `axiom` keyword | None | ✅ Clean |
| `propext` | None | ✅ Clean |

The `Classical.choice` in `derivation₂_of_stepstar` is necessary because `StepStar`
is `Prop`-valued while `Derivation₂` is `Type`-valued, so the extraction genuinely
requires choice. This is documented and acceptable.

The `Subsingleton.elim` uses are at the `Prop` level (comparing `rweq_toEq` outputs),
where proof irrelevance is expected and mathematically unproblematic.

---

## 3. Mathematical Soundness Assessment

### 3.1 Is the construction sound?

**Yes.** The `diamond_filler` constructor is sound for exactly the same reason
`rweq_eq` was sound: it asserts contractibility of `Derivation₂`-hom-spaces,
which holds because:

1. `Derivation₂.toRwEq` projects every `Derivation₂ p q` to `RwEq p q`
2. `RwEq p q` is `Type u`-valued but its underlying equality content lives in `Prop`
3. In Lean 4, `Prop` has proof irrelevance (UIP), so all `RwEq` witnesses between
   the same endpoints are propositionally equal
4. This propositional equality at the `RwEq` level justifies identifying all
   `Derivation₂` witnesses at the 3-cell level

The soundness argument is independent of whether the constructor is called
`rweq_eq` or `diamond_filler`, and independent of whether it carries decorative
Step/StepStar arguments.

### 3.2 Is this a genuine Squier FDT?

**No.** A genuine Squier-style finite derivation type would:

1. **Enumerate** the finitely many critical pairs of the TRS
2. **For each critical pair**, provide a 3-cell connecting the *specific* derivations
   arising from that pair — i.e., connecting `vcomp (step s₁) (derivation₂_of_stepstar j₁)`
   to `vcomp (step s₂) (derivation₂_of_stepstar j₂)`
3. **Prove** that these finitely many 3-cells generate all of `contractibility₃`
   via Newman's lemma + termination

What the code actually does is provide a *single* constructor that connects *any*
two parallel derivations, decorated with *arbitrary* critical-pair data that plays
no constraining role. This is the opposite of the FDT approach: instead of deriving
contractibility from finitely many generators, it postulates contractibility directly.

### 3.3 Can `diamond_filler` be strengthened to a true FDT?

The repo's own analysis (`ANALYSIS_contractibility3_without_rweq_eq.md`) proves
this is **impossible** using only groupoid laws. The Step graph has undirected cycles
(the associativity/unit diamond), so the free groupoid on it has genuinely distinct
morphisms between the same vertices. Contractibility₃ requires identifying these
distinct morphisms, which cannot be done by groupoid laws alone — it requires
appeal to proof irrelevance.

A true FDT constructor would need its conclusion type to be:
```lean
MetaStep₃
  (.vcomp (.step s₁) (derivation₂_of_stepstar j₁))
  (.vcomp (.step s₂) (derivation₂_of_stepstar j₂))
```
i.e., the `d₁` and `d₂` would be *determined by* the critical-pair data, not
independently quantified. The current constructor leaves `d₁` and `d₂` implicit
and unconstrained, making the critical-pair data irrelevant.

### 3.4 What assumptions remain?

The ω-groupoid construction ultimately relies on:

| Assumption | Status | Eliminable? |
|------------|--------|-------------|
| Lean's UIP / proof irrelevance on `Prop` | Built into the kernel | No (fundamental to the approach) |
| `Classical.choice` for `StepStar → Derivation₂` | Explicit in code | Possibly, with a `Type`-valued `StepStar` |
| Blanket 3-cell contractibility (`diamond_filler` ≡ `rweq_eq`) | Postulated as constructor | Not without FDT + mechanized Newman's lemma |
| Blanket 4-cell+ contractibility | Postulated as constructor | Follows from level 3 by the same argument |

The construction is an **extensional** ω-groupoid: it works precisely because Lean
validates UIP, making higher cells trivially contractible. In intensional type theory
(where UIP fails), this approach would not work — which is acknowledged in the paper's
Remark 6.5.

---

## 4. Paper–Code Discrepancy

### 4.1 The paper still references `rweq_eq`

The paper (`main.tex`) references `rweq_eq` extensively:

| Line(s) | Content |
|---------|---------|
| 1889 | Lists `rweq_eq` as a `MetaStep₃` constructor |
| 2049 | Proof of Theorem 6.1 uses `MetaStep₃.rweq_eq` |
| 2074–2077 | Higher-level proof uses `MetaStep₄.rweq_eq` and `MetaStepHigh.rweq_eq` |
| 2099–2128 | Remark 6.5 discusses the role of `rweq_eq` and proof irrelevance |
| 2148 | Credits contractibility to `rweq_eq` |
| 2239–2243 | Summary table references `rweq_eq` at all levels |
| 3101, 3240 | Related work and conclusion reference `rweq_eq` |

**The code no longer has `rweq_eq`.** Every reference must be updated.

### 4.2 What the paper currently says (accurate for old code)

Remark 6.5 is honest and well-written. It acknowledges:
- Contractibility relies on proof irrelevance via `rweq_eq`
- A fully confluence-only proof is "important future work"
- The result is a "weak 2-groupoid with contractible higher cells"
- This is fundamentally different from Lumsdaine/vdBG

### 4.3 What the paper would need to say (for current code)

The paper should **not** claim that `diamond_filler` achieves the Squier FDT
program, because it doesn't. Instead, it should:

1. **Rename**: Replace all `rweq_eq` references with `diamond_filler`
2. **Clarify**: Explain that `diamond_filler` carries critical-pair witnesses
   as documentation/metadata but does not use them to constrain the conclusion
3. **Preserve the honesty of Remark 6.5**: The mathematical situation is unchanged —
   contractibility still relies on proof irrelevance, not on the FDT structure
4. **Downgrade the Squier claim**: The connection to Squier's FDT is aspirational,
   not realized. The 33 critical pairs are proved joinable, but the contractibility
   proof does not flow through them

---

## 5. Suggested Paper Narrative

### 5.1 Recommended approach

Keep Remark 6.5's intellectual honesty but update terminology:

> **Remark (The role of `diamond_filler` and proof irrelevance).**
> Contractibility at dimension ≥ 3 relies on the `MetaStep₃.diamond_filler`
> constructor, which connects any two parallel derivations. The constructor
> carries critical-pair data (Step witnesses and their StepStar joins) as
> structured metadata, but the current implementation does not restrict
> the conclusion to derivations arising from that specific critical pair.
>
> In effect, `diamond_filler` postulates that all parallel 2-cells are
> connected by a 3-cell — the same content as the earlier `rweq_eq`
> constructor, now annotated with rewriting-theoretic data. The soundness
> of this postulate rests on proof irrelevance: all `RwEq` witnesses between
> the same endpoints are propositionally equal (by UIP on the underlying `Eq`),
> so the Type-valued `Derivation₂` layer carries no information beyond its
> endpoints.
>
> A fully constructive proof — deriving contractibility from finitely many
> critical-pair fillers via Newman's lemma (the Squier finite derivation
> type program) — remains future work. The 33 critical pairs of the Step
> TRS are enumerated with joinability proofs in the formalization, providing
> the raw material for such a construction.

### 5.2 Sections requiring updates

| Paper section | What to change |
|---------------|---------------|
| §6.1 (MetaStep₃ constructors, ~line 1889) | Replace `rweq_eq` with `diamond_filler`; describe its signature |
| Theorem 6.1 proof (~lines 2016–2083) | Replace `rweq_eq` with `diamond_filler`; note that the critical-pair arguments are metadata |
| Remark 6.5 (~lines 2099–2128) | Rewrite per §5.1 above |
| Remark 6.6 (~lines 2131–2159) | Update comparison: still valid, just rename |
| §6.2 summary table (~lines 2239–2243) | Replace `rweq_eq` with `diamond_filler` at all levels |
| Related work (~line 3101) | Update reference |
| Conclusion (~line 3240) | Update reference |
| Future work | Explicitly state the FDT gap: critical pairs exist but don't drive contractibility |

### 5.3 What NOT to claim

- ❌ "We replaced the `rweq_eq` axiom with a Squier-style FDT construction"
- ❌ "`diamond_filler` is more principled / less axiomatic than `rweq_eq`"
- ❌ "Contractibility now follows from critical-pair analysis"

### 5.4 What CAN be claimed

- ✅ "The `diamond_filler` constructor annotates the contractibility postulate with
     rewriting-theoretic structure (critical-pair data)"
- ✅ "The 33 critical pairs of the Step TRS are enumerated with joinability proofs"
- ✅ "A fully constructive Squier-style proof is identified as feasible future work"
- ✅ "Contractibility at level ≥ 3 is sound, justified by proof irrelevance on Eq"

---

## 6. Recommendations

### 6.1 For immediate publication

1. **Update all paper references** from `rweq_eq` to `diamond_filler`
2. **Rewrite Remark 6.5** to accurately describe the current state (see §5.1)
3. **Do not overstate** the Squier connection — it's aspirational, not realized
4. **Keep the honesty**: The existing Remark 6.5 is a model of intellectual
   integrity; preserve its spirit in the updated version

### 6.2 For the formalization (optional, post-publication)

| Priority | Action | Rationale |
|----------|--------|-----------|
| Low | Consider reverting to `rweq_eq` | The name was more honest; `diamond_filler` suggests a connection to Squier that doesn't exist |
| Medium | If keeping `diamond_filler`, constrain its type | Make `d₁` and `d₂` computed from `s₁, s₂, j₁, j₂` to get a genuine FDT constructor |
| High | If constraining the type, prove Newman's lemma | Derive `contractibility₃` from finitely many genuine diamond fillers |

### 6.3 The honest framing

The ω-groupoid construction works and is sound. Its contractibility mechanism
is proof irrelevance on `Eq`, which is a legitimate mathematical fact in Lean's
type theory. The Squier FDT program is a beautiful aspiration that would make
the construction independent of UIP, but it is not yet realized. The paper
should present the construction as what it is: a working ω-groupoid in an
extensional type theory, with higher contractibility from proof irrelevance,
and with the FDT program as identified future work.

---

## 7. Summary

| Question | Answer |
|----------|--------|
| Is `diamond_filler` sound? | **Yes** — same justification as `rweq_eq` |
| Is it a true Squier FDT? | **No** — critical-pair args are decorative |
| Does it introduce new axioms? | **No** — no `axiom`, no `sorry` |
| Does it use `Classical.choice`? | **Yes** — in `derivation₂_of_stepstar` (acceptable) |
| Does it use `Subsingleton.elim`? | **Yes** — at `Prop` level only (acceptable) |
| Is the paper up to date? | **No** — still references `rweq_eq` throughout |
| Is the `RWEQ_ELIMINATION.md` accurate? | **Partially** — describes the aspiration but the implementation fell short |
| What's the honest narrative? | Sound ω-groupoid via UIP; Squier FDT is future work |
