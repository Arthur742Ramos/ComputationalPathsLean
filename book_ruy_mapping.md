# Mapping: Ruy's Book → Our Book (Computational Paths Spinoff)

**Source**: *The Functional Interpretation of Logical Deduction* (de Queiroz, de Oliveira, Gabbay, 2012)
**Target**: *The Algebra of Computational Paths* (our book, Lean 4 formalization)

---

## Executive Summary

Ruy's book establishes the **Labelled Natural Deduction (LND)** framework, culminating in two key innovations that are our direct starting points:

1. **The equality judgement `a =_s b : D`** (Chapter 6), where `s` is the *rewrite reason* — a term recording *why* a equals b.
2. **The LND_EQ term rewriting system** (Chapter 7), an algebra on rewrite reasons {σ, τ, ξ, μ, sub_L, sub_R} with 35 rewrite rules, proved terminating and confluent via Knuth–Bendix completion.

**Our book begins exactly where Ruy's Chapter 7 ends.** We take the rewrite reason algebra, reinterpret it as the algebra of *computational paths*, and discover that this algebra gives rise to:
- A weak ω-groupoid structure (Lumsdaine/van den Berg–Garner style)
- A full homotopy theory (fundamental groups, fibrations, spectral sequences)
- Connections to HoTT identity types

The relationship is: **Ruy provides the 1-dimensional rewriting theory; we provide the higher-dimensional geometry that emerges from it.**

---

## Chapter-by-Chapter Analysis

### Chapter 1 (Overview): Frege → Curry–Howard → LND

#### What we ASSUME
- The entire historical narrative: Frege's two-dimensional calculus (Begriffsschrift + Grundgesetze), Curry–Howard correspondence, formulae-as-types
- The LND paradigm: labels alongside formulas, division of tasks (functional calculus on labels, logical calculus on formulas)
- The subdeduction principle replacing the subformula principle
- The general framework of "keeping track of proof steps" via labels

#### What we EXTEND
- Ruy frames labels as **proof-constructions** (records of deduction steps). We reinterpret them as **computational paths** — first-class algebraic objects that carry geometric structure beyond their role as proof records.
- Ruy's motto "a formula is a theorem iff its label has no free variable" becomes our principle "a path is trivial iff it reduces to `refl` under the rewrite system."

#### What we CONTRADICT/REVISE
- Nothing directly contradicted. But Ruy's framework is essentially **1-categorical** (paths between terms, no paths between paths). Our central thesis is that the *same rewrite reason algebra* naturally generates a **higher-categorical** structure (paths between paths between paths...).

#### Our Chapter 1 should:
- **Recap** (1–2 paragraphs): The LND paradigm, the idea of labels as proof-terms, the division of tasks. Cite Ruy Ch. 1.
- **Cite only**: The full Frege historical development, Curry–Howard details, comparison with Martin-Löf, Gabbay's LDS programme.

---

### Chapter 2 (LND): Labels, Division of Tasks, Canonical Proofs, Normalisation

#### What we ASSUME
- The entire inference rule apparatus: introduction/elimination rules for ∧, ∨, →, ∀, ∃
- The canonical proof forms: ⟨a₁,a₂⟩, inl/inr, λx.b(x), Λx.f(x), εx.(f(x),a)
- The CONSTRUCTORS/DESTRUCTORS terminology
- β-reductions, η-reductions (induction rules), ζ-reductions (permutative)
- The **ι-reduction discovery** (via Knuth–Bendix completion): the new reduction `CASE(c, x̂.inl(x), ŷ.inr(y)) ▷_ι w(c)` that restored confluence when η-rules are included

#### What we EXTEND
- β-equality `APP(λx.b(x), a) =_β b(a/x)` is our **Rule Group I** foundation — these become *elementary rewrite steps* in our Path type
- η-equality `λx.APP(c,x) =_η c` gives us further elementary steps
- The ζ-equality (permutative conversions) becomes part of our context substitution algebra (Rules 33–48)
- The ι-reduction is a key example of how Knuth–Bendix completion *discovers* new path equalities — we extend this methodology to our 76-rule system

#### What we CONTRADICT/REVISE
- Ruy treats normalisation as a meta-mathematical tool (proving consistency). We treat normalisation as the **primary semantic device** — following Tait's intensional interpretation that Ruy himself champions. This is a shift of emphasis, not contradiction.

#### Precise Starting Points
| Ruy's Definition/Theorem | Our Starting Point |
|---|---|
| β-equality: `APP(λx.b(x), a) =_β b(a/x)` | Elementary rewrite step in our Path type |
| η-equality: `λx.APP(c,x) =_η c` | Elementary rewrite step |
| ζ-equality: `w(CASE(p,...)) =_ζ CASE(p,... w(...))` | Context substitution rules (Group IV) |
| ι-reduction: `CASE(c, x̂.inl(x), ŷ.inr(y)) ▷_ι w(c)` | Precursor to our completion-derived rules |
| Theorem: "Every LND proof has a unique normal form" | Our Theorem 3.12 (Confluence) generalizes this |

#### Our Chapter 1 should:
- **Recap** (1 page): The LND inference rules for ∧, ∨, →, the β/η/ζ reductions, the ι-discovery. Focus on what generates our rewrite steps.
- **Cite only**: Full proof trees, the detailed philosophical discussion of canonical proofs vs. Heyting semantics, Martin-Löf's distinctions.

---

### Chapter 3 (Implication): Spectrum of λ-abstraction Disciplines

#### What we ASSUME
- The spectrum: linear → relevant → ticket entailment → intuitionistic → classical implications, all characterized by side conditions on λ-abstraction
- The generalised reductio ad absurdum for classical logic
- That different logics = different abstraction disciplines on the *same* basic framework

#### What we EXTEND
- We work primarily in the intuitionistic fragment (one or more uses of the assumption). But our path algebra is *parametric* over the abstraction discipline: the 76 rewrite rules hold for any well-typed path regardless of the underlying logic.
- The function type β/η rules in our system (Rules 22–25) come from the →-β/η equalities of Ruy's Chapter 3.

#### What we CONTRADICT/REVISE
- Nothing. The spectrum of implications is orthogonal to our higher-dimensional development.

#### Our Chapter 1 should:
- **Cite only**: The full spectrum analysis. Mention that our path algebra works for the general LND framework, not just intuitionistic logic.

---

### Chapter 4 (Existential): ε-terms, Skolem-type Elimination

#### What we ASSUME
- The ε-term construction: εx.(f(x),a) for ∃-introduction
- The INST operator for ∃-elimination with value-range abstractors
- The Skolem-type procedures: opening local branches, introducing new names, abstracting them away
- The Herbrand connection: Skolem functions get universal force via abstraction

#### What we EXTEND
- The ∃-β-reduction `INST(εx.(f(x),a), ĝt̂.d(g,t)) =_β d(f/g, a/t)` is a rewrite step in our system
- The "hiding" of witnesses in Skolem-type connectives (∨, ∃, ≐) is the conceptual precursor to our treatment of **transport** along paths: the witness of an equality is "hidden" in the path structure

#### What we CONTRADICT/REVISE
- Nothing directly.

#### Our Chapter 1 should:
- **Cite only**: Full treatment of ε-terms, Herbrand connections.

---

### Chapter 5 (Normalisation): TRS, Knuth–Bendix, ι-reduction

#### What we ASSUME
- The methodology: proving normalisation/strong normalisation for LND via term rewriting systems
- Termination via recursive path ordering (Dershowitz)
- Confluence via critical pair analysis + Knuth–Bendix completion
- The **ι-reduction discovery**: completion produces `CASE(c, x̂.inl(x), ŷ.inr(y)) ▷ w(c)` as a new rule needed for confluence of the η+ζ system

#### What we EXTEND
- **This is our primary methodological inheritance.** We apply the exact same methodology (TRS construction → termination proof → critical pair analysis → completion if needed) to our 76-rule system on computational paths.
- Our Theorem 3.9 (Termination) uses the same recursive path ordering technique
- Our Theorem 3.12 (Confluence) uses the same Newman's Lemma + critical pair strategy
- Our system has **76 rules** (vs. Ruy's ~15 for the base LND system), organized into 8 groups

#### What we CONTRADICT/REVISE
- Nothing. We are the direct continuation of this methodology at a higher level.

#### Precise Starting Points
| Ruy's Result | Our Extension |
|---|---|
| LND-TRS: ~15 rules on proof-terms | Our TRS: 76 rules on path-terms |
| Termination via recursive path ordering | Same technique, extended to our richer signature |
| Confluence via Knuth–Bendix | Same technique; our critical pairs are more numerous but manageable |
| ι-reduction discovery | Precursor pattern: completion discovers geometrically meaningful rules |

#### Our Chapter 1 should:
- **Recap** (1–2 paragraphs): The TRS methodology, how termination + confluence = normalisation + unique normal forms. Emphasize this as the *method we inherit and scale up*.
- **Cite only**: Full technical details of the TRS proofs, Knuth–Bendix procedure.

---

### Chapter 6 (Equality): `a =_s b : D`, Rewrite Reasons as Computational Paths

#### ⭐ THIS IS THE CRITICAL CHAPTER — THE EXACT BOUNDARY

#### What we ASSUME
- **The equality judgement `a =_s b : D`** where `s` is the rewrite reason
- The distinction between **definitional equality** (rewrite rules: β, η, ξ, μ) and **propositional equality** (the ≐ connective)
- The "missing entity": function symbols for rewrites, carried as indices
- The middle-ground solution between Martin-Löf's extensional (I_ext) and intensional (I_int) identity types
- The ≐ proof rules:
  - ≐-introduction: `(a =_s b : D) → s(a,b) : ≐_D(a,b)`
  - ≐-elimination: `REWR(e, t̂.d(t)) : C` (Skolem-type, with local assumption `[a =_t b : D]`)
  - ≐-reduction (β): `REWR(s(a,b), t̂.d(t)) =_β d(s/t)`
  - ≐-induction (η): `REWR(e, t̂.t(a,b)) =_η e`
  - ≐-permutative (ζ): `w(REWR(e, t̂.d(t))) =_ζ REWR(e, t̂.w(d(t)))`
- The general rules of equality: reflexivity (ρ), symmetry (σ), transitivity (τ)
- The subterm substitution rule with sub_L and sub_R
- The ξ-rule (equality of canonical elements) and μ-rule (equality of non-canonical elements)
- The substitution rule: `(a =_g y : D, f(a) : P(a)) → g(a,y) · f(a) : P(y)`

#### What we EXTEND — THE KEY MOVE

**Ruy's `s` in `a =_s b : D` is our `Path a b`.**

More precisely:
- Ruy's rewrite reason `s` (a term built from {ρ, β, η, ζ} using {σ, τ, ξ, μ, sub_L, sub_R}) is our `Path.steps : List (Step A)`
- Ruy's equality judgement `a =_s b : D` is our `Path a b` structure (steps + proof)
- Ruy's general rules (σ for symmetry, τ for transitivity, ρ for reflexivity) are our `Path.symm`, `Path.trans`, `Path.refl`
- Ruy's ξ-rule becomes our `congrArg` (congruence for canonical terms)
- Ruy's μ-rule becomes our elimination congruence
- Ruy's sub_L, sub_R become our `Context.substLeft`, `Context.substRight`

**THE EXTENSION**: Ruy treats rewrite reasons as *indices* (subscripts to the equality sign). We promote them to *first-class algebraic objects* with their own rich structure:
1. **Rewrite reasons form paths** — they are composable, invertible, functorial
2. **Paths between paths** — our RwEq gives 2-cells (witnesses that two rewrite reasons yield equivalent paths)
3. **The weak ω-groupoid** — the tower Path, RwEq, Derivation₃, ... has the structure of a weak ω-groupoid with contractibility at level ≥ 3

This is the **conceptual leap**: from `s` as a bookkeeping device to `s` as a geometric object with homotopical meaning.

#### What we CONTRADICT/REVISE

1. **On Martin-Löf's equality types**: Ruy positions his ≐ as a middle ground between I_ext and I_int. We go further: our computational paths are a *third option* that captures the intensional content (the rewrite trace) without collapsing it (as I_ext does) or overloading the elimination rule (as I_int does). Our paths carry full computational content AND have decidable equivalence (via normalisation).

2. **On proof irrelevance**: Ruy's propositional equality ≐_D(a,b) "hides" the witness in the introduction rule (Skolem-type). In our framework, the witness is NOT hidden — it IS the path. Two paths with different traces but the same endpoints are genuinely different objects (Theorem 1.1: Non-UIP for Path). This is a philosophical departure from Ruy's Skolem-type treatment of ≐.

3. **On the role of rewrite reasons**: Ruy sees `s` as measuring redundancy (an "orthogonal measure of redundancy for the LND"). We see `s` as carrying *geometric information* — the specific computational route from `a` to `b`. This reinterpretation does not contradict Ruy but substantially enriches the meaning.

#### Precise Correspondences

| Ruy (Chapter 6) | Our Book | Status |
|---|---|---|
| `a =_s b : D` | `Path a b` | DIRECT EXTENSION |
| Rewrite reason `s` | `Path.steps : List (Step A)` | REINTERPRETATION |
| ρ (reflexivity) | `Path.refl` | ASSUMED |
| σ(t) (symmetry) | `Path.symm` | ASSUMED |
| τ(t,u) (transitivity) | `Path.trans` | ASSUMED |
| ξ(r,s) (canonical equality) | `Path.congrArg` | ASSUMED + EXTENDED |
| μ(r) (non-canonical equality) | Elimination congruences | ASSUMED + EXTENDED |
| sub_L(r,s), sub_R(r,s) | `Context.substLeft`, `Context.substRight` | ASSUMED + EXTENDED |
| ≐-introduction | `Path.ofEq` (canonical witness) | REINTERPRETED |
| ≐-elimination (REWR) | Pattern matching / transport | REINTERPRETED |
| β_rewr reduction | Our Rule Group: β-type rules | EXTENDED to all type formers |
| η_rewr reduction | Our Rule Group: η-type rules | EXTENDED to all type formers |
| "Missing entity" = rewrite identifiers | Our fundamental insight: paths ARE the missing entity, and they have geometry | EXTENDED |

#### Our Chapter 1 should:
- **Recap** (2–3 pages): This is the most important recap. Must cover:
  - The equality judgement `a =_s b : D` with full explanation of what `s` is
  - The rewrite reason algebra: {ρ, σ, τ, ξ, μ, sub_L, sub_R}
  - The ≐ proof rules (introduction, elimination, reduction, induction)
  - The distinction between definitional and propositional equality
  - The explicit statement: "Our computational paths are the higher-dimensional development of Ruy's rewrite reasons"
- **Cite only**: The comparison with Martin-Löf's I_ext/I_int, Aczel's propositional equality, Statman/Le Chenadec normal forms, the full Herbrand/Gentzen connections.

---

### Chapter 7 (Normalisation for Equality): LND_EQ, the Rewrite Reason Algebra

#### ⭐ THIS IS OUR DIRECT TECHNICAL STARTING POINT

#### What we ASSUME (entirely)
- The LND_EQ-TRS: 35 rewrite rules on rewrite reasons
- The rewrite reason operators: {σ, τ, ξ, μ, sub_L, sub_R, ρ, β, η, ζ}
- The β_rewr reductions: μ(ξ(r,s)) ▷ r (for FST), μ(ξ(r,s)) ▷ s (for SND), etc.
- The η_rewr reductions: ξ(μ(r)) ▷ r (for ∧), μ(t, ξ(r), ξ(s)) ▷ t (for ∨), etc.
- The symmetry transformations: σ(τ(r,s)) ▷ τ(σ(s), σ(r)), σ(ξ(r)) ▷ ξ(σ(r)), etc.
- The transitivity-substitution interactions: τ(sub_L(r,s), t) ▷ τ(r, sub_R(s,t)), etc.
- The associativity: τ(τ(t,r), s) ▷ τ(t, τ(r,s))
- The termination proof via recursive path ordering with precedence σ > τ > ρ, σ > ξ, σ > μ, etc.
- The confluence proof via superposition algorithm
- The two extra rules added by completion

#### What we EXTEND

**Our 76-rule system is the HIGHER-DIMENSIONAL LIFTING of Ruy's 35-rule system.**

The correspondence:

| Ruy's LND_EQ-TRS Rule | Our Rule (Group) |
|---|---|
| Rule 1: σ(ρ) ▷ ρ | Rule 1: symm(refl(a)) ▷ refl(a) (Group I) |
| Rule 2: σ(σ(r)) ▷ r | Rule 2: symm(symm(p)) ▷ p (Group I) |
| Rules 3–4: τ(C[r], C[σ(r)]) ▷ C[ρ] | Rule 5: trans(p, symm(p)) ▷ refl(a) (Group I) |
| Rules 5–6: τ(C[r], C[ρ]) ▷ C[r] | Rules 3–4: trans(refl, p) ▷ p, trans(p, refl) ▷ p (Group I) |
| Rules 7–8: sub_L(C[r], C[ρ]) ▷ C[r] | Absorbed into Context rules (Group IV) |
| Rules 13–14: μ(ξ(r,s)) ▷ r/s (FST/SND) | Product β-rules (Group II) |
| Rules 15–16: μ(ξ(r), s, u) ▷ s/u (inl/inr) | Coproduct β-rules (Group II) |
| Rule 17: μ(s, ξ(r)) ▷ r (→, ∀) | Function/forall β-rules (Group II) |
| Rule 19: ξ(μ(r)) ▷ r (∧-η) | Product η-rules (Group II) |
| Rule 20: μ(t, ξ(r), ξ(s)) ▷ t (∨-η) | Coproduct η-rules (Group II) |
| Rule 21: ξ(μ(r,s)) ▷ s (→-η, ∀-η) | Function η-rules (Group II) |
| Rule 23: σ(τ(r,s)) ▷ τ(σ(s), σ(r)) | Rule 7: symm(trans(p,q)) ▷ trans(symm(q), symm(p)) (Group I) |
| Rule 26: σ(ξ(r)) ▷ ξ(σ(r)) | Congruence symmetry rules (Group VII) |
| Rules 31–32: τ(r, sub_L(ρ,s)) ▷ sub_L(r,s) | Context β-rules (Group IV) |
| Rule 35: τ(τ(t,r), s) ▷ τ(t, τ(r,s)) | Rule 8: trans(trans(p,q), r) ▷ trans(p, trans(q,r)) (Group I) |

**New in our system** (not in Ruy):
- **Transport rules** (Group III, Rules 26–32): computation rules for transport along paths through type formers — these arise because we work with *dependent* types
- **Dependent context rules** (Group V, Rules 49–60): dependent analogues of context substitution
- **Bi-context rules** (Group VI, Rules 61–68): binary congruences (map2, mapLeft, mapRight)
- **Map congruence rules** (Group VII, Rules 69–72): interaction of congruence with elementary steps
- **Structural closure** (Group VIII, Rules 73–76): the rewrite relation is closed under symm, trans, and context — this is essential for the higher-dimensional structure

#### What we CONTRADICT/REVISE
- Ruy's LND_EQ-TRS operates on **reason terms** (σ, τ, ξ, μ applied to reason variables). Our TRS operates on **path terms** (symm, trans, congrArg, transport applied to path variables). The operators are "the same" at the algebraic level but the *objects they act on* are different: Ruy's are subscripts to equations, ours are first-class proof-relevant terms.
- Ruy's conditional rewriting (β_rewr/η_rewr rules are conditional on the associated terms being β/η-redexes) becomes unconditional in our system because our rules operate directly on path structure, not on the underlying terms.

#### Our Chapter 1 should:
- **Recap** (1–2 pages): The LND_EQ-TRS rules (present the key ones), the termination/confluence results. Present the **correspondence table** above as the bridge to our system.
- **Cite only**: Full proofs of termination/confluence, the completion procedure details, conditional rewriting technicalities.

---

### Chapter 8 (Modal Logic): □ as ∀ over Worlds

#### What we ASSUME
- The basic idea: □A interpreted via Λ-abstraction over world-variables, with worlds as structured collections of labelled formulas
- The analogy between → (abstraction over term-variables) and □ (abstraction over world-variables)
- Different □'s characterized by different ΛW-abstraction disciplines (paralleling different →'s from different λx-abstraction disciplines)

#### What we EXTEND
- Our framework is currently **non-modal** — we work with a single type theory. But the path algebra could be extended to a modal setting: **paths between worlds** would give an explicit computational account of accessibility relations.
- This is **future work**, not current content.

#### Our Chapter 1 should:
- **Cite only**: Brief mention as evidence that LND handles a wide range of logics. Not directly relevant to our development.

---

### Chapter 9 (Meaning): Proof-Theoretic Semantics

#### What we ASSUME
- The proof-theoretic semantics programme (Gentzen → Prawitz → Dummett → Martin-Löf)
- The principle that "meaning is given by proof conditions" (introduction rules)
- Ruy's alternative: "meaning is given by **normalisation** (how elimination acts on introduction)" — the Tait-inspired view

#### What we EXTEND
- **We are the realisation of Ruy's semantics-of-normalisation programme at the level of equality.** Ruy proposes that the normalisation procedure is the key semantic device (not canonical proofs, not truth-conditions). We show that taking this seriously for *equality proofs* yields a rich geometric theory.
- The "semantic triangle" (propositions ↔ proofs ↔ meanings) gets a new vertex: **computational paths** as the constructive content of equality, sitting between proof-irrelevant identity and fully intensional equality.

#### What we CONTRADICT/REVISE
- Ruy explicitly advocates normalisation-as-meaning over assertion-conditions-as-meaning. We agree and push this further: the rewrite system on paths IS the meaning of equality, not just a meta-mathematical tool. This is a radicalization, not a contradiction.

#### Our Chapter 1 should:
- **Recap** (1 paragraph): The philosophical position that normalisation (not canonical proofs) is the key semantic device. This motivates why our rewrite system on paths is semantically significant.
- **Cite only**: The full Gentzen–Prawitz–Dummett–Martin-Löf–Tait philosophical discussion.

---

## The Exact Boundary

### WHERE RUY'S BOOK ENDS:

1. The equality judgement `a =_s b : D` with `s` as a rewrite reason term
2. The LND_EQ-TRS: 35 rules on rewrite reason terms, proved terminating and confluent
3. The ≐ connective with Skolem-type introduction/elimination
4. Normalisation for equational proofs: every equational proof has a unique normal form
5. Applications: Leibniz's law `∀x.∀y.(≐_D(x,y) → (P(x) → P(y)))`, Herbrand connections

### WHERE OUR BOOK BEGINS:

1. **Reinterpretation**: Ruy's rewrite reason `s` is promoted to a computational path `Path a b` — a first-class algebraic object with trace + proof
2. **Non-UIP**: Two paths with different traces are genuinely different (Theorem 1.1), even if they witness the same propositional equality
3. **Expanded rule system**: 76 rules (vs. 35) covering transport, dependent types, binary congruences, structural closure
4. **The weak ω-groupoid**: Path → RwEq → Derivation₃ → ... forms a weak ω-groupoid with contractibility at dimension ≥ 3
5. **Homotopy theory**: π₁(S¹) ≅ ℤ, Seifert–van Kampen, fibrations, covering spaces, spectral sequences
6. **Lean 4 formalization**: 96 modules, ~29,000 lines, 0 axioms, 0 sorries

The boundary is **sharp and clean**: Ruy gives us the 1-dimensional algebra of rewrite reasons; we discover the higher-dimensional geometry.

---

## Chapter 1 Recap vs. Cite Plan

### MUST RECAP (in our Chapter 1, ~4–5 pages):

1. **The LND paradigm** (from Ch. 1–2): Labels alongside formulas, division of tasks, the idea that proofs are recorded in terms. (1 paragraph)

2. **The normalisation methodology** (from Ch. 2, 5): β/η/ζ reductions, the TRS approach to proving normalisation, Knuth–Bendix completion discovering new rules (ι-reduction). (1–2 paragraphs)

3. **The equality judgement `a =_s b : D`** (from Ch. 6): Full explanation of what `s` is, the rewrite reason algebra, the {ρ, σ, τ, ξ, μ} operators, the distinction between definitional and propositional equality. (1–2 pages) — **This is the most important recap.**

4. **The LND_EQ-TRS** (from Ch. 7): The 35 rules, key examples (β_rewr, η_rewr, symmetry/transitivity transformations), the termination and confluence results. The correspondence table showing how these become our rules. (1–2 pages) — **This is the technical bridge.**

5. **The philosophical position** (from Ch. 9): Normalisation-as-meaning (not canonical-proofs-as-meaning) motivates treating the rewrite system on paths as semantically fundamental. (1 paragraph)

### CAN CITE ONLY:

- Full Frege historical development (Ch. 1)
- Detailed Curry–Howard isomorphism exposition (Ch. 1)
- The spectrum of implications (Ch. 3)
- ε-terms and existential quantifier details (Ch. 4)
- Full TRS proofs (recursive path ordering details, superposition algorithm) (Ch. 5, 7)
- Comparison with Martin-Löf's I_ext/I_int (Ch. 6)
- Statman/Le Chenadec equational logic (Ch. 6)
- Herbrand/Skolem/Gentzen connections (Ch. 4, 6)
- Modal logic treatment (Ch. 8)
- Full proof-theoretic semantics discussion (Ch. 9)
- The Leibniz's law proof and other applications (Ch. 6)

---

## Key Theorems: Dependency Chain

```
Ruy Ch.2: β/η/ζ/ι reductions on LND proof-terms
    │
    ▼
Ruy Ch.5: LND-TRS termination + confluence
    │        → Every LND proof has a unique normal form
    │
    ▼
Ruy Ch.6: Equality judgement a =_s b : D
    │        → Rewrite reasons as terms: {ρ, σ, τ, ξ, μ, sub_L, sub_R}
    │        → ≐ connective with Skolem-type rules
    │
    ▼
Ruy Ch.7: LND_EQ-TRS (35 rules on rewrite reasons)
    │        → Termination via recursive path ordering
    │        → Confluence via critical pairs + completion
    │        → "Every equational proof has a unique normal form"
    │
    ╔═══════════════════════════════════════════════╗
    ║           THE BOUNDARY                        ║
    ╚═══════════════════════════════════════════════╝
    │
    ▼
OUR Ch.1-2: Rewrite reasons → Computational paths (Path a b)
    │          → Non-UIP: distinct traces = distinct paths
    │          → 76-rule TRS on paths (extending LND_EQ-TRS)
    │
    ▼
OUR Ch.3: Rewrite system metatheory
    │        → Termination (Thm 3.9)
    │        → Confluence (Thm 3.12)
    │        → Unique normal forms (Cor 3.13)
    │
    ▼
OUR Ch.4-5: Groupoid → Bicategory → ω-groupoid
    │           → Weak category/groupoid structure
    │           → 2-cells = RwEq witnesses
    │           → Contractibility at level ≥ 3
    │
    ▼
OUR Ch.6-10: Homotopy theory
              → π₁(S¹) ≅ ℤ, π₁(T²) ≅ ℤ×ℤ, etc.
              → Fibrations, covering spaces
              → Long exact sequences, spectral sequences
```

---

## Summary: The Sentence That Captures It All

> Ruy's book proves that **rewrite reasons form a confluent term rewriting system**; our book discovers that **rewrite reasons form a weak ω-groupoid** — and this ω-groupoid is rich enough to recover the homotopy theory of spaces.

*Document generated 2026-02-15. To be revised as the book develops.*
