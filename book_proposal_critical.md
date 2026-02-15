# Critical Analysis: Book Proposal for *Computational Paths* Spinoff

**Date:** 15 February 2026  
**Prepared by:** Senior review (mathematician & book editor perspective)  
**Subject:** Proposed spinoff of de Queiroz, de Oliveira & Ramos, *Propositional Equality, Identity Types, and Computational Paths* (2012/2016)

---

## 0. Executive Summary

This project has genuine mathematical substance and a formalization of
extraordinary scope. However, the book will succeed or fail based on how
honestly it confronts a single architectural tension: **computational paths
live inside extensional type theory (Lean's `Prop` with UIP), yet claim to
recover intensional/homotopical phenomena.** Every editorial decision must
flow from a clear, upfront reckoning with this design choice. If the book
hand-waves here, expert reviewers will reject it. If it owns the choice and
explains *precisely* what is and isn't captured, it becomes a unique and
important contribution.

---

## 1. Framing: What Is This Book Really About?

### Recommendation: Option (c) with a twist — "Proof-Relevant Equality via Rewriting: From Labelled Deduction to Higher-Dimensional Algebra"

The options considered:

| Framing | Strengths | Risks |
|---------|-----------|-------|
| (a) "New foundation" | Bold, attention-grabbing | Invites immediate comparison with HoTT, cubical; you will lose that fight because this isn't a new type theory — it's a layer *on top of* extensional type theory |
| (b) "Algebra of rewrite reasons" | Accurate, modest | Too narrow; hides the homotopy-theoretic payoff |
| (c) "Proof theory → homotopy theory" | Shows the arc, tells a story | Risk of seeming derivative of HoTT |
| (d) "Higher-dimensional rewriting meets type theory" | Accurate niche positioning | Too specialist; misses the mathematical audience |

**The winning framing is (c), sharpened.** The book's unique selling proposition
is not that it *does* homotopy type theory — it's that it shows how
**rewrite traces on top of ordinary (extensional, UIP) equality** organically
give rise to the same higher-dimensional structures that HoTT postulates. This
is a *synthetic* result in the sense that the higher structure *emerges* from
the rewrite system rather than being axiomatized.

**Proposed title:**

> **Computational Paths: Higher-Dimensional Algebra from Rewrite Traces**  
> *A Lean 4 Formalization*

Or, if the publisher wants something broader:

> **The Algebra of Equality Proofs: From Labelled Natural Deduction to ω-Groupoids**

### The one-sentence pitch

"We show that if you take ordinary propositional equality and simply *remember
how you proved it* — recording the rewrite steps as combinatorial data — you get,
for free, the same weak ω-groupoid structure that homotopy type theory
postulates, complete with non-trivial fundamental groups, Eckmann–Hilton, and
the full machinery of algebraic topology."

This is genuinely striking. Lead with it.

---

## 2. What Would Make a Referee Say "This Must Be Published"?

### The five strongest cards in your hand:

1. **The J-eliminator derived, not axiomatized.** In HoTT, J (path induction)
   is primitive. Here it's *derived* from contractibility of the based path space
   within the rewrite system. This is a real theorem with content. Emphasize it
   early and prominently.

2. **The two-level structure is natural, not forced.** You get Path (non-UIP,
   proof-relevant traces) vs Eq (UIP, proof-irrelevant) as a *consequence* of
   the architecture, not by fiat. This echoes Voevodsky's two-level type theory
   (2LTT) but arrives at it from a completely different direction. Spell out
   the connection to Annenkov–Capriotti–Kraus–Voevodsky.

3. **77 rules, confluent, terminating, machine-verified.** This is concrete,
   checkable, and rare. Most papers in higher-dimensional rewriting either work
   with tiny systems or leave confluence as folklore. You have a *complete*
   metatheory. This is the kind of thing referees can verify and respect.

4. **The formalization is massive and sorry-free.** 760 files, 175K+ lines,
   7,597 theorems, zero `sorry`. This is comparable in scale to major Mathlib
   contributions. It provides an independent check on every claim.

5. **Concrete computations.** π₁(S¹) ≅ ℤ, π₁(T²) ≅ ℤ², π₁(S¹ ∨ S¹) ≅ F₂,
   Seifert–van Kampen — these are the *same* results HoTT proves, obtained
   by a different method. The comparison is scientifically interesting.

### What referees actually look for:

- **Novelty over prior work.** You must clearly delineate what is new here
  vs. the 2016–2018 SAJL papers, vs. de Veras's 2023 Journal of Logic and
  Computation paper, vs. the PhD thesis. A referee who has seen those papers
  will ask: "Is this just the old results in Lean 4?"

- **Technical depth in the hard parts.** The confluence proof and the ω-groupoid
  construction are where the real mathematics lives. These must be given full,
  detailed treatment — not sketched.

- **Honest comparison with the state of the art.** See §4 below.

---

## 3. Weaknesses and Likely Points of Reviewer Pushback

### 3.1 The Elephant in the Room: You're Working Inside UIP

This is the #1 vulnerability. Let me be blunt about what a hostile reviewer
will say:

> "The authors define `Path a b` as a structure containing `proof : a = b`
> (in Prop, hence proof-irrelevant) plus `steps : List (Step A)` as metadata.
> They then observe that different step-lists give different `Path` values.
> But this is trivially true of *any* structure that wraps an equality proof
> with auxiliary data. The 'non-UIP' result (Theorem 1.1) is an artifact:
> you bolted on combinatorial data and observed it's combinatorial. Where is
> the mathematical content?"

**How to defuse this.** You must argue — carefully, in the introduction —
that:

(a) The step-lists are not arbitrary metadata; they are *rewrite traces* drawn
from a specific, well-defined term rewriting system with a confluent, terminating
metatheory.

(b) The quotient by RwEq *recovers* the identity type (Theorem 3.15 in the
outline). So the construction is a *refinement* of propositional equality, not
a replacement.

(c) The mathematical payoff is that this refinement carries exactly the right
amount of structure to model weak ω-groupoids — and this is a *theorem*, not
a definition. The structure *emerges* from the rewrite system; it's not
hand-coded.

(d) The analogy: in algebraic topology, the fundamental groupoid of a space
records *which* path was taken, even though all paths between the same endpoints
are "the same" at the level of the underlying set. Similarly, computational
paths record *which* rewrite was used, even though all proofs are "the same"
at the level of Prop.

**Dedicate a full section (§1.3 or a standalone §1.4) to this issue.** Title it
something like "On the relationship between Path and Eq: what the two-level
structure captures." Do not bury it.

### 3.2 The "Deep Files" Problem: sorries in advanced modules

You have 5 files with `sorry` (the `*Deep.lean` files). The README claims
"zero sorry," but the grep found them. Even if these are in comments or
docstrings (the grep output suggests `AbstractHomotopyDeep.lean` mentions
"no sorry" textually), you must:

- **Audit rigorously.** Run `lake build` and confirm zero sorry warnings.
- **If any genuine sorry exists, either prove it or remove the file.** A single
  sorry in a 175K-line formalization is not a scandal, but claiming "zero sorry"
  when it's not true *is*.

### 3.3 The "13,000+ Machine-Verified Theorems" Claim

Your README says 7,597 theorems & lemmas. The PAPER_OUTLINE says 885 theorems
and 1,710 definitions. Where does "13,000+" come from? If you're counting
definitions + theorems + lemmas + structures, say so explicitly. Inflated
counts erode trust. **Use the precise number and explain the methodology.**

(Actually: 7,597 theorems/lemmas + 11,021 definitions/structures/classes ≈
18,618 total declarations. So "13,000+" might be an *undercount* of total
declarations, or an earlier snapshot. Clarify.)

### 3.4 The Scope Problem: Too Many Application Domains

The library touches: perfectoid spaces, prismatic cohomology, Langlands
program, Floer homology, tropical geometry, condensed mathematics, Kac–Moody
algebras, derived algebraic geometry, cluster algebras, motivic cohomology,
symplectic duality, Goodwillie calculus, chromatic homotopy theory, surgery
theory, and more.

**A hostile reviewer will say:** "There is no way a single library genuinely
formalizes all of these. Most of these must be thin wrappers or stub structures.
Show me the actual mathematical content."

And they would be partially right. For many of these domains, the library
likely defines the *structures* (a perfectoid space is a structure with
certain fields) and proves basic *path coherence* (that computational paths
respect the structure maps), but does not prove deep theorems *about*
perfectoid spaces (e.g., the tilting equivalence as a genuine mathematical
theorem, not a structure with the right type signature).

**Recommendation:** In the book, be ruthlessly honest about the depth of each
application:

- **Tier 1 (deep, genuine theorems):** Fundamental groups (S¹, T², S², figure-eight, Klein, lens spaces), Seifert–van Kampen, Eckmann–Hilton, ω-groupoid construction, Hurewicz
- **Tier 2 (substantial infrastructure):** Spectral sequences, covering spaces, fibrations, long exact sequences, operads
- **Tier 3 (structural frameworks):** Everything else

Only Tier 1 and Tier 2 should appear in the book proper. Tier 3 goes in an
appendix or a "Landscape" chapter that honestly says "here is infrastructure
we've set up; deep theorems await future work."

### 3.5 What You Don't Have (and Competitors Do)

| Feature | HoTT Book | Cubical Agda | This Work |
|---------|-----------|-------------|-----------|
| Univalence | Axiom | Theorem | Not applicable (extensional) |
| Higher inductive types | Axiom | Primitive | Simulated via PathExpr |
| Canonicity | No (axiom) | Yes | Yes (normalization) |
| Computational content | Partial | Full | Full (rewrite traces) |
| Foundation | Intensional MLTT | Cubical TT | Extensional (Lean CIC) |
| ω-groupoid | Proved (Lumsdaine) | Implicit | Proved |
| Formalization | Partial (Coq, Agda) | Full (Agda) | Full (Lean 4) |

You must be clear: **this is not a competitor to HoTT or cubical type theory
as a foundation.** It is a *different thing*: a combinatorial/algebraic layer
on top of classical type theory that recovers analogous structures. The value
is precisely that it works *without* changing the foundation.

### 3.6 The Confluence Proof

The outline mentions 76 rules (README says 47 primitive rules; some sources
say 77). The inconsistency is a red flag. Settle on a single, canonical count
and explain the discrepancy. (Are structural closure rules counted separately?
Are transport rules counted? Make it precise.)

The confluence proof via direct critical-pair analysis (using `HasJoinOfRw` as
a typeclass) is mathematically solid, but reviewers will want to see:

- The *complete* list of critical pairs
- That the proof handles *all* overlaps, not just representative ones
- Whether the proof is fully formalized or relies on the typeclass assumption
  `HasJoinOfRw` being instantiated

If `HasJoinOfRw` is an uninstantiated assumption in some modules, that's a
gap. The `GroupoidConfluence.lean` approach (direct joinability witnesses) is
better; make sure it covers everything.

---

## 4. Positioning Relative to Existing Literature

### 4.1 The HoTT Book (2013)

The HoTT Book is a *textbook on a new foundation*. Your book is not. Do not
frame it as "an alternative to HoTT." Frame it as: "We show that the
algebraic structures central to HoTT arise naturally from rewrite-trace
analysis, even in extensional type theory. This provides (a) independent
evidence that these structures are fundamental, and (b) a way to access them
without committing to a new foundational framework."

### 4.2 Rijke's *Introduction to HoTT* (2022)

Rijke's book is pedagogically excellent and mathematically clean. It covers
similar territory (identity types, fundamental groups, Eckmann–Hilton,
truncation, etc.) but from within intensional MLTT. Your differentiation:
you get these results *without* postulating anything about the identity type.
Cite Rijke frequently and respectfully.

### 4.3 Bezem–Coquand–Huber Cubical Type Theory

Cubical TT provides *computational* univalence — something you cannot match.
But you have something cubical doesn't emphasize: an explicit, finite,
confluent rewrite system with a complete metatheory. Your system is more
"syntactic" and "combinatorial" than cubical. Position as complementary.

### 4.4 Lumsdaine (2010) and van den Berg–Garner (2011)

These are your most direct predecessors for the ω-groupoid result. Lumsdaine
showed that identity types in intensional MLTT form weak ω-groupoids; van den
Berg–Garner refined this. Your contribution: you prove the analogous result
for a *different* structure (rewrite traces on extensional equality) and
provide a complete formalization. Cite both extensively and explain the
precise relationship.

### 4.5 Burroni, Métayer, Lafont (Higher-Dimensional Rewriting)

This school is your closest methodological kin. They study rewriting systems
on higher-dimensional cells. Your work can be seen as instantiating their
program in the specific context of type-theoretic equality. This connection
is underexplored in your current outline — I'd add a section on it.

---

## 5. Ideal Length and Structure

### Recommendation: 350–400 pages

Here's why:

- **< 250 pages:** Too short to do justice to both the foundations and the
  applications. The rewrite system alone, done properly, is 40–60 pages.
- **250–400 pages:** The sweet spot. Enough for full proofs of the core results
  and deep treatment of 5–6 application domains.
- **400–600 pages:** Only if you want to write a *reference work*. This risks
  the "too long for anyone to read" problem.
- **> 600 pages:** No. The HoTT Book is 589 pages and it's a multi-author
  project covering an entire foundation. You don't have that scope.

### Proposed Structure (350–400pp)

| Part | Content | Pages |
|------|---------|-------|
| **Part I: Foundations** | Ch 1–3: Motivation, Basic constructions, Rewrite system (full metatheory) | 80–100 |
| **Part II: Higher Structure** | Ch 4–6: Groupoid structure, ω-groupoid, Homotopy theory (loop spaces, π_n, Eckmann–Hilton) | 70–90 |
| **Part III: Computations** | Ch 7–9: Fundamental groups (S¹, T², S², figure-eight, Klein, lens), Seifert–van Kampen, Fibrations & exact sequences | 80–100 |
| **Part IV: Applications** | Ch 10–12: Selected deep applications (see §6) | 60–70 |
| **Part V: Meta & Conclusion** | Ch 13–14: Formalization methodology, Future directions | 20–30 |
| **Appendices** | Rule tables, theorem index, dependency graph | 20–30 |
| **Total** | | **330–420** |

### Critical editorial decision: Part I must be self-contained

A reader who knows basic type theory but not computational paths should be
able to read Part I and understand the entire setup. Do not assume familiarity
with the 2016–2018 papers. Restate everything from scratch, with motivation.

---

## 6. Part IV: Selective, Not Broad

### Recommendation: 5–6 domains, done deeply. Not 20+ domains surveyed.

**Why selective:**

1. A broad survey of 20+ domains will feel shallow and invite the "thin wrapper"
   criticism (§3.4 above).
2. Each deep application chapter can demonstrate a *different facet* of the
   computational paths machinery.
3. A reader who sees 5 deep applications will trust that the 6th through 20th
   are feasible. A reader who sees 20 shallow ones will trust none of them.

### Recommended application chapters:

| Chapter | Domain | What It Demonstrates |
|---------|--------|---------------------|
| Ch 10 | **Spectral sequences** | The rewrite system managing differentials and page-turning; shows the algebra at its most computational |
| Ch 11 | **Covering spaces & Galois correspondence** | The two-level structure (Path vs Eq) is essential; covering transformations are path-level, classification is Eq-level |
| Ch 12 | **Operads and A∞-algebras** | The ω-groupoid structure meets algebra; coherence conditions are exactly the higher cells |
| Ch 13 | **Category theory (∞-groupoids, enriched categories)** | Shows the formalism naturally lands in higher category theory; connection to Lurie, Joyal |
| Ch 14 | **Lie groups & differential topology** | π₁(SO(2)) ≅ ℤ via computational paths; connects abstract rewriting to geometric intuition |

**Reserve a final chapter (Ch 15) as a "Landscape" survey:** 2–3 pages each on
the remaining domains (perfectoid, prismatic, tropical, etc.), honestly
framed as "infrastructure laid; deep theorems are future work."

### Domains to *exclude* from deep treatment:

- Langlands program (too far from the core technology)
- Condensed mathematics (Scholze's framework is not naturally path-theoretic)
- Floer homology (requires analytic foundations you don't have)
- Surgery theory / bordism (too classical-topology, too far from rewriting)

These can be mentioned in the Landscape chapter but should not pretend to be
deep applications.

---

## 7. Specific Technical Recommendations

### 7.1 Standardize the rule count

Pick one number and justify it. My recommendation:

- **47 primitive rules** (the constructors of `Step`)
- **+4 structural closure rules** (symm_congr, trans_congr_left/right, context_congr)  
- **+6 cancellation/completion rules** (trans_cancel_left/right, etc.)
- **= 57 rules total** (or however many there actually are)

If you've been saying "76" or "77" elsewhere, explain that you're counting
derived rules or rule instances.

### 7.2 Clarify the sorry situation

Run:
```bash
grep -rn "sorry" ComputationalPaths/ --include="*.lean" | grep -v "no sorry" | grep -v "-- sorry" | grep -v "docstring"
```
and report the result in the book's appendix on formalization methodology.

### 7.3 The J-elimination derivation needs its own section

This is your single most impressive foundational result. Give it a full section
(3–5 pages), with:
- Statement of J in the computational-paths framework
- The proof from contractibility of based path space
- Why this matters: in HoTT, J is axiom; here it's theorem
- What this says about the expressiveness of the rewrite system

### 7.4 Include a "Reading Guide" chapter

Given the book's length and the diversity of potential audiences, include a
1–2 page reading guide:

- **For type theorists:** Read Parts I, II, V; skim III–IV.
- **For algebraic topologists:** Read Ch 1, skim Ch 2–3, read Parts III–IV.
- **For rewriting theorists:** Read Parts I–II, skip III–IV.
- **For formalization enthusiasts:** Read Ch 1, Ch 14 (methodology), appendices.

---

## 8. The Hard Question: Is This One Book or Two?

There's a tension between two books trying to coexist:

**Book A:** "The rewrite system for computational paths: foundations, metatheory,
and the ω-groupoid result." — 200 pages, aimed at logicians and type theorists.

**Book B:** "Algebraic topology via computational paths." — 250 pages, aimed at
mathematicians who want to see homotopy theory done combinatorially.

The proposed 350–400pp volume is essentially A+B. This can work, but only if
the transition from A to B is seamless. The risk is that Part I feels like a
logic paper and Part III feels like a topology textbook, with the connection
underexplained.

**Recommendation:** Write the book so that the ω-groupoid result (end of Part II)
is the *climax* of the theoretical development, and Part III is a sustained
*application* of that result. The narrative should be: "We built a machine
(Parts I–II); now watch it compute (Part III)."

---

## 9. Publisher Targeting

### First tier:
- **Cambridge University Press** (Lecture Notes in Logic, or Cambridge Tracts in Mathematics)
- **Springer** (Lecture Notes in Computer Science, or the "Theory and Applications of Computability" series)

### Second tier:
- **Oxford University Press** (Logic in Computer Science series)
- **College Publications** (edited by Dov Gabbay — very friendly to non-standard logic)

### Longshot but high-impact:
- **IAS / Princeton University Press** (if you can frame it as a foundations book; they published the HoTT Book)

**Recommendation:** Target Cambridge LNL or Springer LNCS first. The formalization
angle makes it attractive to CS-oriented publishers; the mathematical content
makes it attractive to math publishers. CUP has published Ruy de Queiroz's
work before (WoLLIC proceedings), which helps.

---

## 10. Final Verdict

### Strengths (in order of importance):
1. Genuinely novel theoretical contribution (ω-groupoid from rewrite traces)
2. Massive, sorry-free formalization providing verification
3. Concrete computations matching HoTT results via different methods
4. Clear connection to established research program (de Queiroz et al.)
5. The two-level structure echoing 2LTT from a surprising direction

### Weaknesses (in order of severity):
1. Working inside UIP must be explained, not hidden
2. Application domains are too broad — depth is uneven
3. Inconsistent statistics (rule counts, theorem counts) across documents
4. Some typeclass assumptions (`HasLocalConfluenceProp`, etc.) are uninstantiated — these are effectively axioms
5. Relationship to prior publications by the same group needs sharper delineation

### Overall assessment:
**This should be published.** The core contribution — deriving higher-dimensional
groupoid structure from a confluent rewrite system on equality traces — is
mathematically interesting, technically substantial, and well-suited to book
treatment. The formalization provides extraordinary backing. But the book
needs an honest reckoning with its architectural choices and a ruthless pruning
of its application scope. A 350–400 page volume, selective in applications
and upfront about limitations, would be a significant addition to the literature
at the intersection of proof theory, rewriting, and higher-dimensional algebra.

---

*Document prepared for internal planning purposes. Not for distribution.*
