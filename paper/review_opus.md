# Reviewer Report: "The Algebra of Computational Paths: Rewrite-Trace Equality, Weak ω-Groupoids, and Higher-Dimensional Structure"

**Submitted to:** The Bulletin of Symbolic Logic (BSL)  
**Reviewer:** Anonymous  
**Date:** 2026-02-11  

---

## 1. Summary

The paper presents a mathematical theory of *computational paths*—a framework in which propositional equalities between elements of a type are augmented with explicit rewrite traces recording the sequence of elementary steps by which equalities were derived. A computational path from *a* to *b* in type *A* is a pair (s, π) consisting of a list of elementary steps and a propositional equality proof. The key insight is that even in a type theory satisfying UIP (proof irrelevance for Eq), the rewrite traces are distinct combinatorial objects, allowing the recovery of higher-dimensional algebraic structure.

The principal claimed contributions are:

1. **A complete algebraic framework** for computational paths, including reflexivity, symmetry, transitivity, congruence, transport, and operations for products, sums, sigma types, and function types, with many laws holding strictly (as definitional equalities).

2. **A confluent, terminating rewrite system** (the LND_EQ-TRS) with 74 rules in 8 groups, with proofs of soundness, termination via recursive path ordering, local confluence via a strip lemma, and global confluence via Newman's lemma.

3. **A weak ω-groupoid structure** (in the sense of Batanin–Leinster) arising from iterated derivation cells, with contractibility beginning at dimension 3—preserving non-trivial π₁ while collapsing higher coherence.

4. **Homotopy-theoretic applications**: fundamental groups, π₁ computations for standard spaces (S¹, T², S¹∨S¹), the Seifert–van Kampen theorem, fibrations, covering spaces, exact sequences, and advanced topics (Eilenberg–MacLane spaces, Postnikov towers, spectral sequences).

5. **Mechanized verification** in Lean 4.

---

## 2. Technical Soundness

### 2.1. Core Definitions (Sections 1–2)

The basic definitions (Step, Path, toEq, ofEq) are clean and correct. The representation of Path as a record with a step list and a proof field is well-motivated and the choice to *not* require compositional well-formedness of consecutive steps (Definition 1.4: "We do not require that consecutive steps in the list compose") is noted—this is a pragmatic engineering decision that trades internal coherence for convenience. The sole typing guarantee being the proof field π is technically sound but philosophically unusual, and the paper would benefit from more discussion of this design choice and its implications.

The strict algebraic laws (Theorem 2.4, 2.5, 2.6) are correct consequences of list identities. The observation that cancellation (p · p⁻¹ = refl) does *not* hold strictly (Remark 2.7) is a key insight and correctly motivates the rewrite system.

### 2.2. The Rewrite System (Section 3)

The 74-rule count is a central claim but requires clarification:

- **Discrepancy with the formalization.** Inspection of the Lean formalization reveals that the `Step` inductive type has **75 unique constructor names**, not 74. The extra constructor appears to be `subst_sigmaMk_dep_beta`, which is not listed in the paper's appendix. Additionally, many constructors appear at multiple universe instantiations (148 total pattern-matches), though this may be a consequence of Lean's universe polymorphism rather than distinct rules.
  
- **The paper acknowledges discrepancy with prior work** (76 rules in [RDQO18]), attributing it to "two context-congruence rules that serve double duty." This is reasonable but the explanation in the abstract is parenthetical and cursory—it deserves a clearer discussion, ideally in Section 3 proper.

- **Rule R31 / R74 duplication.** Context congruence appears in both Group IV (R31) and Group VIII (R74), which the final remark acknowledges. This is confusing: if it's a single constructor, it should be counted once and its dual role explained. The paper's count of 74 is achieved by this deduplication, but the appendix listing still presents it twice, which is internally inconsistent.

**Termination (Theorem 3.10).** The termination proof via RPO is described at a high level. The definitions of the RPO measure (Definition 3.12) are somewhat vague—the "aggregate weight pathLenSum" and "symbol drawn from {nf} ∪ Rule ∪ {pathLen(n)}" are not precisely defined in the paper. Given that this is a 74-rule system, the case analysis "each rule either reduces the symbol rank or maintains the rank while strictly decreasing the aggregate weight" requires significant effort; the paper defers entirely to the formalization, which is acceptable for a journal with formalization but leaves the paper itself less self-contained.

**Confluence (Theorem 3.15).** The proof strategy (strip lemma + Newman's lemma) is standard and correct. The critical pair analysis (Section 11.3) enumerates representative families but states that the full analysis "covers all pairs among the 74 rules"—with O(74²) = 5,476 potential pairs (reduced by grouping), this is tractable but the paper provides only illustrative cases. Again, the formalization serves as the definitive reference.

**Normalization (Theorem 3.8).** This result is surprisingly strong: normalize(p) = ofEq(toEq(p)), and two paths are RwEq-equivalent iff they have the same normal form—which, by proof irrelevance, means *all* paths with the same endpoints are RwEq-equivalent. This is correctly identified in Remark 3.9 as making RwEq the total relation. The paper argues that the value lies not in the equivalence relation but in the constructive witnesses (the explicit rewrite sequences). This is a valid and important point, but it means that *qua equivalence relation*, the rewrite system is trivial. The paper should more prominently acknowledge this and ensure the reader does not misunderstand the nature of the contribution.

### 2.3. ω-Groupoid Structure (Section 5)

The construction of the globular tower and derivation cells is well-structured. The contractibility theorem at dimension ≥ 3 (Theorem 5.11) is the linchpin: its proof relies on the fact that RwEq is Prop-valued, so projections from Derivation₂ to RwEq are identified by proof irrelevance, and the RwEq-coherence constructor of MetaStep₃ provides the connecting 3-cell. This is technically correct.

**However**, there is a conceptual tension: if all two-cells between the same pair of paths exist (since RwEq is the total relation in the UIP setting), then contractibility at dimension 2 also holds in a sense—any two paths are connected by a two-cell. The paper distinguishes between the *existence* of a two-cell (which requires an explicit RwEq witness) and the *Prop-valuedness* that makes all such witnesses equal. The distinction between Derivation₂ (type-valued, carrying structure) and RwEq (Prop-valued) is crucial and correctly drawn, but deserves even more emphasis.

The pentagon and triangle coherence laws (Theorems 5.4, 5.5) hold trivially by proof irrelevance, which the paper correctly notes in Remark 5.8. This is a feature of the framework but reduces the mathematical content of these results.

### 2.4. Homotopy Theory (Sections 6–10)

The fundamental group construction (Section 6) is standard and correct. The Eckmann–Hilton argument (Theorem 6.10) is carefully stated, using Derivation₃ cells for the intermediate equalities.

**The circle computation (Theorem 7.4)** uses a "path expression" model of S¹ rather than a higher inductive type. The key subtlety is that S¹ is defined as a *single-point type* {base} with a formal loop generator in the path expression system. This is a departure from HoTT's circle HIT, and the paper correctly notes this in Remark 7.2. However, the winding number argument (Lemma 7.3) is essentially the standard argument from HoTT, adapted to the path expression setting. The proof that the winding number is a *complete* invariant for path expressions modulo rewriting requires showing that every path expression rewrites to a canonical power of loop—this is plausible but the details ("use Rule 8 to flatten, Rule 2 to eliminate double symm, Rules 5–6 to cancel") are sketched rather than proved.

**Sections 8–10** (fibrations, Hurewicz, advanced topics) move increasingly from fully formalized to "statement-only" scaffolding. The formalization status table (Table 1) is commendable in its honesty, but the paper presents a vast amount of material (spectral sequences, K-theory, characteristic classes, chromatic homotopy theory, THH, Goodwillie calculus, higher topos theory) at the "statement-only" level. Much of Section 10 reads like a survey of algebraic topology rather than a contribution of the paper. While this may be appropriate for a monograph or thesis, it is questionable for a journal article.

---

## 3. Novelty

### What is new:
1. **The computational paths framework itself**—the idea of augmenting propositional equalities with explicit rewrite traces—was introduced in prior work by the same authors [DQOR16, RDQO18, ramos19]. The present paper is an extended, formalized development.

2. **The Lean 4 formalization** is new and substantial (380 source files, ~76,000 lines of author code).

3. **The weak ω-groupoid theorem** (Theorem 5.16) with contractibility at dimension 3 is the main new mathematical result. The prior work established the rewrite system; this paper proves the higher-dimensional structure theorem.

4. **The homotopy-theoretic applications** (π₁ computations, Seifert–van Kampen, fibrations) extend the earlier framework.

### Significance:
The contribution is significant for the rewriting/type theory community. The framework provides an alternative to HoTT for recovering higher-dimensional structure in a UIP setting. However, some caveats:

- The ω-groupoid structure is, in some sense, "trivial at dimension ≥ 2" due to RwEq being the total relation. The non-trivial content lives in the *syntactic* derivation structure, not in the *semantic* equivalence. This is explicitly acknowledged but may limit the applicability.

- The comparison with Lumsdaine [Lumsdaine10] and van den Berg–Garner [vdBG11] is stated but not developed in detail. A more thorough comparison would strengthen the novelty claim.

---

## 4. Clarity and Presentation

### Strengths:
- The paper is generally well-written, with clear definitions and a logical progression from basic constructions through the rewrite system to the higher-dimensional structure.
- The formalization status table (Table 1) is an excellent practice that should be more widely adopted.
- The design decisions for the formalization (Section 12.2) are informative.

### Weaknesses:

1. **Length and scope.** At approximately 4,600 lines of LaTeX (over 100 pages when compiled), the paper is far too long for a journal article, even for BSL which publishes longer papers. It reads as a condensed monograph covering Sections 1–5 (the core theory, ~50 pages) and Sections 6–10 (applications, ~40 pages), plus metatheory and conclusion. **I strongly recommend splitting this into two papers**: one covering Sections 1–5 (the algebraic framework, rewrite system, and ω-groupoid) and one covering the applications. Alternatively, Sections 8–10 could be significantly compressed.

2. **The "scaffolded" and "statement-only" material.** Presenting definitions and theorems from advanced algebraic topology (Postnikov towers, spectral sequences, K-theory, operads, chromatic homotopy theory) without proofs or even formalized statements dilutes the contribution. The reader cannot assess the correctness of these claims, and they add considerable length without proportionate value.

3. **Notation.** The paper uses both p · q and trans(p, q) for composition, and both p⁻¹ and symm(p) for inversion. While the paper acknowledges this, it increases cognitive load.

4. **Cross-references.** The paper uses both numbered references ("Theorem 2.4", "Rules 3 and 4") and cleveref ("\cref{thm:strict-monoid}"). The numbered references in Sections 6–10 appear to use a different numbering scheme (referring to "Theorem 2.4" rather than section-local theorem numbers), which suggests these sections were converted from a different source and the references were not fully updated.

---

## 5. Section-by-Section Comments

### Section 1 (Introduction)
- **p. 1, Abstract:** "74 rules (the count of 74 follows from the distinct constructors in our formalization; the earlier convention of 76 in [RDQO18] counted two context-congruence rules that serve double duty)"—this parenthetical in the abstract is awkward. Move the explanation to the body.
- **Definition 1.4:** The non-requirement that consecutive steps compose is surprising and should be discussed more prominently—it means the "step list" is not really a rewrite sequence in the classical TRS sense.
- **Theorem 1.7 (Non-UIP):** The proof is simple and correct. However, calling this the "foundational result that enables the entire subsequent development" (Remark 1.8) is somewhat misleading—the key enabler is the *design decision* to use a record type with a list field, not a deep mathematical fact.

### Section 2 (Basic Constructions)
- **Theorem 2.4 (Strict Monoid Laws):** The proof of (iii) claims associativity follows from `List.append_assoc` and "associativity of Eq.trans." The latter requires clarification—associativity of Eq.trans holds by proof irrelevance (all proofs of a = d are equal), not by a structural computation. This should be stated more carefully.
- **Theorem 2.8 (Functoriality):** Part (ii) claims map(F, reverse(map(G, s))) = reverse(map(F ∘ G, s)), which requires map and reverse to commute. The standard fact is `List.map_reverse`, which is correct.
- **Subsection 2.6 (Sigma Paths):** The β-rules reduce to ofEq(toEq(p)), not to p itself. This is a notable weakness compared to HoTT where β-rules are strict—the paper should explicitly discuss this difference.
- **Subsection 2.9 (Contexts):** The definitions of substL and substR are clear, but the "extensive algebra of identities" is mostly deferred to Section 3 (the rewrite system). The β-rules listed here (r · C[p] ↝ substL(C, r, p) and C[p] · t ↝ substR(C, p, t)) are rewrite rules that *fold* expressions into substitution form—this is the opposite direction from what one usually calls a β-rule. The naming is potentially confusing.

### Section 3 (The Rewrite System)
- **Rule numbering:** The rules are numbered R1–R74, but the numbering in the body text (§3.1.2–§3.1.8) does not always match the appendix. For example, rules "22–25" are mentioned as governing "dependent contexts with symmetry" but are not explicitly listed; the reader is referred to Groups V–VI. Similarly, Rule 30 is mentioned as "addresses transport through sigma constructors" without being stated.
- **Section 3.6 (Confluence):** The statement of the strip lemma (Theorem 3.14) says "If p ↝ q and p ↝* r" but the standard strip lemma requires p ↝ q and p ↝* r, which is what's stated. Good.
- **Section 3.7 (Extension Patterns):** This subsection reads like a user guide for extending the TRS. While useful, it is unusual in a mathematical paper and could be moved to the formalization documentation.
- **Section 3.9 (Well-Formed Traces):** This subsection introduces the notion of well-formed traces but does not make clear why it's needed—given that normalize(p) provides a canonical representative, what role do well-formed traces play beyond being a concept?

### Section 4 (Groupoid)
- Clean and well-organized. The table comparing raw paths (weak groupoid) vs. quotient (strict groupoid) is helpful.
- **Definition 4.5 (Equality Functor):** The functoriality witnesses are stated as equalities, which are *strict* by Theorem 2.8. This could be emphasized more.

### Section 5 (Higher-Dimensional Structure)
- **Remark 5.8 (Proof-irrelevance coherence):** This is the most important remark in the section—all coherence conditions at the 2-cell level hold trivially. This should perhaps be promoted to a theorem or at least given more prominence.
- **Theorem 5.16 (Main Structure Theorem):** The proof assembles previously established results but the definition of weak ω-groupoid (Definition 5.15) is somewhat informal. The connection to Batanin–Leinster's precise definition should be made more rigorous—what exactly is a "weak ω-groupoid in the sense of Batanin–Leinster," and how precisely does this construction satisfy the definition? The paper cites [Leinster04] and [Batanin98] but does not reproduce the definition or verify the match in detail.
- **Remark 5.13 (Critical Design Choice):** "on the circle S¹, the loop generator and refl are *not* connected by a two-cell." But RwEq is the total relation (Remark 3.9), so they *are* connected by a two-cell in the sense of RwEq. The resolution is that the loop generator lives in the *path expression* calculus, not in Path—but this distinction is not clear until Section 7. The forward reference creates confusion.

### Section 6 (Fundamental Groups)
- **Reference style change:** This section uses "Theorem 2.4" style references rather than \cref, suggesting it was converted from a separately authored source. The references should be unified.
- **Theorem 6.3:** The proof refers to "Rules 3 and 4" and "Rules 5 and 6" by number. These should use the rule labels (lrr, rrr, tr, tsr) or cross-references for clarity.
- **Theorem 6.10 (Eckmann–Hilton):** The proof is correct but long. The notation switches between ∘_v, ∘_h, ▷_R, ◁_L which is non-standard. The argument could be tightened.

### Section 7 (Spaces)
- **Theorem 7.4 (π₁(S¹) ≅ ℤ):** The proof is essentially the winding number argument. It is correct but relies on a key unstated assumption: that the path expression system for S¹ is "complete" in the sense that every element of π₁(S¹, base) is representable. Since S¹ = {base} with the path expression generators, this is true by construction, but should be made explicit.
- **Sections 7.3–7.6:** These sections (figure-eight, Seifert–van Kampen, suspensions, Klein bottle, projective spaces, lens spaces) are partially or fully unformalized. They constitute a substantial portion of the paper but their contribution is limited to showing that standard results *can be stated* in the framework.

### Section 8 (Fibrations)
- **Theorem 8.3 (Path Lifting):** The lifted path is constructed as ofEq(h), making it a one-step path. This is correct but means that the "lifting" is essentially trivial at the trace level—the lift carries no interesting trace information. This should be discussed.
- **Theorem 8.6 (Hopf Fibration Data):** Labeled as PS (Partially Scaffolded). The proof says "The computational path witnesses ensure that all conditions hold constructively," but this is a claim about the formalization that cannot be verified from the paper alone. Given the PS status, the reader should be more explicitly warned.

### Section 9 (Hurewicz)
- **Theorem 9.5 (Hurewicz, dimension 1):** "The isomorphism is the identity on the underlying quotient type"—this is tautological, since H₁(A) is *defined* as π₁(A,a)^ab. The theorem is really the definition. The interest lies in the examples and consequences, not in the proof.

### Section 10 (Advanced Homotopy Theory)
- This section surveys a vast range of advanced topics (Eilenberg–MacLane spaces, Postnikov towers, Whitehead's theorem, Freudenthal suspension, spectral sequences, K-theory, characteristic classes, operads, rational homotopy theory, chromatic homotopy theory, THH, Goodwillie calculus, higher topos theory). All are SO (Statement Only) in the formalization. **This section should be either drastically shortened or removed.** It does not contribute mathematical content—it merely restates well-known definitions and results, claiming they can be "stated" in the framework.
- **Proposition 10.5 (Low-dimensional stable stems):** A table of stable stems is presented as a "proposition" with no proof or even a proof sketch. This is a statement of classical results, not a contribution.

### Section 11 (Metatheory)
- **Table 2 (LND_EQ-TRS mnemonics):** Useful but incomplete—only some rules are listed, with "…" covering the rest.
- **Theorem 11.8 (Decidability of RwEq):** The proof is trivially "always return yes" due to proof irrelevance. This is correctly identified in Remark 11.9, but presenting it as a formal theorem when the answer is trivially positive in the UIP setting is somewhat misleading about the depth of the result.

### Section 12 (Conclusion)
- **Formalization metrics:** The paper claims "302 source files, 60,860 total lines of code." My inspection of the repository reveals **380 source files and approximately 76,260 lines** (in the ComputationalPaths directory, excluding .lake dependencies). The paper's numbers may reflect a snapshot at a different time, but they should be verified and updated. If the .lean root file and other top-level files are included, there may be different counting conventions, but the discrepancy is non-trivial.
- The claimed counts of "1,710 definitions, 885 theorems, 701 structures, 69 inductive types" do not match my grep-based analysis of the repository (approximately 2,207 defs, 967 theorems, 1,286 structures, 73 inductives), though counting methodology may differ (e.g., whether to count `instance` as `def`, whether to count declarations inside `where` blocks).

---

## 6. Mathematical Concerns

### 6.1. The Rewrite System

**Rule count.** The formalization's `Step` inductive has 75 unique constructor names, not 74. The discrepancy appears to come from `subst_sigmaMk_dep_beta`, which is present in the code but not listed in the paper's appendix. The paper should reconcile this.

**Confluence proof.** The paper's confluence proof relies on Newman's lemma (terminating + locally confluent ⇒ confluent). This is correct but the application requires:
1. Termination (established via RPO but details are sparse).
2. Local confluence (established via the strip lemma with exhaustive critical pair analysis).

The critical pair analysis with 75 rules generates potentially thousands of pairs. The paper claims these are all checked in the formalization, which is the appropriate level of verification, but the paper itself provides only 5 illustrative cases.

### 6.2. ω-Groupoid Construction

The definition of "weak ω-groupoid in the sense of Batanin–Leinster" (Definition 5.15) is informal. The actual Batanin–Leinster definition involves globular operads and their algebras—a technically demanding framework. The paper does not verify that the computational paths construction satisfies this precise definition. Instead, it verifies a set of conditions (cells at every dimension, groupoid operations, contractibility at dimension ≥ 3, bicategorical coherence as 3-cells) that are *consistent with* the Batanin–Leinster framework but do not constitute a formal verification of it. This gap should be acknowledged.

### 6.3. π₁ Computations

The computations of π₁(S¹), π₁(T²), and π₁(S¹∨S¹) are correct but depend on the path expression construction, which is essentially a formal presentation of the fundamental groupoid. The winding number argument for S¹ is standard. The claim that π₁(S¹∨S¹) ≅ ℤ∗ℤ is marked PS (Partially Scaffolded), as is the Seifert–van Kampen theorem—these are significant results whose incomplete formalization weakens the contribution.

### 6.4. RwEq Triviality

The most mathematically subtle issue in the paper is the tension between:
- RwEq being the total relation on each Path_A(a,b) (Remark 3.9), and
- The claim that computational paths carry non-trivial higher-dimensional structure.

The resolution is that the *structure* lies in the derivation cells (the explicit rewrite sequences), not in the bare equivalence relation. This is correctly stated but could be explored more deeply—what exactly is the mathematical content that survives this triviality? The answer appears to be: the combinatorial structure of the rewrite system itself, viewed as a higher-dimensional rewriting system in the sense of Burroni–Squier.

---

## 7. Formalization Claims

### 7.1. Repository Discrepancy

The paper's body text gives the repository URL as `https://github.com/Arthur742Ramos/ComputationalPathsLean`, while the bibliography entry [cplean] gives `https://github.com/Asjidkalam/ComputationalPathsLean`. These must be made consistent.

### 7.2. Formalization Metrics

As noted above, the claimed metrics (302 files, 60,860 lines, 1,710 defs, 885 theorems, 701 structures, 69 inductives) do not exactly match my inspection of the repository (380 files, ~76,260 lines, ~2,207 defs, ~967 theorems, ~1,286 structures, ~73 inductives). The counts of *structures* in particular differ substantially (701 vs. ~1,286). These discrepancies may reflect different counting conventions, repository snapshots, or the inclusion/exclusion of auto-generated code, but they should be resolved.

### 7.3. Sorry/Axiom Usage

No uses of `sorry` were found in the codebase (two grep matches are false positives—comments stating "no sorry"). No custom axioms were found beyond structure fields (which are standard). This is a positive finding supporting the "fully formalized" claims.

### 7.4. Formalization Status Table

Table 1 is thorough and honest about the verification status. The distinction between FF (Fully Formalized), PS (Partially Scaffolded), and SO (Statement Only) is clear and useful. However, the paper should more clearly separate the FF results (which are the actual contribution of the formalization) from the PS/SO results (which are aspirational).

---

## 8. BSL Format Compliance

### 8.1. Document Class
The paper uses `\documentclass[manuscript]{BSLstyle}`, which is correct.

### 8.2. Abstract
The abstract is substantive and within typical BSL length. However, the parenthetical about the rule count (74 vs. 76) should be removed from the abstract and addressed in the body.

### 8.3. Keywords
Seven keywords are provided, which is reasonable.

### 8.4. Author Information
Four authors with affiliations are correctly specified. The `\AuthorEmail`, `\Affiliation`, `\Funding`, `\Conflict`, `\Ethics`, and `\UseOfGAI` fields are filled in.

### 8.5. Bibliography
The bibliography uses `BSLbibstyle`, which is correct. The entries are generally well-formatted. Some concerns:
- **[Brunerie16]** has the field `journal = {arXiv preprint arXiv:1606.05916}`—this should use `note` or `eprint` for an arXiv preprint, not `journal`.
- **[LicataShulman13]** has both `booktitle` and `journal` fields (as `\article` entry type with `booktitle`), which is inconsistent; it should be `@inproceedings`.
- **[Squier94]** is cited as [Squier94] in the text but the entry is `@article{Squier94,...}` with `year = {1987}`. The note mentions "Squier–Otto–Kobayashi (1994)" which is a different publication.
- **[cplean]** URL discrepancy as noted above.

### 8.6. Length
The paper is extremely long for a journal article. BSL publishes both research articles and survey/expository pieces; the paper's scope suggests it should either be submitted as a survey (with reduced formalism) or substantially shortened to focus on the core contributions (Sections 1–5).

### 8.7. Section Numbering
The paper uses `\section` for all major divisions, which is correct for BSL (as opposed to `\chapter` for a book). The labels use a mix of `sec:`, `ch:`, and `subsec:` prefixes, suggesting conversion from a book format. While this doesn't affect rendering, it should be cleaned up.

---

## 9. Specific Suggestions

### Critical (must fix before acceptance):

1. **Reconcile the rule count.** The Lean formalization has 75 unique Step constructors; the paper claims 74. Either update the paper or explain the discrepancy (e.g., if `subst_sigmaMk_dep_beta` is derived from other rules).

2. **Fix the repository URL discrepancy** between the body text and the bibliography entry [cplean].

3. **Update or verify the formalization metrics** (file count, line count, definition/theorem/structure counts).

4. **Drastically shorten Section 10** (Advanced Homotopy Theory). The SO-level material (K-theory, chromatic homotopy, THH, Goodwillie calculus, higher topos theory) does not contribute to the paper and inflates it unnecessarily.

5. **Address the ω-groupoid definition gap.** The connection to Batanin–Leinster's precise definition should be made explicit or the claim should be softened (e.g., "satisfies the axioms analogous to those of a weak ω-groupoid").

### Major (should be addressed):

6. **Unify cross-reference style.** Sections 6–10 use "Theorem 2.4" style while Sections 1–5 use `\cref`. All references should use `\cref` consistently.

7. **Clarify the role of RwEq triviality** more prominently. The fact that RwEq is the total relation in the UIP setting is the single most important caveat for the reader. It should be highlighted early (e.g., in the introduction) rather than relegated to a remark in Section 3.

8. **Clarify Definition 1.4.** The non-requirement that consecutive steps compose deserves a dedicated remark explaining why this is acceptable and what it means for the interpretation of the step list as a "trace."

9. **Separate FF results from PS/SO results** more clearly in the paper's narrative. Currently, fully formalized results and "statement-only" results are presented with the same level of confidence.

10. **Discuss the relationship to Squier's finite derivation type** more precisely. The paper mentions this in the future directions but the connection is actually central to the contribution—the rewrite system generates higher cells, and the critical pair analysis provides 3-cells, exactly as in Squier's theory.

### Minor:

11. **Abstract:** Remove the parenthetical about 74 vs. 76 rules.

12. **p. Section 2, Theorem 2.4(iii):** Clarify that "associativity of Eq.trans" holds by proof irrelevance, not by a structural computation.

13. **p. Section 2, Remark 2.7:** "the left-hand side has step list s ++ reverse(map(symm_Step, s)), which is non-empty whenever s ≠ []"—this should read "whenever p is not refl", since refl has s = [].

14. **p. Section 3, Remark 3.5:** The remark about including strict equalities as rewrite rules "for two reasons: (i) structural closure rules may produce these patterns nested inside larger contexts; (ii) the rewrite system must be self-contained"—reason (i) is the important one; reason (ii) is circular without further explanation.

15. **p. Section 5, Definition 5.6:** The "Horizontal composition" of two-cells uses the notation (η ◁_R g) ∘_v (f' ▷_L θ), but the whiskering notation ◁_R and ▷_L is backwards from the standard categorical convention (where ▷ indicates left whiskering and ◁ indicates right whiskering in most sources). Verify and standardize.

16. **p. Section 6, Definition 6.1:** "Composition: comp(p, q) = trans(p, q)"—but comp has already been defined as the dot notation p · q. The proliferation of names (comp, trans, ·) for the same operation is confusing.

17. **p. Section 7, Definition 7.1:** The "computational-path circle" S¹ = {base} is not really a definition of the circle as a topological space—it's a definition of a formal loop system. The name is potentially misleading.

18. **p. Section 9, Theorem 9.5:** As noted, the Hurewicz theorem at dimension 1 is essentially the definition of H₁. Consider renaming or reframing.

19. **Appendix A:** Rule R19 (sigma_mk_symm) states "where q' incorporates the transport correction" without specifying q'. This is insufficient.

20. **Bibliography:** Fix [Brunerie16] to use `@misc` or add proper journal information if published. Fix [LicataShulman13] entry type. Fix [Squier94] year discrepancy.

---

## 10. Recommendation

The core contribution (Sections 1–5, 11)—the algebraic framework, rewrite system, and ω-groupoid structure—is novel, technically sound (modulo the minor issues noted), and supported by a substantial formalization. However, the paper in its current form is far too long and tries to cover too much ground, with the later sections (8–10) contributing diminishing returns.

**Recommendation: Major Revision.**

The paper should be substantially shortened (by 40–50%) by:
1. Removing or drastically compressing Sections 8–10 (fibrations, Hurewicz, advanced topics).
2. Focusing the narrative on the core contributions (the algebraic framework, the rewrite system with its metatheory, and the ω-groupoid construction).
3. Fixing the technical issues enumerated above.
4. Providing a clearer upfront discussion of the RwEq triviality and its implications.

A focused version of this paper, covering Sections 1–5, 6–7 (the π₁ computations), 11, and 12, would make a strong contribution to the Bulletin of Symbolic Logic.
