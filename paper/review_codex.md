# Referee Report: "The Algebra of Computational Paths: Rewrite-Trace Equality, Weak ω-Groupoids, and Higher-Dimensional Structure"

**Manuscript submitted to:** Bulletin of Symbolic Logic  
**Date of review:** 2026-02-11  
**Recommendation:** Major revision

---

## 1. Summary

The paper develops a theory of *computational paths*—pairs $(s, \pi)$ where $s$ is a list of elementary rewrite steps and $\pi$ is a propositional equality proof—in a type theory satisfying UIP. Even though the underlying equality is proof-irrelevant, the traces $s$ are distinct combinatorial objects and the space $\mathrm{Path}_A(a,b)$ violates UIP (Theorem 1.7). The authors define a confluent, terminating 74-rule rewrite system (the $\mathrm{LND}_{\mathrm{EQ}}$-TRS) on paths, prove it yields unique normal forms, construct a quotient recovering the standard identity type, and show the resulting tower of iterated derivation cells forms a weak ω-groupoid with contractibility at dimension ≥ 3. Applications include computations of $\pi_1$ for the circle, torus, figure-eight, and related spaces, plus fibrations, covering spaces, exact sequences, the Hurewicz theorem, and a survey of advanced homotopy theory. The development is accompanied by a Lean 4 formalization.

The paper is ambitious in scope, weaving together rewriting theory, categorical algebra, and homotopy theory into a single framework with machine-checked foundations. The core technical contributions—the rewrite system, its metatheory, and the ω-groupoid construction—are substantial and clearly original.

---

## 2. Technical Soundness

### 2.1 Strengths

- The basic path algebra (Section 2) is clean and the proofs that monoid laws, involution, and anti-homomorphism hold *strictly* (as list identities) are correct and elegant.
- The observation that cancellation ($p \cdot p^{-1} = \mathrm{refl}$) fails strictly but holds under rewriting is well-motivated and central to the paper.
- Soundness of the rewrite system (Theorem 3.3) is straightforward but stated precisely.
- The argument from termination + local confluence (strip lemma) to global confluence via Newman's lemma is the standard approach and is correctly applied.
- The ω-groupoid construction is conceptually clear: two-cells are $\mathrm{RwEq}$ witnesses (Prop-valued), so all higher coherence is automatic by proof irrelevance.

### 2.2 Concerns

1. **Trivial RwEq (Remark 3.9) undermines several claims.** The authors acknowledge that *all* paths with the same endpoints are RwEq-equivalent (because normalization collapses everything via $\mathrm{ofEq}(\mathrm{toEq}(p))$ and UIP). This means the fundamental group $\pi_1(A, a) = \mathrm{Path}_A(a,a)/\mathrm{RwEq}$ has *exactly one element* for every type $A$—the quotient is a singleton whenever $a =_A a$ is inhabited (which it always is via refl). Yet Section 7 claims $\pi_1(S^1) \cong \mathbb{Z}$.

   The resolution is that for $S^1$ the authors switch to a *different* type: `CirclePathExpr`, a free inductive type with a formal `loop` generator that does *not* live in $\mathrm{Path}_{S^1}$. The winding number argument operates on this separate syntactic type, not on computational paths of $S^1$. **This crucial distinction is never made explicit.** The paper gives the impression that $\pi_1$ is computed using the same $\mathrm{Path}$ framework, but in fact the circle's non-trivial $\pi_1$ comes from a different formalism (path expressions with formal generators). The authors should:
   - Clearly distinguish $\mathrm{Path}$ (the record type) from $\mathrm{PathExpr}$ / $\mathrm{CirclePathExpr}$ (the free inductive type).
   - Explain why the quotient of $\mathrm{CirclePathExpr}$ by the rewrite rules is *not* trivial (i.e., the rewrite system on path expressions does not conflate $\mathsf{loop}$ with $\mathsf{refl}$).
   - Reconcile this with Remark 3.9, which says all paths with the same endpoints are RwEq-equivalent.

2. **The ω-groupoid theorem (Theorem 5.16) is less deep than suggested.** The contractibility at dimension ≥ 3 follows immediately from proof irrelevance of $\mathrm{RwEq}$. The "weak ω-groupoid" is essentially: non-trivial at dimensions 0 and 1 (elements and paths), trivially coherent at dimension 2 (since $\mathrm{RwEq}$ is Prop-valued), and contractible at dimensions ≥ 3 (again by proof irrelevance). The authors do acknowledge this (Remark 5.12), but the presentation in the abstract and introduction overstates the depth of the result. This should be compared more carefully with the work of Lumsdaine and van den Berg–Garner, where the ω-groupoid structure is *non-trivial* at every dimension.

3. **Termination proof is only sketched.** The paper defines a "recursive path ordering" (RPO) with a rule precedence and aggregate weight (Definitions 3.11–3.12), and claims that every rule application strictly decreases the measure (Theorem 3.14). However, the proof is "by case analysis on the 74 rules" with no cases shown. The RPO definition is also vague—it mentions a "symbol" and "aggregate weight" but does not define `pathLenSum` precisely. For a journal paper, at least a representative case analysis and a precise definition of the measure should be given, or a clear pointer to the formalization file/line should be provided.

4. **Strip lemma critical pair analysis is not shown.** The paper lists five representative critical pair families but does not exhibit any complete case. For a 74-rule system, the number of critical pairs is potentially very large. The paper should either:
   - Provide a count of distinct critical pairs.
   - Show at least one complete case in detail.
   - Give a machine-checkable certificate (e.g., a pointer to the specific Lean file and theorem name).

5. **Transport laws (Theorem 2.18) claimed as strict equalities are questionable.** Parts (ii)–(iv) involve $\mathrm{Eq.rec}$ applied to composed/inverted proofs. In Lean 4, `Eq.rec` only computes definitionally when the proof is `rfl`. For a composed proof $\pi_1 \cdot \pi_2$ (which is not definitionally `rfl` unless both components are), the equality $\mathrm{tr}(p \cdot q, x) = \mathrm{tr}(q, \mathrm{tr}(p, x))$ would typically require a proof by cases on $\pi_1$ and $\pi_2$, making it a *propositional* equality, not a definitional one. The claim that these hold "strictly" needs clarification: do you mean definitionally, or propositionally?

6. **Well-formedness of traces is retroactive.** Definition 1.3 explicitly says that consecutive steps in the trace need not compose (target of step $i$ need not equal source of step $i+1$). This is an unusual design choice—it means the trace is essentially decorative. The paper should discuss the tradeoff more explicitly: this choice simplifies the algebra (list concatenation works freely) but disconnects the trace from any notion of "computation."

### 2.3 Formalization vs. Paper Gap

Several theorems reference "Rules 3 and 4" or "Rule 7" by number (e.g., in the proof of Theorem 6.3), but these numbers refer to the *old* R-numbering from Section 3.1, not to theorem numbers. This is confusing—the reader must cross-reference the Appendix. Use `\cref` consistently or refer to rules by mnemonic name (lrr, rrr, etc.).

---

## 3. Novelty

### 3.1 What is new

- The *formalization in Lean 4* is new and substantial (60,860 lines, 885 theorems). Prior work by de Queiroz, de Oliveira, and Ramos was on paper; this is the first machine-checked version.
- The explicit 74-rule rewrite system with a machine-checked confluence proof is a significant contribution to the rewriting-theoretic foundations.
- The systematic treatment of contexts, bi-contexts, and dependent contexts as rewrite-compatible structures is original.
- The observation that contractibility begins at dimension 3 (preserving non-trivial $\pi_1$) is a clean conceptual contribution.

### 3.2 What is not new

- The basic computational paths idea and many of the algebraic laws appeared in [DQOR16, RDQO18, ramos19].
- The ω-groupoid result, while presented as the "main structure theorem," is conceptually straightforward once one observes that $\mathrm{RwEq}$ is Prop-valued.
- The homotopy-theoretic applications (Sections 6–10) largely reproduce standard results ($\pi_1(S^1) \cong \mathbb{Z}$, Seifert–van Kampen, etc.) within the framework. While this demonstrates expressiveness, the results themselves are not new.
- The "advanced homotopy theory" of Section 10 (spectral sequences, K-theory, operads, chromatic homotopy theory, THH, Goodwillie calculus, higher topos theory) is listed as "statement only"—merely recording standard definitions without proofs. This section is aspirational scaffolding, not a contribution.

### 3.3 Significance

The core contribution (Sections 2–5 plus the metatheory in Section 11) is a solid, original piece of work at the intersection of type theory, rewriting, and higher-dimensional algebra. The formalization adds significant value. However, the paper tries to cover too much ground: the later sections (7–10) dilute the core message with standard material that is either not fully formalized or not novel within this framework.

---

## 4. Clarity & Presentation

### 4.1 Overall structure

The paper is **too long** at 104 pages. The BSL publishes surveys and research papers, but even for a substantial survey, 104 pages is excessive. The core contribution (Sections 1–5 and 11) could be presented in ~40–50 pages. The applications (Sections 6–10) could either be:
- Cut to a shorter "applications" section demonstrating 2–3 key examples.
- Deferred to a companion paper.

### 4.2 Writing quality

The writing is generally clear and professional. Definitions are well-formatted, and the paper follows a logical progression. However:

- There is significant redundancy between Section 3 (rewrite system) and Section 11 (metatheory). Both discuss the strip lemma, confluence, and decidability. These should be merged.
- The notation switches between several conventions without always flagging the change. For example:
  - $p \cdot q$ vs. $\mathrm{trans}(p, q)$ vs. $p \comp q$
  - $p^{-1}$ vs. $\mathrm{symm}(p)$ vs. $\overline{p}$
  - $f_*(p)$ vs. $\mathrm{congrArg}(f, p)$
  - These are acknowledged in some places but not consistently.

### 4.3 Missing definitions/forward references

- The $\mathrm{LND}_{\mathrm{EQ}}$-TRS name appears in Remark 3.9 but is not defined until Definition 11.3.
- "Path expression" ($\mathrm{PathExpr}$) is used informally in Section 7 (CirclePathExpr) but not formally introduced until Section 11.2.
- The term "scaffolded" (used in formalization status remarks) is not standard and should be explained at first use.

---

## 5. Section-by-Section Comments

### Section 1 (Introduction)

- **p. 1 (abstract):** "the count of 74 follows from the distinct constructors in our formalization; the earlier convention of 76 in [RDQO18] counted two context-congruence rules that serve double duty"—this parenthetical is too detailed for an abstract. Move to a remark.
- **Definition 1.3:** The design choice that consecutive steps need not compose deserves more discussion. Why not require well-formedness? The answer is implicit (it would complicate the algebra) but should be explicit.
- **Theorem 1.7 (Non-UIP):** The proof is correct but trivial—it just observes that two lists of different lengths are unequal. This is fine but should be framed more precisely as saying that Path is not a proposition (not a (-1)-type), rather than that it violates UIP in the HoTT sense.
- **Section 1.4 (Related Work):** The comparison with cubical type theory is too brief. The paper cites [BeCH14] and [CCHM18] but does not explain in what precise sense computational paths offer "an alternative computational semantics."

### Section 2 (Basic Constructions)

- Well-written overall.
- **Theorem 2.4 (Strict Monoid Laws), proof of (i):** The claim that $\mathrm{refl} \cdot \pi = \pi$ for Eq.trans needs justification. In Lean 4, `Eq.trans rfl h = h` holds definitionally, but this should be noted.
- **Definition 2.10 (Binary Maps):** The notation $f(a, b_1)$ is ambiguous—is $f$ curried or uncurried? Use $f\,a_1\,b$ consistently.
- **Theorem 2.13 (Product β/η):** Part (i) claims $\mathrm{fst}(\mathrm{prodMk}(p, q)) = p$ strictly, but part (ii) says $\mathrm{snd}(\mathrm{prodMk}(p, q))$ "reduces to $q$ via a single rewrite step." Why the asymmetry? This is not explained.
- **Section 2.8 (Transport):** The claim that transport uses "only the semantic content of $p$, not its trace" is important and correct, but it means that transport is blind to the computational content—which somewhat undermines the program's thesis that computational content matters.
- **Definitions 2.21–2.24 (Contexts):** These are introduced rapidly. A concrete example of a context (e.g., $C[x] = f(x, b)$ for a fixed $b$) before the formal definition would help readability.

### Section 3 (Rewrite System)

- **Rule numbering:** Rules are numbered R1–R74 in groups, but Groups V–VII (rules 47–70) are described only in prose ("Rules 47–58 are the analogues of Group IV…"). For a paper centered on a rewrite system, *all 74 rules should be listed explicitly* in the body or appendix. The appendix does list them, but Groups V and VI are still described narratively even there.
- **Remark 3.5:** Correctly notes overlap between strict laws and rewrite rules. However, this raises a subtle point: if the strict equalities already hold, why include the corresponding rewrite rules? The answer (structural closure may produce them in nested contexts) should be expanded.
- **Remark 3.9 (RwEq triviality):** This is the most important remark in the paper and is somewhat buried. The entire subsequent development (fundamental groups, π₁ computations) depends on using *path expressions* (free inductive types with formal generators), not the record-based `Path` type. This should be elevated to a theorem or at least a prominent subsection, not a remark.
- **Section 3.7 (Extension Patterns):** This reads like a tutorial/manual rather than a mathematical contribution. Consider cutting or moving to an appendix.
- **Theorem 3.15 (Confluence):** The appeal to Newman's lemma is correct, but the paper should cite the specific form used. Newman's lemma in its standard form requires the relation to be *finitely branching* or at least well-founded (which is given by termination). The paper's version is correct but the statement should be more precise.

### Section 4 (Groupoid)

- Clean and well-organized.
- **Definition 4.1 vs. 4.4:** "Weak category" and "weak groupoid" are non-standard terminology (a "weak category" usually means a bicategory). Consider renaming to "pre-category" or "path category" to avoid confusion.

### Section 5 (Higher-Dimensional Structure)

- **Theorem 5.5 (Pentagon):** The proof says "this equality of two-cells holds by proof irrelevance of $\mathrm{RwEq}$." This is correct but anticlimactic—the pentagon law holds trivially, not because of any deep structure. The paper should be more explicit about this.
- **Definition 5.13 (Weak ω-Groupoid):** The definition is attributed to "Batanin–Leinster" but is actually a simplified version. The Batanin–Leinster definition involves globular operads and contractibility conditions on the operad itself. The paper's definition (cells + groupoid ops + contractibility from dim 3) is much simpler. The authors should either:
  - Explicitly state that they use a *simplified* notion, citing the precise axioms.
  - Show that their structure satisfies the Batanin–Leinster definition. As stated, the claim is imprecise.
- **Remark 5.12:** Correctly distinguishes the approach from HoTT. Good.
- **Section 5.3 (Double Groupoid):** This subsection adds little content—everything follows immediately from proof irrelevance. Consider cutting.

### Section 6 (Fundamental Groups)

- **Theorem 6.3 proof:** References "Rules 3 and 4" and "Rules 5 and 6" without labels. Use the mnemonic names (lrr, rrr, tr, tsr) or \cref references.
- **Theorem 6.8 (Product Formula):** Correct proof. The key point is that the β-rules give strict equalities and the η-rule gives RwEq, which suffices for the quotient.
- **Theorem 6.10 (Eckmann–Hilton):** The proof is presented at a high level and uses $\equiv_3$ ("connecting Derivation₃ cell") notation that is not formally introduced. The three steps are plausible but not fully rigorous as written.
- **Section 6.4 (Fundamental Groupoid):** The definition is standard but well-adapted to the framework.

### Section 7 (Spaces)

- **Definition 7.1 (Circle):** This is where the critical equivocation occurs. The "computational-path circle" $S^1$ is defined as a *single-point type* with a *path expression* generator. But $\mathrm{Path}_{S^1}(\mathrm{base}, \mathrm{base})$ in the record-based sense has a trivial $\pi_1$ (by Remark 3.9). The non-trivial $\pi_1$ comes from $\mathrm{CirclePathExpr}$. **This must be clarified.**
- **Theorem 7.4 ($\pi_1(S^1) \cong \mathbb{Z}$):** The proof via winding numbers is correct *for the path expression type*. But the theorem as stated does not specify which notion of "path" is being used. This is the paper's biggest expository gap.
- **Theorem 7.8 ($\pi_1(S^1 \vee S^1) \cong \mathbb{Z} * \mathbb{Z}$):** Marked as "PS" (partially scaffolded). The proof is only sketched.
- **Section 7.4 (Seifert–van Kampen):** Also partially scaffolded. The proof sketch is reasonable but not detailed enough for a journal paper.
- **Section 7.5 (Suspensions):** The proof sketch for $\pi_1(\Sigma X) = 0$ is incomplete—it claims loops "collapse by cancellation" without showing the inductive argument.

### Section 8 (Fibrations)

- **Theorem 8.3 (Path Lifting):** The construction $\widetilde{p} = \mathrm{ofEq}(h)$ is correct but tautological: the lifted path is a single-step canonical witness. This is not "path lifting" in the classical sense (where the lift carries non-trivial trace information); it is just dependent elimination.
- **Theorem 8.6 (Hopf Fibration):** The "proof" is a single paragraph saying the data is "packaged as a record." This is not a proof—it is a claim that certain structures exist. For a journal paper, at least the construction of $\eta : S^3 \to S^2$ should be outlined.
- **Theorem 8.15 (Long Exact Sequence):** The proof outline is reasonable but the connecting homomorphism construction is underspecified.
- **Theorem 8.18 (Mayer–Vietoris):** Marked "SO" (statement only). Should be clearly flagged as a conjecture/future work, not a theorem.

### Section 9 (Hurewicz)

- **Definition 9.3 ($H_1$):** Defining $H_1(A) = \pi_1(A, a)^{\mathrm{ab}}$ is circular as a definition of homology—it *is* the Hurewicz theorem (in dimension 1). The authors should clarify that this is a *definition* of $H_1$ in their framework, not an independent construction.
- **Theorem 9.5 (Hurewicz, dimension 1):** The "proof" is essentially "$H_1 = \pi_1^{\mathrm{ab}}$ by definition." This is tautological. The Hurewicz theorem is interesting when $H_1$ is defined independently (e.g., via singular homology).
- **Theorem 9.10 (Nielsen–Schreier):** Statement only. The proof sketch via covering spaces is standard but the covering-space theory is itself only partially formalized.
- **Section 9.6 (Higher Hurewicz):** Statement only.

### Section 10 (Advanced)

- This entire section consists of definitions and theorem *statements* imported from standard algebraic topology, with no proofs and only "SO" (statement only) formalization status. Topics include:
  - Eilenberg–MacLane spaces, Moore spaces
  - Postnikov towers, obstruction theory
  - Whitehead's theorem
  - Freudenthal suspension, stable homotopy
  - Spectral sequences, Adams spectral sequence
  - K-theory, characteristic classes
  - Operads, rational homotopy theory
  - Chromatic homotopy theory, THH
  - Goodwillie calculus, higher topos theory

  **This section should be drastically cut or moved to a separate document.** Listing standard definitions without proofs does not constitute a contribution. The statement that "the computational-paths framework accommodates" these structures is unsupported when the formalization status is "SO." At most, a short paragraph noting potential future directions would suffice.

### Section 11 (Metatheory)

- Largely redundant with Section 3. The PathExpr formalization is interesting but the strip lemma discussion repeats earlier material.
- **Theorem 11.8 (Decidability of RwEq):** The "decision procedure" is trivially "always return yes" (as the proof states). This should not be presented as a theorem—it follows immediately from Remark 3.9.
- **Theorem 11.11 (J-Elimination):** Correct. The construction via transport is standard.
- **Remark 11.14 (Univalence):** Good discussion distinguishing the approach from HoTT.

### Section 12 (Conclusion)

- The summary is accurate.
- **Formalization statistics:** 302 files, 60,860 lines, 885 theorems—impressive scale.
- **Table 13.1 (Formalization Status):** Very useful. The honest reporting of FF/PS/SO status is appreciated.

### Appendix A (Complete Rule List)

- **Rule R31 (context_congr) appears twice:** once in Group IV (R31) and once in Group VIII (R74). The paper notes this in a concluding remark but the dual listing is confusing. Assign it to one group and cross-reference from the other.
- **Group V (Dependent Context Rules):** Rules 47–58 are listed individually—good. But the mnemonic names are not given (unlike Groups I and IV). Add them for consistency.
- **Group VI (Bi-Context Rules):** All 8 rules (R59–R66) are structural congruence rules—they just propagate rewrites through $\mathrm{mapLeft}$/$\mathrm{mapRight}$/$\mathrm{mapTwo}$ for two flavors of bi-context. Consider noting that these are "lifted" versions of the Group VIII structural closure rules.

---

## 6. Mathematical Concerns

### 6.1 The Rewrite System

- **Counting:** The claimed count of 74 is consistent with the appendix listing (R1–R74, with R31/R74 being the same constructor). However, R74 is labeled "context_congr" and is identical to R31. If these correspond to a single inductive constructor, the count should be 73 distinct rules + a note about the overlap, or 74 with the overlap explicitly resolved.
- **Confluence proof strategy:** Newman's lemma requires termination + local confluence. The termination argument (RPO) is plausible but not fully detailed. The local confluence argument (strip lemma + critical pair analysis) is the right approach but the critical pairs are not enumerated. For a system of this size, a count or table of critical pair families would strengthen the presentation.
- **Orientation of rules:** Several rules (e.g., R38: $r \cdot C[p] \to \mathrm{substL}(C, r, p)$) fold a composition into a substitution form. This increases the complexity of the term (introducing the $\mathrm{substL}$ constructor). How does the RPO handle this? The measure must assign $\mathrm{substL}$ a *lower* rank than $\mathrm{trans}$, which seems counterintuitive. The paper should discuss this.

### 6.2 The ω-Groupoid Construction

- The definition of "weak ω-groupoid" (Definition 5.15) is significantly simpler than the Batanin–Leinster definition (which involves globular operads satisfying contractibility conditions at each dimension). The paper's definition is closer to what Lumsdaine calls a "weak ω-category with all cells invertible" or a Grothendieck-style ω-groupoid. The attribution should be more precise.
- The key property—contractibility at dimension ≥ 3—follows from the fact that $\mathrm{RwEq}$ is Prop-valued and all derivation types project to $\mathrm{RwEq}$. This is a feature of the design (making $\mathrm{Step}$ a Prop), not a deep mathematical theorem. The paper should be explicit about this.

### 6.3 π₁ Computations

- The fundamental tension: on the record-based `Path` type, $\pi_1$ is always trivial (Remark 3.9). On `PathExpr` types with formal generators, $\pi_1$ can be non-trivial. The paper conflates these two settings in its narrative.
- For the circle, the winding number argument is correct *on the path expression type*. The key step—showing that `loop` is not rewrite-equivalent to `refl`—depends on `CirclePathExpr` being a *free* inductive type where the rewrite rules do not identify these generators. This is never explicitly stated or proved.

---

## 7. Formalization Claims

### 7.1 Repository

- **URL mismatch:** The paper text (Section 12.2) gives the URL `https://github.com/Arthur742Ramos/ComputationalPathsLean`, but the bibliography entry `cplean` gives `https://github.com/Asjidkalam/ComputationalPathsLean`. These should be reconciled.
- **Statistics:** 302 files, 60,860 lines, 885 theorems, 1,710 definitions—plausible for a development of this scope.

### 7.2 Formalization Status Table

- The honest reporting of FF/PS/SO status (Table 13.1) is commendable.
- **However:** The paper presents PS and SO results as *theorems* with proof sketches, not as conjectures. For a BSL submission, every numbered theorem should ideally be either:
  - Fully proved in the paper, or
  - Clearly marked as a conjecture/claim with a proof deferred.
  The current approach—stating theorems, giving sketchy proofs, then revealing in a table at the end that some proofs are "admitted"—is not ideal for a journal paper.

### 7.3 Specific Claims

- "The entire development is mechanically verified in the Lean 4 proof assistant" (Section 12.2)—this overstates the case. Many results (Seifert–van Kampen, Hopf fibration, long exact sequence, Mayer–Vietoris, Hurewicz, Nielsen–Schreier, Whitehead, Freudenthal, spectral sequences, etc.) are PS or SO, meaning proofs are admitted or absent in the formalization. The sentence should say "The core algebraic and rewriting-theoretic development is mechanically verified…"

---

## 8. BSL Format Compliance

### 8.1 General

- The paper uses `BSLstyle.cls` and appears to follow the BSL house style.
- Abstract and keywords are present.
- Author affiliations and email addresses are provided via `\AuthorEmail` and `\Affiliation`.
- The `\Funding`, `\Conflict`, `\Ethics`, and `\UseOfGAI` declarations are present.
- `\Acknowledgements` is present (though says "Not applicable").

### 8.2 Issues

- **Length:** 104 pages is very long for the BSL. Most BSL research papers are 20–40 pages. Even survey articles rarely exceed 60 pages. The paper should be significantly shortened.
- **Appendix as a "Section":** The appendix is labeled `\section{Complete List of Rewrite Rules}` rather than `\appendix` followed by a section. This may not match BSL style.
- **Page layout warnings:** The build log shows 40+ "Overfull \hbox" warnings, some significant (up to 122pt overfull). These should be fixed before submission.
- **Font warnings:** Numerous "Font shape `T1/lmr/m/scit' undefined" warnings suggest that the BSL style expects a font shape not provided by lmodern. This should be investigated.
- **Bibliography format:** The `.bib` file uses standard BibTeX entries. The BSL uses its own `BSLbibstyle.bst`, which appears to be used. Some entries need attention:
  - `Brunerie16` uses `journal = {arXiv preprint arXiv:1606.05916}`—this is not a journal. Use `@unpublished` or `@misc` with `note = {arXiv:1606.05916}`.
  - `LicataShulman13` has both `journal` (set to empty string via `article`) and `booktitle` in the original bib. The entry type is `@article` but should be `@inproceedings`.
  - `deBruijn68` has `note = {Les Presses de l'Université de Montréal}` but no journal/booktitle—use `@misc` or `@techreport`.
  - `Squier94` is labeled "1994" in the cite key but dated 1987 in the entry. Fix the key or add the 1994 Squier–Otto–Kobayashi reference.
  - `cplean` uses `@misc` which is fine, but the URL should be verified and match the paper text.
  - `hofmann98` has `journal = {Venice Festschrift}`—use `@incollection` with the proper booktitle.

---

## 9. Specific Suggestions

### High-Priority

1. **Resolve the Path vs. PathExpr equivocation.** Add a subsection (e.g., 1.5 or 3.8) explicitly discussing the two notions of "path" and how π₁ computations use the latter.

2. **Cut or drastically shorten Sections 8–10.** These sections contain standard material that is either not fully formalized or not novel. A 2-page "Applications and Further Directions" section would suffice.

3. **Merge Sections 3 and 11.** The metatheory section largely repeats the rewrite system section. Present the material once, with the PathExpr formalization integrated into the confluence discussion.

4. **Fix the GitHub URL inconsistency** between the paper text and the bibliography.

5. **Clarify the "strict" claims in Theorem 2.18 (Transport Laws).** Do these hold definitionally in Lean 4, or only propositionally?

6. **Strengthen the ω-groupoid claim.** Either (a) define precisely which notion of weak ω-groupoid is used and how it relates to Batanin–Leinster, or (b) state that the paper uses a simplified notion and explain the relationship.

7. **Mark PS/SO results clearly in the text**, not just in a table at the end. Use a visual marker (e.g., a dagger † or a colored box) next to theorem statements that are not fully formalized.

### Medium-Priority

8. Fix the "Theorem 8.18 (Mayer–Vietoris)" and similar SO results: either remove them or clearly label as conjectures.

9. Define "scaffolded" at first use.

10. Add mnemonic names to Groups V and VI in the Appendix for consistency with Groups I and IV.

11. Resolve the R31/R74 duplication: assign context_congr to one group and cross-reference from the other.

12. Add a brief discussion of the RPO measure for rules that *increase* term complexity (e.g., the substL folding rules).

13. Provide a count of critical pairs for the confluence proof, and show at least one complete critical pair resolution in detail.

### Low-Priority

14. Move the parenthetical about the 74/76 rule count from the abstract to a remark in Section 3.

15. Standardize notation: pick either $p \cdot q$ or $p \comp q$ and use it throughout.

16. Fix the numerous Overfull \hbox warnings in the LaTeX build.

17. Check that all bibliography entries have consistent types (fix `Brunerie16`, `LicataShulman13`, `deBruijn68`, `Squier94`, `hofmann98` as noted above).

18. In the proof of the Eckmann–Hilton theorem (Theorem 6.10), formally introduce the $\equiv_3$ notation.

19. The BSL style expects `\appendix` before appendix sections. Check and fix.

20. Consider adding a "Notation Index" or "Glossary" given the large number of symbols introduced.

---

## 10. Summary Assessment

**Strengths:**
- Original framework bridging type theory, rewriting, and higher-dimensional algebra
- Substantial Lean 4 formalization (for the core results)
- Clean algebraic development of path operations
- Honest reporting of formalization status
- Well-motivated design choices (Path as record, Step as Prop)

**Weaknesses:**
- Critical equivocation between Path (record) and PathExpr (free inductive type) undermines the π₁ computations narrative
- Paper is far too long (104 pages) for a journal article; Sections 8–10 should be cut
- The ω-groupoid claim overstates the depth of the result
- Many theorems are stated without full proofs or formalization (PS/SO status)
- Significant overlap between Sections 3 and 11
- Multiple bibliography and cross-reference issues

**Recommendation:** Major revision. The core contribution (Sections 1–5, 11, formalization) is publishable after revision. The paper needs to be significantly shortened, the Path/PathExpr distinction clarified, the ω-groupoid claim tempered, and the presentation polished. The applications (Sections 6–10) should be trimmed to a focused selection of fully formalized results.
