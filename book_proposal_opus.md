# Book Proposal

## *Computational Paths and the Algebraic Topology of Rewriting*
### *From Labelled Deduction to Higher Groupoids*

**Authors:** [To be confirmed — Ruy de Queiroz, Arthur …]

---

## 1. Overview

This book develops a new mathematical theory that begins with a simple observation from proof theory and arrives at structures of deep significance for homotopy theory, higher category theory, and the foundations of mathematics.

The observation is this: in a system of labelled natural deduction (LND), proof-terms are composed by the same operations — transitivity, symmetry, congruence — that define a *groupoid*. When we take the rewrite rules governing these proof-terms seriously as mathematical objects, and study paths-between-paths (sequences of rewrites connecting two proof-terms), we discover a hierarchy of algebraic structures that, remarkably, reproduces the weak ω-groupoid structure that homotopy type theorists axiomatize and that homotopy theorists study in topological spaces.

The central thesis is that **the algebra of rewriting is intrinsically homotopical**. This is not a metaphor. We prove it as a theorem.

Starting from 77 rewrite rules on path expressions — including β-reduction, η-expansion, and congruence laws — we construct:

1. A **groupoid** of computational paths, where composition is transitivity, inverses are symmetry, and the groupoid laws (associativity, left/right unit, inverse laws) are *derived* from the rewrite system, not axiomatized.

2. A **hierarchy of higher cells**: 2-cells (rewrite sequences between paths), 3-cells (homotopies between rewrite sequences), and so on, forming a weak ω-groupoid in the sense of Batanin, Lumsdaine, and van den Berg–Garner.

3. A **derivation of path induction**: the J-eliminator of Martin-Löf type theory is proved as a theorem from the contractibility of the based path space — it is not assumed as a primitive.

4. A proof-relevant identity type where **UIP fails**: distinct computational paths between the same endpoints are genuinely different mathematical objects, distinguished by their rewrite traces.

5. The **Eckmann–Hilton argument**, carried out with full coherence data at the level of 3-cells, establishing commutativity of the second loop space.

6. **Confluence and normalization** for the rewrite system on paths, proved via term rewriting techniques including Newman's Lemma and critical pair analysis.

The book is written as *pure mathematics*. Every theorem is stated and proved in the language of algebra, rewriting theory, and homotopy theory. The formal verification (carried out in Lean 4 with 13,000+ theorems across 950+ files, all without axiom-gaps) serves as a methodological guarantee and is described in an appendix, but the reader needs no knowledge of proof assistants.

---

## 2. The Narrative Arc

The book tells a story in three acts.

**Act I: The Algebra of Proof-Terms.** We begin with Ruy de Queiroz's insight (developed from the late 1980s onward) that the proof-terms labelling deductions in natural deduction carry algebraic structure. When two proof-terms denote the "same" deduction — related by normalization — the *reason* for their equality (the rewrite sequence connecting them) is itself a meaningful mathematical object. This elevates "reasons for equality of proofs" to first-class citizens: computational paths. We develop the algebra of paths (transitivity, symmetry, congruence, transport) and the rewrite system governing their equivalence, proving confluence and normalization by term rewriting methods.

**Act II: The Emergence of Higher Structure.** Here comes the surprise. The equivalence classes of rewrite sequences on paths are themselves connected by higher rewrite sequences. Iterating, we obtain an infinite tower of cells — the skeletal layers of a weak ω-groupoid. We prove this is not an accident: we derive, level by level, the Batanin-style contractibility conditions starting at dimension 3. We show that contractibility at levels ≥ 3 is a *consequence* of proof-irrelevance of the rewrite-equivalence relation, while level 2 remains non-trivial — preserving the possibility of non-trivial fundamental groups. The Eckmann–Hilton argument is carried out with explicit coherence witnesses.

**Act III: Connections and Applications.** We derive the J-eliminator, establish the failure of UIP, and connect the theory to homotopy type theory (HoTT), showing that computational paths provide an independent, *algebraic* route to structures that HoTT obtains axiomatically. We develop applications to fundamental groupoids of combinatorial spaces (circles, tori, Klein bottles, projective planes), to the classification of covering spaces, and to the Seifert–van Kampen theorem. We sketch connections to model categories, ∞-categories, and motivic structures.

The story the book tells is ultimately about **the unreasonable effectiveness of rewriting**: a proof-theoretic mechanism, studied for its own sake, turns out to encode the homotopy theory of spaces.

---

## 3. Chapter-by-Chapter Outline

### Part I: Foundations — The Algebra of Computational Paths

#### Chapter 1: *Introduction and Motivation* (25 pages)

We set the stage by reviewing three traditions that converge in this book: (i) the Curry–Howard correspondence and its extension to rewrite rules, with de Queiroz's thesis that "reasons for equality of proofs" deserve first-class status; (ii) the observation by Hofmann–Streicher, Lumsdaine, and van den Berg–Garner that identity types carry groupoid/ω-groupoid structure; (iii) the connection between rewriting and homotopy (Squier's theorem, higher-dimensional rewriting). We state the main results informally and outline the architecture of the book.

**Key ideas:** Labelled Natural Deduction (LND); proof-terms as paths; the question "what is a reason for equality of proofs?"; historical overview from Brouwer through Martin-Löf to HoTT.

#### Chapter 2: *Labelled Natural Deduction and Proof-Terms* (30 pages)

We present LND following de Queiroz–de Oliveira–Gabbay (2011): natural deduction rules for propositional and predicate logic, each decorated with a proof-term (label). We define the term language, β-reduction and η-expansion for each connective, and the notion of a *rewrite step* between terms. The equality judgment `a =_s b : D` is introduced, where `s` is a "rewrite reason" — a composition of elementary rewrites.

**Key results:** Definition of the term calculus; well-typedness of rewrite steps; subject reduction; Church–Rosser property for the base reduction system.

#### Chapter 3: *Computational Paths: Definition and Elementary Properties* (35 pages)

We give the formal definition of a *computational path* from `a` to `b` as a structured object carrying a sequence of rewrite steps. We define the fundamental operations: `refl` (empty path), `trans` (concatenation), `symm` (reversal), and `congrArg` (functorial action). We prove the basic identities: that these operations satisfy the *laws of a groupoid up to a further equivalence relation*.

**Key results:**
- Definition of `Step`, `Path`, and the operations `refl`, `trans`, `symm`, `congrArg`.
- Paths distinguished by their step-lists: `refl a ≠ stepLoop a`, establishing proof-relevance.
- Failure of UIP for computational paths (Theorem 3.4.1): for any inhabited type, there exist distinct paths with the same endpoints.
- Concatenation and reversal interact correctly with step structure.

#### Chapter 4: *The Rewrite System on Paths* (40 pages)

We define the rewrite system `Rw` (one-step rewrite) and its symmetric–reflexive–transitive closure `RwEq` on computational paths. The rewrite rules codify the groupoid laws: associativity, unit laws, inverse laws, plus functoriality and naturality of `congrArg`. We enumerate all 77 rewrite rules, organized by type (structural, functorial, congruence, transport).

**Key results:**
- Complete enumeration and classification of rewrite rules (Table 4.1).
- `RwEq` is a congruence with respect to `trans`, `symm`, and `congrArg`.
- Normal forms: definition and characterization.
- The quotient `Path/RwEq` as the "path algebra."

#### Chapter 5: *Confluence and Normalization* (40 pages)

We prove that the rewrite system on paths is confluent and terminating, hence every path has a unique normal form. The proof proceeds by Newman's Lemma (local confluence implies confluence for terminating systems), with local confluence verified by critical pair analysis. Termination is established via a well-founded measure on path complexity.

**Key results:**
- Termination theorem (Theorem 5.2.1): the rewrite measure strictly decreases at each step.
- Critical pair lemma (Lemma 5.3.4): all critical pairs are joinable.
- Newman's Lemma for computational paths (Theorem 5.3.7).
- Main confluence theorem (Theorem 5.4.1): `Rw` is confluent.
- Normalization theorem (Theorem 5.5.1): every path reduces to a unique normal form.
- Decision procedure: path equality is decidable via normalization to canonical form.

### Part II: Higher Structure — The ω-Groupoid

#### Chapter 6: *The Groupoid of Computational Paths* (35 pages)

We prove the main algebraic theorem of Part I: under `RwEq`, computational paths form a groupoid. Associativity, unit laws, and inverse laws are all *derived* from the rewrite system — they are theorems, not axioms. We make the groupoid structure explicit: objects are terms, morphisms are `RwEq`-classes of paths, composition is `trans`, and inverses are `symm`.

**Key results:**
- Groupoid laws (Theorem 6.1.1): associativity, left/right unit, left/right inverse, all as `RwEq` equalities.
- Functoriality of `congrArg` (Theorem 6.2.1): `congrArg f` is a groupoid homomorphism.
- The groupoid is *free* on the generating steps, modulo the rewrite rules.
- Comparison with the fundamental groupoid of a space.

#### Chapter 7: *Two-Cells: Derivations Between Paths* (35 pages)

We introduce `Derivation₂` — a 2-cell witnessing that two paths are connected by a sequence of rewrites. These are the first "higher paths." We define vertical composition (sequential rewriting) and show that 2-cells form a category over each pair of endpoints.

**Key results:**
- Definition of `Derivation₂ p q` as a witness of `RwEq p q`.
- Vertical composition of 2-cells (Theorem 7.2.1).
- Whiskering operations: `whiskerLeft` and `whiskerRight` (Theorem 7.3.1).
- Horizontal composition via whiskering (Theorem 7.3.4).
- The interchange law (Theorem 7.4.1): horizontal and vertical composition satisfy the interchange axiom of a 2-category.

#### Chapter 8: *Three-Cells and Contractibility* (30 pages)

We define `Derivation₃` (3-cells between 2-cells) and prove the crucial **contractibility** result: at dimension 3 and above, any two parallel cells are connected. This is the Batanin-style coherence condition for weak ω-groupoids. The proof exploits the fact that `RwEq`-equivalence is a proposition (proof-irrelevant at the meta-level), so any two derivations witnessing the same `RwEq` fact are connected by a 3-cell.

**Key results:**
- `Derivation₃`, `Derivation₄`, and the general pattern (Definition 8.1).
- Contractibility at level 3 (Theorem 8.2.1): for any `d₁ d₂ : Derivation₂ p q`, there exists `Derivation₃ d₁ d₂`.
- Contractibility at level 4+ (Theorem 8.2.3): immediate from proof-irrelevance propagation.
- **Non-contractibility at level 2** (Theorem 8.3.1): there exist parallel paths with no derivation between them, preserving non-trivial fundamental groups.
- The truncation pattern: the ω-groupoid is 3-coskeletal.

#### Chapter 9: *The Weak ω-Groupoid Theorem* (35 pages)

We assemble the results of Chapters 6–8 into the main structural theorem: computational paths on a type `A` form a weak ω-groupoid in the sense of Batanin–Leinster. We verify the globular identities, the composition operations at each level, and the coherence conditions. We compare with the constructions of Lumsdaine and van den Berg–Garner, who showed that identity types in Martin-Löf type theory carry weak ω-groupoid structure.

**Key results:**
- The globular tower (Theorem 9.1.1): source/target maps satisfy globular identities at all levels.
- Composition functors at each dimension (Theorem 9.2.1).
- Coherence: associators, unitors, and interchangers exist and satisfy the required higher coherences (Theorem 9.3.1).
- **Main Theorem** (Theorem 9.4.1): For any type `A`, the tower `(A, Path, Derivation₂, Derivation₃, …)` is a weak ω-groupoid.
- Comparison theorem (Theorem 9.5.1): the ω-groupoid structure is compatible with Lumsdaine's construction applied to the identity type.

#### Chapter 10: *The Eckmann–Hilton Argument* (25 pages)

We carry out the Eckmann–Hilton argument for computational paths. The double loop space Ω²(A, a) — consisting of 2-cells from `refl(refl a)` to itself — admits both vertical and horizontal composition. Using the interchange law and the unit laws, we prove that these compositions coincide and are commutative.

**Key results:**
- The double loop space Ω²(A, a) (Definition 10.1).
- Horizontal composition equals vertical composition on Ω² (Theorem 10.2.1).
- The Eckmann–Hilton theorem (Theorem 10.3.1): Ω²(A, a) is an abelian group.
- Naturality squares for unit laws (Theorem 10.4.1).
- All coherence witnesses are explicit 3-cells from the rewrite system — no axioms invoked.

### Part III: Connections — Type Theory, Homotopy, and Beyond

#### Chapter 11: *Path Induction and the J-Eliminator* (30 pages)

We derive the J-eliminator of Martin-Löf type theory as a *theorem* within the computational paths framework. The argument follows the HoTT-style route: we define the based path space, prove its contractibility, and extract J and its computation rule.

**Key results:**
- The based path space `BasedPathSpace(a) = Σ(y : A), Path(a, y)` (Definition 11.1).
- Contractibility of the based path space (Theorem 11.2.1): every element equals the center `(a, refl a)`.
- **Derivation of J** (Theorem 11.3.1): the J-eliminator follows from contractibility plus transport.
- J computation rule (Theorem 11.3.3): `J(C, d, a, a, refl a) = d(a)`.
- Derived operations: transport, dependent `ap`, function extensionality pattern.
- Equivalence of based and free path induction (Theorem 11.4.1).
- Uniqueness: any J-like eliminator satisfying the computation rule equals the derived one (Theorem 11.5.1).

#### Chapter 12: *Failure of UIP and Proof-Relevance* (25 pages)

We establish rigorously that computational paths are *proof-relevant*: the Uniqueness of Identity Proofs principle fails. We analyze the precise sense in which this failure occurs and compare with Streicher's K axiom, Hedberg's theorem, and the Hofmann–Streicher groupoid model.

**Key results:**
- Non-UIP theorem (Theorem 12.1.1): for any inhabited type `A`, there exist `p, q : Path(a, a)` with `p ≠ q`.
- Failure of Streicher's K (Theorem 12.2.1): not every loop is `refl`.
- Step-counting as a path invariant (Theorem 12.3.1): `|steps(p)|` distinguishes paths.
- Comparison with Hofmann–Streicher: the groupoid model vindicates non-UIP; our paths give a *concrete* rewriting-based model.
- The proof-irrelevance/proof-relevance dialectic: `RwEq` is proof-irrelevant (a proposition), but `Path` itself is proof-relevant.

#### Chapter 13: *Fundamental Groupoids of Combinatorial Spaces* (35 pages)

We apply the computational paths machinery to compute fundamental groupoids of spaces defined combinatorially (in the style of higher inductive types). For each space, we define generators (points, paths, 2-paths), apply the Seifert–van Kampen theorem where applicable, and compute the fundamental group.

**Key results:**
- The circle S¹: `π₁(S¹) ≅ ℤ` via winding number (Theorem 13.2.1).
- The torus T²: `π₁(T²) ≅ ℤ × ℤ` (Theorem 13.3.1).
- The Klein bottle: `π₁(K) ≅ ℤ ⋊ ℤ` (Theorem 13.4.1).
- Real projective plane: `π₁(RP²) ≅ ℤ/2ℤ` (Theorem 13.5.1).
- Bouquets: `π₁(⋁ⁿ S¹) ≅ Fₙ`, the free group (Theorem 13.6.1).
- The figure-eight and Seifert–van Kampen (Theorem 13.7.1).
- Lens spaces (Theorem 13.8.1).
- Higher homotopy: `π₂(S²)` via suspension and the Hopf fibration path-algebraically (sketch).

#### Chapter 14: *Connections to Homotopy Type Theory* (30 pages)

We provide a detailed comparison between computational paths and the HoTT/Univalent Foundations programme. Both frameworks arrive at ω-groupoid structure on identity/path types, but by very different routes: HoTT axiomatically (via the univalence axiom and higher inductive types), computational paths algebraically (via term rewriting). We discuss what each approach illuminates that the other does not.

**Key results:**
- Translation dictionary: HoTT identity type ↔ computational path; `ap` ↔ `congrArg`; `transport` ↔ path-transport; truncation levels ↔ rewrite-skeletal dimension.
- What computational paths add: explicit rewrite witnesses, decidable path equality, computational content of coherences.
- What HoTT adds: univalence, synthetic homotopy theory, higher inductive types as a general mechanism.
- Cubical type theory and computational paths: both provide "computational" identity, but via different mechanisms (Kan operations vs. rewriting).
- Open problem: can computational paths model univalence?

#### Chapter 15: *Connections to Category Theory and Higher Algebra* (25 pages)

We develop the categorical perspective on computational paths. The path groupoid is a special case of the fundamental groupoid of a computad (higher-dimensional rewriting system). We connect to the theory of ∞-categories, model categories, and enriched category theory.

**Key results:**
- The path groupoid as a free groupoid on a computad.
- Enrichment: `Path(a,b)` as a groupoid-enriched hom, recovering a 2-groupoid.
- Relation to Squier's theorem: the rewrite system's homotopy type is a computable invariant.
- The Yoneda lemma for path categories (Theorem 15.3.1).
- Double categories and double groupoids from 2-dimensional rewriting.
- Sketch: path ∞-groupoids and ∞-cosmoi.

#### Chapter 16: *Perspectives and Open Problems* (15 pages)

We survey open problems and future directions: extending computational paths to dependent types and universes, the question of univalence, connections to directed type theory, applications to program verification (rewriting as certified computation), and the broader programme of understanding the homotopy theory latent in formal systems.

**Key open problems:**
1. Can computational paths model the univalence axiom?
2. Is there a model category whose fibrant objects are precisely the computational-path ω-groupoids?
3. Can the normalization/confluence results be extended to a dependent type theory with Σ and Π?
4. Directed computational paths: rewriting without symmetry.
5. What is the homotopy type of the space of rewrite strategies?

### Appendices

#### Appendix A: *Term Rewriting Systems* (15 pages)

Background on abstract rewriting systems, termination orderings, critical pair analysis, the Knuth–Bendix procedure, and Newman's Lemma. Self-contained for readers not specialist in rewriting.

#### Appendix B: *Groupoids and Higher Groupoids* (15 pages)

Background on groupoids, 2-groupoids, Batanin's definition of weak ω-groupoid, and the Grothendieck homotopy hypothesis. Self-contained for readers not specialist in higher category theory.

#### Appendix C: *The Lean 4 Formalization* (20 pages)

Description of the formal verification: architecture of the 950+ file library, methodology of translation from formal proof to pen-and-paper mathematics, statistics (13,000+ theorems, 0 axiom-gaps), and how to access and navigate the code. Includes representative code excerpts illustrating the correspondence between formal and informal proofs.

#### Appendix D: *Complete List of Rewrite Rules* (10 pages)

All 77 rewrite rules, with names, types, and the critical pairs they participate in.

---

**Estimated length:** 520–580 pages.

---

## 4. What Makes This Book Unique — The Contribution

This book makes several contributions that, individually and collectively, are novel:

### 4.1 A New Foundation for Homotopical Algebra from Rewriting

The central novelty is **deriving** ω-groupoid structure from a term rewriting system, rather than axiomatizing it. In HoTT, the groupoid structure of identity types is a *consequence* of the rules for the identity type (as shown by Lumsdaine and van den Berg–Garner), but those rules are themselves axioms. Here, the groupoid laws are theorems of a rewriting system that has independent motivation from proof theory. This provides:

- **A concrete model** of proof-relevant identity that is *computational*: path equality is decidable.
- **An independent path** to ω-groupoid structure that does not require type-theoretic foundations.
- **Evidence for the Grothendieck homotopy hypothesis** from a new direction: rewriting systems naturally produce ω-groupoids.

### 4.2 The Bridge Between Rewriting and Homotopy

The connection between rewriting and homotopy has been observed before (Squier's theorem, Guiraud–Malbos on higher-dimensional rewriting), but this book develops it *systematically* from the ground up, with complete proofs, in a framework that simultaneously touches proof theory, type theory, and algebraic topology. No existing book covers this territory.

### 4.3 Derivation of J

The derivation of the J-eliminator from contractibility of the based path space, carried out within a framework that *starts* from proof-theoretic rewriting rather than from type-theoretic axioms, is (to our knowledge) new. It demonstrates that path induction is a *theorem* about the structure of rewriting, not a foundational assumption.

### 4.4 Explicit Coherence

The Eckmann–Hilton argument and ω-groupoid coherences are carried out with *fully explicit witnesses* — every coherence cell is a named rewrite derivation, not an appeal to "there exists." This level of explicitness, backed by machine-checked proofs, goes beyond what is available in existing treatments.

### 4.5 The Formalization as Methodology

While this is a mathematics book, not a formalization report, the existence of 13,000+ machine-checked theorems with zero axiom-gaps provides an unprecedented level of confidence. It also demonstrates a methodology: using a proof assistant to *explore* mathematical structure (the ω-groupoid structure was discovered during formalization) and then *extracting* a readable mathematical narrative.

---

## 5. Target Audience

**Primary audience:**
- Researchers in **homotopy type theory and univalent foundations** who want to understand the computational/rewriting-theoretic roots of identity type structure.
- Researchers in **higher category theory** interested in concrete constructions of weak ω-groupoids.
- Researchers in **rewriting theory** interested in the homotopical significance of their subject.
- Researchers in **proof theory** interested in the algebraic structure of proof normalization.

**Secondary audience:**
- Advanced graduate students in logic, type theory, algebra, or topology seeking a bridge between these fields.
- Researchers in **formal verification** interested in the mathematical content behind proof-term rewriting.

**Prerequisites:** Graduate-level algebra (groups, categories), basic familiarity with either type theory or algebraic topology. No knowledge of Lean or any proof assistant is required.

---

## 6. Relationship to Existing Literature

### 6.1 HoTT / Univalent Foundations

The HoTT Book (2013) axiomatizes identity types with J, derives groupoid structure, and postulates univalence. Our book *reverses the direction*: we start with rewriting, derive groupoid structure, and then derive J. We do not assume univalence; whether computational paths can model it is an open question we pose. This book is complementary to HoTT, not competing — it provides a concrete algebraic model that illuminates *why* identity types have the structure they do.

**Key references:** The HoTT Book; Lumsdaine (2010); van den Berg–Garner (2011); Licata–Brunerie; Bezem–Coquand–Huber (cubical sets).

### 6.2 Rewriting Theory

Baader–Nipkow (1998) and Terese (2003) are standard references for term rewriting. Guiraud–Malbos (2009, 2012) develop *higher-dimensional rewriting* connecting rewriting to homotopy via Squier's theorem. Our work extends this programme by showing that a specific rewriting system (on proof-terms) produces a full ω-groupoid, not just a 2-dimensional homotopy invariant. The confluence proof via critical pairs (Chapter 5) contributes to the rewriting literature directly.

**Key references:** Baader–Nipkow; Terese; Squier (1987); Guiraud–Malbos (2009, 2012); Knuth–Bendix (1970).

### 6.3 Proof Theory

De Queiroz's original programme (from the late 1980s, culminating in the 2011/2012 book with de Oliveira and Gabbay) established LND and the concept of "rewrite reasons." Our book is the mathematical successor to that work: we take the framework of LND and discover that it contains, implicit in its rewrite system, the higher-categorical structures that have become central to 21st-century mathematics. We also connect to the proof-theoretic tradition of Prawitz, Martin-Löf, and Girard.

**Key references:** de Queiroz–de Oliveira–Gabbay (2011); Prawitz (1965, 1971); Martin-Löf (1975, 1984); Girard–Lafont–Taylor (1989).

### 6.4 Category Theory and Higher Categories

The weak ω-groupoid is a fundamental notion in higher category theory (Batanin 1998, Leinster 2004, Lurie 2009). Our construction provides a *new example* of a naturally occurring weak ω-groupoid — one arising from proof theory rather than topology or homotopy theory. This is relevant to the Grothendieck homotopy hypothesis (every ∞-groupoid should be the fundamental ∞-groupoid of a space) and to the general programme of finding algebraic models for homotopy types.

**Key references:** Batanin (1998); Leinster (2004); Lurie (2009); Grothendieck, *Pursuing Stacks* (1983); Maltsiniotis (2010).

---

## 7. Recommended Publishers

We consider three options, in order of preference:

### First choice: *Cambridge Tracts in Mathematics* (Cambridge University Press)

**Rationale:** This series publishes research monographs that develop a coherent theory and are accessible to a broad mathematical audience. The interdisciplinary nature of the book (proof theory + rewriting + higher categories + homotopy theory) fits Cambridge's tradition of publishing works that bridge fields. The series has published influential works in category theory (Johnstone, Leinster) and logic (Aczel, Rathjen). The 520–580 page length is appropriate.

### Second choice: *Lecture Notes in Mathematics* (Springer)

**Rationale:** LNM is ideal for research monographs that present new theories. The series is fast to publish, widely read, and open to unconventional combinations of fields. A shorter version (400 pages) could target LNM. However, the full version may be better served by a Tracts-style publication.

### Third choice: *Oxford Logic Guides* (Oxford University Press)

**Rationale:** This series has published foundational works in type theory and proof theory (Troelstra–Schwichtenberg, Sorensen–Urzyczyn) and would be a natural home for a book rooted in labelled deduction. However, the homotopy-theoretic content may stretch beyond the series' typical scope.

### Alternative: *Springer Monographs in Mathematics*

If the book expands beyond 600 pages or if the applications to algebraic topology are developed more fully, Springer Monographs would be appropriate.

---

## 8. Summary of Selling Points for Reviewers

A reviewer evaluating this proposal should note:

1. **Novelty of the main theorem:** Deriving weak ω-groupoid structure from a term rewriting system on proof-terms is new. This is not a reformulation of known results — it is a new construction yielding a new model.

2. **The derivation of J is a theorem, not an axiom.** This alone is a publishable result that will interest the type theory community.

3. **Complete confluence proof** for a 77-rule rewrite system on path expressions, with critical pair analysis. This contributes to rewriting theory independently of the homotopical applications.

4. **Machine-verified correctness:** 13,000+ theorems, 0 sorry-admits, in Lean 4. This is among the largest coherent formalizations in mathematics and provides ironclad confidence in correctness.

5. **Bridges four active research communities** (proof theory, rewriting, HoTT, higher categories) with a unified narrative.

6. **Timely:** The connections between rewriting and homotopy are a frontier topic (HDRA workshops, Guiraud–Malbos programme, cubical type theory). This book provides the first comprehensive treatment from the proof-theoretic side.

---

## 9. About the Authors

[To be completed]

---

## 10. Timeline

- Manuscript completion: [12–18 months from proposal acceptance]
- The mathematical content is fully developed and machine-verified; the primary task is exposition, organization, and translation from formal proofs to readable pen-and-paper mathematics.

---

*Prepared: February 2026*
