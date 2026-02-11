# The Algebra of Computational Paths
## Comprehensive Paper Outline

**Based on the Lean 4 formalization: 302 files, 60,860 lines, 1,710 definitions, 885 theorems, 701 structures, 69 inductive types**

---

## Abstract (1 page)

We present a comprehensive mathematical theory of *computational paths*—a formalism
in which propositional equalities between elements of a type carry explicit
rewrite traces. Starting from a type A, a computational path from a to b is a
pair (s, π) where π : a = b is a propositional equality and s is a finite
sequence of elementary rewrite steps recording how π was derived. The space of
computational paths is equipped with a confluent, terminating rewrite system
whose equivalence classes recover the standard identity type. We prove that this
structure gives rise to weak ω-groupoids, develop the associated homotopy
theory (fundamental groups, higher homotopy groups, fibrations, covering spaces,
spectral sequences), and compute fundamental groups of standard spaces (the
circle, torus, figure-eight, Klein bottle, projective spaces, lens spaces).
The entire development is formalized in Lean 4.

---

## Part I: Foundations (Chapters 1–5, ~20 pages)

### Chapter 1. Introduction and Motivation (3–4 pages)

**§1.1 The Curry–Howard–de Bruijn correspondence and propositional equality.**
Recall that in Martin-Löf type theory, the identity type Id_A(a,b) captures
propositional equality. In proof assistants based on the Calculus of Inductive
Constructions (where Eq lives in Prop), proof irrelevance collapses all
inhabitants of Id_A(a,b) into a single equivalence class—the Uniqueness of
Identity Proofs (UIP) principle holds definitionally.

**§1.2 The computational paths program.**
Following de Queiroz, de Oliveira, and Ramos (2011, 2016, 2018), we propose
that equality proofs carry *computational content*: the sequence of rewriting
steps that produced them. Even when the underlying logic satisfies UIP, the
rewrite *traces* are distinct combinatorial objects that can be compared,
composed, and quotiented. This creates a rich algebraic structure atop the
proof-irrelevant equality.

**§1.3 Design principle: Path = proof + trace.**
Formally, a computational path from a to b in a type A is a structure
Path_A(a,b) = { steps : List(Step A), proof : a =_A b } where the list of
steps is the computational trace and the proof field is the semantic witness.
Two paths with the same endpoints but different traces are *distinct* as paths,
even though their proof fields are identical by proof irrelevance.

> **Theorem 1.1** (Non-UIP for Path). For any inhabited type A, the space of
> computational paths does not satisfy the uniqueness of identity proofs:
> there exist p, q : Path_A(a, a) with p ≠ q.
>
> *Proof.* Take p = refl(a) (empty trace) and q = ofEq(refl) (one-step trace
> recording the trivial reflexive rewrite). These have p.steps = [] and
> q.steps = [⟨a, a, rfl⟩], hence p ≠ q. □

**§1.4 Related work.** Connections to:
- Homotopy Type Theory (HoTT) and univalent foundations
- Lumsdaine's "Weak ω-categories from intensional type theory" (2010)
- van den Berg–Garner "Types are weak ω-groupoids" (2011)
- Bezem, Coquand, Huber: cubical type theory
- The rewriting approach to higher-dimensional algebra (Burroni, Métayer, Lafont)

**§1.5 Outline of the paper.** Map of the paper's structure.

---

### Chapter 2. Computational Paths: Basic Constructions (4–5 pages)

**§2.1 Steps and paths.**

> **Definition 2.1** (Elementary Rewrite Step). An *elementary rewrite step*
> in a type A is a triple Step_A = (src, tgt, π) where src, tgt : A and
> π : src =_A tgt.

> **Definition 2.2** (Computational Path). A *computational path* from a to b
> is a pair Path_A(a,b) = (s, π) where s : List(Step_A) and π : a =_A b.

**§2.2 Fundamental operations.**

> **Definition 2.3** (Path operations).
> - *Reflexivity*: refl(a) = ([], refl_a)
> - *Symmetry*: symm(s, π) = (reverse(map(symm_step, s)), π⁻¹)
> - *Transitivity*: trans((s₁, π₁), (s₂, π₂)) = (s₁ ++ s₂, π₁ · π₂)
> - *Canonical witness*: ofEq(π) = ([⟨a, b, π⟩], π) for π : a = b

> **Theorem 2.4** (Monoid laws up to structural equality).
> (i) trans(refl(a), p) = p; (ii) trans(p, refl(b)) = p;
> (iii) trans(trans(p, q), r) = trans(p, trans(q, r)).
> All hold as strict equalities of Path structures.

> **Theorem 2.5** (Involution). symm(symm(p)) = p.

> **Theorem 2.6** (Anti-homomorphism). symm(trans(p, q)) = trans(symm(q), symm(p)).

**§2.3 Congruence operations.**

> **Definition 2.7** (Unary congruence). For f : A → B,
> congrArg(f, (s, π)) = (map(map_step(f), s), congrArg_f(π)).

> **Theorem 2.8** (Congruence is functorial).
> congrArg(f, trans(p, q)) = trans(congrArg(f, p), congrArg(f, q))
> and congrArg(f, symm(p)) = symm(congrArg(f, p)).

> **Definition 2.9** (Binary congruence). For f : A → B → C,
> - mapLeft(f, p, b) = congrArg(λx. f(x, b), p)
> - mapRight(f, a, q) = congrArg(f(a), q)
> - map2(f, p, q) = trans(mapLeft(f, p, b₁), mapRight(f, a₂, q))

**§2.4 Transport and dependent paths.**

> **Definition 2.10** (Transport). For D : A → Sort and p : Path_A(a, b),
> transport_D(p, x) = Eq.rec(π, x) for x : D(a), yielding an element of D(b).

> **Theorem 2.11** (Transport laws).
> (i) transport(refl, x) = x;
> (ii) transport(trans(p, q), x) = transport(q, transport(p, x));
> (iii) transport(symm(p), transport(p, x)) = x.

> **Definition 2.12** (Dependent application). For f : Π(x:A). D(x),
> apd(f, p) : Path_{D(b)}(transport_D(p, f(a)), f(b)).

**§2.5 Products, sums, sigma types, and function types.**

State the β-rules, η-rules, and structural laws for each type former:

> **Theorem 2.13** (Product β/η).
> fst(prodMk(p, q)) = p; snd(prodMk(p, q)) = q;
> prodMk(fst(r), snd(r)) = r for r : Path_{A×B}((a₁,b₁), (a₂,b₂)).

> **Theorem 2.14** (Sigma β/η). Analogous results for dependent pairs.

> **Theorem 2.15** (Function β/η).
> app(lamCongr(p), a) = p(a); lamCongr(λx. app(q, x)) = q.

> **Theorem 2.16** (Sum β). For f : α → C, g : β → C,
> congrArg(Sum.rec(f,g), congrArg(inl, p)) = congrArg(f, p), and similarly for inr.

**§2.6 Contexts: Substitution in sub-expressions.**

> **Definition 2.17** (Unary context). A *context* C : Context(A, B) is a
> function fill : A → B. It acts on paths via C[p] = congrArg(C.fill, p).

> **Definition 2.18** (Context substitution).
> substLeft(C, r, p) = trans(r, C[p]) and substRight(C, p, t) = trans(C[p], t).

> **Theorem 2.19** (Context substitution algebra). The operations substLeft
> and substRight satisfy associativity, unit, and idempotence laws (12 identities).

Extend to binary contexts (BiContext), dependent contexts (DepContext),
and dependent binary contexts (DepBiContext).

---

### Chapter 3. The Rewrite System (5–6 pages)

**§3.1 Rewrite rules: the Step relation.**

> **Definition 3.1** (Single-step rewrite). The relation Step on Path_A(a,b) is
> the smallest relation closed under 76 rules organized into 8 groups:

Group I — Path algebra (Rules 1–8):
1. symm(refl(a)) ▷ refl(a)
2. symm(symm(p)) ▷ p
3. trans(refl(a), p) ▷ p
4. trans(p, refl(b)) ▷ p
5. trans(p, symm(p)) ▷ refl(a)
6. trans(symm(p), p) ▷ refl(b)
7. symm(trans(p, q)) ▷ trans(symm(q), symm(p))
8. trans(trans(p, q), r) ▷ trans(p, trans(q, r))

Group II — Type-former β/η rules (Rules 9–25):
9. map2(f, p, q) ▷ trans(mapRight(f, a₁, q), mapLeft(f, p, b₂))
10–16. Product β, η, symmetry, and congruence rules
17–19. Sigma β, η, symmetry rules
20–21. Coproduct β-rules
22–25. Function β, η, symmetry, and dependent application rules

Group III — Transport β-rules (Rules 26–32):
26. The identity transport refl ▷ refl
27. Transport distributes over trans
28–29. Transport inverse laws
30–32. Transport through sigma constructors

Group IV — Context rules (Rules 33–48):
33–34. Context congruence and symmetry
35–48. substLeft/substRight β, associativity, unit, idempotence, cancellation

Group V — Dependent context rules (Rules 49–60):
49–60. Analogues of Group IV for dependent contexts

Group VI — Bi-context rules (Rules 61–68):
61–68. mapLeft, mapRight, map2 congruence for (dependent) binary contexts

Group VII — Map congruence (Rules 69–72):
69–72. mapLeft/mapRight preserve Step, interaction with ofEq

Group VIII — Structural closure (Rules 73–76):
73. symm_congr: Step(p, q) → Step(symm(p), symm(q))
74. trans_congr_left: Step(p, q) → Step(trans(p, r), trans(q, r))
75. trans_congr_right: Step(q, r) → Step(trans(p, q), trans(p, r))
76. context_congr: Step(p, q) → Step(C[p], C[q])

> **Theorem 3.2** (Soundness). Every rewrite step preserves the underlying
> propositional equality: Step(p, q) implies p.toEq = q.toEq.

**§3.2 Multi-step rewriting: Rw.**

> **Definition 3.3** (Rw). The relation Rw is the reflexive–transitive closure
> of Step. It is defined inductively by: Rw.refl(p) and
> Rw.tail(h : Rw(p,q), s : Step(q,r)) : Rw(p,r).

> **Theorem 3.4**. Rw preserves propositional equality.

**§3.3 Rewrite equality: RwEq.**

> **Definition 3.5** (RwEq). The *rewrite equality* RwEq is the symmetric closure
> of Rw, i.e., the equivalence relation generated by Step. Constructors:
> RwEq.refl, RwEq.step, RwEq.symm, RwEq.trans.

> **Theorem 3.6** (RwEq is a congruence). RwEq is preserved by:
> trans (both arguments), symm, congrArg, mapLeft, mapRight, map2,
> Context.map, BiContext.map2, DepContext.map, lamCongr.

**§3.4 The LNDEQ rule enumeration.**

Present the mnemonic names from the paper (sr, ss, tr, tsr, rrr, lrr, slr, srr,
slss, slsss, srsr, srrrr, mx2l1, ..., mxetaSigma, stss, ssbl, ssbr, sx, sxss,
smss, smfst, smsnd, smcase) and the precedence ranking.

**§3.5 Normalization.**

> **Definition 3.7** (Normal form). A path p is *normal* if p = ofEq(p.toEq).
> The normalization function sends p to ofEq(p.toEq).

> **Theorem 3.8**. normalize(p) is always normal, and RwEq(p, normalize(p))
> for every path p. Two paths are RwEq-equivalent if and only if they have
> the same normal form.

**§3.6 Termination.**

> **Theorem 3.9** (Termination). The rewrite relation Rw is well-founded:
> there are no infinite reduction sequences. (Established via a measure on
> the syntactic complexity of paths, with a compatible rule precedence.)

**§3.7 Confluence.**

> **Definition 3.10** (Join). A *join* of q and r (where Rw(p,q) and Rw(p,r))
> is a path m with Rw(q,m) and Rw(r,m).

> **Theorem 3.11** (Local confluence / Strip Lemma). If Step(p,q) and Rw(p,r),
> then q and r have a common reduct.

> **Theorem 3.12** (Confluence). The rewrite system is confluent: any two
> reductions from a common source can be joined. (Follows from termination
> and local confluence via Newman's lemma.)

> **Corollary 3.13**. Every path has a unique normal form (up to structural
> equality), and two paths are RwEq-equivalent iff they reduce to the same
> normal form.

**§3.8 The quotient PathRwQuot.**

> **Definition 3.14**. PathRwQuot(A, a, b) = Path_A(a, b) / RwEq is the quotient
> type. It inherits well-defined trans, symm, congrArg operations from Path
> and satisfies the groupoid laws *strictly* (as definitional equalities).

> **Theorem 3.15**. PathRwQuot(A, a, b) is equivalent (as a type) to the
> propositional identity type a =_A b.

---

### Chapter 4. The Groupoid of Computational Paths (3–4 pages)

**§4.1 Weak category and weak groupoid structures.**

> **Definition 4.1** (WeakCategory). A *weak category* on A is a choice of
> composition, identity, and witnesses of associativity and unit laws
> holding up to Rw.

> **Theorem 4.2**. Every type A carries a canonical weak category with
> comp = trans, id = refl, and the groupoid laws holding up to Step.

> **Definition 4.3** (WeakGroupoid). A *weak groupoid* enriches a weak category
> with an inversion operation and witnesses that every morphism is invertible
> up to Rw.

> **Theorem 4.4**. Every type A is a weak groupoid under computational paths.

**§4.2 Strict groupoid on the quotient.**

> **Theorem 4.5**. PathRwQuot(A, –, –) is a strict groupoid: all axioms hold
> as equalities.

**§4.3 RewriteLift: functorial transport of rewrites.**

> **Definition 4.6** (RewriteLift). A *rewrite lift* from A to B consists of
> an object map obj : A → B, a path map, and a proof that Step is preserved.
> Any Context, BiContext, or DepContext produces a canonical RewriteLift.

> **Theorem 4.7**. A RewriteLift transports both Rw and RwEq.

---

### Chapter 5. Higher-Dimensional Structure (4–5 pages)

**§5.1 Two-cells and the bicategory of paths.**

> **Definition 5.1** (Two-cell). A *two-cell* between paths p, q : Path_A(a,b) is
> a rewrite equality RwEq(p, q).

> **Definition 5.2** (Bicategorical operations). Vertical composition = RwEq.trans;
> Left whiskering: f ▷_L η, for f : Path(a,b) and η : RwEq(g,h) where g,h : Path(b,c);
> Right whiskering: η ▷_R f; Horizontal composition = left whisker then right whisker.

> **Theorem 5.3**. The computational path data (0-cells = points, 1-cells = paths,
> 2-cells = RwEq witnesses) form a weak 2-category (bicategory). The exchange law,
> associator, and unitor coherences hold up to 3-cells.

**§5.2 The globular tower.**

> **Definition 5.4** (Globular tower). Define iteratively:
> Level 0 = A, Level (n+1) = GlobularCell(Level n). Each level carries refl, symm, trans.

**§5.3 The weak ω-groupoid.**

> **Definition 5.5** (Derivation₂). A *derivation* between paths p, q is an
> RwEq(p, q) witness—a finite tree of steps and their symmetric/transitive closures.

> **Definition 5.6** (Derivation₃, Derivation₄, higher cells). Cells at dimension k ≥ 3
> witness equality of derivations at dimension k − 1.

> **Theorem 5.7** (Contractibility at level ≥ 3, Batanin-style). For k ≥ 3,
> any two parallel (k−1)-cells are connected by a k-cell. This follows from
> proof irrelevance of RwEq witnesses.

> **Theorem 5.8** (Main structure theorem). The tower
> A, Path, Derivation₂, Derivation₃, Derivation₄, ...
> forms a weak ω-groupoid in the sense of Batanin/Leinster, with
> contractibility starting at level 3.

> **Remark 5.9** (Critical design choice). Contractibility does *not* hold at
> level 2: not all parallel paths are RwEq-equivalent. This is essential for
> capturing non-trivial fundamental groups (e.g., π₁(S¹) ≅ ℤ).

**§5.4 The infinity-groupoid approximation.**

> **Definition 5.10** (n-groupoid truncation). The *n-truncation* collapses all
> cells above dimension n to trivial identities, yielding a strict n-groupoid.

> **Theorem 5.11**. The 1-truncation of the ω-groupoid recovers the strict
> groupoid PathRwQuot.

**§5.5 Enriched, double, and symmetric monoidal structures.**

Brief statements of the enriched category, double groupoid, symmetric monoidal
category, and operadic structures derived from the path algebra.

---

## Part II: Homotopy Theory (Chapters 6–10, ~20 pages)

### Chapter 6. Fundamental Groups and Loop Spaces (3–4 pages)

**§6.1 Loop spaces.**

> **Definition 6.1** (Loop space). Ω(A, a) = Path_A(a, a). Composition is path
> concatenation; identity is refl(a); inversion is path symmetry.

> **Definition 6.2** (Loop quotient). LoopQuot(A, a) = PathRwQuot(A, a, a).
> This carries a strict group structure (LoopGroup).

**§6.2 The fundamental group.**

> **Definition 6.3**. π₁(A, a) = LoopQuot(A, a) with multiplication from loop
> concatenation and inversion from symmetry.

> **Theorem 6.4** (Group axioms). π₁(A, a) is a group: associativity,
> left/right identity, left/right inverse all hold strictly on the quotient.

**§6.3 Functoriality.**

> **Theorem 6.5**. A based map f : (A, a) → (B, b) induces a group homomorphism
> f_* : π₁(A, a) → π₁(B, b). The fundamental group is a functor from pointed
> types to groups.

> **Theorem 6.6** (Product formula). π₁(A × B, (a, b)) ≅ π₁(A, a) × π₁(B, b).

**§6.4 Iterated loop spaces and higher homotopy groups.**

> **Definition 6.7**. Ωⁿ(A, a) is the n-fold iterated loop space. The n-th
> homotopy group is πₙ(A, a) = π₀(Ωⁿ(A, a)).

> **Theorem 6.8** (Eckmann–Hilton). For n ≥ 2, πₙ(A, a) is abelian. The proof
> proceeds via the interchange law for 2-cells, showing horizontal and vertical
> composition coincide on Ω²(A, a).

**§6.5 The fundamental groupoid.**

> **Definition 6.9**. The *fundamental groupoid* Π₁(A) has objects = points of A,
> morphisms = elements of PathRwQuot(A, a, b). This is a strict groupoid.

> **Theorem 6.10** (Functoriality). f : A → B induces a groupoid functor
> Π₁(A) → Π₁(B). Natural transformations between functors correspond to paths.

---

### Chapter 7. Spaces and Their Fundamental Groups (4–5 pages)

**§7.1 The computational circle S¹.**

> **Definition 7.1** (Circle). CircleCompPath is a one-point type equipped with
> a formal loop generator via the path expression rewriting system (PathExpr).

> **Theorem 7.2**. π₁(S¹, base) ≅ ℤ. The isomorphism sends the loop class to
> 1 ∈ ℤ and is established via a winding number computation.

**§7.2 The torus T².**

> **Definition 7.3** (Torus). Defined as a one-point type with two formal loop
> generators α, β satisfying the commutation relation αβ = βα.

> **Theorem 7.4**. π₁(T², base) ≅ ℤ × ℤ.

**§7.3 The figure-eight and bouquets.**

> **Definition 7.5** (Figure-eight). One-point type with two free loop generators.

> **Theorem 7.6**. π₁(Figure-eight) ≅ ℤ * ℤ (free product).

> **Definition 7.7** (Bouquet of n circles). Generalization to n loop generators.

> **Theorem 7.8**. π₁(Bouquet_n) ≅ F_n (free group on n generators).

**§7.4 Pushouts and the Seifert–van Kampen theorem.**

> **Definition 7.9** (Pushout). The pushout Pushout(A, B, C, f, g) with
> constructors inl, inr, and path constructor glue.

> **Theorem 7.10** (Seifert–van Kampen). For a pushout along f : C → A
> and g : C → B, there is an equivalence
> π₁(Pushout, inl(f(c₀))) ≅ π₁(A, f(c₀)) *_{π₁(C,c₀)} π₁(B, g(c₀)).

Applications:
> **Corollary 7.11**. π₁(S¹ ∨ S¹) ≅ ℤ * ℤ.
> **Corollary 7.12**. Wedge-free product results and generalizations.

**§7.5 Suspensions, spheres, and projective spaces.**

> **Definition 7.13** (Suspension). Susp(X) with north, south, and merid : X → Path(north, south).

> **Theorem 7.14**. Susp(S¹) ≅ S² (as computational-path types).

> **Theorem 7.15** (Klein bottle, Möbius band, lens spaces, projective spaces).
> Computations of π₁ for these spaces, including:
> - π₁(Klein) ≅ ℤ ⋊ ℤ
> - π₁(RP^n)
> - π₁(L(p,q)) for lens spaces

**§7.6 Mapping cylinders, mapping cones, and joins.**

Definitions of these standard constructions in the computational-path framework,
with their fundamental group consequences.

---

### Chapter 8. Fibrations, Covering Spaces, and Exact Sequences (4–5 pages)

**§8.1 Fibrations.**

> **Definition 8.1** (Fibration structure). A dependent type P : B → Type
> together with path-lifting data. Transport along base paths provides the
> fiber transport.

> **Theorem 8.2** (Path-space fibration). For any pointed type (A, a), the
> path-space fibration ev : Path(a, –) → A is a fibration with contractible total space.

**§8.2 The Hopf fibration.**

> **Theorem 8.3** (Hopf fibration data). There exists a fibration S¹ → S³ → S²
> with the projection and fiber identification recorded as computational-path data.

**§8.3 Covering spaces.**

> **Definition 8.4** (Covering space). A covering is a fibration whose fibers are
> discrete (sets). Covering spaces are classified by actions of π₁.

> **Theorem 8.5** (Covering path lifting). Any path in the base lifts uniquely
> to the total space.

> **Theorem 8.6** (Galois correspondence). Connected coverings of A based at a
> correspond to conjugacy classes of subgroups of π₁(A, a).

**§8.4 Homotopy fiber and cofiber sequences.**

> **Definition 8.7** (Homotopy fiber). hofiber(f, b) = Σ(a : A). Path(f(a), b).

> **Theorem 8.8** (Puppe sequence). The cofiber sequence
> A → B → cofib(f) → ΣA → ΣB → ...
> with path-based connecting maps at each stage.

> **Theorem 8.9** (Barratt–Puppe). Extended exact sequence with suspension structure.

**§8.5 Long exact sequence of homotopy groups.**

> **Theorem 8.10**. For a fibration F → E → B, there is a long exact sequence
> ⋯ → πₙ₊₁(B) →^∂ πₙ(F) → πₙ(E) → πₙ(B) → πₙ₋₁(F) → ⋯ → π₀(E) → π₀(B).

> **Theorem 8.11** (Connecting homomorphism). The boundary map ∂ is a group
> homomorphism that sends the identity to the basepoint and respects composition.

**§8.6 Mayer–Vietoris sequence.**

> **Theorem 8.12**. For a pushout square, there is an exact Mayer–Vietoris
> sequence in homotopy groups.

---

### Chapter 9. The Hurewicz Theorem and Homological Algebra (3–4 pages)

**§9.1 The Hurewicz homomorphism.**

> **Definition 9.1**. The Hurewicz map h : π₁(X, x₀) → H₁(X) sends a loop
> class to its homology class.

> **Theorem 9.2** (Hurewicz theorem, dimension 1). For path-connected X,
> h induces an isomorphism π₁(X)^ab ≅ H₁(X).

**§9.2 Free groups and the Nielsen–Schreier theorem.**

> **Theorem 9.3** (Free group universal property). The loop group of the bouquet
> satisfies the universal property of the free group.

> **Theorem 9.4** (Nielsen–Schreier). Every subgroup of a free group is free.

**§9.3 Abelianization.**

> **Definition 9.5**. The abelianization G^ab = G / [G, G] with the natural
> projection and universal property.

**§9.4 Homological algebra: Ext, Tor, and resolutions.**

> **Definition 9.6**. Projective and injective resolutions in the path-algebraic
> framework. Ext and Tor functors. Universal coefficient theorem.

**§9.5 Cohomology: de Rham, Čech, Hochschild, cyclic.**

Brief definitions and functoriality statements for each cohomology theory
formalized in the library, including:
- de Rham cohomology ring
- Čech cohomology via covers
- Hochschild and cyclic cohomology
- Künneth formula
- Grothendieck duality

---

### Chapter 10. Advanced Homotopy Theory (3–4 pages)

**§10.1 Eilenberg–MacLane spaces and Moore spaces.**

> **Definition 10.1**. K(G, n) with πₙ(K(G,n)) ≅ G and πₖ(K(G,n)) = 0 for k ≠ n.

**§10.2 Postnikov towers and obstruction theory.**

> **Definition 10.2** (Postnikov system). A tower of fibrations
> ⋯ → X_{n+1} → X_n → ⋯ → X_1 → X_0.

> **Theorem 10.3** (Obstruction). Lifting along a Postnikov stage is obstructed
> by cohomology classes.

**§10.3 Whitehead's theorem.**

> **Theorem 10.4** (Whitehead). A map f : X → Y between CW complexes that
> induces isomorphisms on all homotopy groups is a homotopy equivalence.

**§10.4 Suspension, Freudenthal, and stable homotopy.**

> **Theorem 10.5** (Freudenthal suspension). The suspension map
> πₙ(X) → πₙ₊₁(ΣX) is an isomorphism for n < 2·conn(X) + 1.

> **Theorem 10.6** (Stable homotopy category). The colimit of iterated suspensions
> gives stable homotopy groups, and the category of spectra with smash products.

**§10.5 Spectral sequences.**

> **Definition 10.7** (Spectral sequence). A bigraded sequence of differential
> groups E_r^{p,q} with d_r : E_r → E_r of bidegree (r, 1-r).

> **Theorem 10.8** (Adams spectral sequence). Converging to stable stems
> via Ext over the Steenrod algebra.

**§10.6 Further results (survey).**

Brief enumeration with references to the formalization:
- K-theory (algebraic and topological)
- Characteristic classes (Stiefel–Whitney, Chern, Pontryagin)
- Operads and A∞-algebras
- Rational homotopy theory
- Chromatic homotopy theory
- Topological Hochschild homology (THH)
- Goodwillie calculus
- Motivic and étale cohomology
- Surgery theory and bordism
- Derived algebraic geometry
- Higher topos theory
- Floer homotopy theory

---

## Part III: Metalogical Properties and Conclusions (Chapters 11–12, ~8 pages)

### Chapter 11. The Rewrite System: Metatheory (4–5 pages)

**§11.1 The typed rewriting perspective.**

> **Definition 11.1** (Typed rewriting system). The rewrite rules on Path_A(a,b)
> form a typed term rewriting system. Terms are path expressions; types are
> endpoint pairs (a, b).

**§11.2 The strip lemma and local confluence proof.**

> **Theorem 11.2** (Strip lemma). If Step(p, q) and Rw(p, r), then there exists
> m with Rw(q, m) and Rw(r, m).

> **Theorem 11.3** (Detailed confluence proof). By case analysis on the 76 rules,
> we establish the critical-pair lemma for all overlapping rewrites. The constructive
> confluence proof produces explicit join witnesses.

**§11.3 PathExpr: a first-order term language.**

> **Definition 11.4** (PathExpr). An inductive type of *path expressions*
> (refl, symm, trans, congrArg, mapLeft, mapRight, ...) that represents
> the syntactic structure of paths before evaluation.

> **Theorem 11.5** (PathExpr confluence). The rewrite system on PathExpr is
> confluent, with explicit join witnesses computable by the reduction strategy.

**§11.4 Decidability and the path tactic.**

> **Theorem 11.6**. RwEq-equivalence of paths is decidable: two paths are
> RwEq-equivalent iff their normal forms are structurally equal.

Description of the `path_simp` tactic that automates rewrite-equality proofs.

**§11.5 Connection to HoTT identity types.**

> **Theorem 11.7** (HoTT-compatibility). The computational path structure
> satisfies the J-elimination rule (path induction) and function extensionality.
> In the presence of univalence axioms, the path quotient recovers the HoTT
> identity type.

> **Remark 11.8**. The computational-paths approach does *not* require univalence
> or higher inductive types as axioms; instead, the higher structure is derived
> from the rewrite system.

---

### Chapter 12. Conclusion and Future Directions (2–3 pages)

**§12.1 Summary of contributions.**
- A complete algebraic framework for identity proofs with computational content
- A confluent, terminating rewrite system with 76 rules
- Weak ω-groupoid structure with explicit contractibility at dimension ≥ 3
- Comprehensive homotopy-theoretic development: π₁ computations, fibrations,
  covering spaces, spectral sequences, K-theory, operads

**§12.2 The formalization.**
Statistics: 302 Lean 4 files, 60,860 lines, 1,710 definitions, 885 theorems,
701 structures, 69 inductive types. Discussion of the formalization methodology,
design decisions, and the role of proof automation.

**§12.3 Future directions.**
- Constructive models: cubical computational paths
- Machine-checked higher-categorical coherence
- Computational content extraction from rewrite traces
- Applications to automated theorem proving and program verification
- Connections to higher-dimensional rewriting theory
- Synthetic homotopy theory in the computational-paths framework

---

## Appendices

### Appendix A. Complete List of Rewrite Rules (2–3 pages)

Full statement of all 76 rules with their formal names, organized by group.
Cross-reference to the LNDEQ mnemonic table.

### Appendix B. Index of Definitions and Theorems (2–3 pages)

Alphabetical index mapping paper theorem numbers to Lean 4 module paths.

### Appendix C. Dependency Graph (1 page)

Visual representation of the module dependency structure, highlighting the
foundational kernel (Basic → Rewrite → Groupoid) and the homotopy-theoretic
superstructure.

---

## Estimated Page Counts

| Part | Chapters | Pages |
|------|----------|-------|
| I. Foundations | 1–5 | 20–24 |
| II. Homotopy Theory | 6–10 | 17–22 |
| III. Metatheory & Conclusion | 11–12 | 7–8 |
| Appendices | A–C | 5–7 |
| **Total** | | **49–61** |

---

## Key Notation Table

| Paper notation | Lean 4 name | Meaning |
|---|---|---|
| Path_A(a,b) | `Path a b` | Computational path from a to b |
| refl(a) | `Path.refl a` | Reflexive path (empty trace) |
| p⁻¹, invA(p) | `Path.symm p` | Path symmetry |
| p · q, cmpA(p,q) | `Path.trans p q` | Path composition |
| f_*(p) | `Path.congrArg f p` | Congruence / functorial action |
| C[p] | `Context.map C p` | Context substitution |
| transport_D(p,x) | `Path.transport p x` | Transport along path |
| apd(f,p) | `Path.apd f p` | Dependent application |
| p ▷ q | `Step p q` | Single rewrite step |
| p ▷* q | `Rw p q` | Multi-step rewrite |
| p ≈ q | `RwEq p q` | Rewrite equality |
| [p] | `Quot.mk _ p` | RwEq-equivalence class |
| π₁(A,a) | `PiOne A a` | Fundamental group |
| πₙ(A,a) | `PiN n A a` | n-th homotopy group |
| Ω(A,a) | `LoopSpace A a` | Loop space |
| Ωⁿ(A,a) | `IteratedLoopSpace n A a` | Iterated loop space |
| Σ_f X | `Suspension X` | Suspension |

---

## References

1. de Queiroz, R.J.G.B.; de Oliveira, A.G.; Ramos, A.F. "Propositional equality,
   identity types, and direct computational paths." *South American Journal of
   Logic*, 2016.

2. Ramos, A.F.; de Queiroz, R.J.G.B.; de Oliveira, A.G. "Explicit computational
   paths." *South American Journal of Logic*, 2018.

3. Lumsdaine, P.L. "Weak ω-categories from intensional type theory."
   *Logical Methods in Computer Science*, 2010.

4. van den Berg, B.; Garner, R. "Types are weak ω-groupoids."
   *Proc. London Math. Soc.*, 2011.

5. The Univalent Foundations Program. *Homotopy Type Theory: Univalent Foundations
   of Mathematics.* Institute for Advanced Study, 2013.

6. Eckmann, B.; Hilton, P.J. "Group-like structures in general categories. I."
   *Math. Annalen*, 1962.

7. Newman, M.H.A. "On theories with a combinatorial definition of 'equivalence'."
   *Annals of Mathematics*, 1942.

8. Hatcher, A. *Algebraic Topology.* Cambridge University Press, 2002.

9. May, J.P. *A Concise Course in Algebraic Topology.* University of Chicago Press, 1999.

10. Baez, J.; Dolan, J. "Higher-dimensional algebra and topological quantum field theory."
    *J. Math. Phys.*, 1995.
