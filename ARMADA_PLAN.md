# Armada Plan: Waves 21–25

**Generated:** 2026-02-10 22:36 GMT-3
**Commander:** Armada AI
**Status:** PROPOSED — awaiting deployment

---

## Reconnaissance Report

### Fleet Inventory

| Metric | Value |
|--------|-------|
| **Total .lean files** | **295** |
| **sorry count** | **0** ✅ |
| **axiom count** | **0** ✅ |
| Homotopy module (`Path/Homotopy/`) | 137 files |
| Category/Structure module (`Path/`) | 45 files |
| Algebra module (`Path/Algebra/`) | 40 files |
| Spaces module (`Path/CompPath/`) | 39 files |
| Rewrite engine (`Path/Rewrite/`) | 22 files |
| ω-Groupoid module (`Path/OmegaGroupoid/`) | 5 files |
| Core module (`Path/Basic/`) | 5 files |
| Root | 2 files |

### Topics Already Covered

**A. Foundations & Rewrite Engine**
- Core path combinators (id, comp, inv, whisker, congruence)
- LND_EQ-TRS rewrite system (47+ rules)
- Confluence (Newman's lemma, strip lemma, constructive proofs)
- Termination and normalization
- Path expressions (PathExpr) with tactic automation (29 tactics)
- Quotient constructions on paths

**B. Higher Categorical Structure**
- Groupoid, 2-category, bicategory, double category
- ω-groupoid (weak), ∞-groupoid approximation
- Monoidal, symmetric monoidal, enriched categories
- Kan extensions, Yoneda lemma, limits/colimits
- Adjoint equivalences, localization of categories
- Naturality squares, natural transformations
- Operadic structure, A∞-algebras, little cubes operad

**C. Homotopy Theory — Classical**
- Fundamental group & groupoid (+ functoriality)
- π₁ computations: S¹≃ℤ, T²≃ℤ×ℤ, figure-eight≃F₂, bouquets, Klein bottle, RP²
- Higher homotopy groups (π_n), Eckmann-Hilton argument
- Seifert–van Kampen theorem (+ generalized, derived)
- Covering spaces (classification, path lifting, universal cover)
- Fibrations, fiber sequences, path space fibration, long exact sequence
- Hurewicz theorem (H₁ and higher)
- Freudenthal suspension theorem
- Blakers-Massey theorem
- Whitehead theorem, Whitehead product, Whitehead tower
- Postnikov towers and systems
- Truncation and n-types
- Brouwer degree and fixed-point theory

**D. Homotopy Theory — Advanced**
- Loop spaces: iterated, infinite, free, recognition, delooping, adjunction
- Suspension-loop adjunction, James construction
- Hopf fibration and Hopf invariant
- Smash product (+ algebra)
- Spectral sequences (+ Adams spectral sequence)
- Spectrum objects, Ω-spectra, stable homotopy
- Stable stems, stable splittings (Snaith)
- Barratt-Puppe & Puppe sequences, cofiber sequences
- Samelson product, Toda brackets, Massey products
- Steenrod operations & Steenrod algebra
- Brown representability
- Model categories, Quillen adjunctions
- CW complexes, CW approximation, cellular approximation & homology
- Homotopy limits/colimits, homotopy pullbacks

**E. Homological Algebra**
- Chain complexes, path homology
- Projective & injective resolutions
- Ext and Tor functors
- Universal coefficient theorem, Künneth formula
- Homological dimension
- Cohomology rings, cup products
- Dold-Kan correspondence
- Bar complexes, Eilenberg-Zilber / Alexander-Whitney
- Acyclic models
- Hochschild cohomology, cyclic cohomology
- Lie algebra cohomology
- Mayer-Vietoris sequence
- Poincaré duality

**F. K-Theory & Characteristic Classes**
- Algebraic K-theory (K₀ from homotopy perspective)
- Characteristic classes (Stiefel-Whitney, Chern, Pontryagin)
- Vector bundles, principal bundles, fiber bundles
- Topological Hochschild homology (THH)

**G. Spaces & Constructions**
- Circle, torus, spheres (Sⁿ), suspension, Klein bottle, Möbius band
- Real projective space (RP²), projective spaces, lens spaces (+ algebra)
- Grassmannians, Stiefel manifolds, flag manifolds, homogeneous spaces
- Classifying spaces (BG), delooping construction
- Configuration spaces, orbit spaces, join spaces
- Mapping cone, mapping cylinder, smash product, wedge sums
- Pushout/pullback path characterization
- π₅(S³) computation

**H. Frontier Topics**
- Chromatic homotopy theory
- Goodwillie calculus
- Rational homotopy theory
- Motivic homotopy theory, motivic cohomology
- Étale cohomology
- Bordism & cobordism theory
- Surgery theory
- Floer homotopy theory
- Parametrized homotopy theory
- Higher topos theory
- Derived algebraic geometry
- Equivariant homotopy theory
- Localization theory (Bousfield)
- Grothendieck duality, Brown-Gersten
- Čech cohomology, de Rham cohomology
- Morse theory
- Homological stability
- Nerve-realization adjunction, Kan complexes, simplicial homotopy
- HoTT primitives

---

## Gap Analysis

Despite 295 files, the following major areas remain **uncovered or only superficially touched**:

1. **EHP sequence** — The classical James/EHP fiber sequence connecting πₙ(Sᵏ) is absent
2. **Kervaire invariant** — No Kervaire invariant one problem formalization
3. **Sullivan conjecture / Miller's theorem** — Fixed-point theory for classifying spaces absent
4. **Ganea conjecture / Lusternik-Schnirelmann category** — No LS-category theory
5. **Persistent homology / TDA** — No topological data analysis connection
6. **∞-categories** — Only stubs; no quasi-category / (∞,1)-category theory proper
7. **Factorization algebras** — Completely absent (Costello-Gwilliam framework)
8. **Decision procedures** — PathTactic exists but no formal decidability results
9. **Serre classes & C-theory** — Serre's mod C theory not formalized
10. **Adams operations** — K-theory has K₀ but no Adams operations ψᵏ
11. **Bott periodicity** — Not formalized despite K-theory presence
12. **String topology** — Free loop space exists but no Chas-Sullivan product
13. **Galois theory of covering spaces** — Classification exists but no étale π₁ connection
14. **Scissors congruence / algebraic K-theory of spaces** — Waldhausen K-theory absent
15. **Phantom maps** — Not formalized
16. **Nilpotence theorem** — Key chromatic result missing
17. **Thom spectra** — Bordism exists but no Thom isomorphism formalized
18. **Dyer-Lashof operations** — Homology operations on infinite loop spaces absent
19. **Formal group laws** — Connection to chromatic homotopy incomplete
20. **Path normalization algorithms** — Normalization exists but no complexity analysis

---

## Proposed Armadas 21–25

### Armada 21: The EHP Siege — Classical Unstable Homotopy

*Theme: Fill the gap in unstable homotopy theory computations — the EHP sequence, Ganea fibrations, and LS-category, all deeply computational.*

```
1. EHPSequence.lean — The James EHP fiber sequence: E: πₙ(Sᵏ) → πₙ₊₁(Sᵏ⁺¹), H: πₙ₊₁(Sᵏ⁺¹) → πₙ₊₁(S²ᵏ⁺¹), P: πₙ(S²ᵏ⁻¹) → πₙ₋₁(Sᵏ); exactness of the EHP long exact sequence; computational path witnesses for the suspension homomorphism E, the James-Hopf invariant H, and the connecting map P. Includes: proof that E agrees with Freudenthal in the stable range, H detects Hopf invariant one elements, and P computes the first differential.

2. GaneaFibration.lean — Ganea's fibrations Gₙ(X) → X with fiber Gₙ₋₁(X) * ΩX; construction via iterated joins of the loop space; proof that cat(X) ≤ n iff the n-th Ganea fibration admits a section; path-level witnesses for the Ganea-Whitehead characterization; naturality of Ganea fibrations under maps. Proof that G₁(X) is the path space fibration.

3. LSCategory.lean — Lusternik-Schnirelmann category: definition of cat(X) as minimum n such that X is covered by (n+1) contractible-in-X open sets; proof cat(Sⁿ) = 1, cat(Tⁿ) = n; product inequality cat(X × Y) ≤ cat(X) + cat(Y); cup-length lower bound; relationship to Ganea fibrations; Berstein-Hilton theorem connecting cat to cone length.

4. BlakersMasseyImproved.lean — Blakers-Massey triad connectivity theorem (strengthening the existing file): the sharp connectivity bound for pushout squares; Freudenthal as corollary; the relative Hurewicz theorem as corollary; computational path witnesses for the Blakers-Massey map; excision isomorphism in the metastable range; Barratt-Whitehead lemma on wedge connectivity.

5. UnstableStemsLow.lean — Explicit computation of unstable homotopy groups: π₃(S²) ≃ ℤ via Hopf fibration; π₄(S³) ≃ ℤ/2 via suspension and EHP; π₄(S²) ≃ ℤ/2 via composition with η; π₅(S²) ≃ ℤ/2; path-level normal forms for generators; computational verification that the Hopf maps η, ν, σ generate the claimed groups. Connects to the existing Pi5S3 computation.
```
**Directory:** `Path/Homotopy/`

---

### Armada 22: The Chromatic Depths — Periodicity, Nilpotence, and Formal Groups

*Theme: Deepen chromatic homotopy — formalize the structural theorems (nilpotence, periodicity, thick subcategory) and their connections to formal group laws.*

```
1. NilpotenceTheorem.lean — Devinatz-Hopkins-Smith nilpotence theorem: a self-map f: Σᵈ X → X of a finite p-local spectrum is nilpotent iff MU₊(f) is nilpotent; path-level formulation via computational spectra; definition of type-n complexes and vₙ-self-maps; proof that nilpotence detects via MU₊-homology. Computational witnesses for nilpotency of specific maps.

2. PeriodicityTheorem.lean — Hopkins-Smith periodicity theorem: every type-n finite p-local spectrum admits a vₙ-self-map, unique up to iteration; chromatic filtration of the stable category; definition of the thick subcategory theorem (classification of thick subcategories of finite spectra by type); path witnesses for the telescope conjecture at height 1; Bousfield classes of K(n).

3. FormalGroupLaw.lean — Formal group laws in the computational paths framework: definition of formal group laws over path algebras; the universal FGL (Lazard ring); Quillen's theorem MU₊ ≃ L; p-typical formal group laws; the Honda formal group law Γₙ of height n; path-algebraic computation of [p](x) for the additive, multiplicative, and height-n Honda FGL; logarithms and exponentials.

4. BottPeriodicity.lean — Bott periodicity in K-theory: π₂(BU) ≃ ℤ and the 2-fold periodicity BU ≃ Ω²BU; real Bott periodicity with period 8: πₖ(BO) for k = 0..7; the clutching construction; path witnesses for the periodicity maps; Adams operations ψᵏ on K-theory and their properties (ring homomorphisms, ψᵏψˡ = ψᵏˡ); cannibalistic classes.

5. ThomSpectra.lean — Thom spectra and the Thom isomorphism: Thom space construction Th(ξ) for a vector bundle ξ; Thom class and Thom isomorphism Hⁿ(B) ≃ Hⁿ⁺ᵏ(Th(ξ)); MO and MU as Thom spectra of universal bundles; path-level Pontryagin-Thom construction; relationship between cobordism and Thom spectra; Wu formula connecting Steenrod squares and Stiefel-Whitney classes.
```
**Directory:** `Path/Homotopy/`

---

### Armada 23: The Infinity Vanguard — ∞-Categories, Factorization, and String Topology

*Theme: Build genuine (∞,1)-categorical infrastructure, factorization algebras, and string topology — connecting the computational paths framework to modern higher algebra.*

```
1. QuasiCategory.lean — Quasi-categories (∞-categories) via computational paths: definition of inner Kan complexes as quasi-categories; composition witnesses as inner horn fillers; the homotopy category of a quasi-category; mapping spaces Map(x,y) as Kan complexes; the join of quasi-categories; proof that the nerve of a category is a quasi-category; left/right fibrations and their classification via functors to Kan. Connects to existing KanComplex.lean and SimplicialPath.lean.

2. InfinityCatLimits.lean — Limits and colimits in (∞,1)-categories: definition of (co)limit diagrams via terminal objects in slice quasi-categories; path witnesses for products, coproducts, pullbacks, pushouts in quasi-categories; adjoint functor theorem for presentable ∞-categories; Lurie's ∞-categorical Seifert-van Kampen; comparison with homotopy (co)limits from HomotopyLimitColimit.lean; ∞-topos structure on spaces.

3. FactorizationAlgebra.lean — Factorization algebras in the Costello-Gwilliam sense: prefactorization algebras on a topological space; factorization algebra condition (descent/cosheaf); locally constant factorization algebras; Eₙ-algebras as locally constant factorization algebras on ℝⁿ; relationship to the little cubes operad (connecting to LittleCubesOperad.lean); factorization homology ∫_M A as a topological invariant; the nonabelian Poincaré duality theorem.

4. StringTopology.lean — Chas-Sullivan string topology: the free loop space LX (extending FreeLoopSpace.lean); the loop product on H₊(LM) for closed oriented manifolds; BV-algebra structure on H₊(LM) with the BV operator Δ; the string bracket on equivariant homology; proof that H₊(LS^n) is a BV-algebra; path-level representatives for the loop product via transversal intersection; Goldman bracket for surfaces.

5. DyerLashofOperations.lean — Dyer-Lashof operations on infinite loop spaces: homology operations Qˢ: Hₙ(X; 𝔽ₚ) → Hₙ₊ₛ(X; 𝔽ₚ) for infinite loop spaces; Kudo transgression theorem; Nishida relations between Steenrod operations and Dyer-Lashof operations; Araki-Kudo operations at p=2; computation of H₊(QS⁰; 𝔽₂) as a polynomial algebra on Dyer-Lashof generators; relationship to the Barratt-Eccles operad. Connects to SteenrodOperations.lean and InfiniteLoopSpace.lean.
```
**Directory:** `Path/Homotopy/` (QuasiCategory, InfinityCatLimits) and `Path/Algebra/` (FactorizationAlgebra, StringTopology, DyerLashofOperations)

---

### Armada 24: The Persistent Fleet — Topological Data Analysis and Computational Algorithms

*Theme: Bridge to applied topology — persistent homology, Mapper, stability theorems — plus formal decision procedures and complexity results for path normalization.*

```
1. PersistentHomology.lean — Persistent homology via computational paths: filtered simplicial complexes and their path-algebraic representation; persistence modules as functors (ℝ, ≤) → Vect; the structure theorem: decomposition into interval modules [b,d); birth-death pairs and persistence diagrams; path witnesses for the correspondence between bars and homological features; functoriality of the persistent diagram; Vietoris-Rips and Čech filtrations defined via path metrics.

2. StabilityTheorem.lean — Stability theorems for persistence: the bottleneck distance d_B between persistence diagrams; the interleaving distance d_I between persistence modules; the algebraic stability theorem d_B ≤ d_I; the Čech-Rips interleaving; computational path witnesses for stability under perturbation of input data; q-tame modules and their structure theorem; Lipschitz stability for sublevel set persistence.

3. PathNormalizationDecision.lean — Decision procedures and complexity for path normalization: formal proof that path equality in LND_EQ-TRS is decidable; complexity analysis of the normalization algorithm (upper bound on reduction length); word problem for the path algebra as a decision procedure; connection to the word problem for groups via fundamental group; rewriting modulo theory for path expressions; benchmarks on canonical examples (lens space paths, bouquet paths).

4. MapperAlgorithm.lean — The Mapper construction from TDA: definition of the Mapper functor (pullback cover → nerve); Reeb graph as 1-dimensional Mapper; path-algebraic characterization of Mapper output; relationship between Mapper and the underlying topology (convergence theorems); nerve lemma via computational paths; functoriality and stability of Mapper under refinement of covers.

5. ZigzagPersistence.lean — Extended persistence and zigzag persistence: zigzag persistence modules and their interval decomposition; extended persistence for closed manifolds (ordinary, relative, extended bars); diamond principle for computing zigzag persistence; levelset zigzag persistence; path-algebraic proof of the diamond principle; Poincaré duality in extended persistence; connection to the Mayer-Vietoris spectral sequence.
```
**Directory:** `Path/Algebra/` (PersistentHomology, StabilityTheorem, ZigzagPersistence) and `Path/Rewrite/` (PathNormalizationDecision) and `Path/Homotopy/` (MapperAlgorithm)

---

### Armada 25: The Sullivan Fortress — Rigidity, Fixed Points, and the Kervaire Endgame

*Theme: The deepest classical results — Sullivan conjecture, Kervaire invariant one, Serre's mod C theory, and phantom maps — completing the major open/resolved problems of algebraic topology.*

```
1. SullivanConjecture.lean — Miller's theorem / Sullivan conjecture: for a finite group G and a finite CW complex X, the space of pointed maps Map₊(BG, X) is weakly contractible after p-completion; Lannes' T-functor and its left-exactness; unstable modules over the Steenrod algebra and Lannes' characterization; path-level proof for G = ℤ/p and X a sphere; the Bousfield-Kan p-completion; fixed-point theorem: X^G ≃ Map(EG, X)^G for p-complete X.

2. KervaireInvariant.lean — The Kervaire invariant one problem: definition of the Kervaire invariant κ: π₄ₙ₊₂(S²ⁿ⁺¹) → ℤ/2; framed manifolds and the Kervaire invariant; the θⱼ elements in π_{2^{j+1}-2}(S⁰); Hill-Hopkins-Ravenel theorem: θⱼ does not exist for j ≥ 7; path-level formulation via equivariant stable homotopy theory; the slice filtration and the gap theorem; norm maps N: Sp^{C₂} → Sp^{C_{2^n}}.

3. SerreModC.lean — Serre's mod C theory: definition of Serre classes (classes of abelian groups closed under subgroups, quotients, extensions); Serre's mod C Hurewicz theorem; mod C Whitehead theorem; finiteness theorems: πₙ(Sᵏ) is finite for n ≠ k (odd k) and n ≠ k, 2k-1 (even k); path-level witnesses for the mod C fiber sequences; computation that π₃(S²) has ℤ summand and all other πₙ(S²) are finite for n > 3; C-isomorphisms and C-epimorphisms.

4. PhantomMaps.lean — Phantom maps between spectra and spaces: definition of phantom maps (zero on all finite subcomplexes); the phantom group Ph(X,Y); proof that Ph(X,Y) = 0 when Y has finitely generated homotopy groups; lim¹ characterization: Ph(X,Y) ≃ lim¹[Σ Xₙ, Y]; path-level construction of nonzero phantom maps; Gray's theorem on phantom maps between Eilenberg-MacLane spaces; universal phantom maps.

5. WaldhausenKTheory.lean — Waldhausen's algebraic K-theory of spaces: definition of Waldhausen categories (categories with cofibrations and weak equivalences); S•-construction and K-theory spectrum K(C); the fundamental theorem A(X) ≃ Σ^∞ X₊ × Wh^{Diff}(X); path witnesses for the cofinality theorem; additivity theorem for Waldhausen K-theory; the Dennis trace map K(R) → THH(R) connecting to existing THH.lean; comparison with Quillen K-theory for exact categories.
```
**Directory:** `Path/Homotopy/` (SullivanConjecture, KervaireInvariant, SerreModC, PhantomMaps) and `Path/Algebra/` (WaldhausenKTheory)

---

## Summary Table

| Armada | Theme | Files | Key Results |
|--------|-------|-------|-------------|
| **21** | EHP Siege | 5 | EHP sequence, Ganea fibrations, LS-category, improved Blakers-Massey, unstable stems |
| **22** | Chromatic Depths | 5 | Nilpotence, periodicity, formal group laws, Bott periodicity, Thom spectra |
| **23** | Infinity Vanguard | 5 | Quasi-categories, ∞-limits, factorization algebras, string topology, Dyer-Lashof |
| **24** | Persistent Fleet | 5 | Persistent homology, stability, decision procedures, Mapper, zigzag persistence |
| **25** | Sullivan Fortress | 5 | Sullivan conjecture, Kervaire invariant, Serre mod C, phantom maps, Waldhausen K-theory |

**Total new files:** 25
**Projected total after deployment:** 320 .lean files
**Required:** 0 sorry, 0 axioms, full computational paths framework

---

## Dependency Map

```
Armada 21 depends on:
  ├── FreudenthalSuspension.lean, JamesConstruction.lean (EHP)
  ├── HopfFibration.lean, HopfInvariant.lean (unstable stems)
  ├── BlakersMassey.lean (improved)
  └── Pi5S3.lean (low stems)

Armada 22 depends on:
  ├── ChromaticHomotopy.lean (nilpotence, periodicity)
  ├── KTheory.lean, CharacteristicClasses.lean (Bott)
  ├── StableHomotopy.lean, SpectrumTheory.lean (Thom)
  ├── SteenrodAlgebra.lean (Wu formula)
  └── BordismTheory.lean (Thom spectra)

Armada 23 depends on:
  ├── KanComplex.lean, SimplicialPath.lean (quasi-categories)
  ├── HomotopyLimitColimit.lean (∞-limits)
  ├── LittleCubesOperad.lean, OperadTheory.lean (factorization)
  ├── FreeLoopSpace.lean, PoincareDuality.lean (string topology)
  └── SteenrodOperations.lean, InfiniteLoopSpace.lean (Dyer-Lashof)

Armada 24 depends on:
  ├── CechCohomology.lean, PathHomology.lean (persistent)
  ├── Normalization.lean, PathTactic.lean (decision procedures)
  ├── MayerVietoris.lean (zigzag)
  └── NerveRealization.lean (Mapper)

Armada 25 depends on:
  ├── SteenrodAlgebra.lean, LocalizationTheory.lean (Sullivan)
  ├── EquivariantHomotopy.lean, StableHomotopy.lean (Kervaire)
  ├── HurewiczTheorem.lean, WhiteheadTheorem.lean (Serre mod C)
  ├── EilenbergMacLane.lean, SpectrumTheory.lean (phantom)
  └── THH.lean, KTheory.lean (Waldhausen)
```

---

*All hands on deck. No sorry. No axioms. No surrender.*
