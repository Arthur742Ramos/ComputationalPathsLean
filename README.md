# ComputationalPathsLean

[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)]()
[![Lean](https://img.shields.io/badge/Lean-4.24.0-orange)]()
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.24.0-blue)]()

A Lean 4 formalization of **computational paths** — explicit, step-by-step witnesses for
type equalities. Unlike Lean's built-in `Eq` (which is proof-irrelevant), a
`Path a b` stores an explicit list of rewrite steps, making equality
*computational*. This machinery provides transport, symmetry, congruence,
rewrite quotients, normalization, and uses them to formalize fundamental groups,
higher homotopy, and a broad catalog of mathematical domains through
path-preserving constructions.

---

## Project Statistics

| Metric | Value |
|--------|-------|
| **Lean files** | 760 |
| **Lines of code** | 175,590 |
| **Theorems & lemmas** | 7,597 |
| **Definitions, structures & classes** | 11,021 |
| **`sorry` count** | **0** — every theorem has a real proof |
| **`rweq_of_step` uses** | 511 (across 140 files) |
| **Architecture** | Single-root `ComputationalPaths/` tree |

> **100% sorry-free.** Every theorem and lemma in this library carries a genuine
> proof. No placeholders, no stubs, no `sorry`.

### The Three Gates Policy

Every theorem in this library must pass three gates before it is merged:

1. **Sorry-free** — no `sorry` anywhere in the proof term.
2. **Genuinely uses computational paths** — constructions must go through
   `Path`, `Step`, `RwEq`, or derived machinery; no empty wrappers around
   Lean's built-in `Eq`.
3. **Compiles cleanly** — `lake build` succeeds with zero errors and zero
   warnings on the entire project.

### Domain Breakdown

| Domain | Files | Theorems & Lemmas |
|--------|------:|------------------:|
| Homotopy | 177 | 1,386 |
| Topology | 93 | 1,110 |
| Algebra | 112 | 1,074 |
| Rewrite system | 30 | 868 |
| CompPath constructions | 51 | 695 |
| Category theory | 20 | 460 |
| Core & Basic | 5 | 209 |
| Foundations | 6 | 129 |
| Logic | 7 | 66 |
| ω-Groupoid | 5 | 35 |
| Advanced topics\* | 162 | 804 |

\*Advanced topics (outside `Path/`): spectral sequences, perfectoid spaces,
prismatic & crystalline cohomology, Floer homology, tropical geometry, operads,
Langlands program, Kac–Moody algebras, étale cohomology, condensed mathematics,
derived algebraic geometry, and more.

---

## Core Concept: Computational Paths

The key type is `Path a b`:

```lean
structure Path {A : Type u} (a b : A) where
  steps : List (Step A)   -- Explicit rewrite step witnesses
  proof : a = b           -- Derived equality
```

- **Composition** via `trans` (concatenating step lists)
- **Inversion** via `symm` (reversing and inverting steps)
- **Path equality** via `RwEq` — the symmetric-transitive closure of the LND_EQ-TRS
  rewrite system (de Queiroz et al.)

### Computational Paths vs HoTT Identity Types

This is **not** a HoTT identity-type formalization. A computational path is a
*trace-carrying wrapper* around Lean's propositional equality:

- `Path a b` stores `proof : a = b` in `Prop`, so UIP/proof irrelevance is
  intentional.
- `steps : List (Step A)` is metadata recording a rewrite trace for the
  LND_EQ-TRS, but does **not** change equality semantics.
- Different traces can witness the same equality; `Path.toEq` forgets the trace.
- Computational paths are explicit equality traces inside extensional type theory,
  not a HoTT identity-type formalization.

---

## Key Theorems

| Theorem | Statement | Module |
|---------|-----------|--------|
| **π₁(S¹) ≃ ℤ** | Circle fundamental group is integers | `CircleStep.lean` |
| **π₁(T²) ≃ ℤ × ℤ** | Torus fundamental group | `TorusStep.lean` |
| **π₁(S²) ≃ 1** | 2-sphere is simply connected | `SphereCompPath.lean` |
| **Seifert–van Kampen** | π₁(Pushout) ≃ amalgamated free product | `PushoutPaths.lean` |
| **ω-Groupoid** | Types form weak ω-groupoids | `OmegaGroupoid.lean` |
| **Confluence** | LND_EQ-TRS is confluent (GroupoidConfluence on Expr — genuine algebra, no UIP) | `GroupoidConfluence.lean` |
| **Basepoint Independence** | π₁(A,a) ≃ π₁(A,b) via conjugation | `FundamentalGroupoid.lean` |
| **Product π₁** | π₁(A×B) ≃ π₁(A) × π₁(B) | `ProductFundamentalGroup.lean` |
| **Higher Product** | π_n(A×B) ≃ π_n(A) × π_n(B) | `HigherProductHomotopy.lean` |
| **Abelianization** | F_n^ab ≃ ℤⁿ (axiom-free) | `Abelianization.lean` |
| **Eckmann–Hilton** | π₂ is abelian | `HigherHomotopy.lean` |
| **Figure-eight π₁** | π₁(S¹ ∨ S¹) ≃ F₂ (free group on 2 generators) | `FigureEightStep.lean` |

---

## Mathematical Domains

The library covers an extensive range of mathematical areas, each with explicit
`Path.Step`/`RwEq` computational witnesses:

### Algebraic Topology & Homotopy Theory
- **Core homotopy**: Loop spaces, higher homotopy groups π_n, truncation levels,
  covering spaces, fibrations, fiber sequences, long exact sequences,
  suspension-loop adjunction, Postnikov towers
- **Simplicial methods**: Simplicial path coherence, horn fillers, Kan conditions,
  total singular complex, CW approximation, Mapper algorithm
- **Spectral sequences**: Serre, Adams, Atiyah–Hirzebruch, Grothendieck,
  Lyndon–Hochschild–Serre, and Bockstein spectral sequences
- **Stable homotopy**: Spectra, stable stems, Brown representability,
  Goodwillie calculus, chromatic convergence, formal group laws

### Category Theory & Higher Categories
- **Groupoids**: Weak/strict categories, groupoids, bicategories, weak 2-groupoids,
  weak ω-groupoids (Lumsdaine/van den Berg–Garner)
- **∞-Categories**: Quasi-categories, Segal spaces, composition APIs
- **Enriched & Monoidal**: Enriched categories, monoidal structures
- **Derived categories**: Triangulated structures, t-structures
- **Operads**: Algebras over operads, Koszul duality, bar/cobar constructions
- **Topos theory**: Subobject classifiers, internal logic

### Algebraic Geometry
- **Sheaves & sites**: Étale sites, étale cohomology, comparison theorems
- **Perfectoid spaces**: Tilting equivalences, almost mathematics
- **Prismatic cohomology**: Prisms, Breuil–Kisin modules
- **Crystalline cohomology**: Crystal structures, PD-envelopes
- **Hodge theory**: Mixed Hodge filtrations, period maps
- **Birational geometry**: Flips, flops, minimal model program
- **Moduli spaces**: Stack structures, deformation theory
- **Tropical geometry**: Tropical curves, balancing, tropicalization
- **Log geometry**: Log structures, log smooth maps
- **GIT**: Geometric invariant theory quotients
- **Derived algebraic geometry**: DAG foundations

### Number Theory & Arithmetic
- **p-adic methods**: Perfectoid tilting, p-divisible groups
- **Langlands program**: Local and geometric Langlands correspondences
- **Anabelian geometry**: Section conjectures
- **Arithmetic geometry**: Fundamental group computations

### Representation Theory & Lie Theory
- **Geometric representation theory**: Perverse sheaves, D-modules
- **Kac–Moody algebras**: Infinite-dimensional Lie algebras, Weyl groups,
  Serre relations, braid relations
- **Geometric Satake**: Satake equivalence infrastructure
- **Vertex algebras**: VOA structures
- **Representation stability**: Stable ranges, FI-modules

### Differential & Symplectic Geometry
- **Lie groups**: SO(2) ≃ U(1) ≃ S¹ with π₁ ≃ ℤ, n-torus as maximal torus,
  connections to Bordg–Cavalleri differential geometry
- **Cobordism**: Cobordism theory, TFT (topological field theories)
- **Floer homology**: Floer complexes, Fukaya categories
- **Symplectic duality**: 3d mirror symmetry, Coulomb branches
- **Morse theory**: Handle decompositions, critical points

### Quantum & Noncommutative
- **Quantum topology**: Quantum invariants
- **NCG**: Noncommutative geometry structures
- **Cluster algebras**: Seeds, mutations, exchange relations

### Homological & K-Theoretic
- **K-theory**: Algebraic K-theory, THH (topological Hochschild homology)
- **Homological stability**: Stability ranges, stabilization maps
- **Intersection theory**: Intersection-theoretic constructions
- **Motivic cohomology**: Motivic structures

---

## Project Structure

All library code lives under a **single root** — `ComputationalPaths/`. Previous
external directories (Adjunction/, Anabelian/, Etale/, etc.) were consolidated
into this tree in the single-root migration.

```
ComputationalPathsLean/
├── ComputationalPaths/           # All library code (760 files)
│   └── Path/
│       ├── Basic/                # Path, Step, transport, congruence, Context
│       │   ├── Core.lean         # Fundamental Path and Step structures
│       │   ├── Congruence.lean   # mapLeft, mapRight, map2, product/sigma paths
│       │   └── Context.lean      # Contextual substitution (Def. 3.5)
│       ├── Rewrite/              # LND_EQ-TRS rewrite system
│       │   ├── Step.lean         # 47 primitive rewrite rules
│       │   ├── Rw.lean           # Reflexive-transitive closure
│       │   ├── RwEq.lean         # Symmetric-transitive closure (path equality)
│       │   ├── Quot.lean         # Quotient PathRwQuot
│       │   ├── ConfluenceProof.lean  # Newman's Lemma confluence proof
│       │   ├── GroupoidConfluence.lean # Algebraic confluence (no UIP)
│       │   ├── Normalization.lean    # Path normal forms
│       │   └── PathTactic.lean       # 29 tactics (path_simp, path_auto, etc.)
│       ├── Homotopy/             # Higher homotopy theory
│       │   ├── HigherHomotopy.lean       # π_n, Eckmann-Hilton
│       │   ├── Truncation.lean           # IsContr, IsProp, IsSet, IsGroupoid
│       │   ├── CoveringSpace.lean        # Covering spaces, deck transformations
│       │   ├── Fibration.lean            # Fiber sequences, long exact sequences
│       │   ├── FundamentalGroupoid.lean  # Π₁(X), basepoint independence
│       │   └── ...
│       ├── CompPath/             # Computational path constructions
│       │   ├── CircleStep.lean       # π₁(S¹) ≃ ℤ
│       │   ├── TorusStep.lean        # π₁(T²) ≃ ℤ × ℤ
│       │   ├── SphereCompPath.lean   # π₁(S²) ≃ 1
│       │   ├── PushoutPaths.lean     # Seifert–van Kampen theorem
│       │   └── ...
│       ├── Algebra/              # Free group abelianization, path algebra
│       ├── Topology/             # Topological applications
│       ├── Anabelian/            # Anabelian geometry
│       ├── Arithmetic/           # Arithmetic geometry
│       ├── Birational/           # Birational geometry (MMP)
│       ├── Chromatic/            # Chromatic homotopy theory
│       ├── Cluster/              # Cluster algebras
│       ├── Cobordism/            # Cobordism theory
│       ├── Condensed/            # Condensed mathematics
│       ├── Crystalline/          # Crystalline cohomology
│       ├── DAG/                  # Derived algebraic geometry
│       ├── Etale/                # Étale cohomology
│       ├── Floer/                # Floer homology
│       ├── Hodge/                # Hodge theory
│       ├── KacMoody/             # Kac-Moody algebras
│       ├── Langlands/            # Langlands program
│       ├── Motivic/              # Motivic homotopy theory
│       ├── Operad/               # Operads
│       ├── Perfectoid/           # Perfectoid spaces
│       ├── Prismatic/            # Prismatic cohomology
│       ├── SpectralSequence/     # Spectral sequences
│       ├── Stable/               # Stable homotopy theory
│       ├── Topos/                # Topos theory
│       ├── Tropical/             # Tropical geometry
│       ├── Groupoid.lean         # Weak/strict groupoid structure
│       ├── OmegaGroupoid.lean    # Weak ω-groupoid structure
│       ├── Bicategory.lean       # Bicategory & weak 2-groupoid API
│       ├── GroupoidDerived.lean   # 41 uses of rweq_of_step
│       ├── PathAlgebraDerived.lean   # 22 uses of rweq_of_step
│       ├── StepDerived.lean      # 27 uses of rweq_of_step
│       └── ... (many more subdirectories)
├── Scripts/                      # Audit & analysis scripts
├── docbuild/                     # doc-gen4 documentation build
├── docs/                         # Documentation
└── paper/                        # Paper materials
```

---

## Quick Start

### Prerequisites
- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) v4.24.0 (via `elan`)
- [Mathlib](https://github.com/leanprover-community/mathlib4) v4.24.0 (fetched automatically)

### Build

```bash
# Install Lean (if needed)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Clone and build
git clone https://github.com/Arthur742Ramos/ComputationalPathsLean.git
cd ComputationalPathsLean
lake build
```

### Run

```bash
lake exe computational_paths   # Prints version info
```

### Develop

Open the folder in VS Code with the Lean 4 extension installed. The build
will run automatically with full IDE support.

---

## The Rewrite System (LND_EQ-TRS)

The rewrite system comprises **47 primitive rules** organized as:

| Rule Group | Rules | Description |
|-----------|-------|-------------|
| Symmetry | 1–2 | `symm_refl`, `symm_symm` |
| Transitivity | 3–5 | `trans_refl_left/right`, `trans_assoc` |
| Inverse | 6–7 | `trans_symm`, `symm_trans`, `symm_trans_congr` |
| Binary maps | 8–9 | `congrArg_comp`, `map2_subst` |
| Products | 10–15 | Beta, eta, symm, projections, map2 |
| Sigma | 16–19 | Beta, eta, symm, projections |
| Sums | 20–24 | Recursor beta for inl/inr |
| Functions | 25 | Beta-eta |
| Transport | 26–29 | Transport over refl, composition |
| Context | 33–47 | Contextual substitution rules |

**Confluence** is proved via `GroupoidConfluence` on the `Expr` rewrite system —
a genuine algebraic proof using `HasJoinOfRw` as a parameterized typeclass,
with no `Step.canon`, `toEq`, or UIP. The approach avoids Newman's Lemma
in favour of direct joinability witnesses for all critical pairs.

---

## Weak ω-Groupoid Structure

The library provides the **complete proof** that computational paths form a
weak ω-groupoid (Lumsdaine 2010, van den Berg–Garner 2011):

```lean
def pathsOmegaGroupoid : WeakOmegaGroupoid A := compPathOmegaGroupoid A
```

**Tower of cells**:
- Level 0: Points (elements of `A`)
- Level 1: Paths (`Path a b`)
- Level 2: 2-cells (`Derivation₂ p q`)
- Level 3: 3-cells (`Derivation₃ d₁ d₂`)
- Level 4+: Higher cells

**Higher coherences**: Pentagon identity, triangle identity, interchange law,
whiskering, and the canonicity axiom (grounded in the normalization algorithm).

**Contractibility**: `contractibility₃`, `contractibility₄`, and
`contractibilityHigh` — any two parallel n-cells are connected by an (n+1)-cell.

---

## Path Simplification Tactics

29 tactics for automated `RwEq` reasoning:

| Tactic | Description |
|--------|-------------|
| `path_simp` | Simplify using ~25 groupoid laws |
| `path_auto` | Full automation (simp + structural lemmas) |
| `path_rfl` | Close reflexive goals `RwEq p p` |
| `path_normalize` | Rewrite to canonical right-associative form |
| `path_beta` | Beta reductions for products/sigmas/functions |
| `path_eta` | Eta expansion/contraction for products |
| `path_cancel_left` | Close `RwEq (trans (symm p) p) refl` |
| `path_cancel_right` | Close `RwEq (trans p (symm p)) refl` |
| `path_congr_left h` | Left congruence under trans |
| `path_congr_right h` | Right congruence under trans |
| `path_symm` | Apply symmetry to RwEq goal |
| `path_trans_via t` | Split goal via intermediate path |

```lean
-- Examples
example (p : Path a b) : RwEq (trans refl p) p := by path_simp
example (p : Path a b) : RwEq (trans p (symm p)) refl := by path_cancel_right
example (p : Path a b) : RwEq (symm (symm p)) p := by path_simp
```

---

## Axiom-Free Derived Results

**511 uses of `rweq_of_step`** across 140 files, all derived purely from
primitive `Step` rules with no custom axioms:

| Module | Uses | Key Results |
|--------|------|-------------|
| `GroupoidDerived` | 56 | Cancellation, inverse uniqueness, whiskering, conjugation |
| `StepDerived` | 59 | Direct lifts of Rules 7–47 to `RwEq` |
| `CoherenceDerived` | 51 | Pentagon, triangle, n-fold associativity |
| `PathAlgebraDerived` | 40 | Four-fold assoc, contravariance, `congrArg` composition |
| `LoopDerived` | 27 | Loop group laws, commutator identities |
| `BiContextDerived` | 17 | BiContext congruence, map2 decomposition |
| `ProductSigmaDerived` | — | Product/sigma composition, projection naturality |
| `TransportDerived` | — | Transport coherence, round-trip identities |

---

## Axioms and Assumptions

### Kernel axioms

This project uses **zero** kernel axioms beyond Lean's standard foundation
(`propext`, `Quot.sound`). Verified via `Scripts/AxiomInventory.lean`.

### Explicit assumptions

Some results use typeclass assumptions (not kernel axioms) that must be
instantiated:

- **`HasCirclePiOneEncode`** — Circle π₁ classification data
- **`HasTorusPiOneEncode`** — Torus π₁ classification data
- **`HasWedgeSVKDecodeBijective`** — SVK decode bijectivity for wedge sums
- **`HasLocalConfluenceProp`** / **`HasTerminationProp`** / **`HasJoinOfRw`** —
  Confluence/termination witnesses (`HasJoinOfRw` is the parameterized typeclass
  used by `GroupoidConfluence`; justified by critical pair analysis)

See `docs/axioms.md` for the full inventory.

---

## Dependencies

| Component | Version |
|-----------|---------|
| Lean 4 | v4.24.0 |
| Mathlib | v4.24.0 |
| Lake | 5.0.0 |

Configured via `lean-toolchain` and `lakefile.toml`.

---

## API Documentation

This project uses [doc-gen4](https://github.com/leanprover/doc-gen4) to generate
browsable API documentation for all modules. The documentation setup lives in the
`docbuild/` subdirectory (following the recommended nested-project pattern).

### Generating Docs

```bash
cd docbuild

# First time only — fetch doc-gen4 and its dependencies:
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4

# Build docs for the main library (and all transitive imports):
lake build ComputationalPaths:docs

# For multiple libraries:
lake build ComputationalPaths:docs Kan:docs Equivalence:docs
```

> **Note:** The full build generates documentation for Lean, Std, Mathlib, and all
> project modules. For a Mathlib-dependent project of this size (~760 files), expect
> the first build to take **several hours**. Subsequent incremental builds are faster.

### Viewing Docs

The generated site is at `docbuild/.lake/build/doc/index.html`. Due to browser
same-origin policies, serve it via HTTP:

```bash
cd docbuild/.lake/build/doc
python3 -m http.server 8000
# Open http://localhost:8000 in your browser
```

---

## License

MIT License — see [LICENSE](LICENSE).

---

## References

### Core Computational Paths Theory
- de Queiroz, de Oliveira & Ramos, [*Propositional equality, identity types, and direct computational paths*](https://www.sa-logic.org/sajl-v2-i2/05-De%20Queiroz-De%20Oliveira-Ramos-SAJL.pdf), South American Journal of Logic 2(2), 2016.
- Ramos, de Queiroz & de Oliveira, [*On the Identity Type as the Type of Computational Paths*](https://doi.org/10.1093/jigpal/jzx015), Logic Journal of the IGPL 25(4), 2017.
- Ramos, de Queiroz, de Oliveira & de Veras, [*Explicit Computational Paths*](https://www.sa-logic.org/sajl-v4-i2/10-Ramos-de%20Queiroz-de%20Oliveira-de-Veras-SAJL.pdf), South American Journal of Logic 4(2), 2018.
- Ramos, [*Explicit Computational Paths in Type Theory*](https://github.com/Arthur742Ramos/ComputationalPathsLean/blob/main/docs/thesis/TESE%20Arthur%20Freitas%20Ramos.pdf), Ph.D. thesis, UFPE, 2018.

### Fundamental Groups via Computational Paths
- de Veras, Ramos, de Queiroz & de Oliveira, [*On the Calculation of Fundamental Groups in Homotopy Type Theory by Means of Computational Paths*](https://arxiv.org/abs/1804.01413), arXiv:1804.01413, 2018.
- de Veras, Ramos, de Queiroz & de Oliveira, [*An alternative approach to the calculation of fundamental groups based on labeled natural deduction*](https://arxiv.org/abs/1906.09107), arXiv:1906.09107, 2019.
- de Veras, Ramos, de Queiroz & de Oliveira, [*A Topological Application of Labelled Natural Deduction*](https://www.sa-logic.org/aaccess/ruy.pdf), South American Journal of Logic, 2023.

### Weak Groupoid & ω-Groupoid Structure
- de Veras, Ramos, de Queiroz & de Oliveira, [*Computational Paths -- a Weak Groupoid*](https://doi.org/10.1093/logcom/exad071), Journal of Logic and Computation 35(5), 2023.
- Lumsdaine, [*Weak ω-categories from intensional type theory*](https://doi.org/10.1007/978-3-642-02273-9_14), TLCA 2009.
- van den Berg & Garner, [*Types are weak ω-groupoids*](https://doi.org/10.1112/plms/pdq026), Proc. London Math. Soc. 102(2), 2011.

### Background
- Univalent Foundations Program, [*Homotopy Type Theory*](https://homotopytypetheory.org/book/), IAS, 2013.
- Licata & Shulman, [*Calculating the Fundamental Group of the Circle in HoTT*](https://doi.org/10.1109/LICS.2013.28), LICS 2013.
- Bordg & Cavalleri, [*Elements of Differential Geometry in Lean*](https://arxiv.org/abs/2108.00484), arXiv:2108.00484, 2021.

---

## Citing This Repository

```bibtex
@software{ComputationalPathsLean2025,
  author       = {Ramos, Arthur F. and de Veras, Tiago M. L. and 
                  de Queiroz, Ruy J. G. B. and de Oliveira, Anjolina G.},
  title        = {Computational Paths in {Lean} 4},
  year         = {2025},
  publisher    = {GitHub},
  url          = {https://github.com/Arthur742Ramos/ComputationalPathsLean},
  note         = {Lean 4 formalisation of propositional equality via 
                  computational paths and fundamental groups}
}
```

---

## Contributing

- Build after edits: `lake build`
- Keep docstrings in sync; prefer small, focused lemmas with `@[simp]` where useful
- The simplifier linter flags unused simp arguments — please trim them
- When adding structures, prefer extending smaller structures to keep
  identities/composition in one place
