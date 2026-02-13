# Armada Plan — ComputationalPathsLean

## What is an Armada?

An **armada** is a batch deployment of 5 Lean 4 formalization files covering a specific mathematical theme. Each file formalizes a topic using the ComputationalPathsLean framework — meaning genuine `Path`/`Step`/`RwEq` integration, not shallow wrappers.

### Protocol

1. **Tool:** `copex fleet "prompt" -m gpt-5.3-codex -r xhigh`
2. **Batch size:** 5 files per armada
3. **Quality bar:** Zero sorry, zero axiom, genuine Path integration
4. **Fix first, nuke last** (v2 protocol) — broken files get a repair attempt before deletion
5. **Deepening pass** — review files post-deployment to ensure non-shallow integration

### File Requirements

- Import from `ComputationalPaths.Path.{Step,Basic,Rewrite}`
- Use `Path a b` for equalities (not bare `Eq`)
- Domain-specific `Step` inductive types where appropriate
- `Path.trans`/`Path.symm` compositions
- At least one `RwEq` or multi-step construction per file
- Minimum 150 lines of substantive content
- Place files in appropriate subdirectory (`Path/Algebra/`, `Path/Topology/`, `Path/Homotopy/`, etc.)

---

## Completed Armadas

### Foundation Phase (Armadas I–VI, overnight batch)
Core topology and homotopy theory foundations.

### Expansion Phase (Armadas 7–20)
| # | Theme |
|---|-------|
| 7–8 | Brown representability, obstruction theory |
| 9–10 | Postnikov towers, loop spaces |
| 11–12 | Operads, equivariant homotopy |
| 13–14 | Smash products, cofiber sequences |
| 15–16 | Stable categories, chromatic homotopy |
| 17–18 | Rational homotopy, motivic homotopy |
| 19–20 | THH, algebraic K-theory |

### Deep Formalization Phase (Armadas 31–41)
| # | Theme | Key Topics |
|---|-------|------------|
| 31 | Higher Category Theory | Quasi-categories, ∞-limits, Yoneda |
| 32 | Homological Algebra II | Derived categories, spectral sequences |
| 33 | Algebraic K-Theory & Cobordism | Quillen K-theory, Thom spectra |
| 34 | Differential Topology & Morse | Morse theory, handle decomposition |
| 35 | Sheaf Theory & Topos | Grothendieck topologies, classifying topos |
| 36 | Motivic & Arithmetic | Motivic cohomology, étale homotopy |
| 37 | Quantum & TQFT | TQFT axioms, Jones polynomial |
| 38 | Geometric Group Theory | Hyperbolic groups, Bass-Serre theory |
| 39 | Symplectic & Contact | Symplectic manifolds, contact structures |
| 40 | Operads & Deformation | A∞/E∞ operads, deformation quantization |
| 41 | Noncommutative Geometry | Spectral triples, cyclic homology |

### Applied Mathematics Phase (Armadas 42–61)
| # | Theme | Key Topics |
|---|-------|------------|
| 42 | Number Theory | Class field theory, Galois reps, modular forms |
| 43–47 | Various fleets | Prime number theorem, Riemann zeta, Dirichlet, sieves |
| 48–57 | Mathematical Physics | Gauge theory, Ricci flow, mirror symmetry, string topology |
| 58 | Representation Theory | Lie algebras, quantum groups, symmetric functions |
| 59 | Differential Geometry | Riemannian geometry, fiber bundles |
| 60 | Functional Analysis | Banach/Hilbert spaces, spectral theory, distributions |
| 61 | Algebraic Topology II | Stable homotopy, K-theory, cobordism, persistent homology |

### Current Phase (Armadas 62–64, running)
| # | Theme | Key Topics |
|---|-------|------------|
| 62 | Model Categories | Model categories, derived categories, homotopy limits |
| 63 | Arithmetic Geometry | Arithmetic schemes, p-adic Hodge, class field theory |
| 64 | Higher Algebra & Chromatic | E_n algebras, Brown representability, Goodwillie calculus, THH |

---

## Future Armada Candidates

| Theme | Topics |
|-------|--------|
| Derived Algebraic Geometry | Derived schemes, ∞-stacks, deformation contexts |
| Brave New Algebra | Structured ring spectra, modules over E∞-rings |
| Tropical Geometry | Tropical curves, tropical intersection theory |
| Homotopical Combinatorics | Simplicial/cubical sets, dendroidal sets |
| Constructive Mathematics | Constructive analysis, Bishop-style formalization |
| Perfectoid Spaces | Tilting, almost mathematics, perfectoid rings |
| Higher Gauge Theory | 2-groups, gerbes, parallel transport |
