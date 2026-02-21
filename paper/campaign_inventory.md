# Campaign Inventory: Waves 2–5 Complete Listing

## Overview

This document provides a complete inventory of all new files, theorems,
and their mathematical significance from the Waves 2–5 campaign.

## New Lean Files

### Wave 2 (Subsingleton audit, deepening)
Files modified (no new files in this wave — fixes to existing files).

### Wave 3 (Termination, 3-cells, word problem, Squier)
| File | Lines | Key Theorems |
|------|-------|-------------|
| `Path/Rewrite/TerminationTight.lean` | ~170 | `step_lex_decrease`, tight termination measure |
| `Path/Polygraph/ThreeCells.lean` | ~160 | `DerivEquiv`, `nontrivial_three_cell_exists` |
| `Path/Rewrite/WordProblem.lean` | ~150 | `decidable_wp`, `wp_correct`, `wp_complete` |
| `Path/Rewrite/Squier.lean` | ~160 | `squier_hypotheses`, `convergent`, all CP resolutions |
| `Path/Rewrite/CriticalPairEnum.lean` | ~160 | 9 critical pair families enumerated |

### Wave 4 (Coherent presentation, NbE, typed paths, benchmarks)
| File | Lines | Key Theorems |
|------|-------|-------------|
| `Path/Polygraph/CoherentPresentation.lean` | ~250 | `coherentPresentation_groupoid`, `fdt_of_coherent` |
| `Path/Polygraph/RwEqDerivation.lean` | ~140 | `RwEqDeriv`, `hcomp`, `interchange` |
| `Path/Rewrite/NormByEval.lean` | ~200 | NbE homomorphism, normalization |
| `Path/Rewrite/TypedExpr.lean` | ~150 | Typed expression framework |
| `Path/Rewrite/Benchmark.lean` | ~100 | Performance benchmarks |

### Wave 5 (Homotopy basis, transport analysis, Garside, related work)
| File | Lines | Key Theorems |
|------|-------|-------------|
| `Path/Polygraph/HomotopyBasis.lean` | ~295 | `homotopyBasis_complete`, `acyclic_above_3`, `coherentPresentation3d` |
| `Path/Rewrite/TransportConfluence.lean` | ~265 | `transport_groupoid_disjoint`, `all_transport_cps_joinable` |
| `Path/Polygraph/GarsideTheory.lean` | ~200 | `no_universal_divisor_witness`, `posRwEq_iff_toRW` |

## New Documentation Files

### Wave 2
- `paper/wave2_core_fixes.md` — Core subsingleton audit results

### Wave 3
- `paper/wave3_termination.md` — Termination tightness analysis
- `paper/wave3_3cells.md` — 3-cells and derivation equivalence
- `paper/wave3_wordproblem.md` — Word problem decision procedure
- `paper/wave3_squier.md` — Squier's theorem connection
- `paper/wave3_verify.md` — Verification report

### Wave 5
- `paper/wave5_transport.md` — Transport confluence analysis
- `paper/wave5_related.md` — Related work comparison
- `paper/campaign_inventory.md` — This file

## Key Theorems by Mathematical Significance

### Tier 1: Core Mathematical Results
| Theorem | File | Significance |
|---------|------|-------------|
| `confluence` | GroupoidConfluence.lean | Confluence of 10-rule completed TRS |
| `cstep_termination` | GroupoidConfluence.lean | Well-foundedness of CStep |
| `toRW_invariant` | GroupoidConfluence.lean | Free group interpretation |
| `reach_canon` | GroupoidConfluence.lean | Every expr reduces to canonical form |
| `fdt_of_coherent` | CoherentPresentation.lean | All 9 CP families are joinable |
| `homotopyBasis_complete` | HomotopyBasis.lean | 9 families = homotopy basis |

### Tier 2: Structural Results
| Theorem | File | Significance |
|---------|------|-------------|
| `nontrivial_three_cell_exists` | ThreeCells.lean | Distinct derivations of same fact |
| `derivEquivSetoid` | ThreeCells.lean | DerivEquiv is equivalence relation |
| `vcomp_respects_equiv` | ThreeCells.lean | 3-cells compose correctly |
| `hcomp_respects_equiv` | ThreeCells.lean | Horizontal composition well-defined |
| `squier_hypotheses` | Squier.lean | All Squier hypotheses verified |
| `coherentPresentation3d` | HomotopyBasis.lean | 3D coherent presentation |

### Tier 3: Decision Procedures
| Theorem | File | Significance |
|---------|------|-------------|
| `homotopy_basis_decides_rwEq` | HomotopyBasis.lean | ExprRwEq ↔ toRW equality |
| `posRwEq_iff_toRW` | GarsideTheory.lean | Faithful embedding in free group |
| `all_transport_cps_joinable` | TransportConfluence.lean | Transport CPs all join |

### Tier 4: Negative / Structural Results
| Theorem | File | Significance |
|---------|------|-------------|
| `no_universal_divisor_witness` | GarsideTheory.lean | No Garside element in free monoid |
| `transport_groupoid_disjoint` | TransportConfluence.lean | Sort separation |
| `partialGarside_contains` | GarsideTheory.lean | Partial Garside for bounded fragments |

## Statistics

### Code Metrics
- **New Lean files (Waves 3–5)**: 13
- **New documentation files**: 9
- **Total new Lean lines**: ~2,400+
- **Total sorry count**: 0
- **Total admit count**: 0
- **Full build status**: ✅ (6186 jobs)

### Mathematical Content
- **Rewrite rules**: 10 CStep families (8 base + 2 completion)
- **Critical pair families**: 9 (all resolved)
- **3-cell generators**: 9 (form homotopy basis)
- **Polygraph dimensions**: 0=atoms, 1=Expr, 2=CStep, 3=DerivEquiv, ≥4=none
- **Termination measure**: lexicographic (weight, leftWeight)
- **Decidable word problem**: via toRW into free group

### Proof Techniques
1. **Free group interpretation** — novel confluence proof strategy
2. **Knuth-Bendix completion** — discovery of cancellation rules
3. **Lexicographic termination** — polynomial interpretation + leftWeight
4. **Guiraud-Malbos construction** — coherent presentation from convergent TRS
5. **Sort separation** — transport/groupoid orthogonality analysis
