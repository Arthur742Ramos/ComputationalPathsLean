# Correspondence with the native development

The Palomar project is a standalone statement boundary, not a thin wrapper.
Palomar checks the Challenge import closure and therefore does not permit the
Challenge to import `ComputationalPaths.Path.OmegaGroupoid` from this
repository. The compact namespace below reproduces the interfaces needed for
the selected claims so that Comparator can compare an independent Solution.

| Palomar boundary | Native repository development | Relationship |
| --- | --- | --- |
| `Path.trace` and `Path.proof` | `ComputationalPaths.Path` in `ComputationalPaths/Path/Basic.lean` | trace-carrying equality witness |
| `Step` | `ComputationalPaths.Path.Rewrite.Step` | explicit associativity, unit, inverse, and context rules |
| `RwEq` / `RwProp` / `Derivation2` | `ComputationalPaths.Path.Rewrite.RwEq` and `OmegaGroupoid.Derivation₂` | proof-relevant rewrite data and its mere proposition |
| `MetaStep3.rweq_transport` | `MetaStep₃.rweq_transport` in `OmegaGroupoid` | proof-irrelevance transport between parallel witnesses |
| `Derivation3` | `OmegaGroupoid.Derivation₃` | level-3 comparisons of 2-cell data |
| `MetaStep4` / `Derivation4` | `OmegaGroupoid.MetaStep₄` / `Derivation₄` | explicit level-4 boundary |
| `MetaStepHigh` / `DerivationHigh` | `OmegaGroupoid.DerivationHigh` | indexed higher tail; the standalone carrier is intentionally schematic |
| `contractibility3` | `ContractibilityIrrelevance.contractibility₃_native_irrel` | central proof-irrelevance contraction principle |
| `contractibility4` / `contractibilityHigher` | `OmegaGroupoid.contractibility₄` / higher-cell contraction | same pattern at subsequent levels |
| `pentagonLeft` / `pentagonRight` | `OmegaGroupoid.pentagonLeft` / `pentagonRight` | two-step and three-step associativity routes |
| `pentagon_coherence` / `triangle_coherence` | `ContractibilityIrrelevance.pentagonCoherence_irrel` / `triangleCoherence_irrel` | derived named coherence cells |
| `interchange_coherence` | `OmegaGroupoid.Derived.derive_interchange` (generalized here to four composable cells) | full vertical/horizontal interchange route |
| `eckmann_hilton_coherence` | `EckmannHiltonProof.eckmann_hilton` | loop-composition coherence |
| `CellType` / `WeakOmegaGroupoidBoundary` / `compPathOmegaGroupoidBoundary` | `OmegaGroupoid.CellType` / `WeakOmegaGroupoid` / `compPathOmegaGroupoid` | selected cell-tower boundary and canonical assembly |

The standalone project intentionally selects the paper's central path and
higher-coherence construction. It does not claim to reproduce the native
normalizer, Newman-style confluence proof, circle/HIT applications, stable
homotopy computations, or every globular/source-level theorem. The Challenge
uses no native import because Palomar's Challenge closure forbids repository-
local source; the duplicate surface is therefore an auditable reimplementation,
not a hidden wrapper. Those exclusions and this version distinction are part
of the public metadata, so a Palomar reader can distinguish the replayable
boundary from the larger repository.
