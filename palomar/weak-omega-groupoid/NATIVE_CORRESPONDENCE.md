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
| `RwEq` / `RwProp` | `ComputationalPaths.Path.Rewrite.RwEq` | proof-relevant rewrite equality and its mere proposition |
| `Derivation3` | `OmegaGroupoid.Derivation₂` / `Derivation₃` in `ComputationalPaths/Path/OmegaGroupoid.lean` | level-2 witnesses and level-3 comparisons |
| `MetaStep3.rweq_transport` | `MetaStep₃.rweq_transport` | proof-irrelevance transport between parallel witnesses |
| `contractibility3` | `OmegaGroupoid.contractibility₃` | central higher contraction principle |
| `contractibilityHigher` | `OmegaGroupoid.contractibility₄` and the higher tail | same contraction pattern at subsequent levels |
| `pentagon_coherence` / `triangle_coherence` | `OmegaGroupoid.pentagonCoherence` / `triangleCoherence` | named coherence cells |
| `interchange_coherence` / `hcompAlt` | `EckmannHiltonProof.interchange` / `hcomp'` | alternative horizontal-composition route |
| `eckmann_hilton_coherence` | `EckmannHiltonProof.eckmann_hilton` | loop-composition coherence |

The standalone project intentionally selects the paper's central path and
higher-coherence construction. It does not claim to reproduce the native
normalizer, Newman-style confluence proof, circle/HIT applications, or stable
homotopy computations. Those exclusions are part of the public metadata, so a
Palomar reader can distinguish the independently replayable boundary from the
larger repository.
