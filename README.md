# Computational Paths (Lean 4)

Lean 4 formalisation of propositional equality via explicit computational paths and rewrite equality. It provides a practical kernel for transport, symmetry, congruence, rewrite quotients, and normalisation — and uses this machinery to formalise fundamental groups of higher-inductive types.

## Highlights
- **Weak ω-groupoid structure**: Complete proof that computational paths form a weak ω-groupoid with all coherence laws (pentagon, triangle) and contractibility at higher dimensions.
- **Derived groupoid theorems** (axiom-free): Cancellation laws, uniqueness of inverses, mixed trans/symm cancellation, whiskering, and conjugation — all derived from primitive Step rules with no custom axioms.
- **Path algebra derived results** (axiom-free): Four-fold associativity, symmetry-transitivity interactions, congruence composition, pentagon components, and Eckmann-Hilton preparation lemmas.
- **Higher homotopy groups π_n**: Iterated loop spaces (Loop2Space, Loop3Space), π₂(A,a) via derivation quotients, Eckmann-Hilton argument proving π₂ is abelian, and π₂(S²) ≅ 1.
- **Truncation levels (n-types)**: Full hierarchy connecting ω-groupoid to HoTT: IsContr → IsProp → IsSet → IsGroupoid, with all types automatically 1-groupoids via contractibility₃.
- **Eilenberg-MacLane spaces K(G,n)**: Characterization of K(G,1) spaces with circle as K(ℤ,1), group structures, and loop space property Ω(K(G,n+1)) ≃ K(G,n).
- **Fibrations and fiber sequences**: Fiber types, type families as fibrations, path lifting, connecting map ∂ : π₁(B) → F, and long exact sequence of homotopy groups.
- **Hopf fibration**: S¹ → S³ → S² fiber bundle with S³ as suspension of S², Hopf map, fiber equivalence to circle, long exact sequence application, and π₁(S³) = 1.
- **π₂(S²) ≃ ℤ**: Second homotopy group of the 2-sphere via Hopf fibration long exact sequence, with connecting map isomorphism ∂ : π₂(S²) → π₁(S¹) ≃ ℤ.
- **π₃(S²) ≃ ℤ**: Third homotopy group of the 2-sphere via Hopf fibration, with π₃(S³) ≃ ℤ and isomorphism p_* : π₃(S³) → π₃(S²). Generator is the Hopf map η with Hopf invariant 1.
- **π₄(S³) ≃ ℤ/2ℤ**: First torsion in homotopy groups. Generator is Ση (suspended Hopf map). Key property: 2·Ση = 0, demonstrating finite-order elements in higher homotopy groups.
- **Quaternionic Hopf fibration**: S³ → S⁷ → S⁴ with π₇(S⁴) ≃ ℤ. Generator ν (quaternionic Hopf map) with Hopf invariant 1.
- **Octonionic Hopf fibration**: S⁷ → S¹⁵ → S⁸ with π₁₅(S⁸) ≃ ℤ. Generator σ (octonionic Hopf map). Full exact sequence typeclass infrastructure. Completes the four Hopf fibrations. Adams' theorem: only four Hopf fibrations exist (real, complex, quaternionic, octonionic).
- **π₆(S³) ≃ ℤ/12ℤ**: First non-2-torsion homotopy group of spheres. Generator ν' with order 12. Demonstrates the complexity of higher homotopy beyond the 2-primary component.
- **π₂(RP²) ≃ ℤ**: Second homotopy group of projective plane via covering space S² → RP². Shows non-simply-connected spaces can have non-trivial higher homotopy.
- **James construction & stable stems**: J(X) ≃ ΩΣX gives computational approach to stable homotopy. Complete stable stems πₛ₁ through πₛ₇: πₛ₁ ≃ ℤ/2ℤ (η), πₛ₂ ≃ ℤ/2ℤ (η²), πₛ₃ ≃ ℤ/24ℤ (ν), πₛ₄ = 0, πₛ₅ = 0, πₛ₆ ≃ ℤ/2ℤ (ν²), πₛ₇ ≃ ℤ/240ℤ (σ).
- **Adams' H-space theorem**: Sⁿ admits H-space structure iff n ∈ {0, 1, 3, 7}. Proves S², S⁴, S⁵, S⁶, ... are NOT H-spaces. Only 1 axiom needed.
- **Freudenthal suspension theorem**: Σ : π_n(X) → π_{n+1}(ΣX) is iso when n < 2k-1 (X is (k-1)-connected). Key result: π_n(Sⁿ) ≃ ℤ for all n ≥ 1. Stable homotopy groups πₛ_0 ≃ ℤ, πₛ_1 ≃ ℤ/2ℤ (Hopf element η).
- **Suspension-loop adjunction**: Pointed types and maps infrastructure, suspension as pointed type, adjunction map construction, and Freudenthal suspension theorem foundations.
- **Seifert-van Kampen theorem**: Full encode-decode proof that π₁(Pushout) ≃ π₁(A) *_{π₁(C)} π₁(B) (amalgamated free product), with special case π₁(A ∨ B) ≃ π₁(A) * π₁(B) for wedge sums.
- **Lens spaces L(p,q)**: π₁(L(p,q)) ≃ ℤ/pℤ for all coprime p,q via Heegaard decomposition and SVK. Includes general `GeneralLensSpace p q` definition with coprimality requirement. First example of SVK producing **finite cyclic groups** (complementing infinite groups ℤ, ℤ×ℤ, ℤ*ℤ). Requires `HasLensPiOneEncode` or `HasGeneralLensPiOneEncode`.
- **Orientable genus-g surfaces** (Σ_g): Complete proof that π₁(Σ_g) ≃ ⟨a₁,b₁,...,a_g,b_g | [a₁,b₁]...[a_g,b_g] = 1⟩ (surface group presentation), with special cases for sphere (g=0), torus (g=1), and non-abelian higher genus (g≥2).
- **Non-orientable surfaces** (N_n): Complete proof that π₁(N_n) ≃ ⟨a₁,...,a_n | a₁²...a_n² = 1⟩ for genus-n non-orientable surfaces (n crosscaps). Special cases: RP² (n=1) with π₁ ≃ ℤ/2ℤ, Klein bottle (n=2) with π₁ ≃ ℤ ⋊ ℤ. Euler characteristic χ(N_n) = 2 - n.
- **2-Sphere** (S²): π₁(S²) ≅ 1 (trivial) via SVK applied to the suspension decomposition Σ(S¹), plus π₂(S²) ≅ 1 via contractibility₃.
- **Figure-eight space** (S¹ ∨ S¹): π₁ ≃ ℤ * ℤ (free group on 2 generators), demonstrating non-abelian fundamental groups.
- **Bouquet of n circles** (∨ⁿS¹): π₁ ≃ F_n (free group on n generators), generalizing the figure-eight to arbitrary n with special cases n=0 (trivial), n=1 (ℤ), n=2 (ℤ * ℤ).
- **Path simplification tactics**: 29 tactics including `path_simp`, `path_auto`, `path_normalize`, `path_beta`, `path_eta`, plus structural tactics (`path_inv_inv`, `path_inv_distr`, `path_cancel_left/right`, `path_then_cancel_left/right`) and congruence tactics (`path_congr_symm`, `path_congrArg`) for automated RwEq reasoning.
- **Hurewicz theorem**: H₁(X) ≃ π₁(X)^ab (abelianization). First homology as abelianization of fundamental group. Examples: H₁(S¹∨S¹) ≃ ℤ×ℤ (from non-abelian ℤ*ℤ), H₁(Klein bottle) ≃ ℤ×ℤ/2ℤ.
- **Free group abelianization** (axiom-free): Constructive proof that F_n^ab ≃ ℤⁿ (free group on n generators abelianizes to ℤⁿ). Full encode-decode equivalence with lifting respecting both quotient relations (BouquetRel and AbelianizationRel).
- **Covering space classification**: Galois correspondence between covering spaces and subgroups of π₁. Deck(X̃/X) ≃ π₁(X) for universal cover. Regular covers correspond to normal subgroups.
- **Covering space theory**: Total spaces, path lifting, π₁-action on fibers, universal cover, deck transformations.
- **Confluence of LND_EQ-TRS**: Complete proof that the computational path rewrite system is confluent via Newman's Lemma (local confluence + termination). Critical pair analysis for all core path algebra rules including the challenging inverse-related pairs.
- Loop quotients and π₁(A, a) as rewrite classes with strict group laws.
- Higher-inductive circle interface + π₁(S¹) ≃ ℤ via winding number (requires `HasCirclePiOneEncode`; optional raw-loop interface `HasCircleLoopDecode` is derivable).
- Completed proof π₁(S¹) ≃ ℤ using an encode–decode argument with quotient→equality reduction.
- Completed proof π₁(T²) ≃ ℤ × ℤ via the encode/decode equivalence `torusPiOneEquivIntProd` (requires `HasTorusPiOneEncode`; optional raw-loop interface `HasTorusLoopDecode` is derivable).
- Real projective plane RP² with π₁(RP²) ≃ ℤ₂ (represented as Bool with XOR as addition; requires `HasProjectivePiOneEncode`; optional raw-loop interface `HasProjectiveLoopDecode` is derivable).
- **Klein bottle** π₁(K) ≃ ℤ ⋊ ℤ (semidirect product): normal-form equivalence `kleinPiOneEquivIntProd` (requires `HasKleinPiOneEncode`; optional raw-loop interface `HasKleinLoopDecode` is derivable), plus an alternative proof using Seifert-van Kampen on the CW-complex decomposition.
- Möbius band, cylinder HITs with π₁ ≃ ℤ (homotopy equivalent to circle).
- **Fundamental groupoid Π₁(X)**: Explicit groupoid structure with basepoint independence theorem (π₁(A,a) ≃ π₁(A,b) via path conjugation) and functoriality (f : A → B induces Π₁(f) : Π₁(A) → Π₁(B)).
- **Product fundamental group theorem**: π₁(A × B, (a,b)) ≃ π₁(A, a) × π₁(B, b) via path projection/pairing, enabling inductive computation of π₁(T^n) ≃ ℤⁿ.
- **Higher product homotopy**: π_n(A × B) ≃ π_n(A) × π_n(B) for all n, generalizing the π₁ product theorem to higher homotopy groups. Application: π_n(Tᵏ) = 0 for n ≥ 2.
- **Lie group connections**: SO(2) ≃ U(1) ≃ S¹ with π₁ ≃ ℤ, n-torus T^n = (S¹)^n as maximal torus in U(n), simply connected groups, ℤ₂ fundamental groups (SO(n) for n ≥ 3 via RP²), and comparison with Bordg-Cavalleri differential geometry approach.
- **Complex projective spaces** (CP^n): Simply connected for n ≥ 1 (π₁(CP^n) = 1), with π₂(CP^n) ≃ ℤ via the generalized Hopf fibration S¹ → S^{2n+1} → CP^n. CP^∞ ≃ K(ℤ, 2).
- **Quaternionic projective spaces** (HP^n): Simply connected with π₄(HP^n) ≃ ℤ, via S³ → S^{4n+3} → HP^n fibration.
- **Whitehead theorem**: Weak homotopy equivalences between CW complexes are homotopy equivalences. Includes weak h.e. definitions, CW complex structure, and obstruction theory foundations.
- **Mayer-Vietoris sequence**: Long exact sequence H_n(C) → H_n(A) ⊕ H_n(B) → H_n(X) → H_{n-1}(C) for X = A ∪ B, with exactness proofs and applications to sphere/wedge homology.
- **Cellular homology**: Chain complexes, boundary maps, homology groups H_n(X) for CW complexes, with connections to singular homology.
- **SVK applications**: Punctured plane π₁(ℝ² - {p}) ≃ ℤ, multiple punctures π₁(ℝ² - {p₁,...,pₙ}) ≃ F_{n-1}, graph fundamental groups, and doubles of manifolds.

## Quick Start
- Build: `lake build`
- Run demo: `lake exe computational_paths` (prints version)
- Open in VS Code: install Lean 4 extension, open the folder, and build.

## Project Layout (selected)
- [`ComputationalPaths/Path/Basic/`](ComputationalPaths/Path/Basic/) — core path definitions (transport, congruence, symmetry) and helpers.
- [`ComputationalPaths/Path/Rewrite/`](ComputationalPaths/Path/Rewrite/) — rewrite steps, closures (`Rw`, `RwEq`), and the quotient `PathRwQuot`.
- [`ComputationalPaths/Path/Groupoid.lean`](ComputationalPaths/Path/Groupoid.lean) — weak and strict categorical packages for computational paths; groupoids extend the corresponding categories so composition/identities are shared.
- [`ComputationalPaths/Path/GroupoidDerived.lean`](ComputationalPaths/Path/GroupoidDerived.lean) — **axiom-free derived groupoid theorems**: cancellation laws (`rweq_cancel_left/right`), uniqueness of inverses (`rweq_inv_unique_left/right`), mixed trans/symm cancellation, whiskering and conjugation laws, transport compatibility. All depend only on Lean's standard axioms (propext, Quot.sound).
- [`ComputationalPaths/Path/PathAlgebraDerived.lean`](ComputationalPaths/Path/PathAlgebraDerived.lean) — **axiom-free path algebra**: four-fold associativity, symm/trans interactions (`rweq_symm_trans_three`), congruence composition (`rweq_congrArg_comp`), pentagon coherence components, Eckmann-Hilton preparation, and inversion properties.
- [`ComputationalPaths/Path/OmegaGroupoid.lean`](ComputationalPaths/Path/OmegaGroupoid.lean) — **weak ω-groupoid structure** on computational paths with cells at each dimension, globular identities, and all coherence laws.
- [`ComputationalPaths/Path/OmegaGroupoid/`](ComputationalPaths/Path/OmegaGroupoid/) — subdirectory with axiom analysis and derived coherences:
  - [`Derived.lean`](ComputationalPaths/Path/OmegaGroupoid/Derived.lean) — demonstrates that most coherence axioms are derivable from `to_canonical`
  - [`StepToCanonical.lean`](ComputationalPaths/Path/OmegaGroupoid/StepToCanonical.lean) — the key `to_canonical` axiom and its justification
  - [`AxiomElimination.lean`](ComputationalPaths/Path/OmegaGroupoid/AxiomElimination.lean) — systematic elimination of redundant axioms
  - [`AxiomAnalysis.lean`](ComputationalPaths/Path/OmegaGroupoid/AxiomAnalysis.lean) — analysis of axiom dependencies
  - [`AxiomMinimality.lean`](ComputationalPaths/Path/OmegaGroupoid/AxiomMinimality.lean) — minimality proofs for axiom sets
  - [`ComputationalConfluence.lean`](ComputationalPaths/Path/OmegaGroupoid/ComputationalConfluence.lean) — computational aspects of confluence
  - [`ConfluenceWithCells.lean`](ComputationalPaths/Path/OmegaGroupoid/ConfluenceWithCells.lean) — confluence integrated with cell structure
  - [`TypedRewriting.lean`](ComputationalPaths/Path/OmegaGroupoid/TypedRewriting.lean) — typed rewriting system foundations
- [`ComputationalPaths/Path/Homotopy/`](ComputationalPaths/Path/Homotopy/) — loop spaces, rewrite monoids (`LoopMonoid`), loop groups (`LoopGroup`), π₁ interfaces, higher homotopy groups, truncation levels, and covering spaces.
- [`ComputationalPaths/Path/Homotopy/HigherHomotopy.lean`](ComputationalPaths/Path/Homotopy/HigherHomotopy.lean) — higher homotopy groups π_n via iterated loop spaces and derivation quotients.
- [`ComputationalPaths/Path/Homotopy/Truncation.lean`](ComputationalPaths/Path/Homotopy/Truncation.lean) — truncation levels (IsContr, IsProp, IsSet, IsGroupoid) connecting to HoTT n-types.
- [`ComputationalPaths/Path/Homotopy/CoveringSpace.lean`](ComputationalPaths/Path/Homotopy/CoveringSpace.lean) — covering space theory with path lifting and π₁-actions on fibers.
- [`ComputationalPaths/Path/Homotopy/Fibration.lean`](ComputationalPaths/Path/Homotopy/Fibration.lean) — fibrations, fiber sequences F → E → B, connecting map ∂ : π₁(B) → F, long exact sequence of homotopy groups, induced maps on π₁.
- [`ComputationalPaths/Path/Homotopy/SuspensionLoop.lean`](ComputationalPaths/Path/Homotopy/SuspensionLoop.lean) — suspension-loop adjunction [ΣX, Y]_* ≅ [X, ΩY]_*, pointed types/maps, adjunction map construction, connectivity definitions.
- [`ComputationalPaths/Path/Homotopy/FreudenthalSuspension.lean`](ComputationalPaths/Path/Homotopy/FreudenthalSuspension.lean) — **Freudenthal suspension theorem**: Σ : π_n(X) → π_{n+1}(ΣX) is isomorphism in stable range. Proves `sphereN_piN_equiv_int` (π_n(Sⁿ) ≃ ℤ for all n ≥ 1). Stable homotopy groups πₛ_k with πₛ_0 ≃ ℤ, πₛ_1 ≃ ℤ/2ℤ (Hopf element η), πₛ_2 ≃ ℤ/2ℤ (η²).
- [`ComputationalPaths/Path/Homotopy/EilenbergMacLane.lean`](ComputationalPaths/Path/Homotopy/EilenbergMacLane.lean) — Eilenberg-MacLane spaces K(G,n), IsKG1 characterization, circle is K(ℤ,1), loop space property Ω(K(G,n+1)) ≃ K(G,n).
- [`ComputationalPaths/Path/Homotopy/FundamentalGroupoid.lean`](ComputationalPaths/Path/Homotopy/FundamentalGroupoid.lean) — **Fundamental groupoid Π₁(A)** with explicit groupoid structure, basepoint independence theorem (`basepointIsomorphism`), and functoriality (`fundamentalGroupoidMap`, `inducedPiOneMap`).
- [`ComputationalPaths/Path/Homotopy/ProductFundamentalGroup.lean`](ComputationalPaths/Path/Homotopy/ProductFundamentalGroup.lean) — **Product fundamental group theorem**: π₁(A × B, (a,b)) ≃ π₁(A, a) × π₁(B, b) via path projection (`Path.fst`, `Path.snd`) and pairing (`Path.prod`).
- [`ComputationalPaths/Path/Homotopy/HigherProductHomotopy.lean`](ComputationalPaths/Path/Homotopy/HigherProductHomotopy.lean) — **Higher product homotopy theorem**: π_n(A × B) ≃ π_n(A) × π_n(B) for all n ≥ 1, with `prodHigherPiNEquiv`. Generalizes π₁ product theorem; application: π_n(Tᵏ) = 0 for n ≥ 2.
- [`ComputationalPaths/Path/Homotopy/LieGroups.lean`](ComputationalPaths/Path/Homotopy/LieGroups.lean) — **Connections to Lie groups**: SO(2), U(1) as Circle with π₁ ≃ ℤ, n-torus T^n = (S¹)^n with `torusN_product_step` for inductive π₁(T^n) ≃ ℤⁿ, maximal tori in U(n) and SU(n), simply connected types, ℤ₂ fundamental groups, and comparison with Bordg-Cavalleri differential geometry approach.
- [`ComputationalPaths/Path/Homotopy/Hurewicz.lean`](ComputationalPaths/Path/Homotopy/Hurewicz.lean) — **Hurewicz theorem**: H₁(X) ≃ π₁(X)^ab (abelianization). Defines commutators, abelianization, first homology group H₁. Examples: H₁(S¹∨S¹) ≃ ℤ×ℤ, H₁(Klein bottle) ≃ ℤ×ℤ/2ℤ. Higher Hurewicz for simply-connected spaces.
- [`ComputationalPaths/Path/Algebra/Abelianization.lean`](ComputationalPaths/Path/Algebra/Abelianization.lean) — **Free group abelianization** F_n^ab ≃ ℤⁿ (axiom-free). Constructive encode-decode equivalence with `freeGroup_ab_equiv`, `wordToIntPow`, `liftWord_respects_BouquetRel`, and `liftBouquetFreeGroup_respects_AbelianizationRel`.
- [`ComputationalPaths/Path/Algebra/NielsenSchreier.lean`](ComputationalPaths/Path/Algebra/NielsenSchreier.lean) — **Nielsen-Schreier theorem**: subgroups of free groups are free. Infrastructure for free group algebra.
- [`ComputationalPaths/Path/Homotopy/CoveringClassification.lean`](ComputationalPaths/Path/Homotopy/CoveringClassification.lean) — **Covering space classification** via Galois correspondence: covering spaces ↔ subgroups of π₁. Universal cover with `deck_equiv_pi1` (Deck(X̃/X) ≃ π₁(X)). Regular covers, normal subgroups, examples for circle, torus, figure-eight, projective plane.
- [`ComputationalPaths/Path/Homotopy/WhiteheadTheorem.lean`](ComputationalPaths/Path/Homotopy/WhiteheadTheorem.lean) — **Whitehead theorem**: weak homotopy equivalences between CW complexes are homotopy equivalences. Includes `InducesIsoOnPiN`, `WeakHomotopyEquiv`, `HomotopyEquiv` structures, and obstruction theory.
- [`ComputationalPaths/Path/Homotopy/CellularHomology.lean`](ComputationalPaths/Path/Homotopy/CellularHomology.lean) — **Cellular homology** for CW complexes: chain complexes, boundary maps, cellular homology groups H_n(X), and connections to singular homology.
- [`ComputationalPaths/Path/Homotopy/MayerVietoris.lean`](ComputationalPaths/Path/Homotopy/MayerVietoris.lean) — **Mayer-Vietoris sequence**: long exact sequence H_n(C) → H_n(A) ⊕ H_n(B) → H_n(X) → H_{n-1}(C) for X = A ∪ B, with exactness proofs.
- [`ComputationalPaths/Path/Homotopy/LongExactSequence.lean`](ComputationalPaths/Path/Homotopy/LongExactSequence.lean) — general long exact sequence infrastructure for homotopy and homology theories.
- [`ComputationalPaths/Path/Homotopy/Pi2Surfaces.lean`](ComputationalPaths/Path/Homotopy/Pi2Surfaces.lean) — π₂ calculations for surfaces, extending π₁ results to higher homotopy.
- [`ComputationalPaths/Path/Homotopy/LoopIteration.lean`](ComputationalPaths/Path/Homotopy/LoopIteration.lean) — loop iteration infrastructure supporting loop power operations and group structure.
- [`ComputationalPaths/Path/Homotopy/Coproduct.lean`](ComputationalPaths/Path/Homotopy/Coproduct.lean) — coproduct constructions for homotopy-theoretic types.
- [`ComputationalPaths/Path/Homotopy/Sets.lean`](ComputationalPaths/Path/Homotopy/Sets.lean) — set-theoretic constructions supporting homotopy definitions.
- [`ComputationalPaths/Path/Rewrite/PathTactic.lean`](ComputationalPaths/Path/Rewrite/PathTactic.lean) — automation tactics (`path_simp`, `path_rfl`, `path_canon`, `path_decide`) for RwEq proofs.
- [`ComputationalPaths/Path/Rewrite/PathTacticExamples.lean`](ComputationalPaths/Path/Rewrite/PathTacticExamples.lean) — comprehensive test suite for path tactics demonstrating usage patterns.
- [`ComputationalPaths/Path/Rewrite/MinimalAxioms.lean`](ComputationalPaths/Path/Rewrite/MinimalAxioms.lean) — analysis of minimal axiom requirements for the rewrite system.
- [`ComputationalPaths/Path/Rewrite/ConfluenceProof.lean`](ComputationalPaths/Path/Rewrite/ConfluenceProof.lean) — **Confluence proof** via Newman's Lemma: critical pair analysis, local confluence, strip lemma, and `HasJoinOfRw` instance.
- [`ComputationalPaths/Path/Rewrite/TerminationBridge.lean`](ComputationalPaths/Path/Rewrite/TerminationBridge.lean) — **Termination-confluence bridge**: Connects RPO termination to confluence axioms. Proves lexicographic well-foundedness (`lexLt_wf`). Only 1 axiom (`step_nonincreasing`).
- [`ComputationalPaths/Path/HIT/Circle.lean`](ComputationalPaths/Path/HIT/Circle.lean) — circle HIT interface, canonical `circleDecode : ℤ → π₁(S¹)`, and the optional raw-loop interface `HasCircleLoopDecode`.
- [`ComputationalPaths/Path/HIT/CircleStep.lean`](ComputationalPaths/Path/HIT/CircleStep.lean) — quotient-level interface `HasCirclePiOneEncode`, `circlePiOneEquivInt : π₁(S¹) ≃ ℤ`, and winding-number algebra lemmas.
- [`ComputationalPaths/Path/HIT/CirclePiOneAxiom.lean`](ComputationalPaths/Path/HIT/CirclePiOneAxiom.lean) — **opt-in**: installs a global `HasCirclePiOneEncode` instance as a kernel axiom and exports `circlePiOneEquivInt'` with no extra parameters.
- [`ComputationalPaths/Path/HIT/Torus.lean`](ComputationalPaths/Path/HIT/Torus.lean) — torus HIT interface, canonical `torusDecode : ℤ × ℤ → π₁(T²)`, and the optional raw-loop interface `HasTorusLoopDecode`.
- [`ComputationalPaths/Path/HIT/TorusStep.lean`](ComputationalPaths/Path/HIT/TorusStep.lean) — quotient-level interface `HasTorusPiOneEncode` and `torusPiOneEquivIntProd : π₁(T²) ≃ ℤ × ℤ`.
- [`ComputationalPaths/Path/HIT/TorusPiOneAxiom.lean`](ComputationalPaths/Path/HIT/TorusPiOneAxiom.lean) — **opt-in**: installs a global `HasTorusPiOneEncode` instance as a kernel axiom and exports `torusPiOneEquivIntProd'` with no extra parameters.
- [`ComputationalPaths/Path/HIT/ProjectivePlane.lean`](ComputationalPaths/Path/HIT/ProjectivePlane.lean) — real projective plane HIT skeleton and raw loop classification interface `HasProjectiveLoopDecode`, with the raw-loop equivalence `projectivePiOneEquivZ2_ofLoopDecode`.
- [`ComputationalPaths/Path/HIT/ProjectivePlaneStep.lean`](ComputationalPaths/Path/HIT/ProjectivePlaneStep.lean) — quotient-level interface `HasProjectivePiOneEncode` and `projectivePiOneEquivZ2 : π₁(RP²) ≃ ℤ₂`.
- [`ComputationalPaths/Path/HIT/ProjectivePiOneAxiom.lean`](ComputationalPaths/Path/HIT/ProjectivePiOneAxiom.lean) — **opt-in**: installs a global `HasProjectivePiOneEncode` instance as a kernel axiom and exports `projectivePiOneEquivZ2'` with no extra parameters.
- [`ComputationalPaths/Path/HIT/KleinBottle.lean`](ComputationalPaths/Path/HIT/KleinBottle.lean) — Klein bottle HIT skeleton, parity sign `kleinSign`, and raw loop classification interface `HasKleinLoopDecode`, with the raw-loop equivalence `kleinPiOneEquivIntProd_ofLoopDecode`.
- [`ComputationalPaths/Path/HIT/KleinBottleStep.lean`](ComputationalPaths/Path/HIT/KleinBottleStep.lean) — quotient-level interface `HasKleinPiOneEncode` and `kleinPiOneEquivIntProd : π₁(K) ≃ Int × Int`.
- [`ComputationalPaths/Path/HIT/KleinPiOneAxiom.lean`](ComputationalPaths/Path/HIT/KleinPiOneAxiom.lean) — **opt-in**: installs a global `HasKleinPiOneEncode` instance as a kernel axiom and exports `kleinPiOneEquivIntProd'` with no extra parameters.
- [`ComputationalPaths/Path/HIT/KleinBottleSVK.lean`](ComputationalPaths/Path/HIT/KleinBottleSVK.lean) — Alternative proof of π₁(K) ≃ ℤ ⋊ ℤ using Seifert-van Kampen on the CW-complex pushout (D² attached to S¹∨S¹ via boundary word aba⁻¹b).
- [`ComputationalPaths/Path/HIT/MobiusBand.lean`](ComputationalPaths/Path/HIT/MobiusBand.lean) — Möbius band HIT (homotopy equivalent to circle), π₁ ≃ ℤ.
- [`ComputationalPaths/Path/HIT/Cylinder.lean`](ComputationalPaths/Path/HIT/Cylinder.lean) — Cylinder HIT (S¹ × I), π₁ ≃ ℤ.
- [`ComputationalPaths/Path/HIT/Pushout.lean`](ComputationalPaths/Path/HIT/Pushout.lean) — Pushout HIT with constructors (inl, inr, glue), eliminators, and special cases (wedge sum, suspension).
- [`ComputationalPaths/Path/HIT/PushoutPaths.lean`](ComputationalPaths/Path/HIT/PushoutPaths.lean) — Path characterization for pushouts, free products, amalgamated free products, and the **Seifert-van Kampen theorem** (`seifertVanKampenEquiv`).
- [`ComputationalPaths/Path/HIT/FigureEight.lean`](ComputationalPaths/Path/HIT/FigureEight.lean) — Figure-eight space (S¹ ∨ S¹) with π₁ ≃ ℤ * ℤ (free group F₂), demonstrating non-abelian fundamental groups.
- [`ComputationalPaths/Path/HIT/BouquetN.lean`](ComputationalPaths/Path/HIT/BouquetN.lean) — **Bouquet of n circles** (∨ⁿS¹) with π₁ ≃ F_n (free group on n generators), generalizing Figure-Eight with encode-decode equivalence.
- [`ComputationalPaths/Path/HIT/Sphere.lean`](ComputationalPaths/Path/HIT/Sphere.lean) — The 2-sphere S² as suspension of S¹, with π₁(S²) ≅ 1 via SVK. Also defines S³ for the Hopf fibration.
- [`ComputationalPaths/Path/HIT/OrientableSurface.lean`](ComputationalPaths/Path/HIT/OrientableSurface.lean) — **Orientable genus-g surfaces** Σ_g with full fundamental group calculation: π₁(Σ_g) ≃ ⟨a₁,b₁,...,a_g,b_g | [a₁,b₁]...[a_g,b_g] = 1⟩.
- [`ComputationalPaths/Path/HIT/TorusGenus1.lean`](ComputationalPaths/Path/HIT/TorusGenus1.lean) — **Torus as genus-1 surface**: Proves π₁(OrientableSurface 1) ≃ ℤ × ℤ by constructive methods, demonstrating that the torus result follows from the general orientable surface framework.
- [`ComputationalPaths/Path/HIT/LensSpace.lean`](ComputationalPaths/Path/HIT/LensSpace.lean) — **Lens spaces L(p,q)**: Heegaard decomposition as pushout of solid tori, cyclic group ℤ/pℤ representation, general `GeneralLensSpace p q` for coprime p,q, quotient-level interfaces `HasLensPiOneEncode` and `HasGeneralLensPiOneEncode`, and `lensPiOneEquivZMod : π₁(L(p,q)) ≃ ℤ/pℤ`. Special cases: L(1,1) ≃ S³, L(2,1) ≃ RP³.
- [`ComputationalPaths/Path/HIT/LensPiOneAxiom.lean`](ComputationalPaths/Path/HIT/LensPiOneAxiom.lean) — **opt-in**: installs a global `HasLensPiOneEncode` instance as a kernel axiom and exports `lensPiOneEquivZMod'` with no extra parameters.
- [`ComputationalPaths/Path/HIT/HopfFibration.lean`](ComputationalPaths/Path/HIT/HopfFibration.lean) — **Hopf fibration** S¹ → S³ → S² with fiber equivalence, long exact sequence application, π₁(S³) = 1, and foundations for π₂(S²) ≅ ℤ.
- [`ComputationalPaths/Path/HIT/Pi2Sphere.lean`](ComputationalPaths/Path/HIT/Pi2Sphere.lean) — **Second homotopy group π₂(S²) ≃ ℤ** via Hopf fibration long exact sequence. Defines `S2TwoLoop` (2-loops in S²) with winding number, proves connecting map ∂ : π₂(S²) → π₁(S¹) is isomorphism (`hopf_connecting_iso`), and establishes `sphere2_pi2_equiv_int`.
- [`ComputationalPaths/Path/HIT/Pi3Sphere.lean`](ComputationalPaths/Path/HIT/Pi3Sphere.lean) — **Third homotopy group π₃(S²) ≃ ℤ** via Hopf fibration. Defines `S3ThreeLoop` (3-loops in S³) and `S2ThreeLoop` (3-loops in S²), proves `sphere3_pi3_equiv_int` and `hopf_pi3_iso` (isomorphism from LES), establishes `sphere2_pi3_equiv_int`. Generator is the Hopf map η with Hopf invariant 1.
- [`ComputationalPaths/Path/HIT/Pi4S3.lean`](ComputationalPaths/Path/HIT/Pi4S3.lean) — **Fourth homotopy group π₄(S³) ≃ ℤ/2ℤ** showing first torsion in homotopy groups. Generator Ση (suspended Hopf map) with `two_suspEta_trivial` proving 2·Ση = 0. Equivalence `sphere3_pi4_equiv_Z2`.
- [`ComputationalPaths/Path/HIT/Pi6S3.lean`](ComputationalPaths/Path/HIT/Pi6S3.lean) — **Sixth homotopy group π₆(S³) ≃ ℤ/12ℤ** — first non-2-torsion in sphere homotopy. Generator ν' with order 12. Zero axioms (defined via type abbreviation).
- [`ComputationalPaths/Path/HIT/ProjectivePlanePi2.lean`](ComputationalPaths/Path/HIT/ProjectivePlanePi2.lean) — **Second homotopy group π₂(RP²) ≃ ℤ** via covering space S² → RP². Zero axioms.
- [`ComputationalPaths/Path/HIT/JamesConstruction.lean`](ComputationalPaths/Path/HIT/JamesConstruction.lean) — **James construction** J(X) ≃ ΩΣX with complete stable homotopy stems πₛ₁ through πₛ₇: πₛ₁ ≃ ℤ/2ℤ (η), πₛ₂ ≃ ℤ/2ℤ (η²), πₛ₃ ≃ ℤ/24ℤ (ν), πₛ₄ = 0, πₛ₅ = 0, πₛ₆ ≃ ℤ/2ℤ (ν²), πₛ₇ ≃ ℤ/240ℤ (σ). Zero axioms.
- [`ComputationalPaths/Path/HIT/HopfInvariantOne.lean`](ComputationalPaths/Path/HIT/HopfInvariantOne.lean) — **Adams' H-space theorem**: Sⁿ is H-space iff n ∈ {0,1,3,7}. Proves S², S⁴, S⁵, S⁶ are NOT H-spaces. Only 1 axiom (`sphere_HSpace_only`).
- [`ComputationalPaths/Path/HIT/QuaternionicHopf.lean`](ComputationalPaths/Path/HIT/QuaternionicHopf.lean) — **Quaternionic Hopf fibration** S³ → S⁷ → S⁴ with `sphere4_pi7_equiv_int` (π₇(S⁴) ≃ ℤ). Generator ν (quaternionic Hopf map).
- [`ComputationalPaths/Path/HIT/OctonionicHopf.lean`](ComputationalPaths/Path/HIT/OctonionicHopf.lean) — **Octonionic Hopf fibration** S⁷ → S¹⁵ → S⁸ with `sphere8_pi15_equiv_int` (π₁₅(S⁸) ≃ ℤ). Generator σ (octonionic Hopf map). Full exact sequence typeclass `HasOctonionicHopfExactSequence`. Completes the four Hopf fibrations {η, ν, σ}.
- [`ComputationalPaths/Path/HIT/WedgeEncode.lean`](ComputationalPaths/Path/HIT/WedgeEncode.lean) — Constructive encode-decode for wedge sums using bijectivity, eliminating axioms from the SVK approach.
- [`ComputationalPaths/Path/HIT/ProjectivePlaneSVK.lean`](ComputationalPaths/Path/HIT/ProjectivePlaneSVK.lean) — Alternative proof of π₁(RP²) ≃ ℤ₂ using Seifert-van Kampen on the CW-complex pushout.
- [`ComputationalPaths/Path/HIT/NonOrientableSurface.lean`](ComputationalPaths/Path/HIT/NonOrientableSurface.lean) — **Non-orientable surfaces** N_n with π₁(N_n) ≃ ⟨a₁,...,a_n | a₁²...a_n² = 1⟩. Crosscap-based construction, Euler characteristic χ(N_n) = 2 - n, special cases RP² and Klein bottle.
- [`ComputationalPaths/Path/HIT/SVKApplications.lean`](ComputationalPaths/Path/HIT/SVKApplications.lean) — **Additional SVK applications**: punctured plane π₁(ℝ² - {p}) ≃ ℤ, multiple punctures π₁(ℝ² - {p₁,...,pₙ}) ≃ F_{n-1}, graph fundamental groups, doubles of manifolds.
- [`ComputationalPaths/Path/HIT/ComplexProjectiveSpaces.lean`](ComputationalPaths/Path/HIT/ComplexProjectiveSpaces.lean) — **Complex projective spaces** CP^n: π₁(CP^n) = 1 for n ≥ 1 (simply connected), π₂(CP^n) ≃ ℤ via generalized Hopf fibration.
- [`ComputationalPaths/Path/HIT/QuaternionicProjectiveSpaces.lean`](ComputationalPaths/Path/HIT/QuaternionicProjectiveSpaces.lean) — **Quaternionic projective spaces** HP^n: simply connected with π₄(HP^n) ≃ ℤ via S³ → S^{4n+3} → HP^n fibration.
- [`ComputationalPaths/Path/HIT/ProjectiveSpaces.lean`](ComputationalPaths/Path/HIT/ProjectiveSpaces.lean) — unified treatment of real, complex, and quaternionic projective spaces with common structure.
- [`ComputationalPaths/Path/Homotopy/HoTT.lean`](ComputationalPaths/Path/Homotopy/HoTT.lean) — homotopy/groupoid lemmas (reflexivity, symmetry, transitivity for identities) expressed via computational paths and exported to `Eq`.

## Bicategory & weak 2-groupoid API

- [`ComputationalPaths/Path/Bicategory.lean`](ComputationalPaths/Path/Bicategory.lean) packages computational paths into the structures
  ```lean
  open ComputationalPaths.Path

  variable (A : Type u)

  def pathsBicat : WeakBicategory A := weakBicategory A
  def pathsTwoGroupoid : WeakTwoGroupoid A := weakTwoGroupoid A
  ```
  Both constructions expose whiskering, horizontal composition, associator/unitors, the interchange law, and rewrite-level inverses for 1-cells. Import `ComputationalPaths.Path` and open the namespace to bring the API into scope for your own developments.
- Automation helpers: use the tactics `rwEq_auto` / `twoCell_auto` to solve common `RwEq` or `TwoCell` goals (they combine `simp` with the trans/symm constructors).

## Weak ω-Groupoid Structure

- [`ComputationalPaths/Path/OmegaGroupoid.lean`](ComputationalPaths/Path/OmegaGroupoid.lean) provides the **complete proof** that computational paths form a weak ω-groupoid following Lumsdaine (2010) and van den Berg-Garner (2011):
  ```lean
  open ComputationalPaths.Path.OmegaGroupoid

  variable (A : Type u)

  -- The main theorem: computational paths form a weak ω-groupoid
  def pathsOmegaGroupoid : WeakOmegaGroupoid A := compPathOmegaGroupoid A
  ```

- **Proper tower structure** (each level indexed by the previous):
  - Level 0: Points (elements of A)
  - Level 1: Paths between points (`Path a b`)
  - Level 2: 2-cells between paths (`Derivation₂ p q`)
  - Level 3: 3-cells between 2-cells (`Derivation₃ d₁ d₂`)
  - Level 4: 4-cells between 3-cells (`Derivation₄ m₁ m₂`)
  - Level 5+: Higher cells (`DerivationHigh n c₁ c₂`)

- **Operations at each level**:
  - Identity (`refl`), composition (`vcomp`), and inverse (`inv`)
  - Whiskering (`whiskerLeft`, `whiskerRight`) and horizontal composition (`hcomp`)
  - Full whiskering at levels 3, 4, and 5+ for contractibility proofs

- **Groupoid laws** (as higher cells, not equations):
  - Unit laws: `vcomp_refl_left`, `vcomp_refl_right`
  - Associativity: `vcomp_assoc`
  - Inverse laws: `vcomp_inv_left`, `vcomp_inv_right`, `inv_inv`

- **Higher coherences**:
  - Pentagon coherence (Mac Lane's pentagon for associators)
  - Triangle coherence (compatibility of associator and unitors)
  - Interchange law (compatibility of vertical and horizontal composition)
  - Step coherence (`step_eq`): justified by `Step` being in `Prop`

- **Canonicity axiom & contractibility** (the key property):
  - Every path `p` has a **normal form** `‖p‖ := Path.ofEq p.toEq`
  - The **normalizing derivation** `deriv₂_to_normal p : Derivation₂ p ‖p‖` connects any path to its normal form
  - The **canonical derivation** between parallel paths: `canonical p q := deriv₂_to_normal p ∘ inv(deriv₂_to_normal q)`
  - The **canonicity axiom** (`to_canonical`): every derivation connects to the canonical derivation
  - **Contractibility is derived** from the canonicity axiom:
    ```
    contractibility₃ d₁ d₂ := to_canonical d₁ ∘ inv(to_canonical d₂)
    ```
  - This is analogous to the **J-principle** in HoTT, but grounded in the normalization algorithm
  - `contractibility₃`: Any two parallel 2-cells connected by a 3-cell
  - `contractibility₄`: Any two parallel 3-cells connected by a 4-cell
  - `contractibilityHigh`: Pattern continues for all higher levels

- **Implementation notes**:
  - No `sorry` in the entire module
  - The `to_canonical` axiom is grounded in the normalization algorithm of the LND_EQ-TRS
  - Unlike a bare contractibility axiom, `to_canonical` has a concrete, canonical target
  - Semantic justification: normalization + confluence + proof irrelevance of Step

- **References**: This formalisation validates the theoretical results of Lumsdaine (*Weak ω-categories from intensional type theory*, 2010) and van den Berg & Garner (*Types are weak ω-groupoids*, 2011) in the computational paths setting.

## Higher Homotopy Groups π_n (what to read)

- [`ComputationalPaths/Path/Homotopy/HigherHomotopy.lean`](ComputationalPaths/Path/Homotopy/HigherHomotopy.lean) defines higher homotopy groups using the ω-groupoid tower:
  ```lean
  -- Iterated loop spaces
  def Loop2Space (A : Type u) (a : A) := Derivation₂ (Path.refl a) (Path.refl a)
  def Loop3Space (A : Type u) (a : A) := Derivation₃ (Derivation₂.refl ...) ...

  -- Second homotopy group
  def PiTwo (A : Type u) (a : A) := Quotient (Loop2Setoid A a)
  notation "π₂(" A ", " a ")" => PiTwo A a
  ```
- **Group structure on π₂**: `PiTwo.mul`, `PiTwo.inv`, `PiTwo.id` with full group laws
- **Eckmann-Hilton theorem**: `piTwo_comm` proves π₂(A, a) is abelian via the interchange law
- **Key insight**: 2-loops are equivalent if connected by a 3-cell (Derivation₃)
- **π₂(S²) ≅ 1**: In [`Sphere.lean`](ComputationalPaths/Path/HIT/Sphere.lean), `sphere2_pi2_trivial` proves all 2-loops are trivial via contractibility₃

## Truncation Levels (n-types)

- [`ComputationalPaths/Path/Homotopy/Truncation.lean`](ComputationalPaths/Path/Homotopy/Truncation.lean) connects the ω-groupoid to HoTT truncation:
  ```lean
  structure IsContr (A : Type u) where
    center : A
    contr : (a : A) → Path a center

  structure IsProp (A : Type u) where
    eq : (a b : A) → Path a b

  structure IsSet (A : Type u) where
    pathEq : {a b : A} → (p q : Path a b) → RwEq p q

  structure IsGroupoid (A : Type u) where
    derivEq : {a b : A} → {p q : Path a b} →
              (d₁ d₂ : Derivation₂ p q) → Nonempty (Derivation₃ d₁ d₂)
  ```
- **Cumulative hierarchy**: `contr_implies_prop`, `prop_implies_set`, `set_implies_groupoid`
- **All types are 1-groupoids**: `all_types_groupoid` via contractibility₃
- **Connection to π_n triviality**:
  - `IsSet A ↔ π₁(A, a) trivial for all a`
  - `IsGroupoid A ↔ π₂(A, a) trivial for all a`

## Path Simplification Tactics

- [`ComputationalPaths/Path/Rewrite/PathTactic.lean`](ComputationalPaths/Path/Rewrite/PathTactic.lean) provides comprehensive automation for RwEq proofs:

### Primary Tactics

| Tactic | Description |
|--------|-------------|
| `path_simp` | Simplify using ~25 groupoid laws (unit, inverse, assoc, symm) |
| `path_auto` | Full automation combining simp + structural lemmas |
| `path_rfl` | Close reflexive goals `RwEq p p` |

### Structural Tactics

| Tactic | Description |
|--------|-------------|
| `path_symm` | Apply symmetry to RwEq goal |
| `path_normalize` | Rewrite to canonical (right-associative) form |
| `path_beta` | Apply beta reductions for products/sigmas/functions |
| `path_eta` | Apply eta expansion/contraction for products |
| `path_congr_left h` | Left congruence: `RwEq q₁ q₂ → RwEq (trans p q₁) (trans p q₂)` |
| `path_congr_right h` | Right congruence: `RwEq p₁ p₂ → RwEq (trans p₁ q) (trans p₂ q)` |
| `path_cancel_left` | Close `RwEq (trans (symm p) p) refl` |
| `path_cancel_right` | Close `RwEq (trans p (symm p)) refl` |
| `path_trans_via t` | Split goal via intermediate path `t` |

### Usage Examples

```lean
-- Unit elimination (replaces manual rweq_cmpA_refl_left/right)
example (p : Path a b) : RwEq (trans refl p) p := by path_simp
example (p : Path a b) : RwEq (trans p refl) p := by path_simp

-- Inverse cancellation
example (p : Path a b) : RwEq (trans (symm p) p) refl := by path_cancel_left
example (p : Path a b) : RwEq (trans p (symm p)) refl := by path_cancel_right

-- Double symmetry
example (p : Path a b) : RwEq (symm (symm p)) p := by path_simp

-- Product eta
example (p : Path (a₁, b₁) (a₂, b₂)) : RwEq (prodMk (fst p) (snd p)) p := by path_eta
```

- **Simp lemmas**: Unit laws, inverse laws, associativity, double symmetry, congruence, product beta/eta
- **When to use**: `path_simp` for base cases in inductions; `path_auto` for standalone goals; manual lemmas for complex intermediate steps

## Axiom-Free Derived Results

Two modules provide extensive axiom-free, sorry-free results derived purely from the primitive Step rules:

### GroupoidDerived.lean

| Theorem | Description |
|---------|-------------|
| `rweq_cancel_left` | Left cancellation: p · q ≈ p · r → q ≈ r |
| `rweq_cancel_right` | Right cancellation: p · r ≈ q · r → p ≈ q |
| `rweq_inv_unique_left` | Left inverse uniqueness: q · p ≈ refl → q ≈ p⁻¹ |
| `rweq_inv_unique_right` | Right inverse uniqueness: p · q ≈ refl → q ≈ p⁻¹ |
| `rweq_inv_trans_cancel` | (p · q)⁻¹ · p ≈ q⁻¹ |
| `rweq_trans_inv_cancel` | p · (p⁻¹ · q) ≈ q |
| `rweq_symm_trans_cancel` | p⁻¹ · (p · q) ≈ q |
| `rweq_conj_refl` | p · refl · p⁻¹ ≈ refl |
| `rweq_conj_trans` | Conjugation distributes over trans |

### PathAlgebraDerived.lean

| Theorem | Description |
|---------|-------------|
| `rweq_trans_four_assoc` | Four-fold associativity: ((p·q)·r)·s ≈ p·(q·(r·s)) |
| `rweq_symm_trans` | Contravariance: (p·q)⁻¹ ≈ q⁻¹·p⁻¹ |
| `rweq_symm_trans_three` | Triple: (p·q·r)⁻¹ ≈ r⁻¹·q⁻¹·p⁻¹ |
| `rweq_congrArg_comp` | Composition: (g∘f)*(p) = g*(f*(p)) |
| `rweq_pentagon_left/right/top` | Pentagon coherence components |
| `rweq_inv_refl` | refl⁻¹ ≈ refl |
| `rweq_inv_inv` | (p⁻¹)⁻¹ ≈ p |

All theorems depend only on `propext` and `Quot.sound` (Lean's standard axioms) — no HIT axioms.

## Covering Space Theory

- [`ComputationalPaths/Path/Homotopy/CoveringSpace.lean`](ComputationalPaths/Path/Homotopy/CoveringSpace.lean) provides basic covering space infrastructure:
  ```lean
  -- Total space of a type family
  def TotalSpace (P : A → Type u) := Σ (a : A), P a

  -- Covering: fibers are sets
  structure IsCovering (P : A → Type u) where
    fiberIsSet : (a : A) → IsSet (P a)

  -- π₁ action on fibers
  def fiberAction : π₁(A, a) → P a → P a

  -- Universal cover
  def UniversalCoverFiber (A : Type u) (a : A) : A → Type u := fun _ => π₁(A, a)
  ```
- **Path lifting**: `pathLift` lifts base paths to total space paths
- **Deck transformations**: `DeckTransformation` structure with composition and inverses
- **Future work**: Classification theorem (covers ↔ subgroups of π₁)

## Fibrations and Fiber Sequences (what to read)

- [`ComputationalPaths/Path/Homotopy/Fibration.lean`](ComputationalPaths/Path/Homotopy/Fibration.lean) develops fibration theory:
  ```lean
  -- Fiber of a map
  def Fiber (f : A → B) (b : B) : Type u := { a : A // f a = b }

  -- Fiber sequence F → E → B
  structure FiberSeq (F E B : Type u) where
    proj : E → B
    baseB : B
    baseE : E
    toFiber : F → Fiber proj baseB
    fromFiber : Fiber proj baseB → F
    -- ... inverse properties

  -- Connecting map ∂ : π₁(B) → F
  def connectingMapPi1 : π₁(B, b) → P b

  -- Long exact sequence structure
  structure LongExactSequencePi1 where
    incl_star : π₁(F) → π₁(E)
    proj_star : π₁(E) → π₁(B)
    boundary : π₁(B) → F
    exact_at_E : ...  -- im(incl_*) = ker(proj_*)
    exact_at_B : ...  -- im(proj_*) = ker(∂)
  ```
- **Path lifting**: `liftPath` lifts base paths to total space
- **Induced maps**: `inducedPi1Map` takes f : A → B to f_* : π₁(A) → π₁(B)
- **Exactness**: `canonicalFiberSeq_exact` proves exactness for type family fibrations
- **Long exact sequence**: `longExactSequence` constructs π₁(F) → π₁(E) → π₁(B) → π₀(F)

## Suspension-Loop Adjunction (what to read)

- [`ComputationalPaths/Path/Homotopy/SuspensionLoop.lean`](ComputationalPaths/Path/Homotopy/SuspensionLoop.lean) establishes the suspension-loop adjunction:
  ```lean
  -- Pointed types and maps
  structure Pointed where
    carrier : Type u
    pt : carrier

  structure PointedMap (X Y : Pointed) where
    toFun : X.carrier → Y.carrier
    map_pt : toFun X.pt = Y.pt

  -- Suspension as pointed type (north as basepoint)
  def suspPointed (X : Type u) : Pointed

  -- Loop space as pointed type (refl as basepoint)
  def loopPointed (Y : Pointed) : Pointed

  -- Adjunction map: f : ΣX → Y gives X → ΩY
  def adjMap (x₀ : X) (f : Suspension X → Y.carrier) :
      X → LoopSpace Y.carrier Y.pt
  ```
- **Basepoint preservation**: `adjMap_basepoint` proves x₀ maps to refl
- **Connectivity**: `IsPathConnectedPointed`, `IsSimplyConnected` structures
- **Suspension connectivity**: `susp_path_connected_structure` shows south connects to north

## Eilenberg-MacLane Spaces K(G,n) (what to read)

- [`ComputationalPaths/Path/Homotopy/EilenbergMacLane.lean`](ComputationalPaths/Path/Homotopy/EilenbergMacLane.lean) characterizes K(G,n) spaces:
  ```lean
  -- Group structures
  structure GroupStr (G : Type u) where
    one : G
    mul : G → G → G
    inv : G → G
    -- axioms...

  -- K(G,1) characterization
  structure IsKG1 (X : PointedType) (G : Type u) (h : GroupStr G) where
    connected : ∀ x, ∃ _p : Path x X.pt, True
    pi1_iso_toFun : π₁(X) → G
    pi1_iso_surj : ∀ g, ∃ α, pi1_iso_toFun α = g
    pi1_iso_inj : ∀ α β, pi1_iso_toFun α = pi1_iso_toFun β → α = β
    pi1_iso_one : pi1_iso_toFun refl = h.one
    pi1_iso_mul : ∀ α β, pi1_iso_toFun (α · β) = h.mul ...
    pi2_trivial : ∀ l : Loop2Space, Loop2Eq l refl

  -- The circle is K(ℤ,1)
  def circleIsKZ1 : IsKG1 circlePointed Int intAbelianGroup.toGroupStr
  ```
- **Circle is K(ℤ,1)**: Uses encode-decode from Circle.lean with π₂ triviality from contractibility₃
- **Proved theorems** (no longer axioms):
  - `circleConnected`: Every point is path-connected to base (via PLift + circle induction)
  - `circleEncode_mul`: Encoding is a group homomorphism (via round-trip + integer induction)
- **Loop space property**: `loop_of_KGn_shifts_degree` states Ω(K(G,n+1)) ≃ K(G,n)
- **Classifying spaces**: `IsClassifyingSpace` structure for BG = K(G,1)

## Circle π₁(S¹) ≃ ℤ (what to read)
- Encoding: `circleEncode : π₁(S¹) → ℤ` via quotient-lift of `circleEncodePath`.
- Decoding: `circleDecode : ℤ → π₁(S¹)` by z-powers of the fundamental loop.
- Step laws: `circleEncode (x ⋆ loop) = circleEncode x + 1` and the inverse step.
- Identities:
  - Right-inverse on ℤ: `circleEncode (circleDecode z) = z` (by integer induction).
  - Left-inverse on π₁: `circleDecode (circleEncode x) = x` (reduce to equality with `toEq` and use equality induction).
- Homomorphism (circle-specific): decode respects addition, subtraction, and group multiplication — proved from the step laws and encode injectivity.

## Torus π₁(T²) ≃ ℤ × ℤ (what to read)

Two approaches are available:

**Axiomatic approach** ([`Torus.lean`](ComputationalPaths/Path/HIT/Torus.lean), [`TorusStep.lean`](ComputationalPaths/Path/HIT/TorusStep.lean)):
- Encoding: `torusPiOneEncode : π₁(T²) → ℤ × ℤ` from the quotient-level interface `HasTorusPiOneEncode`.
- Decoding: `torusDecode : ℤ × ℤ → π₁(T²)` assembles the z-powers of the two commuting loops.
- Equivalence: `torusPiOneEquivIntProd` shows the maps are inverse, yielding π₁(T²) ≃ ℤ × ℤ.
- Assumption: the classification data is packaged as the typeclass `HasTorusPiOneEncode`.
- Optional: raw loop normal forms are available as `HasTorusLoopDecode` and are derivable from `HasTorusPiOneEncode`.

**Derived approach via OrientableSurface** ([`TorusGenus1.lean`](ComputationalPaths/Path/HIT/TorusGenus1.lean)):
- Defines `Torus'` as `OrientableSurface 1` (genus-1 orientable surface).
- Proves the round-trip properties `torus_left_inv_def` and `torus_right_inv_def` constructively.
- Uses `sumPowersA`/`sumPowersB` winding number functions and the `word_eq_canonical` abelianization lemma.
- Equivalence: `piOneEquivIntProd : π₁(Torus') ≃ ℤ × ℤ` follows from the general surface group machinery.
- Demonstrates that the torus π₁ result is a special case of the orientable surface framework.

## Real Projective Plane π₁(RP²) ≃ ℤ₂ (what to read)
- Reference: de Veras, Ramos, de Queiroz & de Oliveira, "A Topological Application of Labelled Natural Deduction", SAJL.
- HIT Interface: `ProjectivePlane` with base point and fundamental loop `projectiveLoop` satisfying `projectiveLoopSquare : α ∘ α = refl`.
- ℤ₂ representation: `Bool` with XOR as addition (no Mathlib dependency).
- Decoding: `projectiveDecode : Bool → π₁(RP²)` with `projectiveDecodePath : Bool → Path projectiveBase projectiveBase`.
- Encoding: `projectivePiOneEncode : π₁(RP²) → Bool` from the quotient-level interface `HasProjectivePiOneEncode` (the raw-loop `projectiveEncode` lives under `HasProjectiveLoopDecode`).
- Equivalence: `projectivePiOneEquivZ2` shows π₁(RP²) ≃ ℤ₂, assuming `HasProjectivePiOneEncode`.

## Klein bottle π₁(K) ≃ ℤ ⋊ ℤ (what to read)
- Reference: [de Veras, Ramos, de Queiroz & de Oliveira, *An alternative approach to the calculation of fundamental groups based on labeled natural deduction* (2019)](https://arxiv.org/abs/1906.09107).
- HIT Interface: `KleinBottle` with base point, generators `kleinLoopA` (a) and `kleinLoopB` (b), and surface relation `aba⁻¹ = b⁻¹`.
- Normal form: `kleinDecodePath : Int × Int → Path kleinBase kleinBase` builds loops `a^m ⬝ b^n`.
- Decoding: `kleinDecode : Int × Int → π₁(K)` with `kleinDecodePath` as the raw loop normal form.
- Encoding: `kleinPiOneEncode : π₁(K) → Int × Int` from the quotient-level interface `HasKleinPiOneEncode` (the raw-loop `kleinEncode` lives under `HasKleinLoopDecode`).
- Equivalence: `kleinPiOneEquivIntProd` shows π₁(K) ≃ ℤ × ℤ, assuming `HasKleinPiOneEncode`.
- Semidirect product viewpoint (multiplication on `Int × Int`) is developed in `KleinBottleSVK.lean`.
- **Alternative proof via SVK** ([`KleinBottleSVK.lean`](ComputationalPaths/Path/HIT/KleinBottleSVK.lean)):
  - Constructs K as pushout: `FigureEight ←boundary─ S¹ ─collapse→ Point`
  - Boundary map sends `circleLoop` to `aba⁻¹b` (the Klein relation word)
  - SVK gives: π₁(K) ≃ (ℤ * ℤ) / ⟨⟨aba⁻¹b⟩⟩ ≃ ℤ ⋊ ℤ
  - Key computation: `wordToIntProd_boundaryWord` shows aba⁻¹b maps to (0,0) in ℤ ⋊ ℤ

## Lens Spaces π₁(L(p,1)) ≃ ℤ/pℤ (what to read)
- **Definition** ([`LensSpace.lean`](ComputationalPaths/Path/HIT/LensSpace.lean)): Lens space L(p,1) via Heegaard decomposition:
  ```
  L(p,1) = V₁ ∪_φ V₂
  ```
  where V₁, V₂ are solid tori glued along their boundary torus.
- **Cyclic group**: `ZMod p hp` = ℤ/pℤ represented as `Fin p` with addition modulo p.
- **Solid torus HIT**: `SolidTorus` axiomatized with base point and core loop (π₁(V) ≃ ℤ).
- **Boundary torus inclusion**: `torusToSolidTorus : Torus → SolidTorus` with:
  - `meridian_trivial`: Meridian bounds disk, maps to 0 in π₁(V)
  - `longitude_to_core`: Longitude maps to generator of π₁(V)
- **Heegaard decomposition**: `LensSpace p := Pushout SolidTorus SolidTorus Torus`
- **SVK application**: The amalgamation relations from the two solid torus inclusions yield:
  ```
  π₁(L(p,1)) ≃ ℤ *_{ℤ×ℤ} ℤ ≃ ℤ/pℤ
  ```
- **Key axiom**: `lens_loop_order` — the p-th power of the fundamental loop is contractible.
- **Main theorem** (`lensPiOneEquivZMod`): π₁(L(p,1)) ≃ ℤ/pℤ, assuming `HasLensPiOneEncode p hp`.
- **Special cases**:
  - L(1,1) ≃ S³ (3-sphere)
  - L(2,1) ≃ RP³ (real projective 3-space)
- **Significance**: First SVK example producing **finite cyclic groups**, complementing infinite groups (ℤ from S¹, ℤ×ℤ from T², ℤ*ℤ from S¹∨S¹).
- Reference: Hatcher, "Algebraic Topology", Section 1.2; Rolfsen, "Knots and Links", Chapter 9.

## Möbius Band & Cylinder (what to read)
- Both spaces are homotopy equivalent to S¹, so π₁ ≃ ℤ.
- [`MobiusBand.lean`](ComputationalPaths/Path/HIT/MobiusBand.lean): Central loop generates π₁; twist affects fiber structure but not fundamental group.
- [`Cylinder.lean`](ComputationalPaths/Path/HIT/Cylinder.lean): Two boundary circles with connecting segment; surface relation ensures π₁ ≃ ℤ.
- Reference: [de Veras, Ramos, de Queiroz & de Oliveira, *On the Calculation of Fundamental Groups in Homotopy Type Theory by Means of Computational Paths* (2018)](https://arxiv.org/abs/1804.01413).

## Pushouts & Seifert-van Kampen (what to read)
- **Pushout HIT** ([`Pushout.lean`](ComputationalPaths/Path/HIT/Pushout.lean)): Defines the pushout of a span A ←f─ C ─g→ B with:
  - Point constructors `inl : A → Pushout` and `inr : B → Pushout`
  - Path constructor `glue : ∀c, Path (inl (f c)) (inr (g c))`
  - Full eliminators (`rec`, `ind`) with computation rules
  - Special cases: wedge sum (A ∨ B), suspension (ΣA)
- **Free products** ([`PushoutPaths.lean`](ComputationalPaths/Path/HIT/PushoutPaths.lean)):
  - `FreeProductWord G₁ G₂`: Alternating sequences from two groups
  - `AmalgamatedFreeProduct G₁ G₂ H i₁ i₂`: Quotient by i₁(h) = i₂(h)
- **Seifert-van Kampen theorem**: `seifertVanKampenEquiv` establishes
  ```
  π₁(Pushout A B C f g, inl(f c₀)) ≃ π₁(A, f c₀) *_{π₁(C,c₀)} π₁(B, g c₀)
  ```
- **Wedge sum case**: `wedgeFundamentalGroupEquiv` gives π₁(A ∨ B) ≃ π₁(A) * π₁(B) (ordinary free product, since π₁(pt) is trivial).
- Reference: Favonia & Shulman, *The Seifert-van Kampen Theorem in HoTT*; HoTT Book Chapter 8.7.

## Figure-Eight Space (S¹ ∨ S¹) (what to read)
- **Definition** ([`FigureEight.lean`](ComputationalPaths/Path/HIT/FigureEight.lean)): `FigureEight := Wedge Circle Circle circleBase circleBase`
- **Two generators**: `loopA` (left circle) and `loopB` (right circle, conjugated by glue)
- **Main theorem** (`figureEightPiOneEquiv`): π₁(S¹ ∨ S¹) ≃ FreeProductWord ℤ ℤ
- **Proof structure**:
  1. Apply `wedgeFundamentalGroupEquiv` to get π₁(S¹ ∨ S¹) ≃ π₁(S¹) * π₁(S¹)
  2. Lift `circlePiOneEquivInt : π₁(S¹) ≃ ℤ` via `freeProductWordEquiv`
- **Non-abelianness**: `wordAB ≠ wordBA` proves the fundamental group is non-abelian
- The figure-eight is the simplest space with non-abelian π₁, making it important for testing SVK applications.

## Bouquet of n Circles (∨ⁿS¹) (what to read)
- **Definition** ([`BouquetN.lean`](ComputationalPaths/Path/HIT/BouquetN.lean)): Higher-inductive type with:
  - Base point `bouquetBase`
  - n loops `bouquetLoop i` for `i : Fin'B n`
  - Recursion principle `bouquetRec` with computation rules
- **Free group representation** (`BouquetFreeGroup n`):
  - `BouquetWord n`: Words built from letters (generator index + non-zero integer power)
  - `BouquetRel n`: Relation combining/canceling adjacent same-generator letters
  - Quotient gives the free group F_n
- **Main theorem** (`bouquetPiOneEquiv`):
  ```lean
  π₁(∨ⁿS¹, base) ≃ BouquetFreeGroup n ≃ F_n
  ```
- **Encode-decode structure**:
  - `decodeWord`: BouquetWord → LoopSpace (via loop iteration)
  - `encodeLoop`: LoopSpace → BouquetWord (axiomatized)
  - Round-trip properties establish the equivalence
- **Special cases**:
  - **n = 0**: `bouquetPiOne_zero_trivial` — π₁ is trivial (π₁ = 1)
  - **n = 1**: Recovers π₁(S¹) ≃ ℤ
  - **n = 2**: Recovers figure-eight π₁(S¹ ∨ S¹) ≃ ℤ * ℤ
- **Loop iteration axioms**:
  - `iterateLoopInt_add`: l^m · l^n ≈ l^{m+n}
  - `iterateLoopInt_cancel`: l^m · l^{-m} ≈ refl
  - `iterateLoopInt_zero`: l^0 = refl
- The bouquet generalizes the figure-eight to arbitrary numbers of generators, providing a parametric family of free groups.

## 2-Sphere π₁(S²) ≅ 1 (what to read)
- **Definition** ([`Sphere.lean`](ComputationalPaths/Path/HIT/Sphere.lean)): `Sphere2 := Suspension Circle` (suspension of S¹)
- **Mathematical insight**: S² = Σ(S¹) = Pushout PUnit' PUnit' Circle, with both PUnit' having trivial π₁
- **Main theorem** (`sphere2_pi1_trivial`): π₁(S²) ≅ 1 (trivial group)
- **Proof via SVK**: When π₁(A) = π₁(B) = 1 in the pushout, the amalgamated free product collapses:
  ```
  π₁(S²) = 1 *_{π₁(S¹)} 1 = 1
  ```
- **Key lemmas**:
  - `punit_isPathConnected`: PUnit' is path-connected
  - `punit_piOne_trivial`: π₁(PUnit') ≅ 1
  - `sphere2_isPathConnected`: S² is path-connected
- Reference: HoTT Book, Chapter 8.6.

## Orientable Genus-g Surfaces π₁(Σ_g) (what to read)
- **Definition** ([`OrientableSurface.lean`](ComputationalPaths/Path/HIT/OrientableSurface.lean)): Higher-inductive type with:
  - Base point `base g`
  - 2g generators: loops `loopA g i` and `loopB g i` for i < g
  - 2-cell: `surfaceRelation` asserting [a₁,b₁]...[a_g,b_g] = refl
- **Surface group presentation** (`SurfaceGroupPresentation g`):
  ```
  ⟨a₁, b₁, ..., a_g, b_g | [a₁,b₁][a₂,b₂]...[a_g,b_g] = 1⟩
  ```
  where [a,b] = aba⁻¹b⁻¹ is the commutator.
- **Main theorem** (`piOneEquivPresentation`):
  ```lean
  π₁(Σ_g) ≃ SurfaceGroupPresentation g
  ```
- **Encode-decode structure**:
  - `decodePath`: FreeGroupWord → Path (constructive, with full proofs)
  - `encodePath`: Path → FreeGroupWord (via HIT recursion)
  - `decodePath_respects_rel`: decode preserves group relations using RwEq lemmas
  - Round-trip properties establish the equivalence
- **Special cases**:
  - **Genus 0** (S²): `genus0_equiv_unit` gives π₁(Σ₀) ≃ Unit (trivial)
  - **Genus 1** (T²): `genus1_equiv_ZxZ` gives π₁(Σ₁) ≃ ℤ × ℤ (abelian, since [a,b] = 1)
  - **Genus ≥ 2**: `genus_ge2_nonabelian` proves non-commutativity
- **Euler characteristic**: `eulerCharacteristic g = 2 - 2*g` with `euler_determines_genus`
- **Mathematical background**: The proof uses SVK on the decomposition:
  ```
  Σ_g = (Σ_g \ disk) ∪_{S¹} disk
  ```
  where (Σ_g \ disk) ≃ ⋁_{i=1}^{2g} S¹ has π₁ = F_{2g} (free group), the disk has trivial π₁, and the boundary circle maps to [a₁,b₁]...[a_g,b_g].
- Reference: HoTT Book Chapter 8.6; Hatcher, Algebraic Topology Section 1.2.

## Axioms and assumptions

This project tries to minimize **Lean kernel axioms**. We distinguish:

- **Kernel axioms**: Lean `axiom` declarations that extend the trusted base.
- **Assumptions**: explicit hypotheses (usually typeclasses), ranging from `Prop`-valued markers
  (e.g. `HasUnivalence`) to `Type`-valued data interfaces (e.g. `HasCirclePiOneEncode`). These do
  **not** extend the kernel, but must be discharged by providing an instance/proof.

### Measuring kernel axioms

- Kernel axiom inventory for `import ComputationalPaths`:
  - `.\lake.cmd env lean Scripts/AxiomInventory.lean`
- Kernel axiom dependencies for a specific declaration:
  - `.\lake.cmd env lean Scripts/AxiomDependencies.lean` (edit the target name inside the file)
- Typeclass assumption dependencies for a specific declaration:
  - `.\lake.cmd env lean Scripts/AssumptionDependencies.lean` (edit the target name inside the file)
- Quick survey of key theorems’ assumptions:
  - `.\lake.cmd env lean Scripts/AssumptionSurvey.lean`

### Current status

- `Scripts/AxiomInventory.lean` reports **45 kernel axioms** for `import ComputationalPaths`: **43 HIT interface axioms** (types/constructors/recursors) for:
  - `Circle`, `Cylinder`, `Torus`, `KleinBottle`, `MobiusBand`, `ProjectivePlane`, `OrientableSurface`
  - Plus **2 confluence axioms** (`local_confluence`, `step_strip_prop`) justified by critical pair analysis.
- `Scripts/AxiomDependencies.lean` reports that `circlePiOneEquivInt` depends on only the **circle generators** (3 kernel axioms: `Circle`, `circleBase`, `circleLoop`).

Non-kernel assumptions that are intentionally explicit (selected examples):

- **Circle π₁ equivalence data**: `ComputationalPaths.Path.HasCirclePiOneEncode` (minimal interface used by `circlePiOneEquivInt`).
- **(Optional) Raw circle loop normal forms**: `ComputationalPaths.Path.HasCircleLoopDecode` (used only for raw-loop statements; derivable from `HasCirclePiOneEncode`).

### Opt-in axiom imports

For convenience, you can import an "assumption-free" version of each π₁ result that adds the corresponding `Has*PiOneEncode` typeclass **as a kernel axiom**. These are intentionally **not** imported by `ComputationalPaths` by default, but provide a simpler API when you don't want to thread typeclass hypotheses:

| Import | Provides | Wrapper function |
|--------|----------|------------------|
| `ComputationalPaths.Path.HIT.CirclePiOneAxiom` | `HasCirclePiOneEncode` | `circlePiOneEquivInt' : π₁(S¹) ≃ ℤ` |
| `ComputationalPaths.Path.HIT.TorusPiOneAxiom` | `HasTorusPiOneEncode` | `torusPiOneEquivIntProd' : π₁(T²) ≃ ℤ × ℤ` |
| `ComputationalPaths.Path.HIT.ProjectivePiOneAxiom` | `HasProjectivePiOneEncode` | `projectivePiOneEquivZ2' : π₁(RP²) ≃ Bool` |
| `ComputationalPaths.Path.HIT.KleinPiOneAxiom` | `HasKleinPiOneEncode` | `kleinPiOneEquivIntProd' : π₁(K) ≃ ℤ × ℤ` |
| `ComputationalPaths.Path.HIT.LensPiOneAxiom` | `HasLensPiOneEncode` | `lensPiOneEquivZMod' : π₁(L(p,1)) ≃ ℤ/pℤ` |

See `docs/axioms.md` for detailed documentation on each opt-in axiom file.

- **Univalence marker**: `ComputationalPaths.Path.HasUnivalence`.
  - Used by some HoTT-style developments to model “transport along `ua` computes to the equivalence”.
  - **Cannot be instantiated in standard Lean** (proof-irrelevance makes it inconsistent); see `docs/axioms.md` and `Scripts/UnivalenceInconsistency.lean`.
- **Pushout / SVK**: `Pushout.HasGlueNaturalLoopRwEq`, `ComputationalPaths.Path.HIT.PushoutPaths.HasPushoutSVKEncodeQuot`, `ComputationalPaths.Path.HIT.PushoutPaths.HasPushoutSVKDecodeEncode`, `ComputationalPaths.Path.HIT.PushoutPaths.HasPushoutSVKEncodeDecode`, and the Prop-only alternative `ComputationalPaths.Path.HIT.PushoutPaths.HasPushoutSVKDecodeAmalgBijective` (and full `Pushout.HasGlueNaturalRwEq` when needed).
- **Confluence axioms** (justified by critical pair analysis + termination):
  - `local_confluence`: Any two single-step reductions from the same source can be joined.
  - `step_strip_prop`: Strip lemma — single step joins with multi-step derivation.

See `docs/axioms.md` for the authoritative overview.

### Removed global collapse assumptions

We intentionally do **not** assume global UIP-like collapse principles (e.g. the old `Step.canon` / “`toEq` implies `RwEq`”), because they contradict π₁(S¹) ≃ ℤ.

## Contributing
- Build after non-trivial edits: `./lake.cmd build`.
- Keep docstrings in sync, prefer small, focused lemmas with `@[simp]` where useful.
- The simplifier linter flags unused simp arguments; please trim them.
- When a structure adds data on top of an existing interface, prefer extending the smaller structure (e.g. `WeakGroupoid` extends `WeakCategory`) to keep identities/composition definitions in one place.

## Maintenance / refactor opportunities
- **Torus step module**: [`TorusStep.lean`](ComputationalPaths/Path/HIT/TorusStep.lean) now parallels [`CircleStep.lean`](ComputationalPaths/Path/HIT/CircleStep.lean). Adding quotient-level winding-number algebra lemmas (loops, multiplication, etc.) would further reduce proof duplication.
- **Axioms to constructions**: circle and torus HITs are still axioms; replacing them with concrete constructions or a general HIT layer remains an open project.
- **Developer docs**: a short tutorial showing how to apply the π₁ equivalences downstream (e.g. deriving homomorphisms into ℤ) would help new contributors.

## Citation
- Based on the development of computational paths and the fundamental group of the circle. See `docs` for source materials.

## References

This formalisation is based on the following papers:

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

### Background (HoTT & Type Theory)
- Univalent Foundations Program, [*Homotopy Type Theory: Univalent Foundations of Mathematics*](https://homotopytypetheory.org/book/), IAS, 2013.
- Licata & Shulman, [*Calculating the Fundamental Group of the Circle in Homotopy Type Theory*](https://doi.org/10.1109/LICS.2013.28), LICS 2013.
- Hofmann & Streicher, *The groupoid model refutes uniqueness of identity proofs*, LICS 1994.

### Related Work (Differential Geometry in Lean)
- Bordg & Cavalleri, [*Elements of Differential Geometry in Lean*](https://arxiv.org/abs/2108.00484), arXiv:2108.00484, 2021. (Formalizes smooth manifolds, tangent bundles, and Lie groups in Lean — complementary approach to π₁ via covering spaces rather than HITs.)

## Citing This Repository

If you use this formalisation in your work, please cite:

```bibtex
@software{ComputationalPathsLean2025,
  author       = {Ramos, Arthur F. and de Veras, Tiago M. L. and 
                  de Queiroz, Ruy J. G. B. and de Oliveira, Anjolina G.},
  title        = {Computational Paths in {Lean} 4},
  year         = {2025},
  publisher    = {GitHub},
  url          = {https://github.com/Arthur742Ramos/ComputationalPathsLean},
  note         = {Lean 4 formalisation of propositional equality via 
                  computational paths and fundamental groups of HITs}
}
```
