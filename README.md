# Computational Paths (Lean 4)

[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)]()
[![Axioms](https://img.shields.io/badge/kernel%20axioms-0-blue)]()
[![Sorries](https://img.shields.io/badge/sorries-0-blue)]()
[![Lean](https://img.shields.io/badge/Lean-4-orange)]()

Lean 4 formalisation of propositional equality via **explicit computational paths** and rewrite equality. Unlike Lean's built-in `Eq` type which is proof-irrelevant, `Path a b` stores an explicit list of rewrite steps—making equality computational. This machinery provides transport, symmetry, congruence, rewrite quotients, and normalisation, and uses it to formalise fundamental groups of computational-path constructions.

## Project Status

| Metric | Value |
|--------|-------|
| **Lean Modules** | 525+ (in ComputationalPaths/) |
| **Lines of Code** | ~117,000 |
| **Build Jobs** | 140 |
| **Kernel Axioms** | **0** (fully axiom-free) |
| **Sorries** | **0** (all proofs complete) |
| **Derived Theorems** | 307+ uses of `rweq_of_step` |

## Core Concept: Computational Paths

The key type is `Path a b` which consists of:
```lean
structure Path {A : Type u} (a b : A) where
  steps : List (Step A)   -- Explicit rewrite step witnesses
  proof : a = b           -- Derived equality
```

Paths compose via `trans` (concatenating step lists), invert via `symm` (reversing and inverting steps), and are related by the `RwEq` equivalence (the symmetric-transitive closure of the LND_EQ-TRS rewrite system from de Queiroz et al.).

## Computational Paths vs HoTT Identity Types

This development is *not* a HoTT identity-type formalisation. A computational
path is a **trace-carrying wrapper around Lean's propositional equality**:

- `Path a b` stores `proof : a = b` in `Prop`, so UIP/proof irrelevance is
  intentional and relied upon.
- `steps : List (Step A)` is metadata: it records a rewrite trace used by the
  LND_EQ-TRS rewrite system, but it does **not** change the equality semantics.
- Different traces can witness the same equality; `Path.toEq` forgets the trace.
- Univalence (when assumed) is modelled as *propositional* equality plus an
  empty trace; coherence comes from proof irrelevance, not higher paths.

In short: computational paths are explicit equality traces inside extensional
type theory (Lean's `Eq`), not a HoTT identity-type formalisation. They are meant
to preserve rewrite information while keeping equality proof-irrelevant.

## Key Theorems

| Theorem | Statement | Module |
|---------|-----------|--------|
| **π₁(S¹) ≃ ℤ** | Circle fundamental group is integers | `CircleStep.lean` |
| **π₁(T²) ≃ ℤ × ℤ** | Torus fundamental group | `TorusStep.lean` |
| **π₁(S²) ≃ 1** | 2-sphere is simply connected | `SphereCompPath.lean` |
| **Seifert-van Kampen** | π₁(Pushout) ≃ amalgamated free product | `PushoutPaths.lean` |
| **ω-Groupoid Structure** | Types form weak ω-groupoids | `OmegaGroupoid.lean` |
| **Confluence** | LND_EQ-TRS is confluent (Newman's Lemma) | `ConfluenceProof.lean` |
| **Basepoint Independence** | π₁(A,a) ≃ π₁(A,b) via conjugation | `FundamentalGroupoid.lean` |
| **Product π₁** | π₁(A×B) ≃ π₁(A) × π₁(B) | `ProductFundamentalGroup.lean` |
| **Higher Product** | π_n(A×B) ≃ π_n(A) × π_n(B) | `HigherProductHomotopy.lean` |
| **Abelianization** | F_n^ab ≃ ℤⁿ (axiom-free) | `Abelianization.lean` |

## Highlights
- **Weak ω-groupoid structure**: Complete proof that computational paths form a weak ω-groupoid with all coherence laws (pentagon, triangle) and contractibility at higher dimensions.
- **Derived groupoid theorems** (axiom-free): Cancellation laws, uniqueness of inverses, mixed trans/symm cancellation, whiskering, and conjugation — all derived from primitive Step rules with no custom axioms.
- **Path algebra derived results** (axiom-free): Four-fold associativity, symmetry-transitivity interactions, congruence composition, pentagon components, and Eckmann-Hilton preparation lemmas.
- **Higher homotopy groups π_n**: Iterated loop spaces (Loop2Space, Loop3Space), π₂(A,a) via derivation quotients, Eckmann-Hilton argument proving π₂ is abelian, and π₂(S²) ≅ 1.
- **Truncation levels (n-types)**: Full hierarchy connecting ω-groupoid to HoTT: IsContr → IsProp → IsSet → IsGroupoid, with all types automatically 1-groupoids via contractibility₃.
- **Fibrations and fiber sequences**: Fiber types, type families as fibrations, path lifting, connecting map ∂ : π₁(B) → F, and long exact sequence of homotopy groups.
- **Higher homotopy (legacy removed)**: Hopf fibration, π₂(S²), π₃(S²), James construction, and Freudenthal suspension were legacy axiomatic modules and have been removed.
- **Suspension-loop adjunction**: Pointed types and maps infrastructure, suspension as pointed type, adjunction map construction, and legacy Freudenthal scaffolding (removed).
- **Seifert-van Kampen theorem**: Full encode-decode proof that π₁(Pushout) ≃ π₁(A) *_{π₁(C)} π₁(B) (amalgamated free product), with special case π₁(A ∨ B) ≃ π₁(A) * π₁(B) for wedge sums.
- **Lens spaces (legacy removed)**: The lens space module and its encode/decode assumptions were removed as legacy placeholders.
- **2-Sphere** (S²): π₁(S²) ≅ 1 (trivial) via SVK applied to the suspension decomposition Σ(S¹), plus π₂(S²) ≅ 1 via contractibility₃.
- **Figure-eight space** (S¹ ∨ S¹): basic loops are defined; π₁ equivalence to π₁(S¹) * π₁(S¹) is formalized via the wedge SVK interface.
- **Bouquet of n circles** (∨ⁿS¹): free group model and decode map defined; π₁ equivalence is not yet formalized.
- **Path simplification tactics**: 29 tactics including `path_simp`, `path_auto`, `path_normalize`, `path_beta`, `path_eta`, plus structural tactics (`path_inv_inv`, `path_inv_distr`, `path_cancel_left/right`, `path_then_cancel_left/right`) and congruence tactics (`path_congr_symm`, `path_congrArg`) for automated RwEq reasoning.
- **Free group abelianization** (axiom-free): Constructive proof that F_n^ab ≃ ℤⁿ with full encode-decode equivalence.
- **Covering space theory**: Total spaces, path lifting, π₁-action on fibers, universal cover, deck transformations.
- **Simplicial path coherence**: `Simplicial/PathCoherence.lean` transports horns and horn fillers along path-preserving simplicial maps, with explicit `Path.Step`/`RwEq` witnesses for mapped-face normalization and image Kan/inner-Kan conditions.
- **Confluence of LND_EQ-TRS**: Complete proof that the computational path rewrite system is confluent via Newman's Lemma (local confluence + termination). Critical pair analysis for all core path algebra rules including the challenging inverse-related pairs.
- **Geometric representation theory paths**: `GRT/PerverseSheafPaths.lean` and `GRT/DModulePaths.lean` package perverse sheaf and D-module constructions with explicit `Path.Step`/`RwEq` computational witnesses.
- Loop quotients and π₁(A, a) as rewrite classes with strict group laws.
- Computational-path circle interface + π₁(S¹) ≃ ℤ via winding number (requires `HasCirclePiOneEncode`; optional raw-loop interface `HasCircleLoopDecode` is derivable).
- Completed proof π₁(S¹) ≃ ℤ using an encode–decode argument with quotient→equality reduction.
- Completed proof π₁(T²) ≃ ℤ × ℤ via the encode/decode equivalence `torusPiOneEquivIntProd` (requires `HasTorusPiOneEncode`; optional raw-loop interface `HasTorusLoopDecode` is derivable).
- **Fundamental groupoid Π₁(X)**: Explicit groupoid structure with basepoint independence theorem (π₁(A,a) ≃ π₁(A,b) via path conjugation) and functoriality (f : A → B induces Π₁(f) : Π₁(A) → Π₁(B)).
- **Product fundamental group theorem**: π₁(A × B, (a,b)) ≃ π₁(A, a) × π₁(B, b) via path projection/pairing, enabling inductive computation of π₁(T^n) ≃ ℤⁿ.
- **Higher product homotopy**: π_n(A × B) ≃ π_n(A) × π_n(B) for all n, generalizing the π₁ product theorem to higher homotopy groups. Application: π_n(Tᵏ) = 0 for n ≥ 2.
- **Lie group connections**: SO(2) ≃ U(1) ≃ S¹ with π₁ ≃ ℤ, n-torus T^n = (S¹)^n as maximal torus in U(n), simply connected groups, ℤ₂ fundamental groups (SO(n) for n ≥ 3 via RP²), and comparison with Bordg-Cavalleri differential geometry approach.
- **Projective spaces**: Real/complex projective space pi_1 models (RP^1 ~= Z, RP^n>=2 ~= Z/2, CP^n ~= 1) in `CompPath/ProjectiveSpace.lean`.
- **Cellular homology (legacy removed)**: Cellular homology module was removed as legacy placeholder code.

## Quick Start
- Build: `lake build`
- Run demo: `lake exe computational_paths` (prints version)
- Open in VS Code: install Lean 4 extension, open the folder, and build.

## Project Layout (selected)

### Core Path Infrastructure
- [`ComputationalPaths/Path/Basic/`](ComputationalPaths/Path/Basic/) — core path definitions: `Path` structure with explicit step lists, `Step` elementary rewrites, transport, congruence (`congrArg`), symmetry (`symm`), transitivity (`trans`), and `Context` for substitution.
- [`ComputationalPaths/Path/Basic/Core.lean`](ComputationalPaths/Path/Basic/Core.lean) — the fundamental `Path` and `Step` structures that store explicit rewrite witnesses.
- [`ComputationalPaths/Path/Basic/Congruence.lean`](ComputationalPaths/Path/Basic/Congruence.lean) — `mapLeft`, `mapRight`, `map2` for binary functions, product paths (`prodMk`, `fst`, `snd`), sigma paths (`sigmaMk`, `sigmaFst`, `sigmaSnd`).
- [`ComputationalPaths/Path/Basic/Context.lean`](ComputationalPaths/Path/Basic/Context.lean) — contextual substitution (`substLeft`, `substRight`) implementing Definition 3.5 of de Queiroz et al.

### Rewrite System (LND_EQ-TRS)
- [`ComputationalPaths/Path/Rewrite/`](ComputationalPaths/Path/Rewrite/) — the term rewriting system for path equality.
- [`ComputationalPaths/Path/Rewrite/Step.lean`](ComputationalPaths/Path/Rewrite/Step.lean) — **47 primitive rewrite rules** including: symm_refl, symm_symm, trans_refl_left/right, trans_symm, symm_trans, symm_trans_congr, trans_assoc, map2_subst, product/sigma beta-eta, sum recursors, function beta-eta, transport rules (26-29), and context substitution rules (33-47).
- [`ComputationalPaths/Path/Rewrite/Rw.lean`](ComputationalPaths/Path/Rewrite/Rw.lean) — `Rw` reflexive-transitive closure of `Step`.
- [`ComputationalPaths/Path/Rewrite/RwEq.lean`](ComputationalPaths/Path/Rewrite/RwEq.lean) — `RwEq` symmetric-transitive closure (path equivalence), congruence lemmas, `rweq_of_step` lifting.
- [`ComputationalPaths/Path/Rewrite/Quot.lean`](ComputationalPaths/Path/Rewrite/Quot.lean) — quotient `PathRwQuot` for path equality classes.

### Derived Theorems (Axiom-Free)
- [`ComputationalPaths/Path/GroupoidDerived.lean`](ComputationalPaths/Path/GroupoidDerived.lean) — **41 uses of `rweq_of_step`**: cancellation laws (`rweq_cancel_left/right`), uniqueness of inverses (`rweq_inv_unique_left/right`), mixed trans/symm cancellation, whiskering and conjugation laws.
- [`ComputationalPaths/Path/PathAlgebraDerived.lean`](ComputationalPaths/Path/PathAlgebraDerived.lean) — **22 uses of `rweq_of_step`**: four-fold associativity, symm/trans interactions (`rweq_symm_trans_three`), congruence composition (`rweq_congrArg_comp`), pentagon coherence components.
- [`ComputationalPaths/Path/PathAlgebraHomomorphism.lean`](ComputationalPaths/Path/PathAlgebraHomomorphism.lean) — path algebra homomorphisms, category laws, and isomorphism lemmas.
- [`ComputationalPaths/Path/PathAlgebraModule.lean`](ComputationalPaths/Path/PathAlgebraModule.lean) — modules over path algebras: left/right modules, submodules, quotients, tensor products.
- [`ComputationalPaths/Path/StepDerived.lean`](ComputationalPaths/Path/StepDerived.lean) — **27 uses of `rweq_of_step`**: direct lifts of Step rules including symm_trans_congr (Rule 7), map2_subst (Rule 9), product/sigma/sum rules (10-24), transport rules (26), and context substitution rules (33-47).
- [`ComputationalPaths/Path/ProductSigmaDerived.lean`](ComputationalPaths/Path/ProductSigmaDerived.lean) — product/sigma path algebra: composition, symmetry, projection naturality, map2 decomposition.
- [`ComputationalPaths/Path/TransportDerived.lean`](ComputationalPaths/Path/TransportDerived.lean) — transport coherence: triple composition, associativity, double symmetry, round-trip identities.

### Groupoid and ω-Groupoid Structure
- [`ComputationalPaths/Path/Groupoid.lean`](ComputationalPaths/Path/Groupoid.lean) — weak and strict categorical packages for computational paths; groupoids extend the corresponding categories so composition/identities are shared.
- [`ComputationalPaths/Path/OmegaGroupoid.lean`](ComputationalPaths/Path/OmegaGroupoid.lean) — **weak ω-groupoid structure** on computational paths with cells at each dimension, globular identities, and all coherence laws.
- [`ComputationalPaths/Path/OmegaGroupoid/`](ComputationalPaths/Path/OmegaGroupoid/) — subdirectory with derived coherences and supporting notes:
  - [`Derived.lean`](ComputationalPaths/Path/OmegaGroupoid/Derived.lean) — demonstrates that most coherence axioms are derivable from `to_canonical`
  - [`StepToCanonical.lean`](ComputationalPaths/Path/OmegaGroupoid/StepToCanonical.lean) — the key `to_canonical` axiom and its justification
  - [`TypedRewriting.lean`](ComputationalPaths/Path/OmegaGroupoid/TypedRewriting.lean) — typed rewriting system foundations
- [`ComputationalPaths/Path/Homotopy/`](ComputationalPaths/Path/Homotopy/) — loop spaces, rewrite monoids (`LoopMonoid`), loop groups (`LoopGroup`), π₁ interfaces, higher homotopy groups, truncation levels, and covering spaces.
- [`ComputationalPaths/Path/Homotopy/HigherHomotopy.lean`](ComputationalPaths/Path/Homotopy/HigherHomotopy.lean) — higher homotopy groups π_n via iterated loop spaces and derivation quotients.
- [`ComputationalPaths/Path/Homotopy/Truncation.lean`](ComputationalPaths/Path/Homotopy/Truncation.lean) — truncation levels (IsContr, IsProp, IsSet, IsGroupoid) connecting to HoTT n-types.
- [`ComputationalPaths/Path/Homotopy/PostnikovTower.lean`](ComputationalPaths/Path/Homotopy/PostnikovTower.lean) — Postnikov tower stages via n-groupoid truncations, convergence, and stage collapse.
- [`ComputationalPaths/Path/Homotopy/CoveringSpace.lean`](ComputationalPaths/Path/Homotopy/CoveringSpace.lean) — covering space theory with path lifting and π₁-actions on fibers.
- [`ComputationalPaths/Path/Homotopy/Fibration.lean`](ComputationalPaths/Path/Homotopy/Fibration.lean) — fibrations, fiber sequences F → E → B, connecting map ∂ : π₁(B) → F, long exact sequence of homotopy groups, induced maps on π₁.
- [`ComputationalPaths/Path/Homotopy/SuspensionLoop.lean`](ComputationalPaths/Path/Homotopy/SuspensionLoop.lean) — suspension-loop adjunction [ΣX, Y]_* ≅ [X, ΩY]_*, pointed types/maps, adjunction map construction, connectivity definitions.
- [`ComputationalPaths/Path/Homotopy/FundamentalGroupoid.lean`](ComputationalPaths/Path/Homotopy/FundamentalGroupoid.lean) — **Fundamental groupoid Π₁(A)** with explicit groupoid structure, basepoint independence theorem (`basepointIsomorphism`), and functoriality (`fundamentalGroupoidMap`, `inducedPiOneMap`).
- [`ComputationalPaths/Path/Homotopy/ProductFundamentalGroup.lean`](ComputationalPaths/Path/Homotopy/ProductFundamentalGroup.lean) — **Product fundamental group theorem**: π₁(A × B, (a,b)) ≃ π₁(A, a) × π₁(B, b) via path projection (`Path.fst`, `Path.snd`) and pairing (`Path.prod`).
- [`ComputationalPaths/Path/Homotopy/HigherProductHomotopy.lean`](ComputationalPaths/Path/Homotopy/HigherProductHomotopy.lean) — **Higher product homotopy theorem**: π_n(A × B) ≃ π_n(A) × π_n(B) for all n ≥ 1, with `prodHigherPiNEquiv`. Generalizes π₁ product theorem; application: π_n(Tᵏ) = 0 for n ≥ 2.
- [`ComputationalPaths/Path/Homotopy/LieGroups.lean`](ComputationalPaths/Path/Homotopy/LieGroups.lean) — **Connections to Lie groups**: SO(2), U(1) as Circle with π₁ ≃ ℤ, n-torus T^n = (S¹)^n with `torusN_product_step` for inductive π₁(T^n) ≃ ℤⁿ, maximal tori in U(n) and SU(n), simply connected types, ℤ₂ fundamental groups, and comparison with Bordg-Cavalleri differential geometry approach.
- [`ComputationalPaths/Path/Algebra/Abelianization.lean`](ComputationalPaths/Path/Algebra/Abelianization.lean) — **Free group abelianization** F_n^ab ≃ ℤⁿ (axiom-free). Constructive encode-decode equivalence with `freeGroup_ab_equiv`, `wordToIntPow`, `liftWord_respects_BouquetRel`, and `liftBouquetFreeGroup_respects_AbelianizationRel`.
- [`ComputationalPaths/Path/Homotopy/LoopIteration.lean`](ComputationalPaths/Path/Homotopy/LoopIteration.lean) — loop iteration infrastructure supporting loop power operations and group structure.
- [`ComputationalPaths/Path/Homotopy/Coproduct.lean`](ComputationalPaths/Path/Homotopy/Coproduct.lean) — coproduct constructions for homotopy-theoretic types (no global RwEq round-trip assumptions).
- [`ComputationalPaths/Path/Homotopy/CoproductPaths.lean`](ComputationalPaths/Path/Homotopy/CoproductPaths.lean) — coproduct path codes for sums plus wedge π₁ free-product and universal map wrappers.
- [`ComputationalPaths/Path/Homotopy/Sets.lean`](ComputationalPaths/Path/Homotopy/Sets.lean) — set-theoretic constructions supporting homotopy definitions.
- [`ComputationalPaths/Path/Rewrite/PathTactic.lean`](ComputationalPaths/Path/Rewrite/PathTactic.lean) — automation tactics (`path_simp`, `path_rfl`, `path_canon`, `path_decide`) for RwEq proofs.
- [`ComputationalPaths/Path/Rewrite/PathTacticExamples.lean`](ComputationalPaths/Path/Rewrite/PathTacticExamples.lean) — comprehensive test suite for path tactics demonstrating usage patterns.
- [`ComputationalPaths/Path/Rewrite/MinimalAxioms.lean`](ComputationalPaths/Path/Rewrite/MinimalAxioms.lean) — analysis of minimal axiom requirements for the rewrite system.
- [`ComputationalPaths/Path/Rewrite/ConfluenceProof.lean`](ComputationalPaths/Path/Rewrite/ConfluenceProof.lean) — **Confluence proof** via Newman's Lemma: critical pair analysis, local confluence, strip lemma, and `HasJoinOfRw` instance.
- [`ComputationalPaths/Path/CompPath/CircleCompPath.lean`](ComputationalPaths/Path/CompPath/CircleCompPath.lean) — circle construction via path expressions, canonical `circleCompPathPiOneEquivInt : π₁(S¹) ≃ ℤ`.
- [`ComputationalPaths/Path/CompPath/CircleStep.lean`](ComputationalPaths/Path/CompPath/CircleStep.lean) — quotient-level interface `circlePiOneEquivInt : π₁(S¹) ≃ ℤ`, winding-number algebra lemmas.
- [`ComputationalPaths/Path/CompPath/Torus.lean`](ComputationalPaths/Path/CompPath/Torus.lean) — torus definition (`Circle × Circle`) in the computational-path setting.
- [`ComputationalPaths/Path/CompPath/TorusStep.lean`](ComputationalPaths/Path/CompPath/TorusStep.lean) — quotient-level `torusPiOneEquivIntProd : π₁(T²) ≃ ℤ × ℤ`.
- [`ComputationalPaths/Path/CompPath/PushoutCompPath.lean`](ComputationalPaths/Path/CompPath/PushoutCompPath.lean) — pushout construction in computational paths with constructors and elimination principles.
- [`ComputationalPaths/Path/CompPath/PushoutPaths.lean`](ComputationalPaths/Path/CompPath/PushoutPaths.lean) — path characterization for pushouts, free products, amalgamated free products, and the **Seifert-van Kampen theorem** (`seifertVanKampenEquiv`).
- [`ComputationalPaths/Path/CompPath/HomotopyPushout.lean`](ComputationalPaths/Path/CompPath/HomotopyPushout.lean) — homotopy pushout (double mapping cylinder) with universal property and pi_1 amalgamation via SVK.
- [`ComputationalPaths/Path/CompPath/WedgeFreeProductUniversal.lean`](ComputationalPaths/Path/CompPath/WedgeFreeProductUniversal.lean) — universal map from π₁(A ∨ B) built from the free-product word lift.
- [`ComputationalPaths/Path/CompPath/FigureEight.lean`](ComputationalPaths/Path/CompPath/FigureEight.lean) — figure-eight space (S¹ ∨ S¹) with basic loops.
- [`ComputationalPaths/Path/CompPath/FigureEightStep.lean`](ComputationalPaths/Path/CompPath/FigureEightStep.lean) — SVK wedge equivalence π₁(FigureEight) ≃ π₁(S¹) * π₁(S¹).
- [`ComputationalPaths/Path/CompPath/BouquetN.lean`](ComputationalPaths/Path/CompPath/BouquetN.lean) — **Bouquet of n circles** (∨ⁿS¹) with free group model and decode map; π₁ equivalence not yet formalized.
- [`ComputationalPaths/Path/CompPath/SphereCompPath.lean`](ComputationalPaths/Path/CompPath/SphereCompPath.lean) — the 2-sphere S² as suspension of S¹, with π₁(S²) ≅ 1 via SVK. Also defines S³ for the Hopf fibration.
- Wedge encode/decode is now integrated in `ComputationalPaths/Path/CompPath/PushoutPaths.lean` via `wedgeFundamentalGroupEquiv_of_decode_bijective`.
- [`ComputationalPaths/Path/Homotopy/HoTT.lean`](ComputationalPaths/Path/Homotopy/HoTT.lean) — homotopy/groupoid lemmas (reflexivity, symmetry, transitivity for identities) expressed via computational paths and exported to `Eq`.
- [`Topos/SubobjectClassifierPaths.lean`](Topos/SubobjectClassifierPaths.lean) — subobject classifier data and classifying-square coherence stated directly with `Path`/`RwEq`.
- [`Topos/InternalLogicPaths.lean`](Topos/InternalLogicPaths.lean) — internal logic over `1 ⟶ Ω` truth values with conjunction/implication coherence as computational paths.
- [`Chromatic/PathInfrastructure.lean`](Chromatic/PathInfrastructure.lean) — chromatic filtration and Morava K-theory periodicity packaged as explicit computational `Path.Step`/`RwEq` witnesses.
- [`InfinityCategory/PathInfrastructure.lean`](InfinityCategory/PathInfrastructure.lean) — quasi-category and Segal-space composition APIs with explicit `Path.Step` witnesses (`QuasiCategoryPaths`, `SegalSpacePaths`) and derived `RwEq` coherence lemmas.
- [`Perfectoid/PathInfrastructure.lean`](Perfectoid/PathInfrastructure.lean) — tilting equivalences and almost mathematics packaged as path-preserving constructions with explicit `Path.Step`/`RwEq` normalization witnesses.
- [`Tropical/PathInfrastructure.lean`](Tropical/PathInfrastructure.lean) — tropical curve balancing and valuation/tropicalization coherence packaged with explicit `Path.Step` and derived `RwEq` normalization lemmas.
- [`GRT/PathInfrastructure.lean`](GRT/PathInfrastructure.lean) — geometric representation theory path infrastructure exposing perverse sheaf and D-module computational witnesses.
- [`Langlands/PathInfrastructure.lean`](Langlands/PathInfrastructure.lean) — local and geometric Langlands path infrastructure exposing Step-based compatibility and spectral coherence witnesses.

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
- **π₂(S²) ≅ 1**: In [`SphereCompPath.lean`](ComputationalPaths/Path/CompPath/SphereCompPath.lean), `sphere2_pi2_trivial` proves all 2-loops are trivial via contractibility₃

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

Eight modules provide extensive axiom-free, sorry-free results derived purely from the primitive Step rules via `rweq_of_step`. All depend only on Lean's standard axioms (`propext`, `Quot.sound`) — no additional axioms.

**Total: 307+ uses of `rweq_of_step`** across these modules.

### GroupoidDerived.lean (56 uses of `rweq_of_step`)

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

### PathAlgebraDerived.lean (40 uses of `rweq_of_step`)

| Theorem | Description |
|---------|-------------|
| `rweq_trans_four_assoc` | Four-fold associativity: ((p·q)·r)·s ≈ p·(q·(r·s)) |
| `rweq_symm_trans` | Contravariance: (p·q)⁻¹ ≈ q⁻¹·p⁻¹ |
| `rweq_symm_trans_three` | Triple: (p·q·r)⁻¹ ≈ r⁻¹·q⁻¹·p⁻¹ |
| `rweq_congrArg_comp` | Composition: (g∘f)*(p) = g*(f*(p)) |
| `rweq_pentagon_left/right/top` | Pentagon coherence components |
| `rweq_inv_refl` | refl⁻¹ ≈ refl |
| `rweq_inv_inv` | (p⁻¹)⁻¹ ≈ p |

### StepDerived.lean (59 uses of `rweq_of_step`)

Direct lifts of primitive Step rules to RwEq equivalences:

| Theorem | Step Rule | Description |
|---------|-----------|-------------|
| `rweq_step_symm_trans_congr` | Rule 7 | Contravariance: (p·q)⁻¹ ≈ q⁻¹·p⁻¹ |
| `rweq_step_map2_subst` | Rule 9 | Decomposition: f*(p,q) ≈ f*(p,refl)·f*(refl,q) |
| `rweq_step_prod_rec_beta` | Rule 10 | Product recursor β |
| `rweq_step_prod_eta` | Rule 11 | Product η |
| `rweq_step_prod_symm` | Rule 12 | Product symm |
| `rweq_step_prod_fst` | Rule 13 | First projection |
| `rweq_step_prod_snd` | Rule 14 | Second projection |
| `rweq_step_prod_map2` | Rule 15 | Product map2 |
| `rweq_step_sigma_rec_beta` | Rule 16 | Sigma recursor β |
| `rweq_step_sigma_eta` | Rule 17 | Sigma η |
| `rweq_step_sigma_symm` | Rule 18 | Sigma symm |
| `rweq_step_sigma_snd` | Rule 19 | Sigma second projection |
| `rweq_step_sum_inl_beta` | Rule 23 | Sum inl β |
| `rweq_step_sum_inr_beta` | Rule 24 | Sum inr β |
| `rweq_step_transport_refl_beta` | Rule 26 | Transport over refl |
| `rweq_step_context_*` | Rules 33-48 | Context substitution rules |
| `rweq_depContext_*` | Rules 50-59 | Dependent context rules |
| `rweq_context_map_*` | Derived | Context functoriality |

### ProductSigmaDerived.lean

Product and sigma path algebra working with explicit `Path` structures:

| Theorem | Description |
|---------|-------------|
| `prodMk_trans` | Product composition: (p₁,p₂)·(q₁,q₂) = (p₁·q₁,p₂·q₂) |
| `prodMk_symm` | Product symmetry: (p₁,p₂)⁻¹ = (p₁⁻¹,p₂⁻¹) |
| `fst_trans`, `snd_trans` | Projection naturality |
| `map2_prodMk_decomp` | f*(p,q) via product decomposition |
| `sigmaMk_trans`, `sigmaMk_symm` | Sigma composition and symmetry |
| `sigmaFst_trans`, `sigmaSnd_trans` | Sigma projection naturality |

### TransportDerived.lean

Transport coherence laws:

| Theorem | Description |
|---------|-------------|
| `transport_trans_triple` | (p·q·r)_* ≈ r_* ∘ q_* ∘ p_* |
| `transport_trans_assoc` | ((p·q)·r)_* ≈ (p·(q·r))_* |
| `transport_symm_symm` | (p⁻¹)⁻¹_* ≈ p_* |
| `transport_roundtrip` | p⁻¹_* ∘ p_* ≈ id |
| `transport_roundtrip'` | p_* ∘ p⁻¹_* ≈ id |

### CoherenceDerived.lean (51 uses of `rweq_of_step`)

Higher coherence laws for the weak ω-groupoid structure:

| Theorem | Description |
|---------|-------------|
| `rweq_pentagon_face1..5` | All 5 faces of the pentagon identity |
| `rweq_pentagon_full` | Full pentagon: ((f·g)·h)·k → f·(g·(h·k)) |
| `rweq_triangle_full` | Triangle: (f·refl)·g → f·g |
| `rweq_trans_five_assoc` | Five-fold associativity |
| `rweq_trans_six_assoc` | Six-fold associativity |
| `rweq_trans_seven_assoc` | Seven-fold associativity |
| `rweq_whisker_left_comp` | Whiskering is functorial |
| `rweq_double_unit` | (refl·p)·refl ≈ p |
| `rweq_symm_trans_assoc` | ((p·q)·r)⁻¹ ≈ r⁻¹·(q⁻¹·p⁻¹) |
| `rweq_symm_trans_four` | Four-fold symm distribution |
| `rweq_symm_trans_five` | Five-fold symm distribution |
| `rweq_congrArg_symm_natural` | Naturality of symm under congrArg |

### BiContextDerived.lean (17 uses of `rweq_of_step`)

| Theorem | Description |
|---------|-------------|
| `rweq_biContext_mapLeft_congr` | Rule 65: BiContext left map congruence |
| `rweq_biContext_mapRight_congr` | Rule 66: BiContext right map congruence |
| `rweq_biContext_map2_congr_left` | Rule 67: BiContext map2 left congruence |
| `rweq_biContext_map2_congr_right` | Rule 68: BiContext map2 right congruence |
| `rweq_mapLeft_congr_derived` | Rule 69: mapLeft congruence |
| `rweq_mapRight_congr_derived` | Rule 70: mapRight congruence |
| `rweq_mapLeft_ofEq` | Rule 71: mapLeft with propositional equality |
| `rweq_mapRight_ofEq` | Rule 72: mapRight with propositional equality |
| `rweq_biContext_map2_decompose` | Rule 9: BiContext map2 decomposition |

### LoopDerived.lean (27 uses of `rweq_of_step`)

| Theorem | Description |
|---------|-------------|
| `rweq_loop_unit` | refl · p ≈ p |
| `rweq_loop_inv_right` | p · p⁻¹ ≈ refl |
| `rweq_loop_inv_left` | p⁻¹ · p ≈ refl |
| `rweq_loop_assoc` | (p · q) · r ≈ p · (q · r) |
| `rweq_loop_symm_trans` | (p · q)⁻¹ ≈ q⁻¹ · p⁻¹ |
| `rweq_loop_symm_trans3` | ((p·q)·r)⁻¹ ≈ r⁻¹·q⁻¹·p⁻¹ |
| `rweq_loop_conj_refl` | refl·q·refl⁻¹ ≈ q |
| `rweq_loop_self_commutator` | [p, p] ≈ refl |

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
  def Fiber.prop (x : Fiber f b) : Path (f x.point) b

  -- Fiber sequence F → E → B
  structure FiberSeq (F E B : Type u) where
    proj : E → B
    baseB : B
    baseE : E
    base_proj : Path (proj baseE) baseB
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
- [`ComputationalPaths/Path/Homotopy/LoopSpaceAdjunction.lean`](ComputationalPaths/Path/Homotopy/LoopSpaceAdjunction.lean) packages the Sigma/OmegaEq adjunction:
  - Defines Sigma/OmegaEq functors on pointed spaces with unit/counit and naturality.
  - Connects Sigma(circle) to `SuspensionCircleCompPath` and compares propositional loops to computational loops.

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

**Computational-path approach** ([`Torus.lean`](ComputationalPaths/Path/CompPath/Torus.lean), [`TorusStep.lean`](ComputationalPaths/Path/CompPath/TorusStep.lean)):
- Encoding: `torusPiOneEncode : π₁(T²) → ℤ × ℤ` from the quotient-level interface `HasTorusPiOneEncode`.
- Decoding: `torusDecode : ℤ × ℤ → π₁(T²)` assembles the z-powers of the two commuting loops.
- Equivalence: `torusPiOneEquivIntProd` shows the maps are inverse, yielding π₁(T²) ≃ ℤ × ℤ.
- Assumption: the classification data is packaged as the typeclass `HasTorusPiOneEncode`.
- Optional: raw loop normal forms are available as `HasTorusLoopDecode` and are derivable from `HasTorusPiOneEncode`.

- Proves the round-trip properties `torus_left_inv_def` and `torus_right_inv_def` constructively.
- Uses `sumPowersA`/`sumPowersB` winding number functions and the `word_eq_canonical` abelianization lemma.
- Equivalence: `piOneEquivIntProd : π₁(Torus') ≃ ℤ × ℤ` follows from the general surface group machinery.
- Demonstrates that the torus π₁ result is a special case of the orientable surface framework.

## Lens Spaces π₁(L(p,1)) ≃ ℤ/pℤ (what to read)
- Legacy module removed; no current formalization.


## Pushouts & Seifert-van Kampen (what to read)
- **Pushout construction** ([`PushoutCompPath.lean`](ComputationalPaths/Path/CompPath/PushoutCompPath.lean)): Defines the pushout of a span A ←f─ C ─g→ B with:
  - Point constructors `inl : A → Pushout` and `inr : B → Pushout`
  - Path constructor `glue : ∀c, Path (inl (f c)) (inr (g c))`
  - Full eliminators (`rec`, `ind`) with computation rules
  - Special cases: wedge sum (A ∨ B), suspension (ΣA)
- **Free products** ([`PushoutPaths.lean`](ComputationalPaths/Path/CompPath/PushoutPaths.lean)):
  - `FreeProductWord G₁ G₂`: Alternating sequences from two groups
  - `AmalgamatedFreeProduct G₁ G₂ H i₁ i₂`: Quotient by i₁(h) = i₂(h)
- **Seifert-van Kampen theorem**: `seifertVanKampenEquiv` establishes
  ```
  π₁(Pushout A B C f g, inl(f c₀)) ≃ π₁(A, f c₀) *_{π₁(C,c₀)} π₁(B, g c₀)
  ```
- **Wedge sum case**: `wedgeFundamentalGroupEquiv_of_decode_bijective` gives π₁(A ∨ B) ≃ π₁(A) * π₁(B) under `HasWedgeSVKDecodeBijective` (ordinary free product, since π₁(pt) is trivial).
- Reference: Favonia & Shulman, *The Seifert-van Kampen Theorem in HoTT*; HoTT Book Chapter 8.7.

## Figure-Eight Space (S¹ ∨ S¹) (what to read)
- **Definition** ([`FigureEight.lean`](ComputationalPaths/Path/CompPath/FigureEight.lean)): `FigureEight := Wedge Circle Circle circleBase circleBase`
- **Two generators**: `loopA` (left circle) and `loopB` (right circle, conjugated by glue)
- **Main theorem** ([`FigureEightStep.lean`](ComputationalPaths/Path/CompPath/FigureEightStep.lean)):
  `figureEightPiOneEquivFreeGroup` proves π₁(FigureEight) ≃ π₁(S¹) * π₁(S¹)
  under `HasWedgeSVKDecodeBijective`.
- **Non-abelianness**: `wordAB ≠ wordBA` proves the fundamental group is non-abelian.
- The figure-eight is the simplest space with non-abelian π₁, making it important for testing SVK.

## Bouquet of n Circles (∨ⁿS¹) (what to read)
- **Definition** ([`BouquetN.lean`](ComputationalPaths/Path/CompPath/BouquetN.lean)): Higher-inductive style type with:
  - Base point `bouquetBase`
  - n loops `bouquetLoop i` for `i : Fin'B n`
  - Recursion principle `bouquetRec` with computation rules
- **Free group representation** (`BouquetFreeGroup n`):
  - `BouquetWord n`: Words built from letters (generator index + non-zero integer power)
  - `BouquetRel n`: Relation combining/canceling adjacent same-generator letters
  - Quotient gives the free group F_n
- **Main theorem (legacy removed)**: π₁ equivalence to `BouquetFreeGroup n` is not yet formalized.
- **Decode structure**:
  - `decodeWord`: BouquetWord → LoopSpace (via loop iteration)
- **Special cases**:
  - **n = 0**: `bouquetPiOne_zero_trivial` — π₁ is trivial (π₁ = 1)
  - **n = 1**: `freeGroupOneEquivInt` — F₁ ≃ ℤ (free group side only)
- **Loop iteration axioms**:
  - `iterateLoopInt_add`: l^m · l^n ≈ l^{m+n}
  - `iterateLoopInt_cancel`: l^m · l^{-m} ≈ refl
  - `iterateLoopInt_zero`: l^0 = refl
- The bouquet generalizes the figure-eight to arbitrary numbers of generators, providing a parametric family of free groups.

## 2-Sphere π₁(S²) ≅ 1 (what to read)
- **Definition** ([`SphereCompPath.lean`](ComputationalPaths/Path/CompPath/SphereCompPath.lean)): `Sphere2 := Suspension Circle` (suspension of S¹)
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

- `Scripts/AxiomInventory.lean` reports **0 kernel axioms** for `import ComputationalPaths`.
- `Scripts/AxiomDependencies.lean` reports that `circlePiOneEquivInt` depends on no kernel axioms.

Non-kernel assumptions that are intentionally explicit (selected examples):

- **Circle π₁ equivalence data**: `ComputationalPaths.Path.HasCirclePiOneEncode` (minimal interface used by `circlePiOneEquivInt`).
- **(Optional) Raw circle loop normal forms**: `ComputationalPaths.Path.HasCircleLoopDecode` (used only for raw-loop statements; derivable from `HasCirclePiOneEncode`).

### Opt-in axiom imports

This repository no longer ships opt-in kernel-axiom wrappers for π₁ results.
To use the equivalences without threading assumptions through every theorem,
provide local or scoped instances (or define a small wrapper module in your own
project). See `docs/axioms.md` for the authoritative overview of kernel axioms
and explicit assumptions.

- **Univalence marker**: `ComputationalPaths.Path.HasUnivalence`.
  - Used by some HoTT-style developments to model “transport along `ua` computes to the equivalence”.
  - **Cannot be instantiated in standard Lean** (proof-irrelevance makes it inconsistent); see `docs/axioms.md` and `Scripts/UnivalenceInconsistency.lean`.
  - This interface is opt-in only; it is not imported by `ComputationalPaths.Path`.
- **Pushout / SVK**: `Pushout.HasGlueNaturalLoopRwEq`, `ComputationalPaths.Path.CompPath.PushoutPaths.HasPushoutSVKEncodeQuot`, `ComputationalPaths.Path.CompPath.PushoutPaths.HasPushoutSVKDecodeEncode`, `ComputationalPaths.Path.CompPath.PushoutPaths.HasPushoutSVKEncodeDecode`, and the Prop-only alternative `ComputationalPaths.Path.CompPath.PushoutPaths.HasPushoutSVKDecodeAmalgBijective` (and full `Pushout.HasGlueNaturalRwEq` when needed).
- **Confluence assumptions** (justified by critical pair analysis + termination):
  - `HasLocalConfluenceProp`: Any two single-step reductions from the same source can be joined.
  - `HasTerminationProp`: Termination of one-step rewrites (well-founded on the non-empty transitive closure).
  - These remain explicit because `Step` is Prop-valued and `Classical.choose` is used to extract witnesses.

See `docs/axioms.md` for the authoritative overview.

### Removed global collapse assumptions

We intentionally do **not** assume global UIP-like collapse principles (e.g. the old `Step.canon` / “`toEq` implies `RwEq`”), because they contradict π₁(S¹) ≃ ℤ.

## Contributing
- Build after non-trivial edits: `./lake.cmd build`.
- Keep docstrings in sync, prefer small, focused lemmas with `@[simp]` where useful.
- The simplifier linter flags unused simp arguments; please trim them.
- When a structure adds data on top of an existing interface, prefer extending the smaller structure (e.g. `WeakGroupoid` extends `WeakCategory`) to keep identities/composition definitions in one place.

## Maintenance / refactor opportunities
- **Torus step module**: [`TorusStep.lean`](ComputationalPaths/Path/CompPath/TorusStep.lean) now parallels [`CircleStep.lean`](ComputationalPaths/Path/CompPath/CircleStep.lean). Adding quotient-level winding-number algebra lemmas (loops, multiplication, etc.) would further reduce proof duplication.
- **Constructions**: circle and related interfaces are now computational-path constructions; expanding automated equivalence lemmas remains an open project.
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
- Bordg & Cavalleri, [*Elements of Differential Geometry in Lean*](https://arxiv.org/abs/2108.00484), arXiv:2108.00484, 2021. (Formalizes smooth manifolds, tangent bundles, and Lie groups in Lean — complementary approach to π₁ via covering spaces rather than axiomatic loop-space models.)

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
                  computational paths and fundamental groups of computational-path constructions}
}
```
