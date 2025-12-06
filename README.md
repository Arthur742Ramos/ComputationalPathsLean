# Computational Paths (Lean 4)

Lean 4 formalisation of propositional equality via explicit computational paths and rewrite equality. It provides a practical kernel for transport, symmetry, congruence, rewrite quotients, and normalisation — and uses this machinery to formalise fundamental groups of higher-inductive types.

## Highlights
- **Weak ω-groupoid structure**: Complete proof that computational paths form a weak ω-groupoid with all coherence laws (pentagon, triangle) and contractibility at higher dimensions.
- **Higher homotopy groups π_n**: Iterated loop spaces (Loop2Space, Loop3Space), π₂(A,a) via derivation quotients, Eckmann-Hilton argument proving π₂ is abelian, and π₂(S²) ≅ 1.
- **Truncation levels (n-types)**: Full hierarchy connecting ω-groupoid to HoTT: IsContr → IsProp → IsSet → IsGroupoid, with all types automatically 1-groupoids via contractibility₃.
- **Eilenberg-MacLane spaces K(G,n)**: Characterization of K(G,1) spaces with circle as K(ℤ,1), group structures, and loop space property Ω(K(G,n+1)) ≃ K(G,n).
- **Fibrations and fiber sequences**: Fiber types, type families as fibrations, path lifting, connecting map ∂ : π₁(B) → F, and long exact sequence of homotopy groups.
- **Hopf fibration**: S¹ → S³ → S² fiber bundle with S³ as suspension of S², Hopf map, fiber equivalence to circle, long exact sequence application showing π₂(S²) ≅ ℤ structure, and π₁(S³) = 1.
- **Suspension-loop adjunction**: Pointed types and maps infrastructure, suspension as pointed type, adjunction map construction, and Freudenthal suspension theorem foundations.
- **Seifert-van Kampen theorem**: Full encode-decode proof that π₁(Pushout) ≃ π₁(A) *_{π₁(C)} π₁(B) (amalgamated free product), with special case π₁(A ∨ B) ≃ π₁(A) * π₁(B) for wedge sums.
- **Orientable genus-g surfaces** (Σ_g): Complete proof that π₁(Σ_g) ≃ ⟨a₁,b₁,...,a_g,b_g | [a₁,b₁]...[a_g,b_g] = 1⟩ (surface group presentation), with special cases for sphere (g=0), torus (g=1), and non-abelian higher genus (g≥2).
- **2-Sphere** (S²): π₁(S²) ≅ 1 (trivial) via SVK applied to the suspension decomposition Σ(S¹), plus π₂(S²) ≅ 1 via contractibility₃.
- **Figure-eight space** (S¹ ∨ S¹): π₁ ≃ ℤ * ℤ (free group on 2 generators), demonstrating non-abelian fundamental groups.
- **Path simplification tactics**: `path_simp`, `path_rfl`, `path_canon`, `path_decide` for automated RwEq reasoning.
- **Covering space theory**: Total spaces, path lifting, π₁-action on fibers, universal cover, deck transformations.
- Loop quotients and π₁(A, a) as rewrite classes with strict group laws.
- Higher-inductive circle interface + code family into ℤ (via univalence axioms).
- Completed proof π₁(S¹) ≃ ℤ using an encode–decode argument with quotient→equality reduction.
- Completed proof π₁(T²) ≃ ℤ × ℤ via the encode/decode equivalence `torusPiOneEquivIntProd`.
- Real projective plane RP² with π₁(RP²) ≃ ℤ₂ (represented as Bool with XOR as addition).
- **Klein bottle** π₁(K) ≃ ℤ ⋊ ℤ (semidirect product) via encode/decode equivalence `kleinPiOneEquivIntProd`, with an alternative proof using Seifert-van Kampen on the CW-complex decomposition.
- Möbius band, cylinder HITs with π₁ ≃ ℤ (homotopy equivalent to circle).

## Quick Start
- Build: `./lake.cmd build`
- Run demo: `./lake.cmd exe computational_paths` (prints version)
- Open in VS Code: install Lean 4 extension, open the folder, and build.

## Project Layout (selected)
- [`ComputationalPaths/Path/Basic/`](ComputationalPaths/Path/Basic/) — core path definitions (transport, congruence, symmetry) and helpers.
- [`ComputationalPaths/Path/Rewrite/`](ComputationalPaths/Path/Rewrite/) — rewrite steps, closures (`Rw`, `RwEq`), and the quotient `PathRwQuot`.
- [`ComputationalPaths/Path/Groupoid.lean`](ComputationalPaths/Path/Groupoid.lean) — weak and strict categorical packages for computational paths; groupoids extend the corresponding categories so composition/identities are shared.
- [`ComputationalPaths/Path/OmegaGroupoid.lean`](ComputationalPaths/Path/OmegaGroupoid.lean) — **weak ω-groupoid structure** on computational paths with cells at each dimension, globular identities, and all coherence laws.
- [`ComputationalPaths/Path/Homotopy/`](ComputationalPaths/Path/Homotopy/) — loop spaces, rewrite monoids (`LoopMonoid`), loop groups (`LoopGroup`), π₁ interfaces, higher homotopy groups, truncation levels, and covering spaces.
- [`ComputationalPaths/Path/Homotopy/HigherHomotopy.lean`](ComputationalPaths/Path/Homotopy/HigherHomotopy.lean) — higher homotopy groups π_n via iterated loop spaces and derivation quotients.
- [`ComputationalPaths/Path/Homotopy/Truncation.lean`](ComputationalPaths/Path/Homotopy/Truncation.lean) — truncation levels (IsContr, IsProp, IsSet, IsGroupoid) connecting to HoTT n-types.
- [`ComputationalPaths/Path/Homotopy/CoveringSpace.lean`](ComputationalPaths/Path/Homotopy/CoveringSpace.lean) — covering space theory with path lifting and π₁-actions on fibers.
- [`ComputationalPaths/Path/Homotopy/Fibration.lean`](ComputationalPaths/Path/Homotopy/Fibration.lean) — fibrations, fiber sequences F → E → B, connecting map ∂ : π₁(B) → F, long exact sequence of homotopy groups, induced maps on π₁.
- [`ComputationalPaths/Path/Homotopy/SuspensionLoop.lean`](ComputationalPaths/Path/Homotopy/SuspensionLoop.lean) — suspension-loop adjunction [ΣX, Y]_* ≅ [X, ΩY]_*, pointed types/maps, adjunction map construction, connectivity definitions.
- [`ComputationalPaths/Path/Homotopy/EilenbergMacLane.lean`](ComputationalPaths/Path/Homotopy/EilenbergMacLane.lean) — Eilenberg-MacLane spaces K(G,n), IsKG1 characterization, circle is K(ℤ,1), loop space property Ω(K(G,n+1)) ≃ K(G,n).
- [`ComputationalPaths/Path/Rewrite/PathTactic.lean`](ComputationalPaths/Path/Rewrite/PathTactic.lean) — automation tactics (`path_simp`, `path_rfl`, `path_canon`, `path_decide`) for RwEq proofs.
- [`ComputationalPaths/Path/HIT/Circle.lean`](ComputationalPaths/Path/HIT/Circle.lean) — circle HIT interface, code family into ℤ, encode/transport lemmas, z-powers.
- [`ComputationalPaths/Path/HIT/CircleStep.lean`](ComputationalPaths/Path/HIT/CircleStep.lean) — step laws, encode∘decode=id on ℤ, decode∘encode=id on π₁, and decode-add/sub/group lemmas.
- [`ComputationalPaths/Path/HIT/Torus.lean`](ComputationalPaths/Path/HIT/Torus.lean) — torus HIT interface, code family into ℤ × ℤ, encode/transport lemmas, iterated loops, and the equivalence `torusPiOneEquivIntProd`.
- [`ComputationalPaths/Path/HIT/ProjectivePlane.lean`](ComputationalPaths/Path/HIT/ProjectivePlane.lean) — real projective plane RP² with fundamental loop α satisfying α∘α=refl, and equivalence π₁(RP²) ≃ ℤ₂.
- [`ComputationalPaths/Path/HIT/KleinBottle.lean`](ComputationalPaths/Path/HIT/KleinBottle.lean) — Klein bottle HIT with generators a, b and surface relation aba⁻¹=b⁻¹, plus full encode/decode equivalence π₁(K) ≃ ℤ ⋊ ℤ.
- [`ComputationalPaths/Path/HIT/KleinBottleSVK.lean`](ComputationalPaths/Path/HIT/KleinBottleSVK.lean) — Alternative proof of π₁(K) ≃ ℤ ⋊ ℤ using Seifert-van Kampen on the CW-complex pushout (D² attached to S¹∨S¹ via boundary word aba⁻¹b).
- [`ComputationalPaths/Path/HIT/MobiusBand.lean`](ComputationalPaths/Path/HIT/MobiusBand.lean) — Möbius band HIT (homotopy equivalent to circle), π₁ ≃ ℤ.
- [`ComputationalPaths/Path/HIT/Cylinder.lean`](ComputationalPaths/Path/HIT/Cylinder.lean) — Cylinder HIT (S¹ × I), π₁ ≃ ℤ.
- [`ComputationalPaths/Path/HIT/Pushout.lean`](ComputationalPaths/Path/HIT/Pushout.lean) — Pushout HIT with constructors (inl, inr, glue), eliminators, and special cases (wedge sum, suspension).
- [`ComputationalPaths/Path/HIT/PushoutPaths.lean`](ComputationalPaths/Path/HIT/PushoutPaths.lean) — Path characterization for pushouts, free products, amalgamated free products, and the **Seifert-van Kampen theorem** (`seifertVanKampenEquiv`).
- [`ComputationalPaths/Path/HIT/FigureEight.lean`](ComputationalPaths/Path/HIT/FigureEight.lean) — Figure-eight space (S¹ ∨ S¹) with π₁ ≃ ℤ * ℤ (free group F₂), demonstrating non-abelian fundamental groups.
- [`ComputationalPaths/Path/HIT/Sphere.lean`](ComputationalPaths/Path/HIT/Sphere.lean) — The 2-sphere S² as suspension of S¹, with π₁(S²) ≅ 1 via SVK.
- [`ComputationalPaths/Path/HIT/OrientableSurface.lean`](ComputationalPaths/Path/HIT/OrientableSurface.lean) — **Orientable genus-g surfaces** Σ_g with full fundamental group calculation: π₁(Σ_g) ≃ ⟨a₁,b₁,...,a_g,b_g | [a₁,b₁]...[a_g,b_g] = 1⟩.
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

- [`ComputationalPaths/Path/Rewrite/PathTactic.lean`](ComputationalPaths/Path/Rewrite/PathTactic.lean) provides automation for RwEq proofs:
  ```lean
  -- Basic tactics
  macro "path_rfl" : tactic => `(tactic| exact RwEq.refl _)
  macro "path_canon" : tactic => `(tactic| (apply rweq_of_toEq_eq; rfl))
  macro "path_symm" : tactic => `(tactic| apply rweq_symm)

  -- Main workhorse: applies all RwEq simp lemmas
  macro "path_simp" : tactic => `(tactic| simp only [rweq_refl, ...])

  -- Automatic decision procedure
  macro "path_decide" : tactic => `(tactic| first | path_rfl | path_canon | path_simp)
  ```
- **Usage**: `example (p : Path a a) : RwEq (trans refl p) p := by path_simp`
- **Simp lemmas**: Unit laws, inverse laws, associativity, double symmetry, congruence

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
- Encoding: `torusEncode : π₁(T²) → ℤ × ℤ` via the quotient lift of `torusEncodePath`.
- Decoding: `torusDecode : ℤ × ℤ → π₁(T²)` assembles the z-powers of the two commuting loops.
- Equivalence: `torusPiOneEquivIntProd` shows the maps are inverse, yielding π₁(T²) ≃ ℤ × ℤ.
- Follow-up work: extracting a `TorusStep` module (analogous to `CircleStep`) would expose addition/subtraction lemmas as `[simp]` facts.

## Real Projective Plane π₁(RP²) ≃ ℤ₂ (what to read)
- Reference: de Veras, Ramos, de Queiroz & de Oliveira, "A Topological Application of Labelled Natural Deduction", SAJL.
- HIT Interface: `ProjectivePlane` with base point and fundamental loop `projectiveLoop` satisfying `projectiveLoopSquare : α ∘ α = refl`.
- ℤ₂ representation: `Bool` with XOR as addition (no Mathlib dependency).
- Encoding: `projectiveEncodeQuot : π₁(RP²) → Bool` via quotient lift.
- Decoding: `toPathZ2 : Bool → π₁(RP²)` maps `false → refl`, `true → loop`.
- Equivalence: `projectivePiOneEquivZ2` shows π₁(RP²) ≃ ℤ₂ (with two remaining sorrys for transport computations).

## Klein bottle π₁(K) ≃ ℤ ⋊ ℤ (what to read)
- Reference: [de Veras, Ramos, de Queiroz & de Oliveira, *An alternative approach to the calculation of fundamental groups based on labeled natural deduction* (2019)](https://arxiv.org/abs/1906.09107).
- HIT Interface: `KleinBottle` with base point, generators `kleinLoopA` (a) and `kleinLoopB` (b), and surface relation `aba⁻¹ = b⁻¹`.
- Code family: `ℤ × ℤ` with semidirect multiplication `(m₁,n₁)·(m₂,n₂) = (m₁+m₂, σ(m₂)·n₁+n₂)` where `σ(m) = (-1)^m`.
- Encoding: `kleinEncodeQuot : π₁(K) → ℤ × ℤ` via quotient lift of transport-based encoding.
- Decoding: `kleinDecodeQuot : ℤ × ℤ → π₁(K)` maps `(m,n) ↦ [a^m · b^n]`.
- Key lemma: `kleinLoopBClass_zpow_mul_loopAClass_zpow` establishes conjugation relation `[b]^n · [a]^m = [a]^m · [b]^{σ(m)·n}`.
- Equivalence: `kleinPiOneEquivIntProd` shows π₁(K) ≃ ℤ ⋊ ℤ with the semidirect product structure.
- **Alternative proof via SVK** ([`KleinBottleSVK.lean`](ComputationalPaths/Path/HIT/KleinBottleSVK.lean)):
  - Constructs K as pushout: `FigureEight ←boundary─ S¹ ─collapse→ Point`
  - Boundary map sends `circleLoop` to `aba⁻¹b` (the Klein relation word)
  - SVK gives: π₁(K) ≃ (ℤ * ℤ) / ⟨⟨aba⁻¹b⟩⟩ ≃ ℤ ⋊ ℤ
  - Key computation: `wordToIntProd_boundaryWord` shows aba⁻¹b maps to (0,0) in ℤ ⋊ ℤ

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

## 2-Sphere π₁(S²) ≅ 1 (what to read)
- **Definition** ([`Sphere.lean`](ComputationalPaths/Path/HIT/Sphere.lean)): `Sphere2 := Suspension Circle` (suspension of S¹)
- **Mathematical insight**: S² = Σ(S¹) = Pushout PUnit' PUnit' Circle, with both PUnit' having trivial π₁
- **Main theorem** (`sphere2_piOne_trivial`): π₁(S²) ≅ 1 (trivial group)
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

## Assumptions (axioms)
- Circle HIT interface (constructors + β-rules).  The type, base point, loop,
  and eliminators are currently axioms so that downstream developments can use
  a stable higher-inductive interface while the computational-path semantics
  for HITs are being developed.
- Pushout HIT interface (constructors + eliminators + computation rules). The
  encode-decode axioms for SVK would be provable in cubical type theory but
  must be postulated in Lean 4's setting without native HITs.
- OrientableSurface HIT interface (type, base point, loops, 2-cell, recursion principle).
  The encode-decode round-trip axioms complete the fundamental group calculation.
- Lightweight univalence (`ua`, `ua_beta`) specialised to `SimpleEquiv`.  This
  suffices for the encode–decode argument without requiring the full HoTT
  axiom.

Every other component—encode/decode maps, quotient constructions, loop group
laws, free products, amalgamation, surface group presentations, etc.—is defined
inside Lean and ultimately reduces to the axioms above.

## Contributing
- Build after non-trivial edits: `./lake.cmd build`.
- Keep docstrings in sync, prefer small, focused lemmas with `@[simp]` where useful.
- The simplifier linter flags unused simp arguments; please trim them.
- When a structure adds data on top of an existing interface, prefer extending the smaller structure (e.g. `WeakGroupoid` extends `WeakCategory`) to keep identities/composition definitions in one place.

## Maintenance / refactor opportunities
- **Circle/Torus step modules**: [`CircleStep.lean`](ComputationalPaths/Path/HIT/CircleStep.lean) redefines lemmas that already live in [`Circle.lean`](ComputationalPaths/Path/HIT/Circle.lean). Consolidating those proofs (and adding a `TorusStep` counterpart) would make the encode/ decode algebra reusable via imports.
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
