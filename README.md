# Computational Paths (Lean 4)

Lean 4 formalisation of propositional equality via explicit computational paths and rewrite equality. It provides a practical kernel for transport, symmetry, congruence, rewrite quotients, and normalisation — and uses this machinery to formalise fundamental groups of higher-inductive types.

## Highlights
- **Weak ω-groupoid structure**: Complete proof that computational paths form a weak ω-groupoid with all coherence laws (pentagon, triangle) and contractibility at higher dimensions.
- **Seifert-van Kampen theorem**: Full encode-decode proof that π₁(Pushout) ≃ π₁(A) *_{π₁(C)} π₁(B) (amalgamated free product), with special case π₁(A ∨ B) ≃ π₁(A) * π₁(B) for wedge sums.
- Loop quotients and π₁(A, a) as rewrite classes with strict group laws.
- Higher-inductive circle interface + code family into ℤ (via univalence axioms).
- Completed proof π₁(S¹) ≃ ℤ using an encode–decode argument with quotient→equality reduction.
- Completed proof π₁(T²) ≃ ℤ × ℤ via the encode/decode equivalence `torusPiOneEquivIntProd`.
- Real projective plane RP² with π₁(RP²) ≃ ℤ₂ (represented as Bool with XOR as addition).
- **Klein bottle** π₁(K) ≃ ℤ ⋊ ℤ (semidirect product) via encode/decode equivalence `kleinPiOneEquivIntProd`.
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
- [`ComputationalPaths/Path/Homotopy/`](ComputationalPaths/Path/Homotopy/) — loop spaces, rewrite monoids (`LoopMonoid`), loop groups (`LoopGroup`), and π₁ interfaces.
- [`ComputationalPaths/Path/HIT/Circle.lean`](ComputationalPaths/Path/HIT/Circle.lean) — circle HIT interface, code family into ℤ, encode/transport lemmas, z-powers.
- [`ComputationalPaths/Path/HIT/CircleStep.lean`](ComputationalPaths/Path/HIT/CircleStep.lean) — step laws, encode∘decode=id on ℤ, decode∘encode=id on π₁, and decode-add/sub/group lemmas.
- [`ComputationalPaths/Path/HIT/Torus.lean`](ComputationalPaths/Path/HIT/Torus.lean) — torus HIT interface, code family into ℤ × ℤ, encode/transport lemmas, iterated loops, and the equivalence `torusPiOneEquivIntProd`.
- [`ComputationalPaths/Path/HIT/ProjectivePlane.lean`](ComputationalPaths/Path/HIT/ProjectivePlane.lean) — real projective plane RP² with fundamental loop α satisfying α∘α=refl, and equivalence π₁(RP²) ≃ ℤ₂.
- [`ComputationalPaths/Path/HIT/KleinBottle.lean`](ComputationalPaths/Path/HIT/KleinBottle.lean) — Klein bottle HIT with generators a, b and surface relation aba⁻¹=b⁻¹, plus full encode/decode equivalence π₁(K) ≃ ℤ ⋊ ℤ.
- [`ComputationalPaths/Path/HIT/MobiusBand.lean`](ComputationalPaths/Path/HIT/MobiusBand.lean) — Möbius band HIT (homotopy equivalent to circle), π₁ ≃ ℤ.
- [`ComputationalPaths/Path/HIT/Cylinder.lean`](ComputationalPaths/Path/HIT/Cylinder.lean) — Cylinder HIT (S¹ × I), π₁ ≃ ℤ.
- [`ComputationalPaths/Path/HIT/Pushout.lean`](ComputationalPaths/Path/HIT/Pushout.lean) — Pushout HIT with constructors (inl, inr, glue), eliminators, and special cases (wedge sum, suspension).
- [`ComputationalPaths/Path/HIT/PushoutPaths.lean`](ComputationalPaths/Path/HIT/PushoutPaths.lean) — Path characterization for pushouts, free products, amalgamated free products, and the **Seifert-van Kampen theorem** (`seifertVanKampenEquiv`).
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

## Assumptions (axioms)
- Circle HIT interface (constructors + β-rules).  The type, base point, loop,
  and eliminators are currently axioms so that downstream developments can use
  a stable higher-inductive interface while the computational-path semantics
  for HITs are being developed.
- Pushout HIT interface (constructors + eliminators + computation rules). The
  encode-decode axioms for SVK would be provable in cubical type theory but
  must be postulated in Lean 4's setting without native HITs.
- Lightweight univalence (`ua`, `ua_beta`) specialised to `SimpleEquiv`.  This
  suffices for the encode–decode argument without requiring the full HoTT
  axiom.

Every other component—encode/decode maps, quotient constructions, loop group
laws, free products, amalgamation, etc.—is defined inside Lean and ultimately
reduces to the axioms above.

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
