# Axiom minimization status

This project distinguishes:

- **Kernel axioms**: Lean `axiom` declarations that extend the trusted base.
- **Assumptions**: explicit hypotheses (usually typeclasses), ranging from `Prop`-valued markers
  (e.g. `HasUnivalence`) to `Type`-valued data interfaces (e.g. `HasCircleLoopDecode`). These
  do *not* extend the kernel, but must be discharged by providing an instance/proof.

The goal is to keep the **kernel axiom set** as small as possible, and make any additional assumptions **local and explicit** in signatures.

## How to measure

From the repository root:

- Global kernel axiom inventory (for `import ComputationalPaths`):
  - `.\lake.cmd env lean Scripts\AxiomInventory.lean`
- Kernel axiom dependencies for a specific declaration:
  - `.\lake.cmd env lean Scripts\AxiomDependencies.lean`
  - Edit `Scripts/AxiomDependencies.lean` to change the queried declaration.
- Prop-valued typeclass assumptions required by a specific declaration:
  - `.\lake.cmd env lean Scripts\AssumptionDependencies.lean`
  - Edit `Scripts/AssumptionDependencies.lean` to change the queried declaration.
- Quick multi-theorem survey (handy while refactoring):
  - `.\lake.cmd env lean Scripts\AssumptionSurvey.lean`

## Consistency note: `HasUnivalence`

In standard Lean, `Eq` lives in `Prop`, hence is **proof-irrelevant**. This has an important
consequence for any “univalence via `Eq` + `transport`” interface:

- For any type `A`, the equality `A = A` is definitionally reflexive.
- Therefore `transport` along any proof of `A = A` must be the identity function.
- So an axiom stating that transport along `ua (e : A ≃ A)` computes to `e.toFun` forces
  *every* autoequivalence to be judgmentally the identity.

This collapses nontrivial equivalences (e.g. boolean negation), and yields a contradiction.

The script `Scripts/UnivalenceInconsistency.lean` proves `False` from `[HasUnivalence]` using
`Bool` as a tiny witness:

- `.\lake.cmd env lean Scripts\UnivalenceInconsistency.lean`

As a result, `HasUnivalence` is currently best understood as a **meta-level marker** for
HoTT-style developments, not something that can be instantiated inside Lean’s standard logic.

## Current kernel axioms (global)

`Scripts/AxiomInventory.lean` currently reports **45** kernel axioms when importing `ComputationalPaths`.

They fall into two categories:

### HIT interfaces (43 axioms)

- `Circle`, `Cylinder`, `MobiusBand` include point/path constructors **and** recursors.
- `Cylinder` keeps only the β-rules used downstream (base points and the bottom loop).
- `Torus`, `KleinBottle`, `ProjectivePlane` currently expose only point/path constructors (and the
  defining surface relations), keeping the kernel axiom surface smaller.
- `OrientableSurface` exposes the genus-indexed point/loop constructors plus the surface relation.

- `Circle`
- `Cylinder`
- `Torus`
- `KleinBottle`
- `MobiusBand`
- `ProjectivePlane`
- `OrientableSurface`

No univalence or pushout computation/naturality principles remain as kernel axioms.

### Confluence axioms (2 axioms)

The LND_EQ-TRS confluence proof uses two axioms justified by critical pair analysis and termination:

- `ComputationalPaths.Path.Rewrite.ConfluenceProof.local_confluence`
  - **Statement**: For any `Step p q` and `Step p r`, there exists a `Join q r`.
  - **Justification**: All critical pairs have been analyzed and shown to close:
    - `trans_assoc` vs `trans_refl_left/right` (unit laws)
    - `trans_assoc` vs `trans_symm/symm_trans` (inverse laws, via identity context technique)
    - `symm_symm` vs `symm_refl/symm_trans_congr` (symmetry rules)
    - Nested `trans_assoc` (pentagon identity)
    - Non-overlapping steps commute via `commute_trans_left_right`
  - **Technical note**: A fully constructive proof would require either making `Step` Type-valued
    (breaking `Step.casesOn` elimination elsewhere) or exhaustive 76² = 5776 case splits.

- `ComputationalPaths.Path.Rewrite.ConfluenceProof.step_strip_prop`
  - **Statement**: For any `Step p q` and `Rw p r`, there exists `s` with `Rw q s` and `Rw r s`.
  - **Justification**: Follows from `local_confluence` by iterative application (the "strip lemma").
    The standard proof uses nested induction on the `Rw` derivation, applying the diamond lemma
    at each step. Combined with termination (established in `Termination.lean` via RPO ordering),
    this gives Newman's Lemma.

These axioms enable the `HasJoinOfRw` instance in `ConfluenceProof.lean`, which provides:
- `confluence_prop`: Prop-level confluence (proved by induction using the strip lemma)
- `confluence_of_local`: Type-valued `Join` construction (via `Classical.choose`)
- `instHasJoinOfRw`: The typeclass instance for downstream use

## Circle fundamental group (π₁(S¹) ≃ ℤ)

Kernel axioms *used by* `ComputationalPaths.Path.circlePiOneEquivInt`:

- `Circle`, `circleBase`, `circleLoop`

This is reported by `Scripts/AxiomDependencies.lean`.

Non-kernel assumptions required by the circle encode/decode development:

- `ComputationalPaths.Path.HasCircleLoopDecode`
  - Circle-specific loop classification hypothesis (encode/decode “decode∘encode” direction).
  - Defined in `ComputationalPaths/Path/HIT/Circle.lean`.
  - Speaks about *raw* loops (`Path circleBase circleBase`) and provides a normal form
    `loop^n` up to `RwEq`.
  - This interface is now *derivable* from the quotient-level interface
    `HasCirclePiOneEncode` via `hasCircleLoopDecodeOfPiOneEncode` in
    `ComputationalPaths/Path/HIT/CircleStep.lean`.

- `ComputationalPaths.Path.HasCirclePiOneEncode`
  - Weaker, discharge-friendly interface living purely at the `π₁` (quotient) level:
    an `encode : π₁(S¹) → ℤ` with `encode (circleDecode z) = z` and
    `circleDecode (encode x) = x`.
  - Defined in `ComputationalPaths/Path/HIT/CircleStep.lean`.
  - Every `[HasCircleLoopDecode]` provides an instance, and conversely
    `HasCirclePiOneEncode` can be turned back into `HasCircleLoopDecode` when a
    raw-loop statement is required.
  - Downstream developments
    (e.g. `ComputationalPaths/Path/HIT/Pi2Sphere.lean`,
    `ComputationalPaths/Path/Homotopy/LieGroups.lean`) now depend only on this weaker
    hypothesis.

### Opt-in “assumption-free” import

If you want to use the circle π₁ result without threading a typeclass hypothesis
through your signatures, import:

- `ComputationalPaths/Path/HIT/CirclePiOneAxiom.lean`

This file adds a global `HasCirclePiOneEncode` **as a kernel axiom** and exports
`circlePiOneEquivInt' : π₁(S¹) ≃ ℤ` with no extra parameters. The core library
does *not* import it by default.

## Torus fundamental group (π₁(T²) ≃ ℤ × ℤ)

Kernel axioms *used by* `ComputationalPaths.Path.torusPiOneEquivIntProd`:

- `Torus`, `torusBase`, `torusLoop1`, `torusLoop2`

Non-kernel assumptions required by the torus encode/decode development:

- `ComputationalPaths.Path.HasTorusLoopDecode`
  - Torus-specific winding-number classification hypothesis for raw loops.
  - Defined in `ComputationalPaths/Path/HIT/Torus.lean`.
  - Speaks about *raw* loops (`Path torusBase torusBase`) and provides a normal form
    `loop1^m ⬝ loop2^n` up to `RwEq`.
  - This interface is now *derivable* from the quotient-level interface
    `HasTorusPiOneEncode` via `hasTorusLoopDecodeOfPiOneEncode` in
    `ComputationalPaths/Path/HIT/TorusStep.lean`.

- `ComputationalPaths.Path.HasTorusPiOneEncode`
  - Weaker, discharge-friendly interface living purely at the `π₁` (quotient) level:
    an `encode : π₁(T²) → ℤ × ℤ` with `encode (torusDecode z) = z` and
    `torusDecode (encode x) = x`.
  - Defined in `ComputationalPaths/Path/HIT/TorusStep.lean`.
  - Every `[HasTorusLoopDecode]` provides an instance, and conversely
    `HasTorusPiOneEncode` can be turned back into `HasTorusLoopDecode` when a
    raw-loop statement is required.
  - Downstream developments (e.g. `ComputationalPaths/Path/Homotopy/LieGroups.lean`)
    now depend only on this weaker hypothesis.

### Opt-in "assumption-free" import

If you want to use the torus π₁ result without threading a typeclass hypothesis
through your signatures, import:

- `ComputationalPaths/Path/HIT/TorusPiOneAxiom.lean`

This file adds a global `HasTorusPiOneEncode` **as a kernel axiom** and exports
`torusPiOneEquivIntProd' : π₁(T²) ≃ ℤ × ℤ` with no extra parameters. The core library
does *not* import it by default.

## Projective plane (π₁(RP²) ≃ ℤ₂)

Kernel axioms *used by* `ComputationalPaths.Path.projectivePiOneEquivZ2`:

- `ProjectivePlane`, `projectiveBase`, `projectiveLoop`

Non-kernel assumptions required by the RP² encode/decode development:

- `ComputationalPaths.Path.HasProjectiveLoopDecode`
  - `Bool`-valued loop classification hypothesis for raw loops.
  - Defined in `ComputationalPaths/Path/HIT/ProjectivePlane.lean`.
  - This interface implies the quotient-level interface `HasProjectivePiOneEncode`.

- `ComputationalPaths.Path.HasProjectivePiOneEncode`
  - Weaker, discharge-friendly interface living purely at the `π₁` (quotient) level:
    an `encode : π₁(RP²) → Bool` with `encode (projectiveDecode b) = b` and
    `projectiveDecode (encode x) = x`.
  - Defined in `ComputationalPaths/Path/HIT/ProjectivePlaneStep.lean`.
  - Every `[HasProjectiveLoopDecode]` provides an instance, and conversely
    `HasProjectivePiOneEncode` can be turned back into `HasProjectiveLoopDecode`
    when a raw-loop statement is required.

### Opt-in "assumption-free" import

If you want to use the projective plane π₁ result without threading a typeclass hypothesis
through your signatures, import:

- `ComputationalPaths/Path/HIT/ProjectivePiOneAxiom.lean`

This file adds a global `HasProjectivePiOneEncode` **as a kernel axiom** and exports
`projectivePiOneEquivZ2' : π₁(RP²) ≃ Bool` with no extra parameters. The core library
does *not* import it by default.

## Klein bottle (π₁(K) ≃ ℤ ⋊ ℤ)

Kernel axioms *used by* `ComputationalPaths.Path.kleinPiOneEquivIntProd`:

- `KleinBottle`, `kleinBase`, `kleinLoopA`, `kleinLoopB`

Non-kernel assumptions required by the Klein bottle encode/decode development:

- `ComputationalPaths.Path.HasKleinLoopDecode`
  - Normal-form classification hypothesis for raw loops (`a^m ⬝ b^n`).
  - Defined in `ComputationalPaths/Path/HIT/KleinBottle.lean`.
  - This interface implies the quotient-level interface `HasKleinPiOneEncode`.

- `ComputationalPaths.Path.HasKleinPiOneEncode`
  - Weaker, discharge-friendly interface living purely at the `π₁` (quotient) level:
    an `encode : π₁(K) → ℤ × ℤ` with `encode (kleinDecode z) = z` and
    `kleinDecode (encode x) = x`.
  - Defined in `ComputationalPaths/Path/HIT/KleinBottleStep.lean`.
  - Every `[HasKleinLoopDecode]` provides an instance, and conversely
    `HasKleinPiOneEncode` can be turned back into `HasKleinLoopDecode` when a raw-loop
    statement is required.

### Opt-in "assumption-free" import

If you want to use the Klein bottle π₁ result without threading a typeclass hypothesis
through your signatures, import:

- `ComputationalPaths/Path/HIT/KleinPiOneAxiom.lean`

This file adds a global `HasKleinPiOneEncode` **as a kernel axiom** and exports
`kleinPiOneEquivIntProd' : π₁(K) ≃ ℤ × ℤ` with no extra parameters. The core library
does *not* import it by default.

The SVK development in `ComputationalPaths/Path/HIT/KleinBottleSVK.lean` builds the
semidirect-product viewpoint and requires additional pushout assumptions.

## Pushout / SVK

The pushout is implemented as a quotient, but some HIT-style β/naturality laws are not definitional.
These are now **non-kernel assumptions**:

- `Pushout.HasRecGlueRwEq` (recursor β-rule on `glue`, up to `RwEq`)
- `Pushout.HasIndGlueRwEq` (inductor β-rule on `glue`, up to `RwEq`)
- `Pushout.HasGlueNaturalRwEq` (glue naturality, up to `RwEq`)

They are defined in `ComputationalPaths/Path/HIT/Pushout.lean`, and threaded into consumers
like `ComputationalPaths/Path/HIT/PushoutPaths.lean`, `ComputationalPaths/Path/HIT/Sphere.lean`,
and `ComputationalPaths/Path/HIT/HopfFibration.lean`.
