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

`Scripts/AxiomInventory.lean` currently reports **43** kernel axioms when importing `ComputationalPaths`.

They are **exactly the HIT interfaces**:

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

## Projective plane (π₁(RP²) ≃ ℤ₂)

Kernel axioms *used by* `ComputationalPaths.Path.projectivePiOneEquivZ2`:

- `ProjectivePlane`, `projectiveBase`, `projectiveLoop`

Non-kernel assumptions required by the RP² encode/decode development:

- `ComputationalPaths.Path.HasProjectiveLoopDecode`
  - `Bool`-valued loop classification hypothesis for raw loops.
  - Defined in `ComputationalPaths/Path/HIT/ProjectivePlane.lean`.

## Klein bottle (π₁(K) ≃ ℤ ⋊ ℤ)

Kernel axioms *used by* `ComputationalPaths.Path.kleinPiOneEquivIntProd`:

- `KleinBottle`, `kleinBase`, `kleinLoopA`, `kleinLoopB`

Non-kernel assumptions required by the Klein bottle encode/decode development:

- `ComputationalPaths.Path.HasKleinLoopDecode`
  - Normal-form classification hypothesis for raw loops (`a^m ⬝ b^n`).
  - Defined in `ComputationalPaths/Path/HIT/KleinBottle.lean`.
  - This gives an equivalence with `Int × Int` (normal-form coordinates); the SVK development
    in `ComputationalPaths/Path/HIT/KleinBottleSVK.lean` builds the semidirect-product viewpoint.

## Pushout / SVK

The pushout is implemented as a quotient, but some HIT-style β/naturality laws are not definitional.
These are now **non-kernel assumptions**:

- `Pushout.HasRecGlueRwEq` (recursor β-rule on `glue`, up to `RwEq`)
- `Pushout.HasIndGlueRwEq` (inductor β-rule on `glue`, up to `RwEq`)
- `Pushout.HasGlueNaturalRwEq` (glue naturality, up to `RwEq`)

They are defined in `ComputationalPaths/Path/HIT/Pushout.lean`, and threaded into consumers
like `ComputationalPaths/Path/HIT/PushoutPaths.lean`, `ComputationalPaths/Path/HIT/Sphere.lean`,
and `ComputationalPaths/Path/HIT/HopfFibration.lean`.
