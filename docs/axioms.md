# Axiom minimization status

This project distinguishes:

- **Kernel axioms**: Lean `axiom` declarations that extend the trusted base.
- **Assumptions**: `Prop`-valued typeclasses (e.g. `HasUnivalence`) that appear as explicit hypotheses in theorems/definitions, but *do not* extend the kernel.

The goal is to keep the **kernel axiom set** as small as possible, and make any additional assumptions **local and explicit** in signatures.

## How to measure

From the repository root:

- Global kernel axiom inventory (for `import ComputationalPaths`):
  - `.\lake.cmd env lean Scripts\AxiomInventory.lean`
- Kernel axiom dependencies for a specific declaration:
  - `.\lake.cmd env lean Scripts\AxiomDependencies.lean`
  - Edit `Scripts/AxiomDependencies.lean` to change the queried declaration.

## Current kernel axioms (global)

`Scripts/AxiomInventory.lean` currently reports **56** kernel axioms when importing `ComputationalPaths`.

They are **exactly the HIT interfaces** (types/constructors/recursors) for:

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
- `circleRec`, `circleRec_base`, `circleRec_loop`

This is reported by `Scripts/AxiomDependencies.lean`.

Non-kernel assumptions required by the circle encode/decode development:

- `ComputationalPaths.Path.HasUnivalence.{0}` (univalence interface for `Type 0`)
  - Defined in `ComputationalPaths/Path/Basic/Univalence.lean`.
- `ComputationalPaths.Path.HasCircleLoopDecode`
  - Circle-specific loop classification hypothesis (encode/decode “decode∘encode” direction).
  - Defined in `ComputationalPaths/Path/HIT/Circle.lean`.

## Pushout / SVK

The pushout is implemented as a quotient, but some HIT-style β/naturality laws are not definitional.
These are now **non-kernel assumptions**:

- `Pushout.HasRecGlueRwEq` (recursor β-rule on `glue`, up to `RwEq`)
- `Pushout.HasIndGlueRwEq` (inductor β-rule on `glue`, up to `RwEq`)
- `Pushout.HasGlueNaturalRwEq` (glue naturality, up to `RwEq`)

They are defined in `ComputationalPaths/Path/HIT/Pushout.lean`, and threaded into consumers
like `ComputationalPaths/Path/HIT/PushoutPaths.lean`, `ComputationalPaths/Path/HIT/Sphere.lean`,
and `ComputationalPaths/Path/HIT/HopfFibration.lean`.

