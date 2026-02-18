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

`Scripts/AxiomInventory.lean` currently reports **7** kernel axioms when importing `ComputationalPaths` (the Circle constructors and eliminators).

### HIT interfaces (7 axioms)

Kernel axioms are restricted to HIT-style interfaces that are not constructible in standard Lean 4:

- `Circle` (constructors + recursor/β rules)

Torus is now a *constructed* type (Circle × Circle) and contributes no kernel axioms. The Möbius band module was removed as legacy placeholder code.

### Quarantined assumptions (typeclasses)
These assumptions remain explicit in signatures; there are no opt-in kernel-axiom wrapper files anymore.

| Assumption | Scope | Justification |
|-----------|-------|---------------|
| `HasLocalConfluenceProp` | `Rewrite/ConfluenceConstructive.lean` | Critical pair analysis |
| `HasTerminationProp` | `Rewrite/ConfluenceProof.lean` | Newman's lemma |

> **Note:** We keep `HasLocalConfluenceProp` and `HasTerminationProp` as explicit assumptions because the full critical-pair and termination proofs for the complete rewrite system involve a prohibitively large case analysis. These remain non-kernel, local obligations rather than global axioms.
### Non-kernel typeclass assumptions

Rewrite-system confluence is packaged as **non-kernel** typeclass assumptions
(see `ComputationalPaths/Path/Rewrite/Confluence.lean` and `ComputationalPaths/Path/Rewrite/ConfluenceProof.lean`).

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
    (e.g. legacy `Pi2Sphere.lean`,
    `ComputationalPaths/Path/Homotopy/LieGroups.lean`) now depend only on this weaker
    hypothesis.

### Local assumption instance

If you want to use the circle π₁ result without threading a typeclass hypothesis
through your signatures, provide a local instance of `HasCirclePiOneEncode` (or
keep it scoped inside a helper module). The core library no longer ships a
kernel-axiom wrapper.
## Torus fundamental group (π₁(T²) ≃ ℤ × ℤ)

Kernel axioms *used by* `ComputationalPaths.Path.torusPiOneEquivIntProd`:

- `Circle`, `circleBase`, `circleLoop`

Non-kernel assumptions required by the torus encode/decode development:

- `ComputationalPaths.Path.HasTorusPiOneEncode`
  - Weaker, discharge-friendly interface living purely at the `π₁` (quotient) level:
    an `encode : π₁(T²) → ℤ × ℤ` with `encode (torusDecode z) = z` and
    `torusDecode (encode x) = x`.
  - Defined in `ComputationalPaths/Path/HIT/TorusStep.lean`.
  - Since `Torus` is defined as `Circle × Circle`, `TorusStep.lean` provides an instance
    `[HasCirclePiOneEncode] → HasTorusPiOneEncode` using the product fundamental
    group theorem.
  - Downstream developments can therefore depend only on the circle π₁ hypothesis.

### Local assumption instance

If you want to use the torus π₁ result without threading a typeclass hypothesis
through your signatures, provide a local instance of `HasTorusPiOneEncode` (or
keep it scoped inside a helper module). The core library no longer ships a
kernel-axiom wrapper.

## Lens space (π₁(L(p,1)) ≃ ℤ/pℤ)
The lens space module was removed as legacy placeholder code. Any future
formalization should reintroduce the equivalence without new axioms.
## Pushout / SVK

The pushout is implemented as a quotient, but some HIT-style β/naturality laws are not definitional.
These are now **non-kernel assumptions**:

- `Pushout.HasGlueNaturalRwEq` (full glue naturality, up to `RwEq`)
- `Pushout.HasGlueNaturalLoopRwEq` (loop-only glue naturality at a chosen basepoint)
- `ComputationalPaths.Path.HIT.PushoutPaths.HasPushoutSVKEncodeQuot` (SVK encode map)
- `ComputationalPaths.Path.HIT.PushoutPaths.HasPushoutSVKDecodeEncode` (SVK law: `decode ∘ encode = id`)
- `ComputationalPaths.Path.HIT.PushoutPaths.HasPushoutSVKEncodeDecode` (SVK law: `encode ∘ decode ~ id` up to `AmalgEquiv`)
- `ComputationalPaths.Path.HIT.PushoutPaths.HasPushoutSVKEncodeDecodeFull` (SVK law: `encode ∘ decode ~ id` up to `FullAmalgEquiv`)
- `ComputationalPaths.Path.HIT.PushoutPaths.HasPushoutSVKDecodeAmalgBijective` (SVK: Prop-level `pushoutDecodeAmalg` bijective)
- `ComputationalPaths.Path.HIT.PushoutPaths.HasPushoutSVKDecodeFullAmalgBijective` (SVK: Prop-level `pushoutDecodeFullAmalg` bijective)

They are defined in `ComputationalPaths/Path/HIT/Pushout.lean` and
`ComputationalPaths/Path/HIT/PushoutPaths.lean`.

Notes:

- The SVK decoding proof only needs the **loop-only** naturality hypothesis
  `Pushout.HasGlueNaturalLoopRwEq c₀`, and this is derived automatically in common cases
  (e.g. `Subsingleton C`, `IsHSet C`, or when both legs satisfy Axiom K / `IsHSet`
  such as `Subsingleton A` and `Subsingleton B`).
- `seifertVanKampenEquiv` depends on the split SVK assumptions above; the legacy bundled
  class `ComputationalPaths.Path.HIT.PushoutPaths.HasPushoutSVKEncodeData` remains as a convenience wrapper.
- `seifertVanKampenFullEquiv` is the corresponding equivalence with the *full* target
  `FullAmalgamatedFreeProduct` (amalgamation + free reduction). It depends on
  `HasPushoutSVKEncodeDecodeFull`, which is weaker than `HasPushoutSVKEncodeDecode`
  (and is derived automatically when `HasPushoutSVKEncodeDecode` is available).
- If you want to avoid assuming an explicit `encode` map, use the Prop-only wrapper
  `seifertVanKampenEquiv_of_decodeAmalg_bijective`, which depends only on
  `HasPushoutSVKDecodeAmalgBijective` (and builds `encode` by classical choice).
- The analogous wrapper for the full target is
  `seifertVanKampenFullEquiv_of_decodeFullAmalg_bijective`, which depends only on
  `HasPushoutSVKDecodeFullAmalgBijective`.
- If you need the legacy word-level `encode` data, it can be reconstructed noncomputably from
  `HasPushoutSVKDecodeAmalgBijective` via
  `hasPushoutSVKEncodeData_of_decodeAmalg_bijective` (in `PushoutPaths.lean`).
- The wedge case `π₁(A ∨ B) ≃ π₁(A) * π₁(B)` is available in two layers:
  - Explicit (non-kernel) encode/decode assumptions:
    `WedgeSVKInstances.HasWedgeSVKEncodeQuot`, `WedgeSVKInstances.HasWedgeSVKDecodeEncode`,
    and `WedgeSVKInstances.HasWedgeSVKEncodeDecode` (bundled as `WedgeSVKInstances.HasWedgeSVKEncodeData`).
  - Prop-level interface `HasWedgeSVKDecodeBijective`, plus the choice-based equivalence
    `wedgeFundamentalGroupEquiv_of_decode_bijective` (no wrapper class).
  Provide local instances of the Prop-level interface where needed; the old
  kernel-axiom wrapper file has been removed.








