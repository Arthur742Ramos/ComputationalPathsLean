# ComputationalPaths — Axiom & Typeclass Inventory

> Last corrected 2026-07-24 (hand-verified against the source tree).

---

## §1  Lean `axiom` declarations — **none**

The project is **axiom-free**: there are **zero** custom `axiom` declarations in
the source tree.  You can verify this at any time:

```bash
grep -rnE "^axiom " ComputationalPaths --include="*.lean" | grep -v ".lake"
# (no output — the only textual match is a docstring in ContractibilityIrrelevance.lean)
```

An earlier revision of this document listed 30 `axiom` declarations (HoTT higher
inductive-type constructors, univalence, propositional/n-truncation, and SKI
combinator equations).  **Those axioms and the files that declared them have been
removed** (`Path/Algebra/HigherInductiveDeep.lean`, `Path/HoTT/UnivalenceDeep.lean`,
`Path/HoTT/UnivalencePaths.lean`, `Path/Homotopy/HigherInductiveTypes.lean`,
`Path/Homotopy/TruncationTheory.lean`, `Path/Homotopy/UnivalenceApplications.lean`,
`Path/Rewriting/CombinatorReductionDeep.lean`).  Removing them is a rigor
improvement: the library now stands on Lean's kernel axioms alone.

### Kernel-axiom footprint

Definitions and theorems depend only on the standard Lean/Mathlib kernel axioms:

| Axiom | When it appears |
|-------|-----------------|
| `propext` | Propositional extensionality — used pervasively (e.g. via `Eq`/`Quot`). |
| `Quot.sound` | Quotient soundness — `RwEq`/`Quot`-based constructions. |
| `Classical.choice` | Only where classical/noncomputable Mathlib machinery is invoked. A **choice-free core** exists and is verified: e.g. `ContractibilityIrrelevance` and `compPathOmegaGroupoidIrrel` depend on `propext`/`Quot.sound` only. |

Many core results are fully choice-free.  Check any declaration with:

```lean
#print axioms <declarationName>
```

> Note: `native_decide` (currently used in a small number of files) additionally
> pulls `Lean.ofReduceBool` + `Lean.trustCompiler` into the trusted base of the
> declarations that use it; prefer kernel `decide`/`rfl`/`omega` where possible.

---

## §2  Instantiated typeclasses (proved) ✅

These classes have concrete, `sorry`-free instances.

| Class | Instance | File | Technique |
|-------|----------|------|-----------|
| `HasTerminationProp` | `instHasTerminationProp` | `Path/Rewrite/ConfluenceProof.lean:570` | Polynomial weight function on `Expr` |
| `HasConfluencePropExpr` | `instHasConfluencePropExpr` | `Path/Rewrite/ConfluenceProof.lean:619` | Free group interpretation (`toRW`) of groupoid TRS |
| `HasCirclePiOneEncode` | `instHasCirclePiOneEncode` | `Path/CompPath/CircleStep.lean:35` | Winding number (`windingNumber`) |
| `HasTorusPiOneEncode` | `instHasTorusPiOneEncode_ofCircle` | `Path/CompPath/TorusStep.lean:90` | Delegates to circle via projection |
| `HasGlueNaturalLoopRwEq` | `instHasGlueNaturalLoopRwEq_Wedge` | `Path/CompPath/PushoutCompPath.lean:345` | Wedge specialisation (`C = PUnit'`) |
| `HasWedgeProvenanceEncode` | `instHasWedgeProvenanceEncode_FigureEight` | `Path/CompPath/FigureEight.lean:124` | Provenance tagging for figure-eight |
| `HasDifferentialSquaredZero` | `(trivialPage r)` | `Path/Homotopy/AdamsSpectralSequence.lean:185` | Trivial spectral sequence page |
| `HasVcompAssoc` | `instHasVcompAssoc_EqTwoCat` | `TwoCategoryInstances.lean` | `PLift Eq` 2-cells; proof irrelevance |
| `HasHcompFunctorial` | `instHasHcompFunctorial_EqTwoCat` | `TwoCategoryInstances.lean` | `PLift Eq` 2-cells; proof irrelevance |
| `HasInterchange` | `instHasInterchange_EqTwoCat` | `TwoCategoryInstances.lean` | `PLift Eq` 2-cells; proof irrelevance |

> Honesty note: `HasCirclePiOneEncode`/`HasTorusPiOneEncode` establish that
> explicitly **synthetic winding-expression quotients** are `≃ ℤ` (resp.
> `ℤ×ℤ`).  They do not compute the framework's genuine `PathRwQuot`
> fundamental groups.  For the current one-constructor `Circle` and product
> `Torus`, `MetadataRepair.lean` proves the genuine loop quotients contractible,
> the synthetic quotients noncontractible, and the corresponding `SimpleEquiv`
> bridges impossible.

---

## §3  Impossible typeclasses ⛔ (formally proved unsatisfiable)

These classes have **formal impossibility proofs** showing no instance can
exist.  They are retained for documentation but marked `-- DEPRECATED`.

| Class | Obstruction | Proof location |
|-------|-------------|----------------|
| `HasWedgeSVKEncodeDecode` | `nil` and `consLeft 0 nil` both decode to the identity loop but are structurally distinct words; no `encodeQuot` can round-trip both. | `WedgeSVKCircleInstances.not_hasWedgeSVKEncodeDecode_Circle` |
| `HasWedgeSVKEncodeData` | Contains `encode_decode` field from `HasWedgeSVKEncodeDecode` ⇒ inherits its impossibility. | `PushoutSVKInstances.hasWedgeSVKEncodeData_impossible_PUnit` |
| `HasPushoutSVKEncodeDecode` | `AmalgEquiv` preserves word length while `pushoutDecode` maps words of different lengths to the same π₁ element. | `PushoutSVKInstances.hasPushoutSVKEncodeDecode_impossible_PUnit` |
| `HasPushoutSVKDecodeAmalgBijective` | Same word-length obstruction as `HasPushoutSVKEncodeDecode`. | `PushoutSVKInstances.hasPushoutSVKDecodeAmalgBijective_impossible_PUnit` |

The formerly “open” circle bridge
`SimpleEquiv (π₁(Circle, circleBase)) circlePiOne` is also impossible under the
current definitions; see
`MetadataRepair.no_circle_genuine_synthetic_bridge`.  The analogous torus
bridge is ruled out by `no_torus_genuine_synthetic_bridge`.  These are
no-bridge theorems rather than missing encode/decode instances.

**Replacement**: Use `HasPushoutSVKEncodeDecodeFull` / `HasWedgeSVKEncodeDataFull`
which quotient by `FullAmalgEquiv` (amalgamation + free group reduction).

---

## §4  Fundamentally blocked at Path level ⛔

These classes are **not** impossible in general — they hold for the `Expr`
representation — but cannot be instantiated when 2-cells are `Path` values
(which carry distinct step lists for the same propositional equality).

| Class | Why blocked | Working alternative |
|-------|------------|---------------------|
| `HasJoinOfRw` | Two `Path`s with `p.proof = q.proof` but different `.steps` lists are not `Rw`-joinable without a step-erasure rule. | `GroupoidConfluence.confluence` on `Expr` |
| `HasLocalConfluenceProp` | Same step-list obstruction. | `HasConfluencePropExpr` |
| `HasConfluenceProp` | Same step-list obstruction. | `HasConfluencePropExpr` |

---

## §5  Open problems — SVK encode direction 🔴

These classes are **not known to be impossible** but remain uninstantiated.
They require constructing the universal cover of the relevant space, which
is a significant open formalisation problem.

| Class | What's needed |
|-------|---------------|
| `HasWedgeSVKEncodeQuot` | Universal cover of `Wedge A B` ⇒ `encodeQuot` function |
| `HasWedgeSVKDecodeEncode` | `decode ∘ encode = id` on loop representatives |
| `HasWedgeSVKDecodeBijective` | Bijectivity of `wedgeDecodeAmalg` |
| `HasPushoutSVKEncodeQuot` | Universal cover of `Pushout A B C f g` ⇒ `encodeQuot` function |
| `HasPushoutSVKDecodeEncode` | `decode ∘ encode = id` for general pushouts |
| `HasPushoutSVKEncodeDecodeFull` | `encode ∘ decode = id` modulo `FullAmalgEquiv` |
| `HasPushoutSVKDecodeFullAmalgBijective` | Bijectivity of `pushoutDecodeFullAmalg` |

All seven require the **encode-decode method** via covering spaces, which
demands constructing a type family over the HIT whose total space is
contractible.  This is feasible in principle (Favonia–Shulman, Brunerie)
but has not been carried out in this codebase.

---

## §6  Structural 2-category classes

| Class | Status | Notes |
|-------|--------|-------|
| `HasDifferentialSquaredZero` | ✅ for trivial page; 🔴 for non-trivial | Trivial instance at `AdamsSpectralSequence.lean:185`. Non-trivial requires computing `d ∘ d` on actual spectral sequence pages. |
| `HasVcompAssoc` | ✅ | Instantiated on `EqTwoCat` (see §2). |
| `HasHcompFunctorial` | ✅ | Instantiated on `EqTwoCat` (see §2). |
| `HasInterchange` | ✅ | Instantiated on `EqTwoCat` (see §2). |

---

## Summary

| Category | Count |
|----------|-------|
| custom `axiom` declarations | **0** (axiom-free) |
| Instantiated typeclasses ✅ | **10** |
| Impossible typeclasses ⛔ | **4** |
| Blocked at Path level ⛔ | **3** |
| Open problems 🔴 | **7** |
| Structural (mixed) | **1** (`HasDifferentialSquaredZero`) |
