# ComputationalPaths — Axiom & Typeclass Inventory

> Auto-generated 2026-02-18.  Covers every `axiom` declaration in the
> project source tree and every typeclass whose instantiation status is
> tracked.

---

## §1  Lean `axiom` declarations (30 total)

### 1.1  HoTT axioms — Higher Inductive Type constructors (9)

| # | File | Name | Purpose |
|---|------|------|---------|
| 1 | `Path/Algebra/HigherInductiveDeep.lean:31` | `S1.loop` | The non-trivial loop on the circle `S¹` |
| 2 | `Path/Algebra/HigherInductiveDeep.lean:106` | `Interval.seg` | Path from `Interval.zero` to `Interval.one` |
| 3 | `Path/Algebra/HigherInductiveDeep.lean:160` | `Susp.merid` | Meridian path in the suspension `Susp A` |
| 4 | `Path/Algebra/HigherInductiveDeep.lean:262` | `QType.glue` | Gluing path for quotient types `A/R` |
| 5 | `Path/Algebra/HigherInductiveDeep.lean:312` | `Pushout.glue` | Gluing path in pushouts `A ⊔_C B` |
| 6 | `Path/Algebra/HigherInductiveDeep.lean:369` | `Coeq.glue` | Gluing path in coequalizers |
| 7 | `Path/Algebra/HigherInductiveDeep.lean:413` | `Torus.loopA` | First generator loop on the torus |
| 8 | `Path/Algebra/HigherInductiveDeep.lean:414` | `Torus.loopB` | Second generator loop on the torus |
| 9 | `Path/Algebra/HigherInductiveDeep.lean:417` | `Torus.surface` | 2-cell filling `loopA·loopB = loopB·loopA` |

### 1.2  HoTT axioms — Univalence (8)

| # | File | Name | Purpose |
|---|------|------|---------|
| 10 | `Path/HoTT/UnivalenceDeep.lean:115` | `ua` | Univalence: equivalence → path of types (`Equiv' A B → Path A B`) |
| 11 | `Path/HoTT/UnivalenceDeep.lean:116` | `ua_transport` | Transport along `ua e` computes as `e.toFun` |
| 12 | `Path/HoTT/UnivalenceDeep.lean:118` | `ua_refl'` | `ua (Equiv'.refl A) = Path.refl A` |
| 13 | `Path/HoTT/UnivalencePaths.lean:352` | `ua'` | Univalence (alternate equiv `≃ₚ` variant) |
| 14 | `Path/HoTT/UnivalencePaths.lean:354` | `ua'_transport` | Transport computation for `ua'` |
| 15 | `Path/HoTT/UnivalencePaths.lean:359` | `ua'_idEquiv` | `ua' idEquiv = refl` |
| 16 | `Path/HoTT/UnivalencePaths.lean:364` | `ua'_comp` | `ua'` respects composition of equivalences |
| 17 | `Path/HoTT/UnivalencePaths.lean:393` | `ua'_symm_transport` | Inverse transport along `ua'` |

### 1.3  HoTT axioms — Univalence (function form) (1)

| # | File | Name | Purpose |
|---|------|------|---------|
| 18 | `Path/Homotopy/UnivalenceApplications.lean:42` | `univalence` | `IsEquiv (@idtoeqv A B)` — univalence as equivalence-of-maps |

### 1.4  Truncation axioms (9)

| # | File | Name | Purpose |
|---|------|------|---------|
| 19 | `Path/Homotopy/HigherInductiveTypes.lean:73` | `Trunc` (propositional) | Propositional truncation type former |
| 20 | `Path/Homotopy/HigherInductiveTypes.lean:76` | `Trunc.mk` (propositional) | Constructor for propositional truncation |
| 21 | `Path/Homotopy/HigherInductiveTypes.lean:79` | `Trunc.isProp` | All elements of `Trunc A` are equal |
| 22 | `Path/Homotopy/HigherInductiveTypes.lean:82` | `Trunc.rec` | Eliminator for propositional truncation |
| 23 | `Path/Homotopy/TruncationTheory.lean:58` | `Trunc` (n-truncation) | n-truncation type former `Trunc n A` |
| 24 | `Path/Homotopy/TruncationTheory.lean:61` | `Trunc.mk` (n-truncation) | Constructor for n-truncation |
| 25 | `Path/Homotopy/TruncationTheory.lean:64` | `Trunc.isOfHLevel` | `Trunc n A` has h-level `n` |
| 26 | `Path/Homotopy/TruncationTheory.lean:68` | `Trunc.elim` | Eliminator for n-truncation (non-dependent) |
| 27 | `Path/Homotopy/TruncationTheory.lean:72` | `Trunc.ind` | Dependent eliminator for n-truncation |

### 1.5  SKI combinator equations (3)

| # | File | Name | Purpose |
|---|------|------|---------|
| 28 | `Path/Rewriting/CombinatorReductionDeep.lean:71` | `I_ax` | `I x = x` |
| 29 | `Path/Rewriting/CombinatorReductionDeep.lean:72` | `K_ax` | `K x y = x` |
| 30 | `Path/Rewriting/CombinatorReductionDeep.lean:73` | `S_ax` | `S x y z = (x z)(y z)` |

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
| **`HasVcompAssoc`** | `instHasVcompAssoc_EqTwoCat` | `TwoCategoryInstances.lean` | **NEW** — `PLift Eq` 2-cells; proof irrelevance |
| **`HasHcompFunctorial`** | `instHasHcompFunctorial_EqTwoCat` | `TwoCategoryInstances.lean` | **NEW** — `PLift Eq` 2-cells; proof irrelevance |
| **`HasInterchange`** | `instHasInterchange_EqTwoCat` | `TwoCategoryInstances.lean` | **NEW** — `PLift Eq` 2-cells; proof irrelevance |

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
| `axiom` declarations | **30** |
| Instantiated typeclasses ✅ | **10** |
| Impossible typeclasses ⛔ | **4** |
| Blocked at Path level ⛔ | **3** |
| Open problems 🔴 | **7** |
| Structural (mixed) | **1** (`HasDifferentialSquaredZero`) |
