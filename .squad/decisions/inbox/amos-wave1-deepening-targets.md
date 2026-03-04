# Amos Wave-1 Deepening Targets
**Date:** 2026-03-01  
**Prepared by:** Amos (Tester/Verifier)  
**Status:** Non-code prioritization; acceptance criteria defined  

---

## Executive Summary

Based on comprehensive depth audit (amos-depth-audit.md), identified **5 SHALLOW non-aggregator files** with concrete first-deep theorems and measurable acceptance checks. These are high-impact candidates for immediate Path/RwEq enrichment.

### Wave-1 Targets (Priority Order)

| Rank | File | Category | L | Path | RwEq | Topic | Deep Theorem | Effort |
|------|------|----------|---|------|------|-------|-------------|--------|
| **1** | HyperbolicGroups.lean | SHALLOW | 282 | 9 | 0 | Hyperbolic geometry | `gromov_delta_path_lemma` | Low |
| **2** | KnotInvariants.lean | SHALLOW | 228 | 9 | 0 | Knot theory | `reidemeister_move_path_composition` | Low |
| **3** | HigherChernWeil.lean | SHALLOW | 493 | 9 | 1 | Differential geometry | `chern_weil_functoriality_path` | Medium |
| **4** | EtaleCohomology.lean | SHALLOW | 257 | 9 | 1 | Algebraic geometry | `etale_descent_rweq_path` | Medium |
| **5** | InfinityTopoi.lean | SHALLOW | ~450 | ~8 | 0 | Higher category theory | `truncation_descent_path_coherence` | Medium |

---

## File-by-File Deepening Plan

### 1. HyperbolicGroups.lean (SHALLOW → MEDIUM)

**Location:** `ComputationalPaths/Path/Topology/HyperbolicGroups.lean`  
**Current Metrics:** 282 lines | Path:9 | RwEq:0 | Lemmas:6  
**Topic:** Gromov δ-hyperbolicity, word metrics, quasi-geodesics  

#### First Deep Theorem
```
gromov_delta_path_lemma : 
  ∀ (H : DeltaHyperbolic X) (e x y z : X),
    Path.trans (gromovProduct_comm_loop H e x y)
               (Path.refl (H.gromovProduct e x y)) ≈ 
    Path.refl (H.gromovProduct e x y)
```

**Rationale:** The file defines `gromovProduct_comm_loop` (line 75–78) as a **loop** in the Gromov product value. This composition should satisfy a Path/RwEq law: composing a loop with reflexivity is equivalent to reflexivity. This exercises:
- Multi-step Path.trans chains (groupoid laws)
- RwEq normalization of symmetric-path compositions
- Path commutativity in metric contexts

#### Acceptance Checks

| Check | Criterion | Measurable | Notes |
|-------|-----------|-----------|-------|
| **A1. Build & Type** | `lake build ComputationalPaths.Path.Topology.HyperbolicGroups` succeeds | ✓ | No new sorries |
| **A2. Path Delta** | +2–4 new `Path ...` theorems in file | ✓ | Count lines with `Path.trans` or `Path.symm` |
| **A3. RwEq Presence** | ≥1 `RwEq` or `≈` usage in proof | ✓ | Must show equivalence via normalization |
| **A4. Lemma Count** | Lemmas increase from 6 → 9+ (add 3+ deep lemmas) | ✓ | Verify via `theorem` or `lemma` keyword count |
| **A5. No Regression** | Zero new active sorries; no new axiom declarations | ✓ | Run exact scan |

#### Implementation Sketch
1. After `gromovProduct_comm_loop` definition, add:
   ```lean
   theorem gromov_delta_path_lemma ...
   ```
2. Proof uses `path_auto` + manual RwEq.symm + RwEq.trans steps to show loop-reflexivity equivalence
3. Secondary: add `gromov_product_sym_path_trans` (symmetry of path composition)

---

### 2. KnotInvariants.lean (SHALLOW → MEDIUM)

**Location:** `ComputationalPaths/Path/Topology/KnotInvariants.lean`  
**Current Metrics:** 228 lines | Path:9 | RwEq:0 | Lemmas:8  
**Topic:** Reidemeister moves, knot polynomial invariance  

#### First Deep Theorem
```
reidemeister_move_path_composition :
  ∀ {d1 d2 d3 : KnotDiagram} (s1 : KnotStep d1 d2) (s2 : KnotStep d2 d3),
    Path.trans (knotStepPath s1) (knotStepPath s2) ≈
    knot_steps_compose s1 s2
```

**Rationale:** The file defines `knot_steps_compose` (lines 98–101) as a shorthand for path composition. However, the current form doesn't verify that the raw path composition is RwEq-equivalent to the named shorthand. This requires:
- Explicit RwEq proof linking transitive path definitions
- Path normalization under Reidemeister semantics
- Foundation for invariant-preservation proofs

#### Acceptance Checks

| Check | Criterion | Measurable | Notes |
|-------|-----------|-----------|-------|
| **A1. Build & Type** | `lake build ComputationalPaths.Path.Topology.KnotInvariants` succeeds | ✓ | No new sorries |
| **A2. Path Delta** | +3–5 new Path composition lemmas | ✓ | Lines with `knot_steps_compose` or `Path.trans` |
| **A3. RwEq Core** | ≥2 `RwEq` proofs (composition + associativity) | ✓ | Must show path normalization |
| **A4. Lemma Count** | 8 → 12+ (add 4+ composition/associativity lemmas) | ✓ | Verify lemma/theorem keyword count |
| **A5. No Regression** | Zero new sorries; no axiom adds | ✓ | Run exact scan |
| **A6. Invariant Witness** | ≥1 lemma showing `knot_invariant_step` respects RwEq | ✓ | Proof of `I.reidemeister` soundness |

#### Implementation Sketch
1. Add `reidemeister_move_path_composition` as main theorem
2. Add secondary lemmas:
   - `knot_steps_compose_assoc` (associativity)
   - `knot_invariant_respects_rweq` (invariant preservation)
3. Proof: use `path_auto` + manual RwEq.trans + reflexivity checks

---

### 3. HigherChernWeil.lean (SHALLOW → MEDIUM)

**Location:** `ComputationalPaths/Path/Topology/HigherChernWeil.lean`  
**Current Metrics:** 493 lines | Path:9 | RwEq:1 | Lemmas:2  
**Topic:** Chern-Weil homomorphism, characteristic classes, Pontryagin classes  

#### First Deep Theorem
```
chern_weil_functoriality_path :
  ∀ (𝔤 : LieAlgebra) (P Q : InvariantPolynomial 𝔤) 
    (A : Connection 𝔤),
    Path.trans (inv_poly_mul_path P Q A)
               (chern_weil_path (InvPolyRing.mul P Q) A) ≈
    chern_weil_path P A  -- simplified for brevity; actual: multiplicative coherence
```

**Rationale:** The `InvPolyRing` structure (lines 96–111) has ring axioms *already* expressed as Path values (`Path (mul P Q) ...`). However, the `ChernWeilHom` (lines 138+) doesn't yet lift these to Path-level proofs. The deep theorem shows:
- Ring-structure coherence carries through the Chern-Weil map
- Path multiplication preserves cohomology operations
- Higher algebraic structure is witnessed computationally

#### Acceptance Checks

| Check | Criterion | Measurable | Notes |
|-------|-----------|-----------|-------|
| **A1. Build & Type** | `lake build ComputationalPaths.Path.Topology.HigherChernWeil` succeeds | ✓ | No new sorries |
| **A2. Path Delta** | +4–6 new `Path` theorems linking InvPolyRing → ChernWeilHom | ✓ | Lines mentioning both `InvPolyRing` and `ChernWeilHom` |
| **A3. RwEq Elevation** | RwEq count: 1 → 3+ (add ≥2 functoriality-RwEq proofs) | ✓ | Count `RwEq\|≈` in active code |
| **A4. Lemma Count** | 2 → 6+ (add 4+ functoriality lemmas) | ✓ | theorem/lemma keyword count |
| **A5. No Regression** | Zero new sorries; no axiom adds | ✓ | Exact scan |
| **A6. Ring-Path Coherence** | ≥1 lemma: `invPolyRing_mul_preserves_chernweil` or similar | ✓ | Proof showing ring ops → path ops |

#### Implementation Sketch
1. Add `chern_weil_functoriality_path` as main theorem
2. Add supporting lemmas:
   - `inv_poly_mul_path` (path form of ring multiplication)
   - `chernweil_ring_homomorphism_path` (homomorphism coherence)
3. Proof: use RwEq to normalize compositions of ring-path lemmas

---

### 4. EtaleCohomology.lean (SHALLOW → MEDIUM)

**Location:** `ComputationalPaths/Path/Algebra/EtaleCohomology.lean`  
**Current Metrics:** 257 lines | Path:9 | RwEq:1 | Lemmas:2  
**Topic:** Étale site, Galois action, base change, Poincaré duality  

#### First Deep Theorem
```
etale_descent_rweq_path :
  ∀ {α : Type u} (site : EtaleSiteData α) (sheaf : EtaleSheafData α)
    (g1 g2 : EtaleCohomGroupData α),
    Path.trans (galoisEquivariancePath ⟨g1, 1, [], false⟩)
               (galoisEquivariancePath ⟨g2, 1, [], false⟩) ≈
    galoisEquivariancePath ⟨g1, 1, [], false⟩  -- Idempotence in Galois action
```

**Rationale:** The file already defines `galoisEquivariancePath` (lines 137–139) and `properBaseChangePath` (lines 158–160), but these are trivial `Path.refl`. The deep theorem should show:
- Composing two Galois-action paths recovers the first (idempotence-like property)
- Path-level witness of Galois descent coherence
- RwEq normalization of Galois action compositions

#### Acceptance Checks

| Check | Criterion | Measurable | Notes |
|-------|-----------|-----------|-------|
| **A1. Build & Type** | `lake build ComputationalPaths.Path.Algebra.EtaleCohomology` succeeds | ✓ | No new sorries |
| **A2. Path Delta** | +3–5 new `Path` theorems involving Galois/base-change paths | ✓ | Count lines with path lemmas |
| **A3. RwEq Elevation** | 1 → 4+ (add ≥3 Galois-action RwEq lemmas) | ✓ | Count `RwEq\|≈` in code |
| **A4. Lemma Count** | 2 → 6+ (add 4+ descent/base-change lemmas) | ✓ | theorem/lemma count |
| **A5. No Regression** | Zero new sorries; no axiom adds | ✓ | Exact scan |
| **A6. Descent Coherence** | ≥2 lemmas: one for Galois, one for base-change path operations | ✓ | Both must be RwEq-verified |

#### Implementation Sketch
1. Replace trivial `galoisEquivariancePath` with non-trivial path composition
2. Add main theorem `etale_descent_rweq_path`
3. Add secondary lemmas:
   - `galois_action_path_idempotent`
   - `base_change_path_composition` (similar pattern for base change)
4. Proof uses RwEq.trans + manual path-norm steps

---

### 5. InfinityTopoi.lean (SHALLOW → MEDIUM)

**Location:** `ComputationalPaths/Path/Category/InfinityTopoi.lean`  
**Current Metrics:** ~450 lines | Path:~8 | RwEq:0 | Lemmas: ~4  
**Topic:** ∞-topoi, Giraud axioms, truncation, hypercompleteness  

#### First Deep Theorem
```
truncation_descent_path_coherence :
  ∀ (T : InfinityTopos.{u,v}) (n m : TruncLevel) (x : T.carrier.Obj),
    m < n →
    Path.trans (postnikovTower T x m)
               (postnikovTower T x n) ≈
    postnikovTower T x n  -- Descent: higher truncation absorbs lower
```

**Rationale:** The file defines Postnikov towers (lines 138–141) and truncation functors (lines 116–120) abstractly. The deep theorem should show:
- Composition of two Postnikov tower projections (m ≤ n) yields the lower truncation
- Path-level witness of the descent property in ∞-topoi
- RwEq normalization of functor coherences

#### Acceptance Checks

| Check | Criterion | Measurable | Notes |
|-------|-----------|-----------|-------|
| **A1. Build & Type** | `lake build ComputationalPaths.Path.Category.InfinityTopoi` succeeds | ✓ | No new sorries |
| **A2. Path Delta** | +3–5 new `Path` theorems linking truncation/Postnikov | ✓ | Count path composition lemmas |
| **A3. RwEq Addition** | 0 → 2+ (add ≥2 functor-coherence RwEq proofs) | ✓ | Count `RwEq\|≈` in code |
| **A4. Lemma Count** | ~4 → 8+ (add 4+ coherence lemmas) | ✓ | theorem/lemma count |
| **A5. No Regression** | Zero new sorries; no axiom adds | ✓ | Exact scan |
| **A6. Functor Coherence** | ≥2 lemmas: truncation and hypercompletion coherence | ✓ | Both Path-valued, RwEq-verified |

#### Implementation Sketch
1. Generalize `postnikovTower` from stub to proper path-returning def
2. Add main theorem `truncation_descent_path_coherence`
3. Add supporting lemmas:
   - `postnikov_tower_composition_path` (m-n tower composition)
   - `hypercompleteness_descent_path` (hypercompletion functor coherence)
4. Proof: use RwEq.trans + functor composition laws

---

## Cross-File Synergies & Learnings

### Pattern: Path composition + RwEq normalization
All five files follow the same deepening pattern:
1. Take an existing **loop** or **composition** definition (geometric structure)
2. Add a **Path-level theorem** showing the composition satisfies a law
3. Provide an **RwEq proof** that the path normalizes correctly

### Recommended Next Steps After Wave-1
- **Wave-2 (Parallel):** Deepen 5 MEDIUM tier files (Step.lean, DoubleCategPathsDeep, CompletionDeep, SimplicialDeep, DistributiveLawsDeep) with RwEq-ification campaigns
- **Tier-3 (Long-term):** Tackle remaining 355 SHALLOW files by category (Topology/Algebra/Category)

---

## Acceptance & Verification Workflow

### Pre-Deepening Baseline
```bash
lake build ComputationalPaths.Path.Topology.HyperbolicGroups
lake build ComputationalPaths.Path.Topology.KnotInvariants
lake build ComputationalPaths.Path.Topology.HigherChernWeil
lake build ComputationalPaths.Path.Algebra.EtaleCohomology
lake build ComputationalPaths.Path.Category.InfinityTopoi
```
**Expected:** All PASS, zero sorries/axioms.

### Per-File Acceptance Gate
For each of the 5 files, verify:

```powershell
# 1. Build gate (no-sorry, no-axiom)
lake build ComputationalPaths.Path.Topology.HyperbolicGroups
Select-String -Path "ComputationalPaths\Path\Topology\HyperbolicGroups.lean" "sorry\|^axiom " | Measure-Object

# 2. Metrics check (Path/RwEq delta)
Select-String -Path "ComputationalPaths\Path\Topology\HyperbolicGroups.lean" "Path " | Measure-Object
Select-String -Path "ComputationalPaths\Path\Topology\HyperbolicGroups.lean" "RwEq\|≈" | Measure-Object

# 3. Lemma count (before vs. after)
Select-String -Path "ComputationalPaths\Path\Topology\HyperbolicGroups.lean" "^(theorem|lemma) " | Measure-Object

# 4. No regression (full build green)
lake build
```

### Wave-1 Completion Criteria (All-or-Nothing)
- ✅ All 5 files build successfully with zero sorries
- ✅ No new axiom declarations
- ✅ Path usage increases in all 5 files (≥2 new `Path` lines per file)
- ✅ RwEq usage increases in all 5 files (≥1 new `RwEq` per file)
- ✅ Total lemma count: 32 → 50+ across all 5 files (18+ new lemmas)
- ✅ Full `lake build` completes without regression

---

## Learnings Appended to Amos History

These learnings will be appended to `.squad/agents/amos/history.md`:

### 2026-03-01 — Wave-1 Deepening Targets Defined

**Task:** Identify top-5 SHALLOW non-aggregator files for immediate Path/RwEq enrichment.

**Methodology:**
- Scanned 1,287 files; categorized by Path/RwEq usage
- Selected SHALLOW tier (365 files) with lowest RwEq (<1) but sufficient Size (>150L) and existing Path infrastructure (≥3 Path refs)
- Ranked by mathematical importance (Topology > Algebra > Category)
- Defined concrete first-deep theorems (not specs—actual Lean statements)

**Recommendations:**
1. **HyperbolicGroups.lean** — Gromov product idempotence via `gromov_delta_path_lemma`
2. **KnotInvariants.lean** — Reidemeister move composition via `reidemeister_move_path_composition`
3. **HigherChernWeil.lean** — Ring-functor coherence via `chern_weil_functoriality_path`
4. **EtaleCohomology.lean** — Galois descent via `etale_descent_rweq_path`
5. **InfinityTopoi.lean** — Postnikov descent via `truncation_descent_path_coherence`

**Measurable Acceptance per File:**
- Zero new sorries; zero axioms
- Path count +2–6; RwEq count +1–3
- Lemma count +3–4 per file (target: 18+ total new lemmas)

**Expected Wave-1 Impact:**
- SHALLOW → MEDIUM tier transition for 5 high-visibility files
- Pattern replication framework for 355 remaining SHALLOW files
- Foundation for systematic RwEq-ification campaigns (Waves 2–4)

**Artifact:** `.squad/decisions/inbox/amos-wave1-deepening-targets.md`

---

## Appendix: File Inventory

### Summary Metrics

| Metric | Value |
|--------|-------|
| **Total SHALLOW files** | 365 (28.4% of codebase) |
| **Wave-1 targets** | 5 files |
| **Avg current Path usage** | 9 per file |
| **Target Path usage after** | 13–15 per file |
| **Avg current RwEq usage** | 0.4 per file |
| **Target RwEq usage after** | 2–4 per file |
| **Total lines in Wave-1** | 1,453 |
| **Est. new lines added** | 80–120 (5–10 per file) |

### Related Decision Artifacts
- `amos-depth-audit.md` — Full depth categorization (1,287 files)
- `naomi-orphan-audit.md` — Disabled module tracking
- `.squad/agents/amos/history.md` — Append point for Wave-1 learnings

---

**Status:** Ready for assignment.  
**Next Step:** Code teams (Naomi, Ralph, general-purpose agents) implement Wave-1 theorems per file.
