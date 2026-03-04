# Holden Wave 1–2 Execution Plan & Deepening Targets

**Lead:** Holden (Architecture & Scope Triage)  
**Date:** 2026-03-02  
**Charter:** Prioritize reconnection waves and deepening by ROI/risk. No code edits.

---

## Executive Summary

**101 disabled imports** present a clear prioritization ladder:
- **Quick wins (completed 2026-03-01):** 5 fixes, 45% reduction in active failures
- **Wave 1 (next sprint):** Fix 3 root causes → unblock 13 modules (~4 hours)
- **Wave 2 (following sprint):** Fix symbol collisions + VanKampen family → unblock 7 more modules (~6 hours)
- **Deepening:** 3 strategic files (Step.lean, DoubleCategPathsDeep, CompletionDeep) to lift from shallow→medium-deep

**Rationale:** Fix highest-impact root causes first (BouquetN unblocks 5, HigherHomotopyGroups unblocks 8). Collisions are low-effort disambiguation.

---

## WAVE 1 (Next Sprint — 4 hours, 13 modules unblocked)

### Task 1.1: Path.CompPath.BouquetN
**Owner:** Naomi  
**Effort:** 1–2 hours  
**Unblocks:** 5 downstream modules
- `Path.Algebra.BouquetFreeGroupOps`
- `Path.Algebra.FreeGroupProperties`
- `Path.Algebra.Abelianization`
- `Path.Algebra.NielsenSchreier`
- `Path.Algebra.NielsenSchreierDerived`

**Issue:** Tactic errors in encode-decode proofs (path normalization, RwEq reasoning)  
**Minimal Fix:** Replace scaffold `path_auto` placeholders with explicit `rweq_trans` + `rweq_cmpA_*` chains  
**Success Criteria:**
- ✅ File type-checks
- ✅ Lake build passes
- ✅ No new sorries introduced
- ✅ All 5 downstream modules unblock in Path.lean

---

### Task 1.2: Path.Homotopy.HigherHomotopyGroups
**Owner:** Naomi  
**Effort:** 0.5 hours  
**Unblocks:** 8 downstream modules
- `Path.Homotopy.HomotopyGroup`
- `Path.Homotopy.DoldThom`
- `Path.Homotopy.EHPSequence`
- `Path.Homotopy.KervaireInvariant`
- `Path.Homotopy.MooreSpace`
- `Path.Homotopy.PhantomMaps`
- `Path.Homotopy.SerreModC`
- `Path.Homotopy.WhiteheadProduct`

**Issue:** Universe level mismatch in `PiN` definition (returns `Type (u+2)`, consumers expect `Type u`)  
**Minimal Fix:** Add universe parameter wrappers (`ULift`) to `higherPiN_refl`, `higherPiN_comp`  
**Success Criteria:**
- ✅ File type-checks
- ✅ All 8 dependent modules pass
- ✅ Lake build completes without regressions

---

### Task 1.3: HigherCategory.Bicategory (+ GrayCategory/Tricategory chain)
**Owner:** Naomi  
**Effort:** 1–1.5 hours  
**Unblocks:** 3 modules (Bicategory, GrayCategory, Tricategory)

**Issue:** Compilation errors (likely universe mismatches or missing proofs)  
**Minimal Fix:** Triage root cause; resolve universe/syntax errors; apply targeted patches  
**Success Criteria:**
- ✅ All 3 modules in HigherCategory.lean uncommented and type-check
- ✅ No circular dependency reintroduced
- ✅ Lake build + HigherCategory subset builds complete

---

## WAVE 2 (Following Sprint — 6 hours, 7 modules unblocked)

### Task 2.1: Path.Rewrite.CompletionTheorem + TerminationProofs
**Owner:** Naomi  
**Effort:** 1.5 hours  
**Unblocks:** 2 modules (both in Rewriting aggregator)

**Issue:** Compilation defects (syntax/type errors)  
**Strategy:** Triage each independently; apply targeted fixes  
**Success Criteria:**
- ✅ Both files type-check
- ✅ Rewriting aggregator remains stable
- ✅ Lake build passes

---

### Task 2.2: Path.Homotopy.VanKampen Family (3 files)
**Owner:** Naomi  
**Effort:** 2–3 hours  
**Unblocks:** 3 modules
- `Path.Homotopy.VanKampen`
- `Path.Homotopy.VanKampenApplications`
- `Path.Homotopy.ModelStructure`

**Issue:** Each has independent root cause (type errors, missing lemmas, tactic failures)  
**Strategy:** Separate triage per file; fix in order of dependency  
**Success Criteria:**
- ✅ All 3 files type-check
- ✅ No new sorries introduced
- ✅ Lake build + Homotopy subset passes

---

### Task 2.3: Symbol Collisions Batch (5 files)
**Owner:** Naomi  
**Effort:** 1.5 hours  
**Resolves:** 5 name-collision disabling reasons

**Files to Resolve:**
1. `Coherence.CoherenceDeep` (collision: AssociativityCoherence)
2. `Path.Equivalence.PathInfrastructure` (collision: PathEquivalence)
3. `Enriched.EnrichedPaths` (symbol collisions)
4. `Kan.AdjunctionCoherence` (symbol collisions)
5. `TypeFormers.UniverseCoherence` (collision: CwF.UniverseCoherence)

**Minimal Fix:** Fully qualify names or rename conflicting definitions to avoid ambiguity  
**Success Criteria:**
- ✅ All 5 files disambiguated (comments added if renaming necessary)
- ✅ No root-cause changes needed; renaming only
- ✅ Colliding modules (if re-enabled) can coexist

---

## DEEPENING TARGETS (Post-Reconnection, 1–2 weeks)

### Priority 1: Step.lean

**Current State:** 1,745 lines | Path:380 | RwEq:1 (critically shallow)  
**Why:** Core rewrite-rule infrastructure; only 1 RwEq usage despite 83 lemmas  
**Target:** Lift from RwEq:1 → RwEq:20+

**Concrete Acceptance Criteria:**
1. ✅ Add RwEq-respecting proofs for 5+ major lemmas
   - Example: `rweq_trans_congr_left`, `rweq_cmpA_refl`, `rweq_normalize_chain`
2. ✅ Document each with a 1-line proof sketch (why it respects RwEq)
3. ✅ Include at least 1 multi-step chain proof (Path.trans → Path.symm → Path.trans with RwEq equivalence)
4. ✅ No sorries; all proofs complete
5. **Deliverable:** Updated Step.lean with inline comments showing RwEq relationships

---

### Priority 2: Algebra/DoubleCategPathsDeep.lean

**Current State:** 750 lines | Path:296 | RwEq:0 (shallow despite "Deep" name)  
**Why:** Heavy Path infrastructure but zero RwEq; coherence laws are natural RwEq targets  
**Target:** Lift from RwEq:0 → RwEq:15+

**Concrete Acceptance Criteria:**
1. ✅ Formalize pentagon coherence as RwEq equivalence
   - Prove: `pentagon_law : RwEq (path_expr_1) (path_expr_2)`
2. ✅ Formalize hexagon identity similarly
3. ✅ Implement 3+ domain-specific `DoubleCategStep` inductive constructors for rewrite rules
4. ✅ Include 1 encode-decode style proof (DoubleCategory lemma ↔ Path witness)
5. ✅ All proofs completed; zero sorries
6. **Deliverable:** DoubleCategPathsDeep with coherence proofs expressed as RwEq

---

### Priority 3: Rewriting/CompletionDeep.lean

**Current State:** 936 lines | Path:369 | RwEq:0 (abstract theory without Path evidence)  
**Why:** 99 theorems on rewrite systems; ripe for computational path formalization  
**Target:** Lift from RwEq:0 → RwEq:10+ with genuine step-based reasoning

**Concrete Acceptance Criteria:**
1. ✅ Implement `CompletionStep` inductive type (5+ constructors for rewrite rules)
2. ✅ Prove confluence lemma using RwEq path witnesses (not pure logic)
3. ✅ Prove termination metric using Path-indexed reasoning
4. ✅ Add critical-pair resolution proof with step-based Path construction
5. ✅ All proofs completed; zero sorries; no axioms
6. **Deliverable:** CompletionDeep with Step-based proofs for 3+ key theorems

---

## Risk & Mitigation

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|-----------|
| BouquetN/HigherHomotopyGroups patch breaks downstream | Medium | High | Incremental testing after each Wave 1 fix; full rebuild before Wave 2 |
| VanKampen fixes have conflicting root causes | Medium | Medium | Triage each file independently; document fix in comments |
| Deepening introduces new sorries | Low | Critical | QA: `grep -r "sorry" --include="*.lean"` post-edit; zero-tolerance rule |
| Collision renames break external imports | Low | Low | Check import graph per file before renaming |

---

## Success Metrics (Cumulative)

| Phase | Modules Enabled | Build Status | Sorries | Axioms |
|-------|-----------------|--------------|---------|--------|
| **Current (2026-03-01)** | 913 | ✅ PASS | 0 | 0 |
| **After Wave 1** | 926 (+13) | ✅ PASS | 0 | 0 |
| **After Wave 2** | 933 (+20) | ✅ PASS | 0 | 0 |
| **After Deepening** | 933 | ✅ PASS | 0 | 0 |

**Deepening Impact:**
- Step.lean: RwEq count 1 → 20+
- DoubleCategPathsDeep: RwEq count 0 → 15+
- CompletionDeep: RwEq count 0 → 10+
- **Total RwEq surface growth:** ~45 lemmas with explicit path witnesses

---

## Next Actions (for Naomi)

1. **Immediately after Wave 1 approval:**
   - Schedule 1.1, 1.2, 1.3 in parallel (no interdependencies)
   - Test each fix independently; commit with "Wave 1 reconnection: [module]" messages

2. **Between Wave 1 → Wave 2:**
   - Full regression test on 913 currently-enabled modules
   - Confirm no new sorries/axioms introduced

3. **Wave 2 execution:**
   - Start 2.1 (CompletionTheorem/TerminationProofs) in parallel with 1.1–1.3
   - Sequence 2.2 (VanKampen) after 2.1 (lighter collateral damage)
   - Finalize 2.3 (collisions) last (purely cosmetic renames)

4. **Deepening (post-Wave 2):**
   - Each deepening target is independent; can start in parallel
   - Assign Priority 1 (Step.lean) to Naomi (1–2 hours)
   - Assign Priorities 2–3 to specialized domain experts if available (math depth required)

---

**Decision Authority:** Holden (Lead)  
**Reviewed by:** Arthur Freitas Ramos  
**Status:** Ready for Naomi execution approval
