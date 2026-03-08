# Skill: Identifying and Compartmentalizing Loop-Transport Boundaries

**Domain:** Omega-groupoid architecture, constructive type theory, residual boundaries

**Pattern:** When a term-rewriting system has pushed constructive content far (100+ lemmas of atomic loops, forward chains, etc.), but retains a small Prop-level fallback zone, compartmentalization often succeeds where direct elimination doesn't. If the boundary is loop-only, a second pass often succeeds by specializing to explicit loop indices before revisiting the global connector.

## Recognition

**Signature:** A zero-fuel fallback that:
1. Fires on a restricted domain (e.g., only loops, only when fuel exhausted)
2. Blocks a large recursive system's forward progress
3. Has already had tactical reductions applied

**Example:** `strict_transport₃` in `OmegaGroupoid.lean` — originally the last resort for loop comparisons after `connect_strict_structural_go` exhausted fuel; later shrunk by routing loop contraction through `strict_loop_contract_go`.

## The Three-Option Framework

When you identify such a boundary, always ask:

1. **Option A: Eliminate entirely via stronger theory?** (e.g., confluence hypothesis)
   - Cost: Medium (2–3h). Fits well if underlying infrastructure exists.
   
2. **Option B: Characterize and integrate?** (e.g., extend StepStar coverage)
   - Cost: Low-Medium (1.5–2.5h). Fits if domain is well-characterized.
   
3. **Option C: Compartmentalize?** (e.g., move behind clean API)
   - Cost: Tiny (30 min). Always viable. Unblocks future work.

**Decision rule:** If user says "review only unless tiny surgical change," use Option C. Maintains momentum while establishing clear interface.

## Refinement Pattern: Specialize the Loop Domain

After Option C, check whether the fallback is still primarily a **loop** problem.

If yes:

1. Define a loop-only recursion on explicit indices (`Derivation₂ p p`, not generic `Derivation₂ p q`).
2. Add constructive cases there first:
   - atomic loops
   - inverse atomic loops
   - forward `StepStar` tails
   - normalized-inverse recursion
   - immediately cancellable mixed-sign loop heads
3. Keep the original fallback only as the zero-fuel branch of the loop recursion.
4. Rewire the exported loop contraction API to use the loop recursion instead of the general connector.

**Why this works:** the explicit `p p` indices avoid the dependent-elaboration friction that often blocks surgical improvements in the generic `p q` connector.

## Implementation Checklist

- [ ] Decide whether the boundary should move behind a dedicated helper or a loop-only recursion
- [ ] If loop-only, specialize to explicit `Derivation₂ p p`
- [ ] Add constructive cases before the zero-fuel fallback
- [ ] Update calling site to use the specialized API
- [ ] Verify full build
- [ ] Document follow-up roadmap

## Anti-Pattern

❌ **Don't:** Try to eliminate boundary directly if Option A/B require major infrastructure changes.

✅ **Do:** Compartmentalize first, then specialize the loop domain if you can make constructive progress without rewriting the global connector.

---

**First use:** ComputationalPaths omega-groupoid (2026-03-06)  
**Updated:** 2026-03-08 with `strict_loop_contract_go` refinement  
**Status:** Proven effective
