# HEARTBEAT — Overnight Work Directive

## User went to sleep at ~12:04 AM Feb 22, 2026
## Wake expectation: repo pristine, paper rewritten, CI green

## Active Priority Queue
1. **Build errors → 0**: Armadas 765-767 fixing all remaining `lake build` errors
2. **Guard RwEq**: Armada 768 ensuring no Subsingleton(RwEq) sneaks back
3. **CI green**: After build clean, ensure GitHub Actions pass
4. **Paper rewrite**: After repo is clean, rewrite paper with genuine results

## CRITICAL CONSTRAINTS
- **NEVER add `Subsingleton (RwEq)` instance or `rweq_proof_irrel` axiom**
- **NEVER add sorry or admit**
- **NEVER delete old ComputationalPaths/ files without approval**
- **All code via `copex fleet --worktree`**
- **Keep 5 armadas running at all times**

## Current Repo State (as of midnight)
- 1,255 .lean files, unified under ComputationalPaths/
- 0 sorry, 0 admit (verified)
- 0 Subsingleton(RwEq), 0 rweq_proof_irrel (verified)  
- ~525 build errors remaining
- RwEq is Type-valued (correct)
- GitHub synced through commit b7b9f02

## Cycle Pattern
1. Wait for armadas to complete
2. Commit/push any unstaged changes
3. Check error count
4. Launch new armadas for remaining errors
5. After 0 build errors: launch paper rewrite
6. After paper done: verify CI
7. Repeat until perfect
