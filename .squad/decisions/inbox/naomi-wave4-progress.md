# Naomi Wave-4 Progress (BouquetN + Dependents + Étale)

**Date:** 2026-03-04  
**By:** Naomi (Core Dev)  
**Requested by:** Arthur Freitas Ramos

## Scope Completed

### 1) BouquetN compile blockers fixed

File: `ComputationalPaths/Path/CompPath/BouquetN.lean`

Applied surgical proof repairs:
- Replaced two non-progressing `path_simp` proofs with explicit inverse laws:
  - `loop_cancel` uses `rweq_cmpA_inv_right`
  - `loop_cancel'` uses `rweq_cmpA_inv_left`
- Replaced non-progressing base-case simplification with `rweq_cmpA_refl_right`.
- Removed elimination-from-`Prop` into `Type` blockers:
  - `Exists` extraction via `obtain` replaced by arithmetic rewrite on `m - 1`.
  - `cases/match Nat.lt_or_eq_of_le` in `RwEq` goals replaced with `by_cases` + `Nat.le_antisymm`.
- Fixed mixed pattern branch (`| inr`) and aligned branch logic in integer sign-split cases.

Result: `lake build ComputationalPaths.Path.CompPath.BouquetN` ✅

### 2) Re-enabled `BouquetN` and dependent imports

`ComputationalPaths/Path.lean` re-enabled:
- `ComputationalPaths.Path.CompPath.BouquetN`
- `ComputationalPaths.Path.Algebra.BouquetFreeGroupOps`
- `ComputationalPaths.Path.Algebra.FreeGroupProperties`
- `ComputationalPaths.Path.Algebra.Abelianization`
- `ComputationalPaths.Path.Algebra.NielsenSchreier`
- `ComputationalPaths.Path.Algebra.NielsenSchreierDerived`

Dependent files had local import lines restored:
- `Path/Algebra/BouquetFreeGroupOps.lean` (imports BouquetN)
- `Path/Algebra/FreeGroupProperties.lean` (imports BouquetN + BouquetFreeGroupOps)
- `Path/Algebra/Abelianization.lean` (imports BouquetN)
- `Path/Algebra/NielsenSchreier.lean` (imports FreeGroupProperties)
- `Path/Algebra/NielsenSchreierDerived.lean` (imports NielsenSchreier)

Additional minimal syntax hygiene:
- `NielsenSchreierDerived.lean`: converted detached doc comments to regular comments and removed an extra nested `noncomputable section` opener that caused unmatched `end` errors.

Results:
- `lake build ComputationalPaths.Path.Algebra.BouquetFreeGroupOps` ✅
- `lake build ComputationalPaths.Path.Algebra.FreeGroupProperties` ✅
- `lake build ComputationalPaths.Path.Algebra.Abelianization` ✅
- `lake build ComputationalPaths.Path.Algebra.NielsenSchreier` ✅ (warnings only)
- `lake build ComputationalPaths.Path.Algebra.NielsenSchreierDerived` ✅

### 3) Deepening in Étale cohomology

File: `ComputationalPaths/Path/Algebra/EtaleCohomology.lean`

Added theorem:
- `zetaFunctional_chain_rweq`

What it proves:
- A nested path composition
  `trans (trans zeta (symm zeta)) (trans functional refl)`
  contracts to `functional` up to `RwEq`.

Proof uses nontrivial RwEq chaining:
- `rweq_trans`
- `rweq_trans_congr_left`
- `rweq_cmpA_inv_right`
- `rweq_cmpA_refl_left`
- `rweq_cmpA_refl_right`

Result: `lake build ComputationalPaths.Path.Algebra.EtaleCohomology` ✅

## Validation

Targeted module builds (all touched):
- `lake build ComputationalPaths.Path.CompPath.BouquetN` ✅
- `lake build ComputationalPaths.Path.Algebra.BouquetFreeGroupOps` ✅
- `lake build ComputationalPaths.Path.Algebra.FreeGroupProperties` ✅
- `lake build ComputationalPaths.Path.Algebra.Abelianization` ✅
- `lake build ComputationalPaths.Path.Algebra.NielsenSchreier` ✅
- `lake build ComputationalPaths.Path.Algebra.NielsenSchreierDerived` ✅
- `lake build ComputationalPaths.Path.Algebra.EtaleCohomology` ✅
- `lake build ComputationalPaths.Path` ✅

Full:
- `lake build` ✅

## Decisions / Blockers

- **Decision:** Re-enable full Bouquet chain in `Path.lean` now; all requested modules compile with minimal local edits.
- **Blockers:** None for this wave’s requested modules.
- **Note:** `NielsenSchreier.lean` emits existing unused simp-arg warnings (`Path.toEq`), non-blocking.
