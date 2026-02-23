# Axiom Audit Report for ComputationalPathsLean

**Audit Date:** 2026-02-23  
**Auditor:** Tali (Engineering Audit Subagent)

## Executive Summary

The core theorems (ω-groupoid structure, confluence, π₁(S¹) ≅ ℤ) use **only Lean 4's built-in axioms** and **do not depend on any custom project axioms**.

---

## 1. Custom Axiom Count

**Total custom axioms: 34** (across 8 files)

| File | Axiom Count | Category |
|------|-------------|----------|
| `Path/Algebra/HigherInductiveDeep.lean` | 9 | HIT path constructors |
| `Path/HoTT/UnivalencePaths.lean` | 5 | Univalence (ua') |
| `Path/HoTT/UnivalenceDeep.lean` | 3 | Univalence (ua) |
| `Path/Homotopy/TruncationTheory.lean` | 5 | Truncation |
| `Path/Homotopy/HigherInductiveTypes.lean` | 5 | HIT (glue, Trunc) |
| `Path/Homotopy/UnivalenceApplications.lean` | 3 | Univalence inverse |
| `Path/Homotopy/SyntheticHomotopy.lean` | 3 | Circle.loop, Susp.merid |
| `Path/Homotopy/HomotopyPushout.lean` | 1 | HPushout.glue |

### Axiom Categories

1. **Univalence axioms (11):** `ua`, `ua'`, `ua_transport`, `ua_refl'`, `ua'_comp`, `ua'_symm_transport`, etc.
2. **HIT path constructors (14):** `S1.loop`, `Interval.seg`, `Susp.merid`, `glue`, `Torus.surface`, etc.
3. **Truncation axioms (9):** `Trunc`, `Trunc.mk`, `Trunc.isOfHLevel`, `Trunc.elim`, `Trunc.ind`, etc.

---

## 2. Core Result Import Analysis

### ✓ OmegaGroupoid.lean (ω-groupoid structure)
```
Imports: Path.Basic, Path.Rewrite.Step, Path.Rewrite.RwEq, Path.Rewrite.Rw
```
**Status: NO CUSTOM AXIOMS**

### ✓ ConfluenceDeep.lean (confluence theorem)
```
Imports: Path.Basic, Path.Rewrite.RwEq
```
**Status: NO CUSTOM AXIOMS**

### ✓ CircleCompPath.lean (π₁(S¹) ≅ ℤ)
```
Imports: Path.Basic, Path.Rewrite.SimpleEquiv, Path.Homotopy.FundamentalGroup
  └── FundamentalGroup ← Loops ← Basic, Rewrite.RwEq, Rewrite.Quot
```
**Status: NO CUSTOM AXIOMS**

---

## 3. Lean 4 Built-in Axioms Used

The core modules do use Lean 4's standard axioms:

| Axiom | Usage | Location |
|-------|-------|----------|
| `Classical.choice` | Converting `RwEqProp` ↔ `RwEq` | `Path/Rewrite/RwEq.lean` |
| `Quot.sound` | Quotient constructions | `Path/Basic/CongruenceClosure.lean` |
| `propext` | Implicit (used by tactics) | Standard |
| `funext` | Function extensionality | Theorem in Lean 4, not axiom |

**Note:** `Classical.choice` is used in `RwEq.lean` (lines 67, 845) for converting between propositional and data-level rewrite equivalence. This is inherited by all three core theorem files.

---

## 4. Isolation Architecture

The codebase has clean separation:

```
Core Results (axiom-free)          Exploratory/HoTT (has axioms)
─────────────────────────          ─────────────────────────────
Path/Basic/*                       Path/HoTT/*
Path/Rewrite/*                     Path/Homotopy/SyntheticHomotopy
Path/CompPath/CircleCompPath       Path/Homotopy/TruncationTheory
Path/OmegaGroupoid                 Path/Algebra/HigherInductiveDeep
Path/Confluence*                   Comparison/UnivalenceAnalog
```

The `Path.lean` umbrella file imports everything (including axiom files), but individual theorem files maintain clean dependencies.

---

## 5. Paper Disclosure Recommendation

### For Main Results Section:
> "The core results (ω-groupoid structure, confluence, π₁(S¹) ≅ ℤ) are formalized in Lean 4 using only the standard axiomatic basis: `propext`, `Quot.sound`, and `Classical.choice`. No additional axioms such as univalence or function extensionality are required."

### For Technical Appendix (if discussing HoTT connections):
> "The development includes exploratory modules connecting computational paths to HoTT concepts (univalence, higher inductive types). These modules introduce 34 custom axioms for HIT path constructors and univalence, but these are strictly isolated from the core results and not transitively imported by any main theorem."

### Detailed Footnote Option:
> "We note that `Classical.choice` is used in `RwEq.lean` for convenience in converting between propositional witnesses and computational data. The core mathematical content could be refactored to be constructive if desired, at the cost of some ergonomic overhead."

---

## 6. Verification Commands

To verify this audit independently:

```bash
# Find all custom axioms
grep -rn "^axiom " --include="*.lean" ComputationalPaths/

# Check core file imports
grep "^import" ComputationalPaths/Path/OmegaGroupoid.lean
grep "^import" ComputationalPaths/Path/Rewrite/ConfluenceDeep.lean
grep "^import" ComputationalPaths/Path/CompPath/CircleCompPath.lean

# Check for Classical usage
grep -rn "Classical\." ComputationalPaths/Path/Basic/ ComputationalPaths/Path/Rewrite/
```

---

**Audit Status: COMPLETE ✓**
