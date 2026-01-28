# GitHub Copilot Instructions for ComputationalPaths

This document provides guidance for GitHub Copilot when working with the Computational Paths codebase.

## Project Overview

**Computational Paths** is a Lean 4 formalization of propositional equality via explicit computational paths and rewrite equality. It provides:

1. **A rewrite-based equality system**: Paths are explicit witnesses of equality, related by a term rewriting system (LND_EQ-TRS)
2. **Fundamental group calculations**: π₁ of computational-path constructions using encode-decode methods
3. **Higher categorical structures**: Weak ω-groupoid structure on types via computational paths

## Build Commands

```bash
# Build everything
lake build

# Build specific module
lake build ComputationalPaths.Path.CompPath.CircleCompPath

# Run executable
lake exe computational_paths

# Clean build artifacts
lake clean
```

## Key Types

| Type | Description |
|------|-------------|
| `Path a b` | Computational path from `a` to `b` |
| `Step p q` | Single-step rewrite from path `p` to `q` |
| `Rw p q` | Multi-step rewrite (reflexive-transitive closure of Step) |
| `RwEq p q` | Rewrite equivalence (symmetric-transitive closure of Rw) |
| `π₁(A, a)` | Fundamental group (notation for `LoopQuot A a`) |
| `SimpleEquiv α β` | Lightweight type equivalence |

## Path Constructors

```lean
Path.refl : (a : A) → Path a a
Path.symm : Path a b → Path b a
Path.trans : Path a b → Path b c → Path a c
Path.congrArg : (f : A → B) → Path a a' → Path (f a) (f a')
```

## Path Tactics

Import: `import ComputationalPaths.Path.Rewrite.PathTactic`

| Tactic | Use Case |
|--------|----------|
| `path_auto` | Try first for RwEq goals |
| `path_simp` | Simplify using groupoid laws |
| `path_normalize` | Right-associative form |
| `path_rfl` | Close reflexive goals |

## Coding Conventions

### File Structure

```lean
/-
# Module Title
Brief description.
## Key Results
- `theorem1`: Description
-/

import ...

namespace ComputationalPaths
namespace Path

/-! ## Section Name -/

-- Content here

end Path
end ComputationalPaths
```

### Naming Conventions

| Pattern | Example | Use |
|---------|---------|-----|
| `snake_case` | `decode_encode` | Theorems, lemmas |
| `camelCase` | `circleBase` | Definitions |
| `PascalCase` | `FreeGroupWord` | Types, structures |

### Axiom Usage

Avoid new axioms. Prefer computational-path constructions (inductive point types + path-expression syntax) and keep any assumptions local and explicit in signatures.

## Common Patterns

### Encode-Decode Equivalence

```lean
noncomputable def decode : Presentation → π₁(X, base) := ...
noncomputable def encode : π₁(X, base) → Presentation := ...

theorem decode_encode (α : π₁(X, base)) : decode (encode α) = α := by
  induction α using Quot.ind with
  | _ p => exact Quot.sound (decode_encode_path p)

noncomputable def piOneEquiv : SimpleEquiv (π₁(X, base)) Presentation where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode
```

### Working with Quotients

```lean
def myFun : QuotType → Result :=
  Quot.lift
    (fun x => ...)  -- function on representatives
    (fun _ _ h => ...) -- proof it respects the relation
```

## Common Pitfalls

1. **Don't use `Quot.liftOn₂`** - it doesn't exist in Lean 4; use nested `Quot.lift`
2. **RwEq lemma names**: Use `rweq_cmpA_*` not `rweq_trans_*` for unit/inverse laws
3. **Universe levels**: Prefer `Type u` for new inductive types; be consistent
4. **Noncomputable**: Encode/decode and quotient lifts often need `noncomputable`
5. **Fin' vs Fin**: This codebase uses custom `Fin'` type, not Mathlib's `Fin`

## Key Theorems

| Module | Theorem | Statement |
|--------|---------|-----------|
| `CircleStep.lean` | `circlePiOneEquivInt` | π₁(S¹) ≃ ℤ |
| `TorusStep.lean` | `torusPiOneEquivIntProd` | π₁(T²) ≃ ℤ × ℤ |
| `FigureEight.lean` | `figureEightPiOneEquiv` | π₁(S¹ ∨ S¹) ≃ ℤ * ℤ |
| `OmegaGroupoid.lean` | `compPathOmegaGroupoid` | Types are weak ω-groupoids |

## References

- de Queiroz et al., *Propositional equality, identity types, and direct computational paths*, SAJL 2016
- HoTT Book, Chapters 2 and 8
