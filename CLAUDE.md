# CLAUDE.md - Guide for AI Assistants

This document provides guidance for AI assistants working with the Computational Paths codebase.

## Project Overview

**Computational Paths** is a Lean 4 formalization of propositional equality via explicit computational paths and rewrite equality. It provides:

1. **A rewrite-based equality system**: Paths are explicit witnesses of equality, related by a term rewriting system (LND_EQ-TRS)
2. **Fundamental group calculations**: π₁ of various higher-inductive types (HITs) using encode-decode methods
3. **Higher categorical structures**: Weak ω-groupoid structure on types via computational paths

### Mathematical Foundation

The key insight is that identity types can be modeled as *computational paths* - explicit syntactic witnesses of equality that form a term rewriting system. Two paths are considered equal (RwEq) if they normalize to the same canonical form.

## Architecture

```
ComputationalPaths/
├── Basic.lean                    # Re-exports
├── Path.lean                     # Main import hub
└── Path/
    ├── Basic/                    # Core path definitions
    │   ├── Core.lean             # Path type, refl, symm, trans
    │   ├── Congruence.lean       # congrArg, transport
    │   ├── Context.lean          # Contexts for rewriting
    │   ├── Globular.lean         # Globular identities
    │   ├── UIP.lean              # Path → Eq conversion
    │   └── Univalence.lean       # Lightweight UA for SimpleEquiv
    │
    ├── Rewrite/                  # The rewrite system
    │   ├── Step.lean             # Single-step rewrites (40+ rules)
    │   ├── Rw.lean               # Multi-step rewrite closure
    │   ├── RwEq.lean             # Symmetric-transitive closure
    │   ├── Quot.lean             # PathRwQuot quotient type
    │   ├── SimpleEquiv.lean      # Lightweight equivalence structure
    │   ├── LNDEQ.lean            # Rule enumeration and instantiation
    │   ├── Termination.lean      # Normalization witnesses
    │   └── Confluence.lean       # Critical pair joins
    │
    ├── Homotopy/                 # Homotopy-theoretic structures
    │   ├── Loops.lean            # Loop spaces, LoopSpace type
    │   ├── FundamentalGroup.lean # π₁ definition, group operations
    │   ├── HoTT.lean             # Homotopy lemmas exported to Eq
    │   └── ...
    │
    ├── HIT/                      # Higher-Inductive Types
    │   ├── Circle.lean           # S¹ with π₁(S¹) ≃ ℤ
    │   ├── CircleStep.lean       # Circle encode-decode proofs
    │   ├── Torus.lean            # T² with π₁(T²) ≃ ℤ × ℤ
    │   ├── Sphere.lean           # S² with π₁(S²) ≅ 1
    │   ├── Pushout.lean          # Pushout HIT, wedge sum, suspension
    │   ├── PushoutPaths.lean     # SVK theorem, free products
    │   ├── FigureEight.lean      # S¹ ∨ S¹ with π₁ ≃ ℤ * ℤ
    │   ├── OrientableSurface.lean # Σ_g with surface group π₁
    │   ├── KleinBottle.lean      # K with π₁(K) ≃ ℤ ⋊ ℤ
    │   ├── ProjectivePlane.lean  # RP² with π₁(RP²) ≃ ℤ₂
    │   ├── MobiusBand.lean       # Möbius band, π₁ ≃ ℤ
    │   └── Cylinder.lean         # Cylinder, π₁ ≃ ℤ
    │
    ├── Groupoid.lean             # Weak/strict category & groupoid
    ├── Bicategory.lean           # Weak bicategory, 2-groupoid
    └── OmegaGroupoid.lean        # Weak ω-groupoid structure
```

## Key Types and Concepts

### Core Types

| Type | Description |
|------|-------------|
| `Path a b` | Computational path from `a` to `b` |
| `Step p q` | Single-step rewrite from path `p` to `q` |
| `Rw p q` | Multi-step rewrite (reflexive-transitive closure of Step) |
| `RwEq p q` | Rewrite equivalence (symmetric-transitive closure of Rw) |
| `PathRwQuot A a b` | Quotient of paths by RwEq |
| `π₁(A, a)` | Fundamental group (notation for `LoopQuot A a`) |
| `SimpleEquiv α β` | Lightweight type equivalence |

### Path Constructors

```lean
Path.refl : (a : A) → Path a a
Path.symm : Path a b → Path b a
Path.trans : Path a b → Path b c → Path a c
Path.congrArg : (f : A → B) → Path a a' → Path (f a) (f a')
Path.transport : (P : A → Type) → Path a a' → P a → P a'
```

### RwEq Lemmas (commonly used)

```lean
rweq_symm : RwEq p q → RwEq q p
rweq_trans : RwEq p q → RwEq q r → RwEq p r
rweq_cmpA_refl_left : RwEq (trans refl p) p
rweq_cmpA_refl_right : RwEq (trans p refl) p
rweq_cmpA_inv_left : RwEq (trans (symm p) p) refl
rweq_cmpA_inv_right : RwEq (trans p (symm p)) refl
rweq_tt : RwEq (trans (trans p q) r) (trans p (trans q r))
rweq_trans_congr_left : RwEq q₁ q₂ → RwEq (trans p q₁) (trans p q₂)
rweq_trans_congr_right : RwEq p₁ p₂ → RwEq (trans p₁ q) (trans p₂ q)
rweq_congrArg_of_rweq : RwEq p q → RwEq (congrArg f p) (congrArg f q)
```

## Coding Conventions

### File Structure

Every module should follow this pattern:

```lean
/-
# Module Title

Brief description of what this module does.

## Key Results

- `theorem1`: Description
- `definition1`: Description

## Mathematical Background

Explanation of the mathematical concepts if needed.

## References

- Paper citations
-/

import ...

namespace ComputationalPaths
namespace Path

-- Content organized with section headers:
/-! ## Section Name -/

end Path
end ComputationalPaths
```

### Documentation

1. **Module-level doc comment**: Every file starts with `/-` containing title, description, key results, and references
2. **Section headers**: Use `/-! ## Section Name -/` to organize code
3. **Docstrings**: Every public definition, theorem, and axiom needs a `/-- Description -/` docstring
4. **Summary section**: Complex modules end with a `/-! ## Summary -/` reviewing what was proved

### Naming Conventions

| Pattern | Example | Use |
|---------|---------|-----|
| `snake_case` | `decode_encode` | Theorems, lemmas |
| `camelCase` | `circleBase` | Definitions, axioms |
| `PascalCase` | `FreeGroupWord` | Types, structures |
| `_of_*` | `rweq_of_toEq_eq` | Construction from condition |
| `*_respects_*` | `decode_respects_rel` | Preservation lemmas |
| `*Equiv*` | `piOneEquivPresentation` | Equivalence constructions |

### Axiom Usage

HITs require axioms for:
- The type itself (`axiom Circle : Type u`)
- Point constructors (`axiom circleBase : Circle`)
- Path constructors (`axiom circleLoop : Path circleBase circleBase`)
- Higher path constructors (2-cells, etc.)
- Recursion/elimination principles
- Computation rules (β-rules)

Everything else should be proved from these axioms. Minimize axiom usage.

### Proof Style

1. **Prefer term-mode** for simple proofs
2. **Use tactic mode** with clear structure for complex proofs
3. **Use `calc`** for equational reasoning chains
4. **Avoid `sorry`** - use axioms explicitly if needed
5. **Use `by omega`** for arithmetic goals
6. **Use `Quot.ind`** for quotient induction
7. **Match on `RwEq` constructors** in inductive proofs on relations

### Common Patterns

#### Encode-Decode Equivalence

```lean
-- Define decode (constructive when possible)
noncomputable def decode : Presentation → π₁(X, base) := ...

-- Define encode (often via HIT recursion axiom)
axiom encodePath : Path base base → Word
axiom encodePath_respects_rweq : RwEq p q → Rel (encodePath p) (encodePath q)

noncomputable def encode : π₁(X, base) → Presentation :=
  Quot.lift (fun p => Quot.mk _ (encodePath p))
    (fun _ _ h => Quot.sound (encodePath_respects_rweq h))

-- Prove round-trips
theorem decode_encode (α : π₁(X, base)) : decode (encode α) = α := by
  induction α using Quot.ind with
  | _ p => exact Quot.sound (decode_encode_path p)

theorem encode_decode (x : Presentation) : encode (decode x) = x := by
  induction x using Quot.ind with
  | _ w => exact Quot.sound (encode_decode_word w)

-- Package as SimpleEquiv
noncomputable def piOneEquiv : SimpleEquiv (π₁(X, base)) Presentation where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode
```

#### Proving RwEq Goals

```lean
-- Use transitivity and congruence
theorem my_rweq : RwEq p q := by
  apply rweq_trans (rweq_trans_congr_right a h₁)
  apply rweq_trans _ (rweq_symm (rweq_trans_congr_left b h₂))
  exact rweq_tt ...

-- Or use calc for clarity
theorem my_rweq : RwEq p q := by
  calc p
    _ ≈ p' := h₁
    _ ≈ p'' := h₂
    _ ≈ q := h₃
```

#### Working with Quotients

```lean
-- Lift functions through quotients
def myFun : QuotType → Result :=
  Quot.lift
    (fun x => ...)  -- function on representatives
    (fun _ _ h => ...) -- proof it respects the relation

-- Prove equality in quotients
theorem quot_eq : Quot.mk r x = Quot.mk r y :=
  Quot.sound (relation_proof)
```

## Build Commands

```bash
# Build everything
lake build

# Build specific module
lake build ComputationalPaths.Path.HIT.OrientableSurface

# Run executable (prints version)
lake exe computational_paths

# Clean build artifacts
lake clean
```

## Adding New Content

### Adding a New HIT

1. Create `ComputationalPaths/Path/HIT/NewHIT.lean`
2. Define the type and constructors as axioms
3. Define the recursion principle
4. Define encode/decode functions
5. Prove the round-trip properties
6. Add to imports in `ComputationalPaths/Path.lean`
7. Update `README.md` with the new result

### Adding a New π₁ Calculation

1. Define the group presentation type
2. Define the relation (as an inductive)
3. Create the quotient type
4. Implement `decode`: presentation → π₁(X)
5. Implement `encode`: π₁(X) → presentation (may need axioms)
6. Prove `decode_respects_rel` using RwEq lemmas
7. Prove round-trip properties
8. Package as `SimpleEquiv`

## Key Theorems by Module

| Module | Main Theorem | Statement |
|--------|--------------|-----------|
| `Circle.lean` | `circlePiOneEquivInt` | π₁(S¹) ≃ ℤ |
| `Torus.lean` | `torusPiOneEquivIntProd` | π₁(T²) ≃ ℤ × ℤ |
| `Sphere.lean` | `sphere2_pi1_equiv_unit` | π₁(S²) ≃ 1 |
| `FigureEight.lean` | `figureEightPiOneEquiv` | π₁(S¹ ∨ S¹) ≃ ℤ * ℤ |
| `OrientableSurface.lean` | `piOneEquivPresentation` | π₁(Σ_g) ≃ SurfaceGroup |
| `KleinBottle.lean` | `kleinPiOneEquivIntProd` | π₁(K) ≃ ℤ ⋊ ℤ |
| `ProjectivePlane.lean` | `projectivePiOneEquivZ2` | π₁(RP²) ≃ ℤ₂ |
| `PushoutPaths.lean` | `seifertVanKampenEquiv` | π₁(Pushout) ≃ π₁(A) *_{π₁(C)} π₁(B) |
| `OmegaGroupoid.lean` | `compPathOmegaGroupoid` | Types are weak ω-groupoids |

## Common Pitfalls

1. **Don't use `Quot.liftOn₂`** - it doesn't exist in Lean 4; use nested `Quot.lift`
2. **RwEq lemma names**: Use `rweq_cmpA_*` not `rweq_trans_*` for unit/inverse laws
3. **Universe levels**: HITs are typically `Type u`; be consistent
4. **Noncomputable**: Most definitions involving HITs need `noncomputable`
5. **Quotient equality direction**: `Quot.sound` needs `Setoid.r a b`, check the direction
6. **Fin' vs Fin**: This codebase uses custom `Fin'` type, not Mathlib's `Fin`

## References

### Papers
- de Queiroz, de Oliveira & Ramos, *Propositional equality, identity types, and direct computational paths*, SAJL 2016
- Ramos et al., *On the Identity Type as the Type of Computational Paths*, IGPL 2017
- de Veras et al., *On the Calculation of Fundamental Groups in HoTT by Means of Computational Paths*, 2018
- Lumsdaine, *Weak ω-categories from intensional type theory*, TLCA 2009
- van den Berg & Garner, *Types are weak ω-groupoids*, Proc. LMS 2011

### HoTT Book
- Chapter 2: Homotopy Type Theory
- Chapter 6: Higher Inductive Types
- Chapter 8: Homotopy Theory (π₁ calculations)

## Tips for Claude

1. **Read before editing**: Always `Read` a file before making changes
2. **Check existing patterns**: Look at similar modules (e.g., Circle.lean when adding a new HIT)
3. **Build incrementally**: Build after each significant change
4. **Use the Task tool**: For exploring the codebase, use `subagent_type=Explore`
5. **Document everything**: Follow the docstring conventions strictly
6. **Minimize axioms**: Prove as much as possible from existing axioms
7. **Test edge cases**: For Fin'-indexed things, test genus 0, 1, and ≥2
8. **Keep README updated**: Add new results to the README and highlights
