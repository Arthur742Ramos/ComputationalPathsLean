# Architecture Overview

This document provides a high-level view of the ComputationalPaths library structure.

## Project Statistics

| Metric | Value |
|--------|-------|
| Lean Modules | 96 (in ComputationalPaths/) |
| Lines of Code | ~29,000 |
| Build Jobs | 140 |
| Kernel Axioms | 0 |
| Sorries | 0 |

## Module Dependency Layers

The library is organized in layers, with each layer depending only on layers below it:

```
┌─────────────────────────────────────────────────────────────────────┐
│  Layer 5: Applications & Derived Results                            │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌───────────────┐  │
│  │ LieGroups   │ │ Covering    │ │ Higher      │ │ Abelianization│  │
│  │             │ │ Spaces      │ │ Homotopy    │ │               │  │
│  └─────────────┘ └─────────────┘ └─────────────┘ └───────────────┘  │
└─────────────────────────────────────────────────────────────────────┘
                              ▲
┌─────────────────────────────────────────────────────────────────────┐
│  Layer 4: Space Constructions (CompPath/)                           │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌───────────────┐  │
│  │ Circle      │ │ Torus       │ │ Sphere      │ │ Pushout/SVK   │  │
│  │ π₁(S¹)≃ℤ    │ │ π₁(T²)≃ℤ×ℤ │ │ π₁(S²)≃1   │ │               │  │
│  └─────────────┘ └─────────────┘ └─────────────┘ └───────────────┘  │
│  ┌─────────────┐ ┌─────────────┐                                    │
│  │ FigureEight │ │ BouquetN    │                                    │
│  │ S¹ ∨ S¹    │ │ ∨ⁿS¹        │                                    │
│  └─────────────┘ └─────────────┘                                    │
└─────────────────────────────────────────────────────────────────────┘
                              ▲
┌─────────────────────────────────────────────────────────────────────┐
│  Layer 3: Homotopy Theory & Higher Structures                       │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌───────────────┐  │
│  │ FundGroup   │ │ Fundamental │ │ OmegaGroup  │ │ Truncation    │  │
│  │ π₁(A,a)     │ │ Groupoid    │ │ ω-groupoid  │ │ n-types       │  │
│  └─────────────┘ └─────────────┘ └─────────────┘ └───────────────┘  │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐                    │
│  │ Bicategory  │ │ Fibration   │ │ Suspension  │                    │
│  │ 2-cells     │ │ LES         │ │ Loop Adj.   │                    │
│  └─────────────┘ └─────────────┘ └─────────────┘                    │
└─────────────────────────────────────────────────────────────────────┘
                              ▲
┌─────────────────────────────────────────────────────────────────────┐
│  Layer 2: Rewrite System (LND_EQ-TRS)                               │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌───────────────┐  │
│  │ Step        │ │ Rw          │ │ RwEq        │ │ Quot          │  │
│  │ 47+ rules   │ │ multi-step  │ │ equivalence │ │ quotient      │  │
│  └─────────────┘ └─────────────┘ └─────────────┘ └───────────────┘  │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐                    │
│  │ Confluence  │ │ PathTactic  │ │ Termination │                    │
│  │ Newman      │ │ 29 tactics  │ │             │                    │
│  └─────────────┘ └─────────────┘ └─────────────┘                    │
└─────────────────────────────────────────────────────────────────────┘
                              ▲
┌─────────────────────────────────────────────────────────────────────┐
│  Layer 1: Core Path Infrastructure                                  │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌───────────────┐  │
│  │ Core        │ │ Congruence  │ │ Context     │ │ Globular      │  │
│  │ Path, Step  │ │ congrArg    │ │ substitution│ │ identities    │  │
│  │ refl,symm,  │ │ transport   │ │             │ │               │  │
│  │ trans       │ │ map2        │ │             │ │               │  │
│  └─────────────┘ └─────────────┘ └─────────────┘ └───────────────┘  │
└─────────────────────────────────────────────────────────────────────┘
```

## Core Types

### Path (Layer 1)

```lean
structure Path {A : Type u} (a b : A) where
  steps : List (Step A)   -- Explicit rewrite trace
  proof : a = b           -- Propositional equality
```

Key operations:
- `refl : Path a a` — identity path
- `symm : Path a b → Path b a` — inverse
- `trans : Path a b → Path b c → Path a c` — composition
- `congrArg : (f : A → B) → Path a a' → Path (f a) (f a')` — functoriality

### Step (Layer 2)

47+ primitive rewrite rules organized into categories:
- **Basic path algebra** (Rules 1-8): `symm_refl`, `symm_symm`, `trans_refl_*`, `trans_assoc`
- **Product types** (Rules 9-16): beta/eta for products
- **Sigma types** (Rules 17-22): beta/eta for dependent pairs
- **Sum types** (Rules 23-24): coproduct recursors
- **Function types** (Rules 25-28): beta/eta for functions
- **Transport** (Rules 29-36): transport computation rules
- **Context** (Rules 37-52): substitution rules

### RwEq (Layer 2)

```lean
inductive RwEq : Path a b → Path a b → Prop
  | refl : RwEq p p
  | step : Step p q → RwEq p q
  | symm : RwEq p q → RwEq q p
  | trans : RwEq p q → RwEq q r → RwEq p r
```

The symmetric-transitive closure of the rewrite relation.

### π₁ (Layer 3)

```lean
def LoopQuot (A : Type u) (a : A) := Quot (RwEqSetoid A a a).r
notation "π₁(" A ", " a ")" => LoopQuot A a
```

The fundamental group as loops modulo rewrite equivalence.

## Key Module Categories

### Derived Theorem Modules

Eight modules providing 307+ derived theorems via `rweq_of_step`:

| Module | Uses | Description |
|--------|------|-------------|
| `GroupoidDerived.lean` | 56 | Cancellation, inverse uniqueness |
| `StepDerived.lean` | 59 | Direct rule lifts |
| `CoherenceDerived.lean` | 51 | Pentagon, triangle coherences |
| `PathAlgebraDerived.lean` | 40 | Multi-fold associativity |
| `LoopDerived.lean` | 27 | Loop algebra |
| `BiContextDerived.lean` | 17 | Binary context rules |
| `ProductSigmaDerived.lean` | varies | Product/sigma algebra |
| `TransportDerived.lean` | varies | Transport coherence |

### Space Construction Modules

| Module | Space | Key Result |
|--------|-------|------------|
| `CircleCompPath.lean` | S¹ | Path expressions + loop powers |
| `CircleStep.lean` | S¹ | `π₁(S¹) ≃ ℤ` |
| `Torus.lean` | T² | `T² = S¹ × S¹` |
| `TorusStep.lean` | T² | `π₁(T²) ≃ ℤ × ℤ` |
| `SphereCompPath.lean` | S² | `π₁(S²) ≃ 1` |
| `PushoutCompPath.lean` | Pushout | Construction + eliminators |
| `PushoutPaths.lean` | Pushout | SVK theorem |
| `FigureEight.lean` | S¹ ∨ S¹ | Two generators |
| `BouquetN.lean` | ∨ⁿS¹ | Free group model |

### Higher Structure Modules

| Module | Structure | Description |
|--------|-----------|-------------|
| `Groupoid.lean` | Groupoid | Weak/strict groupoid |
| `Bicategory.lean` | Bicategory | 2-cells, whiskering, interchange |
| `OmegaGroupoid.lean` | ω-Groupoid | Full tower with contractibility |
| `FundamentalGroupoid.lean` | Π₁(A) | Groupoid + functoriality |
| `Truncation.lean` | n-types | IsContr → IsProp → IsSet → IsGroupoid |

## Import Graph (Simplified)

```
ComputationalPaths.lean
    └── Path.lean
        ├── Basic.lean
        │   ├── Core.lean
        │   ├── Congruence.lean
        │   └── Context.lean
        ├── Rewrite.lean
        │   ├── Step.lean
        │   ├── Rw.lean
        │   └── RwEq.lean
        ├── Groupoid.lean
        ├── Bicategory.lean
        ├── OmegaGroupoid.lean
        └── Homotopy/
            ├── FundamentalGroup.lean
            └── FundamentalGroupoid.lean
```

## Design Principles

1. **Axiom-Free**: No kernel axioms; all results from Lean's standard foundation
2. **Constructive**: Explicit witnesses where possible
3. **Modular**: Clear layer separation, minimal imports
4. **Documented**: Module headers, docstrings, summary sections
5. **Tested**: PathTacticExamples.lean provides regression tests

## Build System

```bash
# Build all
lake build

# Run axiom inventory
lake env lean Scripts/AxiomInventory.lean

# Run executable
lake exe computational_paths
```

## References

- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
- Lumsdaine, "Weak ω-categories from intensional type theory"
- van den Berg & Garner, "Types are weak ω-groupoids"
- HoTT Book, Chapters 2 and 8
