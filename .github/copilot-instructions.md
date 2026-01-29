# GitHub Copilot Instructions for ComputationalPaths

> **TL;DR**: Lean 4 formalization proving that propositional equality can be modeled as computational paths forming a term rewriting system (LND_EQ-TRS). Key results: π₁(S¹)≃ℤ, π₁(T²)≃ℤ×ℤ, types are weak ω-groupoids.

## ⚡ Critical Facts (Read First)

| Aspect | Details |
|--------|---------|
| **Language** | Lean 4 (Lake build system) |
| **Core Insight** | Identity types = explicit syntactic paths + rewrite equivalence |
| **Main Purpose** | Prove fundamental group calculations via encode-decode |
| **Build** | `lake build` (clean: `lake clean`) |
| **Test a module** | `lake build ComputationalPaths.Path.CompPath.CircleStep` |

## Why This Architecture Exists

### The Core Idea: Paths as Syntax, Not Black Boxes

Unlike Lean's built-in `Eq` which is opaque, this library makes equality **explicit syntactic objects**:

```lean
-- Standard Lean: equality is abstract
#check @Eq.refl  -- ∀ a, a = a (you can't inspect why)

-- Computational Paths: equality is concrete syntax
inductive Path : A → A → Type where
  | refl : (a : A) → Path a a
  | symm : Path a b → Path b a
  | trans : Path a b → Path b c → Path a c
  | congrArg : (f : A → B) → Path a a' → Path (f a) (f a')
```

**Why?** Because explicit paths let us:
1. **Normalize** paths to canonical forms via term rewriting
2. **Quotient** by rewrite equivalence to get a computable equality
3. **Calculate** π₁ by encoding loops as algebraic objects

### The Rewrite Hierarchy

```
Path p q       -- Raw syntactic paths (many paths between same endpoints)
    ↓ Step
Rw p q         -- Multi-step rewrite (reflexive-transitive closure)
    ↓
RwEq p q       -- Rewrite equivalence (also symmetric) - THIS IS THE KEY TYPE
    ↓ Quot.mk
PathRwQuot     -- Quotient = "paths up to RwEq"
```

**Design Rationale**: We DON'T quotient immediately. The unquotiented `Path` type lets us write simple inductive proofs, then lift through quotients only when needed.

## Key Types

| Type | Description | When to Use |
|------|-------------|-------------|
| `Path a b` | Computational path from `a` to `b` | Raw syntactic equality |
| `RwEq p q` | Rewrite equivalence (the `≈` notation) | Proving paths are "the same" |
| `π₁(A, a)` | Fundamental group (loops up to RwEq) | Final quotient for group calcs |
| `SimpleEquiv α β` | Lightweight equivalence | Avoid Mathlib dependency |

### RwEq Lemmas You'll Use Constantly

```lean
-- Unit laws (cmpA = component-associativity, historic name)
rweq_cmpA_refl_left  : trans refl p ≈ p
rweq_cmpA_refl_right : trans p refl ≈ p

-- Inverse laws
rweq_cmpA_inv_left  : trans (symm p) p ≈ refl
rweq_cmpA_inv_right : trans p (symm p) ≈ refl

-- Associativity
rweq_tt : trans (trans p q) r ≈ trans p (trans q r)

-- Congruence (essential for substitution)
rweq_trans_congr_left  : q₁ ≈ q₂ → trans p q₁ ≈ trans p q₂
rweq_trans_congr_right : p₁ ≈ p₂ → trans p₁ q ≈ trans p₂ q
```

⚠️ **GOTCHA**: The lemma names use `cmpA` prefix (from the papers), NOT `trans_unit` or similar.

## Path Tactics

Import: `import ComputationalPaths.Path.Rewrite.PathTactic`

| Tactic | What It Does | When to Use |
|--------|--------------|-------------|
| `path_auto` | Full automation (~25 simp lemmas) | **Try first** for any RwEq goal |
| `path_simp` | Just the groupoid laws | Base cases in induction |
| `path_rfl` | Close `p ≈ p` goals | Trivial reflexive goals |
| `path_normalize` | Right-associate all `trans` | Before structural comparison |

**Workflow**: `path_auto` → if it fails → manual lemmas → `path_simp` for cleanup

⚠️ **Multi-argument syntax**: Use commas! `path_congr h1, h2` NOT `path_congr h1 h2`

## The Encode-Decode Pattern (Most Common Task)

Every π₁ calculation follows this template:

```lean
-- 1. Define your group presentation type
inductive CircleWord where
  | zero | succ : CircleWord → CircleWord | pred : CircleWord → CircleWord

-- 2. Quotient by the group relations
def CircleGroup := Quot (fun a b => ... relation ...)

-- 3. decode: presentation → π₁ (turn integers into loops)
noncomputable def decode : CircleGroup → π₁(Circle, base) := ...

-- 4. encode: π₁ → presentation (count winding number)
-- This is the hard part - must respect RwEq!
def encodePath : Path base base → CircleWord := ...
theorem encodePath_respects_rweq : p ≈ q → Rel (encodePath p) (encodePath q)

noncomputable def encode : π₁(Circle, base) → CircleGroup :=
  Quot.lift (fun p => Quot.mk _ (encodePath p))
    (fun _ _ h => Quot.sound (encodePath_respects_rweq h))

-- 5. Round-trip proofs
theorem decode_encode : decode (encode α) = α  -- Usually by Quot.ind
theorem encode_decode : encode (decode x) = x  -- By induction on presentation
```

**Why `noncomputable`?** Quotient operations often need Classical.choice internally.

## ⚠️ Common Pitfalls

### 1. Quot.liftOn₂ Doesn't Exist
```lean
-- WRONG: This function doesn't exist in Lean 4
Quot.liftOn₂ q1 q2 f ...

-- RIGHT: Nest Quot.lift calls
Quot.lift (fun a => Quot.lift (fun b => f a b) ...) ...
```

### 2. Wrong Lemma Names for Unit/Inverse Laws
```lean
-- WRONG: Searching for these will fail
rweq_trans_refl_left   -- doesn't exist
rweq_unit_left         -- doesn't exist

-- RIGHT: Use the cmpA prefix
rweq_cmpA_refl_left
rweq_cmpA_inv_right
```

### 3. Fin' vs Fin
This codebase uses a **custom `Fin'` type**, not Mathlib's `Fin`. They are NOT interchangeable.

### 4. Quotient Direction
`Quot.sound` requires the relation in a specific direction. Check the relation definition:
```lean
-- If your relation is: Rel a b means "a reduces to b"
-- Then: Quot.sound : Rel a b → Quot.mk r a = Quot.mk r b
```

### 5. Universe Consistency
```lean
-- WRONG: Mixing universe levels
inductive MyType : Type where ...  -- implicit Type 0

-- RIGHT: Be explicit and consistent
inductive MyType : Type u where ...
```

### 6. Import Order Matters
```lean
-- Core definitions
import ComputationalPaths.Path.Basic.Core      -- Path type
import ComputationalPaths.Path.Rewrite.RwEq    -- RwEq type

-- Tactics (must come after)
import ComputationalPaths.Path.Rewrite.PathTactic

-- CompPath constructions
import ComputationalPaths.Path.CompPath.CircleCompPath
```

## File Structure Convention

```lean
/-
# Module Title

Brief description of what this module proves.

## Key Results
- `mainTheorem`: What it states

## Mathematical Background
Why this construction matters.

## References
- de Queiroz et al., SAJL 2016
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path

/-! ## Section Name -/

-- All code in namespace
-- snake_case for theorems: `decode_encode`
-- camelCase for definitions: `circleBase`
-- PascalCase for types: `FreeGroupWord`

end ComputationalPaths.Path
```

## Key Theorems (The Main Results)

| File | Theorem | Mathematical Statement |
|------|---------|----------------------|
| `CircleStep.lean` | `circlePiOneEquivInt` | π₁(S¹) ≃ ℤ |
| `TorusStep.lean` | `torusPiOneEquivIntProd` | π₁(T²) ≃ ℤ × ℤ |
| `FigureEight.lean` | `figureEightPiOneEquiv` | π₁(S¹ ∨ S¹) ≃ ℤ * ℤ (free product) |
| `SphereCompPath.lean` | `sphere2_pi1_equiv_unit` | π₁(S²) ≃ 1 (simply connected) |
| `OmegaGroupoid.lean` | `compPathOmegaGroupoid` | Every type is a weak ω-groupoid |
| `PushoutPaths.lean` | `seifertVanKampenEquiv` | π₁(A ∪_C B) ≃ π₁(A) *_{π₁(C)} π₁(B) |

## Axiom Policy

**Avoid new axioms.** The library aims to be constructive where possible.

- ✅ Inductive types for point spaces
- ✅ Path-expression syntax for generators
- ✅ Quotients by explicit relations
- ❌ Classical.choice (only when unavoidable)
- ❌ Univalence (we have lightweight `SimpleEquiv` instead)
- ❌ Arbitrary axioms in signatures

If you must assume something, make it a **Prop-valued typeclass** parameter, not a global axiom.

## Aristotle Integration (Auto-Prover)

For files that don't import axiom modules, you can auto-fill `sorry` placeholders:

```bash
export ARISTOTLE_API_KEY='arstl_...'
uvx --from aristotlelib aristotle.exe prove-from-file "path/to/file.lean"
```

⚠️ **Limitation**: Aristotle rejects files that transitively import any `*Axiom.lean` modules.

## References

- de Queiroz et al., *Propositional equality, identity types, and direct computational paths*, SAJL 2016
- Ramos et al., *On the Identity Type as the Type of Computational Paths*, IGPL 2017
- HoTT Book, Chapters 2 (Homotopy Type Theory) and 8 (π₁ calculations)
- Lumsdaine, *Weak ω-categories from intensional type theory*, TLCA 2009
