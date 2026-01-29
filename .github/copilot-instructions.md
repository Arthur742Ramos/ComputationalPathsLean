# GitHub Copilot Instructions for ComputationalPaths

> **Lean 4 • Homotopy Type Theory • Term Rewriting**
>
> A formal proof that Martin-Löf's identity types are *computational paths*—explicit syntactic witnesses of equality that form a confluent term rewriting system (LND_EQ-TRS). Key results: π₁(S¹)≃ℤ, π₁(T²)≃ℤ×ℤ, all types are weak ω-groupoids.

## 🧭 Origin Story: Why This Project Exists

**The Problem (2011–2016)**: Homotopy Type Theory (HoTT) showed that identity types have rich structure—they're not just "two things are equal" but carry *paths* between points, paths between paths, and so on infinitely. But HoTT relied on the *univalence axiom*, which is non-constructive and doesn't compute.

**The Insight**: Ruy de Queiroz and collaborators at UFPE (Brazil) asked: *What if we took the path metaphor literally?* Instead of identity being abstract, make it **explicit syntax**—you can *see* the proof term that witnesses `a = b`. These proof terms form a term rewriting system, and two proofs are "the same" when they normalize to the same form.

**The Result**: This library formalizes 20+ years of research (SAJL 2016, IGPL 2017, LSFA 2011) proving that this "computational paths" approach:
1. Gives the same π₁ calculations as classical algebraic topology
2. Requires **zero axioms** beyond Lean's core type theory
3. Makes every type a weak ω-groupoid (Lumsdaine's theorem, computationally!)

**Why Lean 4?** Unlike Coq/Agda HoTT libraries that postulate univalence, we derive structure from *computation*. Lean 4's quotient types + definitional proof irrelevance give us clean quotients without axioms.

## ⚡ Critical Facts (Read First)

| Aspect | Details |
|--------|---------|
| **Language** | **Lean 4** with Lake build system |
| **Mathematical Field** | Homotopy Type Theory (constructive fragment) |
| **Core Insight** | Identity types = explicit syntactic paths + rewrite equivalence |
| **Main Purpose** | Prove fundamental group calculations via encode-decode |
| **Build** | `lake build` (clean: `lake clean`) |
| **Test a module** | `lake build ComputationalPaths.Path.CompPath.CircleStep` |

## 💡 Mathematical Background (Not in the Code)

### Connection to Algebraic Topology

In classical topology, the **fundamental group** π₁(X, x₀) is "loops at x₀ up to homotopy." We prove the *same* groups emerge from pure type theory:

| Space | Classical Result | Our Proof |
|-------|------------------|-----------|
| Circle S¹ | π₁ ≃ ℤ (winding number) | Loops = `loop^n`, encode counts n |
| Torus T² | π₁ ≃ ℤ×ℤ | Two independent generators |
| Sphere S² | π₁ ≃ 1 | Surface relation kills loops |
| Figure-8 | π₁ ≃ F₂ (free group) | No relations between generators |

**Key insight**: The encode-decode method from HoTT (Licata-Shulman 2013) works computationally! We don't need univalence—quotients suffice.

### The ω-Groupoid Connection

A **weak ω-groupoid** is an infinite-dimensional structure where:
- 0-cells are points
- 1-cells are paths between points  
- 2-cells are "paths between paths"
- n-cells are paths between (n-1)-cells
- Composition is associative and unital *up to higher cells*

**Lumsdaine's Theorem (2009)**: Every type in intensional type theory is a weak ω-groupoid. We prove this *computationally* in `OmegaGroupoid.lean`—the groupoid laws hold up to `RwEq`, not just propositionally.

### Why "LND_EQ-TRS"?

The name comes from the papers: **L**abelled **N**atural **D**eduction with **EQ**uality as a **T**erm **R**ewriting **S**ystem. The 47+ rewrite rules in `Step.lean` form a confluent, terminating TRS that normalizes path expressions.

## 🧠 Development Philosophy

### Why Explicit Paths Over Implicit Tactics?

**Design choice**: We *don't* use Lean's built-in `Eq` and `rfl`. Instead:

```lean
-- Standard Lean: equality is abstract
#check @Eq.refl  -- ∀ a, a = a (you can't inspect HOW)

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
4. **Prove** the groupoid laws *computationally*, not axiomatically

**The tradeoff**: More verbose proofs, but every step is inspectable. When `path_auto` fails, you can *see* exactly which rewrite rule is missing.

### Why Avoid Mathlib?

Mathlib provides `Fin`, groupoids, and quotients. We define our own (`Fin'`, `SimpleEquiv`, etc.) because:
1. **Minimal dependencies** = faster builds, clearer foundations
2. **Custom `Fin' n`** is n ∈ {1,...,n} not {0,...,n-1} (matches paper conventions)
3. **`SimpleEquiv`** is just `toFun`/`invFun`/round-trips—no `Equiv.symm` complexity

### The Core Idea: Paths as Syntax, Not Black Boxes

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

## 🎓 Mental Models for Newcomers

### Think of Paths as Proof Terms

In standard Lean, `rfl : a = a` is opaque. Here, think of paths as **explicit proof scripts**:

```
Path.trans (Path.symm (Path.congrArg f p)) (Path.trans q Path.refl)
```

This is a *data structure* you can pattern-match on, rewrite, and normalize.

### RwEq is "Proof Irrelevance for Paths"

Two paths `p q : Path a b` might be syntactically different but represent the "same" equality. `RwEq p q` means they normalize to the same canonical form. Think: "These are the same proof, written differently."

### The Quotient Hierarchy

```
Path a b          -- Many syntactically distinct paths
    ↓ RwEq
PathRwQuot a b    -- Paths up to normalization (≈)
    ↓ (when a = b)
π₁(A, a)          -- Loops at a, up to RwEq (the fundamental group!)
```

### Encode-Decode = "Universal Property"

When proving `π₁(S¹) ≃ ℤ`, think:
- **Encode**: Count winding number (loops → integers)
- **Decode**: Build loop from count (integers → loops)
- **Round-trip**: These are mutual inverses

This is the computational version of "ℤ is the free group on one generator."

## 🚨 Common Newcomer Mistakes

### 1. Trying to Use Lean's `Eq` Instead of `Path`
```lean
-- WRONG: Using built-in equality
theorem foo : a = b := ...

-- RIGHT: Using computational paths
theorem foo : Path a b := ...
```

### 2. Forgetting That Path is a Type, Not a Prop
```lean
-- Paths live in Type, not Prop!
-- This means: different paths between the same points are distinguishable
-- (until you quotient by RwEq)
```

### 3. Expecting `rfl` to Work
```lean
-- WRONG: Lean's rfl doesn't apply
example : Path.refl a = Path.refl a := rfl  -- This works (Lean eq)
example : RwEq p p := rfl  -- WRONG! Use `RwEq.refl` or `path_rfl`
```

### 4. Not Respecting RwEq When Lifting Through Quotients
```lean
-- When defining functions on π₁, you MUST prove they respect RwEq:
def myFun : π₁(X, x) → Result :=
  Quot.lift (fun loop => ...)
    (fun p q h => ...)  -- h : RwEq p q, must show same result
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

### Primary Sources (The Papers Behind This Code)

- **de Queiroz et al., *Propositional equality, identity types, and direct computational paths*, SAJL 2016** — The foundational paper introducing LND_EQ-TRS
- **Ramos et al., *On the Identity Type as the Type of Computational Paths*, IGPL 2017** — Extended treatment with confluence proofs
- **de Queiroz & Gabbay, *Equality in Labelled Deductive Systems*, LSFA 2011** — Early work on labelled deduction

### Background Reading

- **HoTT Book, Chapters 2 and 8** — Homotopy Type Theory foundations and π₁ calculations
- **Lumsdaine, *Weak ω-categories from intensional type theory*, TLCA 2009** — The ω-groupoid structure we formalize
- **Licata & Shulman, *Calculating the Fundamental Group of the Circle*, LICS 2013** — The encode-decode method

### Related Formalizations

- **HoTT-Agda** — Agda formalization using univalence axiom (contrast: we're axiom-free)
- **Cubical Agda** — Computational univalence via cubical type theory (different approach)
- **Lean 4 Mathlib** — We deliberately avoid Mathlib to stay self-contained
