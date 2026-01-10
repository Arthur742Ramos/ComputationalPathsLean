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
    │   ├── TorusGenus1.lean      # Torus via OrientableSurface 1, π₁ ≃ ℤ × ℤ
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

### Path Tactics (in PathTactic.lean)

**Import**: `import ComputationalPaths.Path.Rewrite.PathTactic`

The `path_*` tactics automate RwEq reasoning:

| Tactic | Description | Use Case |
|--------|-------------|----------|
| `path_simp` | Simplify using groupoid laws | Base cases, unit/inverse elimination |
| `path_auto` | Main automation (~25 simp lemmas) | Most standalone RwEq goals |
| `path_rfl` | Close reflexive goals (p ≈ p) | Trivial equality |
| `path_symm` | Apply symmetry | Flip RwEq direction |
| `path_normalize` | Right-associative form | Structural normalization |
| `path_beta` | Product/sigma beta rules | `fst (prodMk p q) ≈ p` |
| `path_eta` | Eta expansion/contraction | `prodMk (fst p) (snd p) ≈ p` |
| `path_congr_left h` | Left congruence for trans | Apply hypothesis on right |
| `path_congr_right h` | Right congruence for trans | Apply hypothesis on left |
| `path_cancel_left` | Left inverse cancellation | `trans (symm p) p ≈ refl` |
| `path_cancel_right` | Right inverse cancellation | `trans p (symm p) ≈ refl` |
| `path_trans_via t` | Transitivity via `t` | Split proof at intermediate |
| `path_congr h1, h2` | Both sides congruence | Multi-argument (comma-separated) |
| `path_congrArg f, h` | congrArg congruence | Multi-argument (comma-separated) |
| `path_chain h1, h2` | Chain two hypotheses | Multi-argument (comma-separated) |
| `path_chain3 h1, h2, h3` | Chain three hypotheses | Multi-argument (comma-separated) |
| `path_chain4 h1, h2, h3, h4` | Chain four hypotheses | Multi-argument (comma-separated) |
| `path_both_eq h1, h2` | Close when both reduce to same | Multi-argument (comma-separated) |
| `path_trans_congr_left h` | Transitivity + left congruence | Transform left of trans |
| `path_trans_congr_right h` | Transitivity + right congruence | Transform right of trans |
| `path_then_cancel_right` | Congruence + right inverse cancel | `trans p (trans q (symm q)) ≈ p` |
| `path_then_cancel_left` | Congruence + left inverse cancel | `trans (trans (symm q) q) p ≈ p` |

#### When to Use Each Tactic

**`path_simp`** - Best for base cases in induction proofs:
```lean
-- Before (verbose):
exact rweq_cmpA_refl_left (iterateLoopPos l n)

-- After (concise):
path_simp  -- refl · X ≈ X
```

**`path_auto`** - Try first for standalone goals, falls back gracefully

**Manual lemmas** - Still needed for complex intermediate steps:
```lean
-- Complex proof still requires explicit lemmas
apply rweq_trans (rweq_tt (loopIter l n) l (Path.symm l))
apply rweq_trans (rweq_trans_congr_right (loopIter l n) (loop_cancel_right l))
path_simp  -- Only the final step simplifies automatically
```

#### The `≈` Notation

The `≈` notation for RwEq is scoped in `ComputationalPaths.Path` and works with calc:
```lean
calc trans (refl a) p
  _ ≈ p := rweq_cmpA_refl_left _
```

#### Test Examples

See `PathTacticExamples.lean` for comprehensive tests of all tactics.

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

## Aristotle Integration (Automated Theorem Proving)

This project supports [Aristotle](https://aristotle.harmonic.fun), an AI-powered theorem prover for Lean 4. Aristotle can automatically fill `sorry` placeholders in your Lean files.

### Quick Start

```bash
# Set API key (add to ~/.bashrc or ~/.zshrc for persistence)
export ARISTOTLE_API_KEY='arstl_YOUR_KEY_HERE'

# Run Aristotle on a file
uvx --from aristotlelib aristotle.exe prove-from-file "path/to/file.lean"
```

### Installation

1. **Install UV** (recommended package manager):
   ```bash
   # See https://github.com/astral-sh/uv for installation
   ```

2. **Set your API key** (get one from https://aristotle.harmonic.fun):
   ```bash
   # Windows (PowerShell)
   $env:ARISTOTLE_API_KEY = "arstl_YOUR_KEY_HERE"

   # Windows (add to profile for persistence)
   # Add to $PROFILE: $env:ARISTOTLE_API_KEY = "arstl_YOUR_KEY_HERE"

   # Linux/Mac (add to ~/.bashrc or ~/.zshrc)
   export ARISTOTLE_API_KEY='arstl_YOUR_KEY_HERE'
   ```

3. **Run Aristotle**:
   ```bash
   uvx --from aristotlelib aristotle.exe prove-from-file <file.lean>
   ```

### CLI Options

```bash
uvx --from aristotlelib aristotle.exe prove-from-file <input_file> [options]

Options:
  --api-key KEY              API key (overrides environment variable)
  --output-file FILE         Output path (default: <input>_aristotle.lean)
  --no-auto-add-imports      Disable automatic import resolution
  --context-files FILE...    Additional context files
  --context-folder DIR       Include all .lean/.md/.txt/.tex from directory
  --no-wait                  Submit job without waiting for completion
  --polling-interval SECS    Check interval (default: 30)
  --informal                 Use natural language input mode
  --silent                   Suppress console output
```

### Usage Examples

```bash
# Basic usage - fill sorries in a file
uvx --from aristotlelib aristotle.exe prove-from-file \
  "ComputationalPaths/Path/MyFile.lean"

# Specify output location
uvx --from aristotlelib aristotle.exe prove-from-file \
  "ComputationalPaths/Path/MyFile.lean" \
  --output-file "ComputationalPaths/Path/MyFile_proved.lean"

# Include additional context
uvx --from aristotlelib aristotle.exe prove-from-file \
  "ComputationalPaths/Path/MyFile.lean" \
  --context-folder "ComputationalPaths/Path/Basic"
```

### Guiding Aristotle with Proof Hints

You can provide natural language hints in docstrings using `PROVIDED SOLUTION`:

```lean
/--
Prove that the composition of three reflexivity paths equals reflexivity.

PROVIDED SOLUTION
Use the fact that trans (refl a) p = p (left unit law) twice.
First simplify trans (trans (refl a) (refl a)) (refl a) to trans (refl a) (refl a),
then simplify again to refl a.
-/
theorem triple_refl_eq_refl : trans (trans (refl a) (refl a)) (refl a) = refl a := by
  sorry
```

### Important: HIT Axiom Limitation

**Aristotle rejects files that import Higher Inductive Type (HIT) axioms.**

When processing imports, Aristotle checks for new axioms. Since this project defines HITs via axioms (Circle, Torus, OrientableSurface, etc.), files that import HIT modules will fail with:

```
Aristotle encountered an error while processing imports for this file.
Error: Axioms were added during init_sorries: ['Circle', 'circleBase', ...]
```

#### Which Files Work with Aristotle

| Module Category | Works? | Reason |
|-----------------|--------|--------|
| `Path/Basic/*` | ✅ Yes | Core definitions, no axioms |
| `Path/Rewrite/*` | ✅ Yes* | Rewrite system (*except ConfluenceConstructiveAxiom) |
| `Path/Groupoid.lean` | ✅ Yes | Category theory, no HITs |
| `Path/Bicategory.lean` | ✅ Yes | 2-category theory |
| `Path/HIT/*` | ❌ No | Defines HIT axioms |
| `Path/Homotopy/*` | ⚠️ Depends | Check if imports HITs |
| Files importing HITs | ❌ No | Transitively imports axioms |

#### Workaround Strategy

1. **Factor out non-HIT code** into separate modules
2. **Use Aristotle** on those modules
3. **Manually prove** theorems that require HIT axioms

Example: If you have a file with both pure path lemmas and HIT-dependent theorems:

```lean
-- File: MyProofs.lean (imports Circle - won't work with Aristotle)
import ComputationalPaths.Path.HIT.Circle

theorem pure_path_lemma : ... := by sorry  -- Could be auto-proved
theorem circle_lemma : ... := by sorry     -- Needs HIT
```

Refactor to:
```lean
-- File: MyPureProofs.lean (works with Aristotle)
import ComputationalPaths.Path.Basic

theorem pure_path_lemma : ... := by sorry  -- Aristotle can fill this

-- File: MyCircleProofs.lean
import ComputationalPaths.Path.HIT.Circle
import MyPureProofs

theorem circle_lemma : ... := by sorry     -- Manual proof
```

### What Aristotle Produces

Aristotle replaces `sorry` with proof tactics. Common outputs:

| Tactic | Meaning |
|--------|---------|
| `exact?` | Search tactic - found matching lemma |
| `grind` | Powerful automation tactic |
| `simp` | Simplification |
| `rfl` | Reflexivity |
| `omega` | Linear arithmetic |

The output includes suggestions in comments:
```lean
theorem foo : ... := by
  exact?
-- info: Try this: exact rfl
```

### Counterexample Detection

Aristotle can disprove false statements. If a theorem is false, Aristotle leaves a comment with the counterexample:

```lean
/-
Aristotle found this block to be false.
Here is a proof of the negation:
theorem false_claim : ... := by
    negate_state;
    -- Proof of negation here
-/
theorem false_claim : ... := by
  sorry
```

### Best Practices

1. **Check file imports first** - Ensure no transitive HIT dependencies
2. **Use `admit` for partial runs** - Replace sorries you don't want filled with `admit`
3. **Provide hints** - Use `PROVIDED SOLUTION` for complex proofs
4. **Build after Aristotle** - Verify the output compiles: `lake build ModuleName`
5. **Review `exact?` suggestions** - Replace with concrete terms for cleaner code

### Troubleshooting

| Issue | Solution |
|-------|----------|
| "Axioms were added" | File imports HITs - factor out non-HIT code |
| "already been declared" | Theorem name conflicts with imported module |
| Timeout | Try `--no-wait` and check status later |
| `exact?` left in output | Run `lake build` to see suggested replacement |

### Version Compatibility

Aristotle runs on fixed versions:
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: `v4.24.0` (commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`)

This project's `lean-toolchain` should be compatible. If you encounter issues, check version alignment.

### Further Resources

- [Aristotle Dashboard](https://aristotle.harmonic.fun/dashboard)
- [Aristotle Documentation](https://aristotle.harmonic.fun/dashboard/docs/overview)

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
| `CircleStep.lean` | `circlePiOneEquivInt` | π₁(S¹) ≃ ℤ |
| `TorusStep.lean` | `torusPiOneEquivIntProd` | π₁(T²) ≃ ℤ × ℤ |
| `Sphere.lean` | `sphere2_pi1_equiv_unit` | π₁(S²) ≃ 1 |
| `FigureEight.lean` | `figureEightPiOneEquiv` | π₁(S¹ ∨ S¹) ≃ ℤ * ℤ |
| `OrientableSurface.lean` | `piOneEquivPresentation` | π₁(Σ_g) ≃ SurfaceGroup |
| `TorusGenus1.lean` | `piOneEquivIntProd` | π₁(OrientableSurface 1) ≃ ℤ × ℤ |
| `KleinBottleStep.lean` | `kleinPiOneEquivIntProd` | π₁(K) ≃ ℤ ⋊ ℤ |
| `ProjectivePlaneStep.lean` | `projectivePiOneEquivZ2` | π₁(RP²) ≃ ℤ₂ |
| `PushoutPaths.lean` | `seifertVanKampenEquiv` | π₁(Pushout) ≃ π₁(A) *_{π₁(C)} π₁(B) |
| `OmegaGroupoid.lean` | `compPathOmegaGroupoid` | Types are weak ω-groupoids |
| `FundamentalGroupoid.lean` | `basepointIsomorphism` | π₁(A, a) ≃ π₁(A, b) via path conjugation |
| `LieGroups.lean` | `SO2.piOneEquivInt` | π₁(SO(2)) ≃ ℤ (via Circle) |

## Common Pitfalls

1. **Don't use `Quot.liftOn₂`** - it doesn't exist in Lean 4; use nested `Quot.lift`
2. **RwEq lemma names**: Use `rweq_cmpA_*` not `rweq_trans_*` for unit/inverse laws
3. **Universe levels**: HITs are typically `Type u`; be consistent
4. **Noncomputable**: Most definitions involving HITs need `noncomputable`
5. **Quotient equality direction**: `Quot.sound` needs `Setoid.r a b`, check the direction
6. **Fin' vs Fin**: This codebase uses custom `Fin'` type, not Mathlib's `Fin`
7. **Multi-argument macro syntax**: In Lean 4, tactic macros with multiple term arguments need comma separators (e.g., `path_congr h1, h2` not `path_congr h1 h2`). Without commas, Lean parses `h1 h2` as function application.

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

## Continuity Ledger (Compaction-Safe Sessions)

For long-running sessions that may exceed context limits, maintain a **Continuity Ledger** in `CONTINUITY.md`. This ensures session state survives context compaction.

### How It Works

1. **At the start of every turn**: Read `CONTINUITY.md`, update it to reflect the latest goal/constraints/decisions/state, then proceed with work.

2. **Update the ledger** whenever any of these change:
   - Goal or success criteria
   - Constraints or assumptions
   - Key decisions made
   - Progress state (Done/Now/Next)
   - Important tool outcomes

3. **Keep it short and stable**: Facts only, no transcripts. Use bullets. Mark uncertainty as `UNCONFIRMED` (never guess).

4. **After compaction**: If you notice missing recall or a summary event, refresh the ledger from visible context, mark gaps `UNCONFIRMED`, ask 1-3 targeted questions, then continue.

### Ledger Format

```markdown
# CONTINUITY.md

## Goal
[What we're trying to achieve, including success criteria]

## Constraints/Assumptions
- [Key constraint 1]
- [Assumption 2]

## Key Decisions
- [Decision 1]: [rationale]
- [Decision 2]: [rationale]

## State
- **Done**: [completed items]
- **Now**: [current focus]
- **Next**: [upcoming items]

## Open Questions
- [Question 1] (UNCONFIRMED if uncertain)

## Working Set
- Files: [list of active files]
- Commands: [recent important commands]
```

### Ledger vs TodoWrite

| Tool | Purpose | Scope |
|------|---------|-------|
| `TodoWrite` | Short-term execution scaffolding | 3-7 step task list with pending/in_progress/completed |
| `CONTINUITY.md` | Long-running continuity across compaction | What/why/current state (not micro-steps) |

Keep them consistent: when the plan or state changes, update the ledger at the intent/progress level.

### In Replies

Begin long sessions with a brief **Ledger Snapshot**:
```
**Ledger**: [Goal summary] | Now: [current task] | Next: [upcoming]
```

Print the full ledger only when it materially changes or when requested.

## Tips for Claude

1. **Read before editing**: Always `Read` a file before making changes
2. **Check existing patterns**: Look at similar modules (e.g., Circle.lean when adding a new HIT)
3. **Build incrementally**: Build after each significant change
4. **Use the Task tool**: For exploring the codebase, use `subagent_type=Explore`
5. **Document everything**: Follow the docstring conventions strictly
6. **Minimize axioms**: Prove as much as possible from existing axioms
7. **Test edge cases**: For Fin'-indexed things, test genus 0, 1, and ≥2
8. **Keep README updated**: Add new results to the README and highlights
9. **Use the Continuity Ledger**: For long sessions, maintain `CONTINUITY.md` to survive compaction
10. **Use Aristotle for non-HIT files**: For files that don't import HITs, use Aristotle to auto-fill sorries:
    ```bash
    uvx --from aristotlelib aristotle.exe prove-from-file "path/to/file.lean"
    ```
    See the "Aristotle Integration" section above for details and limitations.
