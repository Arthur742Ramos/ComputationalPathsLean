---
name: rweq-proofs
description: Helps construct RwEq (rewrite equivalence) proofs using transitivity, congruence, and canonical lemmas from the LND_EQ-TRS system. Use when proving path equalities, working with quotients, or establishing rewrite equivalences in the ComputationalPaths library.
allowed-tools: Read, Grep, Glob
---

# RwEq Proof Construction

This skill assists with constructing proofs of rewrite equivalence (`RwEq`) in the ComputationalPaths library. RwEq is the symmetric-transitive closure of the multi-step rewrite relation (`Rw`), which itself is the reflexive-transitive closure of single-step rewrites (`Step`).

## The Rewrite Hierarchy

```
Step p q    -- Single rewrite step (one rule application)
    ↓
Rw p q      -- Multi-step rewrite (reflexive-transitive closure)
    ↓
RwEq p q    -- Rewrite equivalence (symmetric-transitive closure)
```

## Core RwEq Lemmas

### Equivalence Properties

```lean
rweq_refl : RwEq p p
rweq_symm : RwEq p q → RwEq q p
rweq_trans : RwEq p q → RwEq q r → RwEq p r
```

### Unit Laws (Composition with refl)

```lean
rweq_cmpA_refl_left : RwEq (trans refl p) p
rweq_cmpA_refl_right : RwEq (trans p refl) p
```

### Inverse Laws

```lean
rweq_cmpA_inv_left : RwEq (trans (symm p) p) refl
rweq_cmpA_inv_right : RwEq (trans p (symm p)) refl
```

### Associativity

```lean
rweq_tt : RwEq (trans (trans p q) r) (trans p (trans q r))
rweq_tt_symm : RwEq (trans p (trans q r)) (trans (trans p q) r)  -- via rweq_symm
```

### Congruence (Composition)

```lean
rweq_trans_congr_left : RwEq q₁ q₂ → RwEq (trans p q₁) (trans p q₂)
rweq_trans_congr_right : RwEq p₁ p₂ → RwEq (trans p₁ q) (trans p₂ q)
rweq_trans_congr : RwEq p₁ p₂ → RwEq q₁ q₂ → RwEq (trans p₁ q₁) (trans p₂ q₂)
```

### Symmetry Congruence

```lean
rweq_symm_congr : RwEq p q → RwEq (symm p) (symm q)
rweq_symm_symm : RwEq (symm (symm p)) p
rweq_symm_refl : RwEq (symm refl) refl
rweq_symm_trans : RwEq (symm (trans p q)) (trans (symm q) (symm p))
```

### CongrArg Congruence

```lean
rweq_congrArg_of_rweq : RwEq p q → RwEq (congrArg f p) (congrArg f q)
rweq_congrArg_refl : RwEq (congrArg f refl) refl
rweq_congrArg_trans : RwEq (congrArg f (trans p q)) (trans (congrArg f p) (congrArg f q))
rweq_congrArg_symm : RwEq (congrArg f (symm p)) (symm (congrArg f p))
```

### Transport Rules

```lean
rweq_transport_refl : RwEq (transport P refl x) x  -- (as paths in P a)
```

## Proof Strategies

### Strategy 1: Direct Transitivity Chain

For simple proofs, chain lemmas with `rweq_trans`:

```lean
theorem my_proof : RwEq p q := by
  apply rweq_trans h₁
  apply rweq_trans h₂
  exact h₃
```

### Strategy 2: Calc Block (Preferred for Clarity)

Use `calc` with the `≈` notation for RwEq:

```lean
theorem my_proof : RwEq p q := by
  calc p
    _ ≈ p' := rweq_cmpA_refl_left
    _ ≈ p'' := rweq_trans_congr_right h
    _ ≈ q := rweq_symm rweq_tt
```

### Strategy 3: Working from Both Ends

When the goal has symmetric structure, work from both sides:

```lean
theorem my_proof : RwEq (trans (trans a b) c) (trans a (trans b c)) := by
  -- Forward direction uses rweq_tt
  exact rweq_tt
```

### Strategy 4: Congruence for Subterms

When paths differ only in subterms:

```lean
-- Goal: RwEq (trans p₁ q) (trans p₂ q)
-- Use: rweq_trans_congr_right (h : RwEq p₁ p₂)

theorem my_proof (h : RwEq p₁ p₂) : RwEq (trans p₁ q) (trans p₂ q) :=
  rweq_trans_congr_right h
```

### Strategy 5: Nested Congruence

For deeply nested paths, apply congruence lemmas repeatedly:

```lean
-- Goal: RwEq (trans (trans (symm a) b) c) (trans (trans (symm a') b) c)
-- Given: RwEq a a'
theorem my_proof (h : RwEq a a') : RwEq (trans (trans (symm a) b) c) (trans (trans (symm a') b) c) := by
  apply rweq_trans_congr_right
  apply rweq_trans_congr_right
  exact rweq_symm_congr h
```

## Common Proof Patterns

### Proving decode_respects_rel

When proving that decode respects a group relation:

```lean
theorem decode_respects_rel : Rel w₁ w₂ → RwEq (wordToLoop w₁) (wordToLoop w₂) := by
  intro h
  induction h with
  | inv_left => exact rweq_cmpA_inv_left
  | inv_right => exact rweq_cmpA_inv_right
  | mul_assoc => exact rweq_tt
  | mul_id_left => exact rweq_cmpA_refl_left
  | mul_id_right => exact rweq_cmpA_refl_right
  -- etc.
```

### Proving Quotient Equality

To show `Quot.mk r x = Quot.mk r y`:

```lean
theorem quot_eq : Quot.mk RwEq p = Quot.mk RwEq q :=
  Quot.sound my_rweq_proof
```

### Normalizing Complex Paths

To simplify `trans (trans (trans refl p) refl) refl`:

```lean
theorem normalize : RwEq (trans (trans (trans refl p) refl) refl) p := by
  calc trans (trans (trans refl p) refl) refl
    _ ≈ trans (trans p refl) refl := rweq_trans_congr_right (rweq_trans_congr_right rweq_cmpA_refl_left)
    _ ≈ trans p refl := rweq_trans_congr_right rweq_cmpA_refl_right
    _ ≈ p := rweq_cmpA_refl_right
```

## The LND_EQ-TRS Rules

The rewrite system includes 40+ rules organized into categories:

| Category | Example Rules |
|----------|---------------|
| Unit laws | `trans refl p → p`, `trans p refl → p` |
| Inverse laws | `trans (symm p) p → refl`, `trans p (symm p) → refl` |
| Associativity | `trans (trans p q) r ↔ trans p (trans q r)` |
| Symmetry | `symm (symm p) → p`, `symm refl → refl` |
| CongrArg | `congrArg f refl → refl`, distributivity |
| Transport | `transport P refl x → x` |
| Horizontal comp | 2-cell composition rules |

## Debugging RwEq Proofs

1. **Check term structure**: Use `#check` to see the actual path structure
2. **Unfold definitions**: Ensure wordToLoop and similar are unfolded
3. **Try both directions**: If `rweq_tt` doesn't work, try `rweq_symm rweq_tt`
4. **Break into smaller steps**: Use intermediate `have` statements

```lean
theorem debug_proof : RwEq p q := by
  have h1 : RwEq p p' := sorry
  have h2 : RwEq p' q := sorry
  exact rweq_trans h1 h2
```

## Quick Reference

| Goal Shape | Likely Lemma |
|------------|--------------|
| `RwEq (trans refl p) p` | `rweq_cmpA_refl_left` |
| `RwEq (trans p refl) p` | `rweq_cmpA_refl_right` |
| `RwEq (trans (symm p) p) refl` | `rweq_cmpA_inv_left` |
| `RwEq (trans p (symm p)) refl` | `rweq_cmpA_inv_right` |
| `RwEq (trans (trans p q) r) _` | `rweq_tt` or `rweq_tt_symm` |
| `RwEq (symm (symm p)) p` | `rweq_symm_symm` |
| `RwEq (congrArg f refl) refl` | `rweq_congrArg_refl` |
| `RwEq (trans p _) (trans p _)` | `rweq_trans_congr_left` |
| `RwEq (trans _ q) (trans _ q)` | `rweq_trans_congr_right` |
