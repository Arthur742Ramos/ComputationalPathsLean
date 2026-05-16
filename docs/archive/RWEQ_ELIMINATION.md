# Eliminating `rweq_eq`: From Blanket Axiom to Finite Derivation Type

## Author: Arthur Freitas Ramos
## Date: 2026-02-22
## Status: IN PROGRESS (armada 861)

---

## 1. The Problem

The ω-groupoid structure on computational paths has a **blanket axiom** called
`rweq_eq` in `MetaStep₃` (the 3-cell type):

```lean
| rweq_eq {a b : A} {p q : Path a b} {d₁ d₂ : Derivation₂ p q}
    : MetaStep₃ d₁ d₂
```

This constructor takes **no arguments** — it says that ANY two parallel
`Derivation₂` witnesses are connected by a 3-cell. This makes `Derivation₂`
contractible by fiat, not by proof.

### Why this is unsatisfying

- It's essentially an axiom — no computational content
- It makes the entire 3-cell structure trivial
- Reviewers will (rightly) question whether this is "real math"
- It hides what should be a THEOREM behind an axiom

### Why it can't simply be removed (proven in armada 859)

The free groupoid on a graph with undirected cycles has genuinely distinct
parallel morphisms. The Step graph has cycles (e.g., the associativity diamond).
Two derivations `[e₂]` vs `[e₁, e₃]` are genuinely different reduced words
in the free groupoid. So SOME mechanism for contractibility₃ is needed.

---

## 2. The Solution: Squier's Finite Derivation Type (FDT)

Instead of one blanket axiom, we add **finitely many specific 3-cells** — one
for each critical pair of the Step TRS (term rewriting system). This is exactly
Squier's theory of finite derivation types (1994).

### Key Insight

The Step TRS has **33 critical pairs** (already enumerated in
`CriticalPairs.lean` with joinability proofs). Each critical pair represents
a place where two different Step rules can apply to the same term, producing
different results. The joinability proofs show these results can be brought
back together.

### The Diamond Filler

For each critical pair:
```
        p
       / \
  s₁  /   \  s₂
     /     \
    q       r
     \     /
  j₁  \   /  j₂
       \ /
        m
```

We add a 3-cell that says: the derivation going left-then-down equals the
derivation going right-then-down:

```lean
| diamond_filler {p q r m : Path a b}
    (s₁ : Step p q) (s₂ : Step p r)
    (j₁ : StepStar q m) (j₂ : StepStar r m) :
    MetaStep₃
      (.vcomp (.step s₁) (derivation₂_of_stepstar j₁))
      (.vcomp (.step s₂) (derivation₂_of_stepstar j₂))
```

### Why This Works (Newman's Lemma)

1. **Local confluence**: Every critical pair is joinable (33 diamond fillers)
2. **Termination**: The Step TRS is terminating (complexity measure decreases)
3. **Newman's Lemma**: Local confluence + termination → global confluence
4. **Global confluence → contractibility₃**: Any two derivations can be
   connected by composing finitely many diamond fillers + groupoid laws

### What Stays in MetaStep₃

The existing groupoid law constructors remain:
- `vcomp_refl_left/right` — unit laws
- `vcomp_assoc` — associativity
- `inv_inv` — double inverse
- `vcomp_inv_left/right` — inverse laws
- `inv_vcomp` — inverse distributes
- `step_eq` — Step proof irrelevance
- `pentagon` — pentagon coherence
- `triangle` — triangle coherence
- `interchange` — Eckmann-Hilton
- `whisker_left₃/right₃` — functoriality

What's NEW:
- `diamond_filler` — critical pair 3-cells (replaces `rweq_eq`)
- `step_inv_cancel` / `inv_step_cancel` — step-inverse cancellation

What's REMOVED:
- `rweq_eq` — the blanket axiom

---

## 3. Architecture Overview

### Type Hierarchy

```
Level 0: A (types/elements)
Level 1: Path a b (computational paths — explicit step lists)
Level 2: Derivation₂ p q (rewrite derivations — Type-valued)
         = refl | step | inv | vcomp
Level 3: Derivation₃ d₁ d₂ (meta-derivations — from MetaStep₃)
         = refl | step(MetaStep₃) | inv | vcomp
Level 4+: Contractible (iterated argument)
```

### Key Files

| File | Role |
|------|------|
| `Path/Rewrite/Step.lean` | 78 Step constructors + 33 critical pair joinability proofs |
| `Path/OmegaGroupoid.lean` | Derivation₂, MetaStep₃, Derivation₃ definitions |
| `Path/OmegaGroupoid/TruncationProof.lean` | ThreeCell type, contractibility₃ proof |
| `Path/OmegaGroupoid/Normalizer.lean` | Normal form computation (5 rweq_eq uses) |
| `Path/Rewrite/CriticalPairs.lean` | 33 critical pairs enumerated |
| `Path/OmegaGroupoid/ConfluenceFull.lean` | Full confluence proof (2 rweq_eq uses) |
| `Path/OmegaGroupoid/StepToCanonical.lean` | Step-to-canonical form (3 rweq_eq uses) |

### Current `rweq_eq` Usage (30 occurrences)

| File | Count | Usage Pattern |
|------|-------|---------------|
| TruncationProof.lean | ~20 | ThreeCell construction, contractibility proofs |
| Normalizer.lean | 5 | Normal form uniqueness, reduced loop reflexivity |
| StepToCanonical.lean | 3 | Canonical form construction |
| ConfluenceFull.lean | 2 | Full confluence theorem |

---

## 4. The 33 Critical Pairs

From `Step.lean` (already proved joinable):

### Groupoid Fragment (most important)
1. `trans_assoc` vs `trans_refl_left` — assoc meets left unit
2. `trans_assoc` vs `trans_refl_right` — assoc meets right unit
3. `trans_assoc` vs `trans_symm` — assoc meets right inverse
4. `trans_assoc` vs `symm_trans` — assoc meets left inverse
5. `trans_assoc` vs `trans_assoc` — assoc meets itself (Mac Lane pentagon)
6. `trans_assoc` vs `trans_cancel_left` — assoc meets cancellation
7. `trans_assoc` vs `trans_cancel_right` — assoc meets cancellation
8. `symm_congr` vs `symm_refl` — symm congruence meets symm-refl
9. `symm_congr` vs `symm_symm` — symm congruence meets double-symm
10. `symm_congr` vs `symm_trans_congr` — symm congruence meets distribution
11. `symm_congr` vs `trans_symm` — symm congruence meets inverse
12. `symm_congr` vs `symm_trans` — symm congruence meets inverse
13. `trans_congr_left` vs various — left congruence overlaps
14. `trans_congr_right` vs various — right congruence overlaps

### Type-Specific Fragment
15-33. Product, sigma, sum, function, transport, context critical pairs

---

## 5. Mathematical Justification

### Squier's Theorem (1994)

A finitely presented monoid has solvable word problem if and only if it
admits a finite derivation type — a finite set of 3-cells (homotopy
generators) that make the 2-complex simply connected.

### Application to CompPaths

- The Step TRS is a finite presentation of the path groupoid
- The 33 critical pairs generate all 3-cells needed
- `contractibility₃` becomes a THEOREM, not an axiom
- This is the standard approach in rewriting theory

### References

- Squier, C. (1994). "A finiteness condition for rewriting systems"
- Squier, Otto, Kobayashi (1994). "A finiteness condition for rewriting systems"
- Guiraud, Malbos (2009). "Higher-dimensional categories with finite derivation type"
- Lafont (1995). "A new finiteness condition for monoids presented by complete rewriting systems"

---

## 6. Implementation Status

### Done
- [x] Located MetaStep₃ definition (OmegaGroupoid.lean, line ~180)
- [x] Located all 30 rweq_eq usages across 4 files
- [x] Located 33 critical pairs with joinability proofs (Step.lean)
- [x] Designed diamond_filler constructor
- [x] Mathematical justification (Squier's FDT theory)

### In Progress (armada 861)
- [ ] Add diamond_filler to MetaStep₃
- [ ] Add derivation₂_of_stepstar helper
- [ ] Remove rweq_eq
- [ ] Fix 30 downstream usages
- [ ] Build and verify

### Blocked
- [ ] Paper update (Remark 6.5) — depends on implementation landing

---

## 7. Fallback Plan

If full elimination proves too complex in one pass:

1. **Keep `rweq_eq` but RENAME** to `contractibility₃_axiom`
2. **Add critical pair constructors** alongside it
3. **Document** that `contractibility₃_axiom` is derivable from the critical
   pair constructors + Newman's lemma (mathematical proof, not yet formalized)
4. **Mark as future work** in the paper

This is honest: the axiom is mathematically justified (we know it follows
from the FDT structure), we just haven't mechanized the derivation yet.
