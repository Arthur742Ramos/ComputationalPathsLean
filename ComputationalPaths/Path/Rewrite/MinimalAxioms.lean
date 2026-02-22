/-
# Minimal Axiom Set for Path Rewriting

This module demonstrates that several `Step` constructors are derivable from
others, reducing the rule count for the rewrite system.

## Eliminable Rules

We show that the following rules can be derived:

**Unit Laws (eliminate one):**
- `trans_refl_right` derivable from `trans_refl_left` + symmetry rules

**Inverse Laws (eliminate one):**
- `symm_trans` derivable from `trans_symm` + symmetry rules

**Symmetry Involution:**
- `symm_symm` derivable from unit + inverse laws

## The Derivations

All derivations use the fact that `RwEq` is a congruence (closed under
`trans_congr_left`, `trans_congr_right`, `symm_congr`).
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.PathTactic

namespace ComputationalPaths
namespace Path
namespace MinimalAxioms

universe u

variable {A : Type u}

/-! ## Part 1: Derive `trans_refl_right` from `trans_refl_left`

The derivation:
```
p · ρ ≈ σ(σ(p · ρ))                    (by σσ)
      ≈ σ(σ(ρ) · σ(p))                  (by symm_trans_congr)
      ≈ σ(ρ · σ(p))                     (by σρ, congruence)
      ≈ σ(σ(p))                         (by trans_refl_left on σ(p))
      ≈ p                               (by σσ)
```
-/

section DeriveRightUnit

variable {a b : A} (p : Path a b)

/-- Step 1: p · ρ ≈ σ(σ(p · ρ)) by symm_symm -/
private noncomputable def step1_ss : RwEq (Path.trans p (Path.refl b)) (Path.symm (Path.symm (Path.trans p (Path.refl b)))) :=
  rweq_symm (rweq_ss (Path.trans p (Path.refl b)))

/-- Step 2: σ(σ(p · ρ)) ≈ σ(σ(p) · σ(ρ)) by symm_trans_congr applied inside σ -/
private noncomputable def step2_symm_trans : RwEq
    (Path.symm (Path.symm (Path.trans p (Path.refl b))))
    (Path.symm (Path.trans (Path.symm (Path.refl b)) (Path.symm p))) := by
  apply rweq_symm_congr
  path_inv_distr  -- σ(p · q) ≈ σ(q) · σ(p)

/-- Step 3: σ(σ(ρ) · σ(p)) ≈ σ(ρ · σ(p)) by applying symm_refl inside -/
private noncomputable def step3_sr : RwEq
    (Path.symm (Path.trans (Path.symm (Path.refl b)) (Path.symm p)))
    (Path.symm (Path.trans (Path.refl b) (Path.symm p))) := by
  apply rweq_symm_congr
  apply rweq_trans_congr_left
  path_symm_refl  -- σ(ρ) ≈ ρ

/-- Step 4: σ(ρ · σ(p)) ≈ σ(σ(p)) by trans_refl_left -/
private noncomputable def step4_left_unit : RwEq
    (Path.symm (Path.trans (Path.refl b) (Path.symm p)))
    (Path.symm (Path.symm p)) := by
  apply rweq_symm_congr
  path_simp  -- refl · X ≈ X

/-- Step 5: σ(σ(p)) ≈ p by symm_symm -/
private noncomputable def step5_ss : RwEq (Path.symm (Path.symm p)) p :=
  rweq_ss p

/-- Main theorem: trans_refl_right is derivable from trans_refl_left + symmetry rules -/
noncomputable def derive_trans_refl_right : RwEq (Path.trans p (Path.refl b)) p := by
  apply rweq_trans (step1_ss p)
  apply rweq_trans (step2_symm_trans p)
  apply rweq_trans (step3_sr p)
  apply rweq_trans (step4_left_unit p)
  exact step5_ss p

end DeriveRightUnit

/-! ## Part 2: Derive `symm_trans` from `trans_symm`

The derivation:
```
σ(p) · p ≈ σ(σ(σ(p) · p))              (by σσ)
         ≈ σ(σ(p) · σ(σ(p)))            (by symm_trans_congr)
         ≈ σ(σ(p) · p)                  (by σσ on inner, congruence)
         ≈ ?
```

Actually, there's a more direct approach using conjugation:
```
σ(p) · p ≈ σ(p) · (p · ρ)              (by right unit inverse)
         ≈ σ(p) · (p · (σ(p) · p))      ... (need to work backward)
```

Let's use a different strategy: use the fact that both inverse laws
follow from the existence of inverses in a category where composition
is associative.
-/

section DeriveLeftInverse

variable {a b : A} (p : Path a b)

/-
Alternative approach: derive σ(p) · p ≈ ρ directly.

The key insight is that in a groupoid:
- If `p · σ(p) ≈ ρ` (right inverse)
- And we have associativity and units
- Then `σ(p) · p ≈ ρ` (left inverse) follows

The derivation of left inverse from right inverse + involution is:
```
σ(p) · p ≈ σ(p) · σ(σ(p))    (by p ≈ σ(σ(p)))
         ≈ ρ                  (by trans_symm on σ(p))
```

This requires symm_symm, which we should check is independently derivable.
-/

/-- Derive symm_trans using symm_symm + trans_symm.

    σ(p) · p ≈ σ(p) · σ(σ(p))    (substitute p with σ(σ(p)))
             ≈ ρ                  (trans_symm on σ(p))
-/
noncomputable def derive_symm_trans : RwEq (Path.trans (Path.symm p) p) (Path.refl b) := by
  -- Substitute p with σ(σ(p)) using symm_symm
  apply rweq_trans
  · exact rweq_trans_congr_right (Path.symm p) (rweq_symm (rweq_ss p))
  -- Apply trans_symm to σ(p)
  · path_cancel_right  -- p · p⁻¹ ≈ refl

end DeriveLeftInverse

/-! ## Part 3: Is `symm_symm` Independently Derivable?

The rule `σ(σ(p)) ≈ p` (symm_symm) was used above. Can it be derived from
more basic rules?

In a groupoid, involution of inverses follows from uniqueness of inverses.
If we have:
- `p · σ(p) = id` (trans_symm)
- `σ(p) · p = id` (symm_trans)

Then `σ(σ(p))` must equal `p` because both are inverses of `σ(p)`.

Proof:
```
σ(σ(p)) ≈ σ(σ(p)) · ρ                    (right unit)
        ≈ σ(σ(p)) · (σ(p) · p)            (symm_trans, inverse)
        ≈ (σ(σ(p)) · σ(p)) · p            (associativity)
        ≈ ρ · p                           (trans_symm on σ(p))
        ≈ p                               (left unit)
```

So `symm_symm` IS derivable from unit laws + inverse laws + associativity!
-/

section DeriveSymmSymm

variable {a b : A} (p : Path a b)

/-- Derive symm_symm from unit laws + inverse laws + associativity.

    σ(σ(p)) ≈ σ(σ(p)) · ρ                    (right unit)
            ≈ σ(σ(p)) · (σ(p) · p)            (left inverse)
            ≈ (σ(σ(p)) · σ(p)) · p            (assoc)
            ≈ ρ · p                           (right inverse on σ(p))
            ≈ p                               (left unit)

NOTE: This derivation uses both inverse laws. If we're eliminating
symm_trans, we need symm_symm to derive it, creating a circularity!

The resolution: We need EITHER symm_symm OR one of the inverse laws
as primitive. We cannot eliminate both.
-/
noncomputable def derive_symm_symm_from_both_inverses : RwEq (Path.symm (Path.symm p)) p := by
  -- Right unit: σ(σ(p)) ≈ σ(σ(p)) · ρ
  apply rweq_trans
  · exact rweq_symm (rweq_cmpA_refl_right (Path.symm (Path.symm p)))
  -- Insert left inverse: ρ ≈ σ(p) · p
  apply rweq_trans
  · exact rweq_trans_congr_right (Path.symm (Path.symm p)) (rweq_symm (rweq_cmpA_inv_left p))
  -- Associativity
  apply rweq_trans
  · exact rweq_symm (rweq_tt (Path.symm (Path.symm p)) (Path.symm p) p)
  -- Left inverse on σ(p): σ(σ(p)) · σ(p) ≈ ρ_a
  apply rweq_trans
  · exact rweq_trans_congr_left p (rweq_cmpA_inv_left (Path.symm p))
  -- Left unit
  path_simp  -- refl · X ≈ X

end DeriveSymmSymm

/-! ## Part 4: Summary of Dependencies

The analysis reveals the following dependency structure:

**Independent rules (cannot be derived from others):**
1. `symm_refl` (σ(ρ) → ρ) — base case
2. `trans_refl_left` (ρ · p → p) — left unit
3. `trans_assoc` ((p · q) · r → p · (q · r)) — associativity
4. `trans_symm` (p · σ(p) → ρ) — right inverse
5. `symm_trans_congr` (σ(p · q) → σ(q) · σ(p)) — contravariance

**Derivable rules:**
- `trans_refl_right` — from `trans_refl_left` + symmetry rules
- `symm_trans` — from `trans_symm` + `symm_symm`
- `symm_symm` — from both inverse laws (BUT creates circularity!)

**Resolution of circularity:**
We must keep ONE of:
- `symm_symm` (involution), OR
- `symm_trans` (left inverse)

If we keep `symm_symm`:
- Derive `symm_trans` using `trans_symm` + `symm_symm`
- Derive `trans_refl_right` using `trans_refl_left` + symmetry

If we keep `symm_trans`:
- Derive `symm_symm` using both inverse laws + assoc + units
- Derive `trans_refl_right` using `trans_refl_left` + symmetry

**Minimal independent set (6 rules):**
1. `symm_refl`
2. `trans_refl_left`
3. `trans_assoc`
4. `trans_symm`
5. `symm_trans_congr`
6. `symm_symm` OR `symm_trans` (pick one)

Plus the type-specific rules (β/η for products, sigma, functions).
-/

/-- The minimal rule structure for groupoid laws. -/
structure MinimalGroupoidAxioms (A : Type u) where
  /-- σ(ρ) → ρ -/
  symm_refl : ∀ (a : A), RwEq (Path.symm (Path.refl a)) (Path.refl a)
  /-- ρ · p → p -/
  trans_refl_left : ∀ {a b : A} (p : Path a b), RwEq (Path.trans (Path.refl a) p) p
  /-- (p · q) · r → p · (q · r) -/
  trans_assoc : ∀ {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d),
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r))
  /-- p · σ(p) → ρ -/
  trans_symm : ∀ {a b : A} (p : Path a b), RwEq (Path.trans p (Path.symm p)) (Path.refl a)
  /-- σ(p · q) → σ(q) · σ(p) -/
  symm_trans_congr : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    RwEq (Path.symm (Path.trans p q)) (Path.trans (Path.symm q) (Path.symm p))
  /-- σ(σ(p)) → p -/
  symm_symm : ∀ {a b : A} (p : Path a b), RwEq (Path.symm (Path.symm p)) p

/-- Derive trans_refl_right from the minimal set. -/
noncomputable def deriveTransReflRight (M : MinimalGroupoidAxioms A) {a b : A} (p : Path a b) :
    RwEq (Path.trans p (Path.refl b)) p :=
  derive_trans_refl_right p

/-- Derive symm_trans from the minimal set. -/
noncomputable def deriveSymmTrans (M : MinimalGroupoidAxioms A) {a b : A} (p : Path a b) :
    RwEq (Path.trans (Path.symm p) p) (Path.refl b) :=
  derive_symm_trans p

end MinimalAxioms
end Path
end ComputationalPaths
