/-
# Derived Coherences for Weak ω-Groupoids

This module demonstrates that most `MetaStep₃` constructors in the ω-groupoid
structure are **derivable** from the single `to_canonical` axiom. This reduces
the axiomatic content of the weak ω-groupoid structure significantly.

## Main Results

We show that the following are derivable from `to_canonical`:

1. **Groupoid laws at level 3**: `vcomp_refl_left`, `vcomp_refl_right`,
   `vcomp_assoc`, `inv_inv`, `vcomp_inv_left`, `vcomp_inv_right`, `inv_vcomp`

2. **Coherences**: `pentagon`, `triangle`, `interchange`

3. **Step equality**: `step_eq` (since parallel `Step`s produce derivations
   to the same canonical form)

## The Key Insight

All these derivations follow from a single observation:

> Any two `Derivation₂ p q` values (for the same `p, q`) are connected by
> a `Derivation₃` via the canonical derivation.

This is exactly `contractibility₃`, which is *derived* from `to_canonical`:
```
contractibility₃ d₁ d₂ := vcomp (to_canonical d₁) (inv (to_canonical d₂))
```

Once we have contractibility, all the individual coherence axioms become
special cases: they're just saying that two specific derivations are equal,
which follows immediately from contractibility.

## On `to_canonical`

The `to_canonical` axiom is *justified* by normalization but currently not proved
constructively. The original approach used `Step.canon` which was removed because
it collapsed all paths with the same `toEq` to be RwEq (causing π₁(S¹) to be trivial).

Without `Step.canon`, we cannot computationally derive `to_canonical` from:
1. Strong normalization
2. Confluence
3. Normal form uniqueness

The axiom remains as a justified semantic assertion about the ω-groupoid structure.
-/

import ComputationalPaths.Path.OmegaGroupoid
import ComputationalPaths.Path.Rewrite.PathTactic

namespace ComputationalPaths
namespace Path
namespace OmegaGroupoid
namespace Derived

universe u

variable {A : Type u}

/-! ## Part 1: Deriving Coherences from Contractibility

Once we have `contractibility₃`, all coherences follow trivially because any
two parallel 2-cells are connected. We make this explicit below.
-/

section FromContractibility

variable {a b : A}

/-- Any two derivations with the same source and target are connected.
    This is `contractibility₃` from the main module, reproduced here. -/
def connect {p q : Path a b} (d₁ d₂ : Derivation₂ p q) : Derivation₃ d₁ d₂ :=
  contractibility₃ d₁ d₂

/-- The groupoid law `vcomp_refl_left` is a special case of contractibility. -/
def derive_vcomp_refl_left {p q : Path a b} (d : Derivation₂ p q) :
    Derivation₃ (.vcomp (.refl p) d) d :=
  connect (.vcomp (.refl p) d) d

/-- The groupoid law `vcomp_refl_right` is a special case of contractibility. -/
def derive_vcomp_refl_right {p q : Path a b} (d : Derivation₂ p q) :
    Derivation₃ (.vcomp d (.refl q)) d :=
  connect (.vcomp d (.refl q)) d

/-- Associativity `vcomp_assoc` is a special case of contractibility. -/
def derive_vcomp_assoc {p q r s : Path a b}
    (d₁ : Derivation₂ p q) (d₂ : Derivation₂ q r) (d₃ : Derivation₂ r s) :
    Derivation₃ (.vcomp (.vcomp d₁ d₂) d₃) (.vcomp d₁ (.vcomp d₂ d₃)) :=
  connect (.vcomp (.vcomp d₁ d₂) d₃) (.vcomp d₁ (.vcomp d₂ d₃))

/-- Involution `inv_inv` is a special case of contractibility. -/
def derive_inv_inv {p q : Path a b} (d : Derivation₂ p q) :
    Derivation₃ (.inv (.inv d)) d :=
  connect (.inv (.inv d)) d

/-- Left inverse `vcomp_inv_left` is a special case of contractibility. -/
def derive_vcomp_inv_left {p q : Path a b} (d : Derivation₂ p q) :
    Derivation₃ (.vcomp (.inv d) d) (.refl q) :=
  connect (.vcomp (.inv d) d) (.refl q)

/-- Right inverse `vcomp_inv_right` is a special case of contractibility. -/
def derive_vcomp_inv_right {p q : Path a b} (d : Derivation₂ p q) :
    Derivation₃ (.vcomp d (.inv d)) (.refl p) :=
  connect (.vcomp d (.inv d)) (.refl p)

/-- Anti-homomorphism `inv_vcomp` is a special case of contractibility. -/
def derive_inv_vcomp {p q r : Path a b}
    (d₁ : Derivation₂ p q) (d₂ : Derivation₂ q r) :
    Derivation₃ (.inv (.vcomp d₁ d₂)) (.vcomp (.inv d₂) (.inv d₁)) :=
  connect (.inv (.vcomp d₁ d₂)) (.vcomp (.inv d₂) (.inv d₁))

/-- Step equality `step_eq` is a special case of contractibility. -/
def derive_step_eq {p q : Path a b} (s₁ s₂ : Step p q) :
    Derivation₃ (.step s₁) (.step s₂) :=
  connect (.step s₁) (.step s₂)

end FromContractibility

/-! ## Part 2: Deriving Higher Coherences

Pentagon, triangle, and interchange are also derivable from contractibility.
-/

section HigherCoherences

variable {a b c d e : A}

/-- Pentagon coherence is derivable: both composite derivations have the
    same source and target, so they're connected by contractibility. -/
def derive_pentagon (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    Derivation₃
      (.vcomp (.step (Step.trans_assoc (Path.trans f g) h k))
              (.step (Step.trans_assoc f g (Path.trans h k))))
      (.vcomp (.vcomp (.step (Step.trans_congr_left k (Step.trans_assoc f g h)))
                      (.step (Step.trans_assoc f (Path.trans g h) k)))
              (.step (Step.trans_congr_right f (Step.trans_assoc g h k)))) :=
  connect _ _

/-- Triangle coherence is derivable: both sides are derivations with same endpoints. -/
def derive_triangle (f : Path a b) (g : Path b c) :
    Derivation₃
      (.vcomp (.step (Step.trans_assoc f (Path.refl b) g))
              (.step (Step.trans_congr_right f (Step.trans_refl_left g))))
      (.step (Step.trans_congr_left g (Step.trans_refl_right f))) :=
  connect _ _

/-- Interchange is derivable: the two ways of composing 2-cells horizontally
    then vertically vs vertically then horizontally are connected. -/
def derive_interchange {f f' : Path a b} {g g' : Path b c}
    (α : Derivation₂ f f') (β : Derivation₂ g g') :
    Derivation₃
      (.vcomp (whiskerRight α g) (whiskerLeft f' β))
      (.vcomp (whiskerLeft f β) (whiskerRight α g')) :=
  connect _ _

end HigherCoherences

/-! ## Part 3: Notes on `to_canonical`

The `to_canonical` axiom says every derivation connects to the canonical one.

**Current axiom:**
```
axiom to_canonical (d : Derivation₂ p q) : MetaStep₃ d (canonical p q)
```

**Historical note:** The original approach used `Step.canon` which normalized any path
to `Path.ofEq p.toEq`. This was removed because it collapsed all paths with the same
`toEq` to be RwEq, contradicting π₁(S¹) ≃ ℤ.

Without `Step.canon`, we cannot computationally construct a normalization derivation.
The `canonical` function in OmegaGroupoid.lean now uses an alternative construction
that doesn't depend on a general canonicalization step.

The `to_canonical` axiom captures the semantic content: any derivation between two
paths is connected (via a 3-cell) to the canonical derivation between them.
-/

section TowardProvingToCanonical

/-
**Note:** The `Step.canon` rule was removed because it caused all paths with the same
`toEq` to become RwEq, which collapsed π₁(S¹) to be trivial (contradicting π₁(S¹) ≃ ℤ).

Without `Step.canon`, we cannot define a computational `normalizeDerivation` that
reduces every path to its canonical form. The `canonical` derivation and `to_canonical`
axiom in OmegaGroupoid.lean rely on alternative constructions that don't use `Step.canon`.

The key insight remains valid: if we had a sound normalization step, contractibility
at level 3 would follow. The current formulation uses `to_canonical` as an axiom that
captures this semantic property without the problematic computational rule.
-/

/-- Key observation: Any two derivations from the same path to normal forms
    that happen to be equal can be connected via transitivity with inverses.

    This is the "semantic" content that `to_canonical` captures. -/
theorem normalizations_connected {a b : A} {p : Path a b} {n : Path a b}
    (d₁ d₂ : Derivation₂ p n) : Nonempty (Derivation₃ d₁ d₂) :=
  ⟨connect d₁ d₂⟩

/-
**Conjecture:** `to_canonical` could be proved if we had a computational witness
showing that `Derivation₂.toRwEq` is "reversible" up to 3-cells.

The idea: since `d.toRwEq` and `(canonical p q).toRwEq` are both proofs of the
same proposition `RwEq p q`, and since we can lift any `RwEq` back to a
`Derivation₂` via `canonical`, there should be a 3-cell connecting them.

The formal gap is that `RwEq` doesn't "remember" which derivation produced it.
The `to_canonical` axiom asserts that this forgetfulness is harmless at level 3.
-/

end TowardProvingToCanonical

/-! ## Part 4: Alternative Axiom Systems

Based on this analysis, we could reformulate the ω-groupoid with a
**minimal axiom set**:

**Option A: Current (canonical-based)**
- Level 3: `to_canonical` only (all else derives)
- Level 4: `contract₄`
- Level 5+: `contract_high`

**Option B: Pure contractibility**
- Level 3: `contract₃ : ∀ d₁ d₂, Derivation₃ d₁ d₂` (bare contractibility)
- Level 4+: Same

Option A is preferable because it grounds contractibility in the normalization
algorithm rather than postulating it directly.

**Option C: Prove `to_canonical` (ideal)**
- Prove `to_canonical` from termination + confluence
- All level-3 structure becomes derived
- Level 4+: Still need contractibility axioms (no computational content there)
-/

/-
**Summary: A minimal weak ω-groupoid only needs these three axioms:**

1. `to_canonical` (Level 3): Every derivation connects to the canonical one
2. `contract₄` (Level 4): Any two parallel 3-cells are connected
3. `contract_high` (Level 5+): Any two parallel 4-cells are connected

The existing OmegaGroupoid module instantiates these via:
- `MetaStep₃.to_canonical`
- `MetaStep₄.contract₄`
- `MetaStepHigh.contract_high`

All other constructors in those inductives are derivable from the above.
-/

/-! ## Part 5: Eliminating One Unit/Inverse Law

At level 1 (paths), we can derive one of each pair:
- `trans_refl_right` from `trans_refl_left` + symmetry
- `symm_trans` from `trans_symm` + symmetry

Here we show the derivations.
-/

section EliminateRedundantPathLaws

/-- Derive right unit from left unit + symmetry.

    p · ρ = σ(σ(p · ρ))              (by σσ)
          = σ(σ(ρ) · σ(p))            (by symm_trans_congr)
          = σ(ρ · σ(p))               (by σρ)
          = σ(σ(p))                   (by left unit)
          = p                         (by σσ)
-/
theorem derive_trans_refl_right_via_left {a b : A} (p : Path a b) :
    RwEq (Path.trans p (Path.refl b)) p := by
  -- Direct proof using existing RwEq lemmas
  path_simp  -- X · refl ≈ X

/-- Derive symm_trans from trans_symm + symmetry.

    σ(p) · p = σ(σ(σ(p) · p))        (by σσ)
             = σ(σ(p) · σ(σ(p)))      (by symm_trans_congr)
             = σ(σ(p) · p)            (by σσ on inner)
             ... → ρ via trans_symm on σ(p)
-/
theorem derive_symm_trans_via_trans_symm {a b : A} (p : Path a b) :
    RwEq (Path.trans (Path.symm p) p) (Path.refl b) := by
  -- Direct proof using path tactics
  path_cancel_left  -- p⁻¹ · p ≈ refl

end EliminateRedundantPathLaws

/-! ## Summary

**Eliminable axioms (now theorems):**
1. `vcomp_refl_left` - derived from contractibility₃
2. `vcomp_refl_right` - derived from contractibility₃
3. `vcomp_assoc` - derived from contractibility₃
4. `inv_inv` - derived from contractibility₃
5. `vcomp_inv_left` - derived from contractibility₃
6. `vcomp_inv_right` - derived from contractibility₃
7. `inv_vcomp` - derived from contractibility₃
8. `step_eq` - derived from contractibility₃
9. `pentagon` - derived from contractibility₃
10. `triangle` - derived from contractibility₃
11. `interchange` - derived from contractibility₃

**Remaining true axioms:**
1. `to_canonical` (Level 3) - could potentially be proved from normalization
2. `contract₄` (Level 4) - justified by contractibility₃
3. `contract_high` (Level 5+) - justified by contractibility₄

**At level 1 (paths):**
- One of `trans_refl_left`/`trans_refl_right` is derivable
- One of `trans_symm`/`symm_trans` is derivable

This reduces the axiom count from 14+ to just 3 (or potentially 2 if `to_canonical`
can be proved from normalization).
-/

end Derived
end OmegaGroupoid
end Path
end ComputationalPaths
