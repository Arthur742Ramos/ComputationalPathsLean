/-
# Analysis: `to_canonical` and `step_to_canonical`

This module documents the analysis of the `to_canonical` assumption and its relationship
to a hypothetical `step_to_canonical` assumption.

## Historical Context

The original formalization attempted to define:
```
canonical p q := .vcomp (deriv₂_to_normal p) (.inv (deriv₂_to_normal q))
```

where `deriv₂_to_normal p := .step (Step.canon p)` used a canonicalization step
`Step.canon : ∀ p, Step p (Path.stepChain p.toEq)`.

**This approach was abandoned** because `Step.canon` caused all paths with the
same `toEq` to become `RwEq`, replacing the explicit generated relation by a
proof-erasing collapse.  This destroys raw trace distinctions.  It is not a
contradiction with the current one-constructor circle: its genuine
`PathRwQuot` loop fiber is already contractible, while the nontrivial `ℤ`
winding quotient is a separate synthetic object.

## Current Status

Without `Step.canon`, the `canonical` function requires a different construction.
The current formalization no longer needs `to_canonical`: contractibility at level 3
now routes through the inverse loop `d₁ · d₂⁻¹` and contracts that loop via the
normalizer-based loop connector.

## The quotient boundary

`RwEq` itself is Type-valued and retains a rewrite certificate.
`RwEqProp := Nonempty (RwEq p q)` is the Prop-valued relation used by
`PathRwQuot`. Passing to `RwEqProp` forgets which certificate was supplied; it
does not prove equality of arbitrary `RwEq` or `Derivation₂` witnesses.

## The Structural Gap

The relevant gap is between explicit Type-valued certificates and their
propositional truncation:
- `RwEq p q` and `Derivation₂ p q` are Type-valued certificates;
- `RwEqProp p q` is Prop-valued and records only inhabitance.

The exported `contractibility₃` witness first isolates an inverse loop and
contracts that loop constructively; no proof-irrelevance shortcut for explicit
derivations is claimed.

## Analysis Summary

| Level | Current Axioms | Notes |
|-------|----------------|-------|
| 1 | Step constructors (~76) | Term rewriting rules |
| 3 | None | Contractibility via inverse-loop normalization |
| 4 | `contractibility₄` (1) | Contractibility |
| 5+ | `contractibilityHigh` (1) | Higher contractibility |

The previous analysis showing that `to_canonical` could be reduced to
`step_to_canonical` (one assumption per Step constructor) is no longer applicable
without `Step.canon`.
-/

import ComputationalPaths.Path.OmegaGroupoid

namespace ComputationalPaths
namespace Path
namespace OmegaGroupoid
namespace StepToCanonical

universe u

variable {A : Type u}

/-! ## Part 1: Equality after projecting certificates

The theorem below compares only the ambient equality proofs obtained by
`rweq_toEq`.  It does not equate Type-valued `RwEq` certificates or
`Derivation₂` values.
-/

section SemanticArgument

variable {a b : A} {p q : Path a b}

/-- All derivations between the same paths project to the same ambient equality
proof via `rweq_toEq`, by proof irrelevance of Lean's `Eq`. -/
theorem derivations_toRwEq_prop_eq (d₁ d₂ : Derivation₂ p q) :
    rweq_toEq d₁.toRwEq = rweq_toEq d₂.toRwEq :=
  rfl

end SemanticArgument

/-! ## Part 2: Derivability from Contractibility

All coherences at level 3 are derivable from `contractibility₃`. See
`Derived.lean` for details.
-/

section FromContractibility

variable {a b : A}

/-- Any two derivations with the same source and target are connected.
    This is the foundation for deriving all level-3 coherences. -/
noncomputable def connect {p q : Path a b} (d₁ d₂ : Derivation₂ p q) : Derivation₃ d₁ d₂ :=
  contractibility₃ d₁ d₂

/-- The groupoid law `vcomp_refl_left` is a special case of contractibility. -/
noncomputable def derive_vcomp_refl_left {p q : Path a b} (d : Derivation₂ p q) :
    Derivation₃ (.vcomp (.refl p) d) d :=
  connect (.vcomp (.refl p) d) d

/-- The groupoid law `vcomp_refl_right` is a special case of contractibility. -/
noncomputable def derive_vcomp_refl_right {p q : Path a b} (d : Derivation₂ p q) :
    Derivation₃ (.vcomp d (.refl q)) d :=
  connect (.vcomp d (.refl q)) d

/-- Associativity `vcomp_assoc` is a special case of contractibility. -/
noncomputable def derive_vcomp_assoc {p q r s : Path a b}
    (d₁ : Derivation₂ p q) (d₂ : Derivation₂ q r) (d₃ : Derivation₂ r s) :
    Derivation₃ (.vcomp (.vcomp d₁ d₂) d₃) (.vcomp d₁ (.vcomp d₂ d₃)) :=
  connect (.vcomp (.vcomp d₁ d₂) d₃) (.vcomp d₁ (.vcomp d₂ d₃))

end FromContractibility

/-! ## Part 3: Axiom Analysis

This section documents the minimal assumption set for the ω-groupoid structure.

### Level 1: Path Rewrite Rules (Step)

The `Step` inductive has ~76 constructors. These form the term rewriting system.

**Minimal groupoid assumptions (6 rules):**
1. `symm_refl` : σ(ρ) → ρ
2. `trans_refl_left` : ρ · p → p
3. `trans_assoc` : (p · q) · r → p · (q · r)
4. `trans_symm` : p · σ(p) → ρ
5. `symm_trans_congr` : σ(p · q) → σ(q) · σ(p)
6. `symm_symm` : σ(σ(p)) → p

### Level 2: Derivations (Derivation₂)

No assumptions needed — `Derivation₂` is a free structure.

### Level 3: Meta-derivations (Derivation₃)

No assumption is needed: `contractibility₃` is now implemented by explicit
inverse-loop isolation together with the loop normalizer and the local
`strict_loop_contract_go` recursion, with only a residual raw-`Path`
projection boundary left inside that loop connector.
All groupoid laws, coherences, and step equality are derivable from
`contractibility₃`.

### Level 4+: Higher cells

No higher contractibility assumptions: levels 4+ are obtained from the explicit
level-3 tower plus the higher diamond fillers already present in the core
development.

### Total Minimal Axioms

| Level | Axiom | Justification |
|-------|-------|---------------|
| 3 | None | Contractibility for 2-cells |
| 4 | `contractibility₄` | Contractibility₃ (derived) |
| 5+ | `contractibilityHigh` | Contractibility₄ (derived) |

The level 1 Step rules are structural and define the rewriting system.
They are not assumptions in the ω-groupoid sense but rather the computational
content of path equality.
-/

end StepToCanonical
end OmegaGroupoid
end Path
end ComputationalPaths
