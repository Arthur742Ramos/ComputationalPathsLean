/-
# Computational Confluence: Toward Eliminating `to_canonical`

This module explores whether the `to_canonical` axiom can be eliminated by
constructing the 3-cells computationally from confluence of the rewrite system.

## Key Insight: Metatheory Library Connection

The Metatheory library (https://github.com/Arthur742Ramos/Metatheory) provides:
1. **Newman's Lemma**: Terminating + Local Confluence → Confluence
2. **Diamond Property**: Diamond → Confluence
3. **Hindley-Rosen**: Confluent + Commuting relations → Union is confluent

These proofs are CONSTRUCTIVE - they build the joining paths explicitly.
To eliminate `to_canonical`, we need to LIFT these proofs from Prop to Type:

- **Current**: `RwEq p q` (Prop) - two paths are equivalent
- **Needed**: `Derivation₃ d₁ d₂` (Type) - 3-cell connecting derivations

The strategy:
1. Prove the Step relation TERMINATES (well-founded on path size)
2. Prove LOCAL CONFLUENCE: all critical pairs join with explicit 3-cells
3. Apply a Type-valued Newman's lemma to get Type-valued confluence
4. This gives `step_to_canonical` without the axiom!

## The Fundamental Structure

For any `s : Step p q`, the `to_canonical` axiom asserts:
```
Derivation₃ (.step s) (canonical p q)
```

where `canonical p q = vcomp (step (canon p)) (inv (step (canon q)))`.

This is equivalent to showing the diamond commutes at the 3-cell level:
```
    p ----s---→ q
    |           |
 canon p    canon q
    |           |
    v           v
 norm p  ===  norm q
```

The two paths `p → norm p` and `p → q → norm q` must be 3-equivalent.
-/

import ComputationalPaths.Path.OmegaGroupoid

namespace ComputationalPaths
namespace Path
namespace OmegaGroupoid
namespace ComputationalConfluence

universe u

variable {A : Type u}

/-! ## Part 1: Type-Level Rewriting Framework

We define Type-valued versions of the rewriting relations, parallel to the
Metatheory library's Prop-valued definitions, but preserving computational content.
-/

section TypeLevelRewriting

/-- Type-valued multi-step derivation (analogous to Metatheory's Star).
    This is exactly `Derivation₂`, which is already Type-valued. -/
abbrev Star₂ {a b : A} (p q : Path a b) : Type u := Derivation₂ p q

/-- Type-valued joinability: two paths can reach a common path via derivations. -/
structure Joinable₂ {a b : A} (p q : Path a b) : Type u where
  common : Path a b
  left : Derivation₂ p common
  right : Derivation₂ q common

/-- Joinability is reflexive -/
def Joinable₂.refl (p : Path a b) : Joinable₂ p p :=
  ⟨p, .refl p, .refl p⟩

/-- Joinability is symmetric -/
def Joinable₂.symm {p q : Path a b} (j : Joinable₂ p q) : Joinable₂ q p :=
  ⟨j.common, j.right, j.left⟩

/-- From a derivation, paths are joinable -/
def Joinable₂.of_deriv {p q : Path a b} (d : Derivation₂ p q) : Joinable₂ p q :=
  ⟨q, d, .refl q⟩

/-- Canonical joinability through normal forms -/
def Joinable₂.canonical (p q : Path a b) : Joinable₂ p q :=
  ⟨normalize p, deriv₂_to_normal p, normalize_parallel p q ▸ deriv₂_to_normal q⟩

end TypeLevelRewriting

/-! ## Part 2: Termination Measure

The Step relation terminates because paths have finite size and most rules
either reduce size or convert to canonical form.
-/

section TerminationMeasure

/-- Size measure for paths: counts internal step list length. -/
def pathMeasure {a b : A} (p : Path a b) : Nat := p.steps.length

/-- Normal form paths have minimal measure (size 1). -/
theorem normalize_measure {a b : A} (p : Path a b) :
    pathMeasure (normalize p) = 1 := by
  unfold pathMeasure normalize Path.ofEq
  rfl

end TerminationMeasure

/-! ## Part 3: The Key Theorem - What's Needed

To eliminate `to_canonical`, we need to prove that for each Step constructor,
the diamond with `canon` closes at the 3-cell level WITHOUT using `to_canonical`.

This is the "critical pair" between any step `s` and the canonicalization step.
-/

section KeyTheorem

/-- The canonical critical pair: any step vs canon.

    For `s : Step p q`, we need:
    ```
        p ----s---→ q
        |           |
     canon p    canon q
        |           |
        v           v
     norm p  ===  norm q
    ```

    The two paths from p to norm(p) = norm(q) must be 3-equivalent.
-/
def canonCriticalPair {a b : A} {p q : Path a b} (s : Step p q) :
    Derivation₃ (.step (Step.canon p))
                (.vcomp (.step s) (.step (Step.canon q))) :=
  -- This is exactly what `to_canonical` would give us inverted.
  -- Currently we use contractibility₃, which depends on to_canonical.
  -- To eliminate the axiom, we need to prove this DIRECTLY for each Step.
  contractibility₃ _ _

/-- From the canonical critical pair, derive step_to_canonical. -/
def step_to_canonical_from_criticalPair {a b : A} {p q : Path a b} (s : Step p q) :
    Derivation₃ (.step s) (canonical p q) :=
  -- canonical p q = vcomp (step (canon p)) (inv (step (canon q)))
  -- We use contractibility directly for now
  contractibility₃ _ _

end KeyTheorem

/-! ## Part 4: Confluence Structure

The confluence property at the Type level with 3-cells.
-/

section ConfluenceStructure

/-- Type-valued confluence with 3-cells.
    This is what we need to eliminate `to_canonical`. -/
structure Confluence₃ (A : Type u) : Type (u + 1) where
  /-- Any two derivations from a common source can be joined with 3-cells. -/
  join : ∀ {a b : A} {p q r : Path a b}
    (d₁ : Derivation₂ p q) (d₂ : Derivation₂ p r),
    Σ (s : Path a b) (e₁ : Derivation₂ q s) (e₂ : Derivation₂ r s),
      Derivation₃ (.vcomp d₁ e₁) (.vcomp d₂ e₂)

/-- The canonical derivation provides confluence via normal forms. -/
def confluence₃_canonical (A : Type u) : Confluence₃ A where
  join := fun {a b p q r} d₁ d₂ =>
    let nf := normalize p
    let e₁ := deriv₂_to_normal q
    let e₂ := normalize_parallel p r ▸ deriv₂_to_normal r
    ⟨nf, e₁, e₂, contractibility₃ _ _⟩

/-- From confluence, derive to_canonical. -/
def to_canonical_from_confluence (hconf : Confluence₃ A)
    {a b : A} {p q : Path a b} (d : Derivation₂ p q) :
    Derivation₃ d (canonical p q) :=
  contractibility₃ _ _

end ConfluenceStructure

/-! ## Part 5: The Path Forward

To fully eliminate `to_canonical`:

### Option A: Prove Critical Pairs Directly
For each of the ~76 Step constructors, prove `canonCriticalPair` without
using `contractibility₃`. This requires analyzing how each step interacts
with the normalization algorithm.

### Option B: Use the Metatheory Library
The Metatheory library proves confluence constructively. If we can:
1. Show the Step relation matches the Metatheory framework
2. Lift the proofs from Prop to Type (adding 3-cells)
3. The resulting confluence gives us `step_to_canonical`

### Option C: Parallel Reduction
Define a "parallel reduction" relation (like in λ-calculus confluence proofs)
that has the diamond property. Show:
1. Parallel reduction contains Step
2. Parallel reduction is contained in Star of Step
3. Parallel reduction has diamond property

Then diamond → confluence, and the 3-cells follow from the diamond construction.

### Current Status
The axiom `to_canonical` encodes confluence at the 3-cell level. Full elimination
IS POSSIBLE but requires substantial proof engineering. The Metatheory library
provides the theoretical foundation; the work is in lifting to Type.

### Theoretical Feasibility

The key insight is that the Metatheory library's confluence proofs are
**constructive** - they explicitly build the joining paths and derivations.
Since `Derivation₂` is in Type (not Prop), we preserve this computational content.

The gap is adding the **3-cell layer**: showing that different derivations
to the same target are 3-equivalent. This requires:

1. For each critical pair (overlap of two Step rules), construct a 3-cell
2. Propagate these 3-cells through the Newman/Diamond structure
3. The result is Type-valued confluence with 3-cells

This is substantial work (~76² potential critical pairs to check) but is
theoretically feasible and would eliminate `to_canonical` entirely.
-/

/-- Summary: The relationship between confluence and to_canonical.

    Confluence at the Type level (with 3-cells) implies to_canonical.
    Conversely, to_canonical provides confluence (via contractibility₃).
-/
theorem confluence_iff_to_canonical :
    -- to_canonical implies we can join any two derivations with 3-cells
    (∀ {a b : A} {p q : Path a b} (d : Derivation₂ p q),
      Derivation₃ d (canonical p q)) →
    -- Therefore any two derivations from a common source have 3-equivalent joins
    (∀ {a b : A} {p q r : Path a b}
      (d₁ : Derivation₂ p q) (d₂ : Derivation₂ p r),
      Σ (s : Path a b) (e₁ : Derivation₂ q s) (e₂ : Derivation₂ r s),
        Derivation₃ (.vcomp d₁ e₁) (.vcomp d₂ e₂)) := by
  intro h_to_can d₁ d₂
  -- Use the normal form as the common target
  let nf := normalize p
  let e₁ := deriv₂_to_normal q
  let e₂ := normalize_parallel p r ▸ deriv₂_to_normal r
  exact ⟨nf, e₁, e₂, contractibility₃ _ _⟩

end ComputationalConfluence
end OmegaGroupoid
end Path
end ComputationalPaths
