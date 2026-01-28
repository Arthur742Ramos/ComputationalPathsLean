# Paper Rewrite Task

## Goal
Rewrite `original_paper.tex` (the arXiv:2512.00657 paper) to incorporate all improvements from the Lean 4 formalization, producing a new `paper_v2.tex`.

## Key Improvements to Incorporate

### 1. MAJOR: Contractibility is Now DERIVED, Not Axiomatized

**Original paper (Section 3.6)** says:
> "The canonicity axiom states that every derivation is connected to the canonical derivation... In this formalization, we axiomatize the existence of the 3-cell `can_d`."

**New approach**: Contractibility at ALL levels (3, 4, 5+) is now DERIVED from proof irrelevance of `RwEq`:

```lean
/-- Contractibility at Level 3: any two parallel 2-cells are connected by a 3-cell. -/
def contractibility₃ {p q : Path a b}
    (d₁ d₂ : Derivation₂ p q) : Derivation₃ d₁ d₂ :=
  .step (.rweq_eq (Subsingleton.elim d₁.toRwEq d₂.toRwEq))
```

The key insight: `RwEq` lives in `Prop`, which is proof-irrelevant. Any two `RwEq p q` proofs are equal by `Subsingleton.elim`. This gives us a primitive `MetaStep₃.rweq_eq` constructor, from which all contractibility follows.

**UPDATE Section 3.6** to show this derivation instead of axiomatization.

### 2. All Coherences are Derivable from Contractibility

**Original paper**: Pentagon, triangle, interchange, and groupoid laws are **primitive constructors** of `MetaStep₃`.

**New approach** (`OmegaGroupoid/Derived.lean`): All coherences are **special cases** of contractibility:

```lean
def derive_pentagon (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    Derivation₃ _ _ :=
  connect _ _  -- Just invoke contractibility!
```

**ADD a new section** showing coherences are derived, not primitive.

### 3. Confluence Proof is Complete

**Original paper (Section 2.5)**: References confluence as a property of LND_EQ-TRS but doesn't prove it.

**New approach** (`Rewrite/ConfluenceProof.lean`): Complete confluence proof via Newman's Lemma:
- Critical pair analysis for all core path algebra rules
- Local confluence proof with explicit join witnesses
- Strip lemma derivation

**EXPAND Section 2.5** with the confluence proof outline.

### 4. New Applications (Add New Section)

The formalization now includes:

**Stable Homotopy Groups** (`Homotopy/StableStems.lean`):
- πₛ₁ ≅ ℤ/2ℤ (η), πₛ₂ ≅ ℤ/2ℤ (η²), πₛ₃ ≅ ℤ/24ℤ (ν)
- πₛ₄ = πₛ₅ = 0
- πₛ₆ ≅ ℤ/2ℤ (ν²), πₛ₇ ≅ ℤ/240ℤ (σ)
- πₛ₈ ≅ (ℤ/2ℤ)², πₛ₉ ≅ (ℤ/2ℤ)³

**Adams Spectral Sequence** (`Homotopy/AdamsSpectralSequence.lean`):
- BiGradedGroup structure
- Differentials d_r with d∘d=0

**Free Group Abelianization** (`Algebra/Abelianization.lean`):
- F_n^ab ≅ ℤⁿ with full encode-decode equivalence

**π₅(S³) ≅ ℤ/2ℤ** (`CompPath/Pi5S3.lean`)

### 5. Update Axiom Count

**Original**: 14+ axioms
**New**: 0 axioms beyond Lean's Prop

Add a comparison table in the introduction.

### 6. Update Verification Claims

**Original**: "formalized in Lean 4"
**New**: "130+ verified modules, zero sorry placeholders, no custom axioms beyond Lean's Prop, complete confluence proof"

## Files to Reference

- `original_paper.tex` - The source to rewrite
- `original_references.bib` - Original bibliography (update as needed)
- `/Users/arthur/Desktop/ComputationalPathsLean/ComputationalPaths/` - The Lean formalization

Key Lean files to check:
- `Path/OmegaGroupoid.lean` - Main ω-groupoid structure
- `Path/OmegaGroupoid/Derived.lean` - Derived coherences
- `Rewrite/ConfluenceProof.lean` - Confluence proof
- `Homotopy/StableStems.lean` - Stable homotopy groups
- `Homotopy/AdamsSpectralSequence.lean` - Adams SS
- `Algebra/Abelianization.lean` - Free group abelianization

## Output

Create `paper_v2.tex` in the same directory with the full rewritten paper.
Keep the same overall structure but update content as described above.
The paper should be ~24+ pages like the original.
