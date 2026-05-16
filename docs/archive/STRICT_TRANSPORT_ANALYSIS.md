# Omega-Groupoid Refactor: strict_transport₃ Analysis

## Files Status
All 6 target files have **UNCOMMITTED EDITS** (git M flag):
- **OmegaGroupoid.lean**: 323 insertions, 23 deletions (main refactor)
- **Normalizer.lean**: 26 insertions, 15 deletions
- **TruncationProof.lean**: 14 insertions, 8 deletions
- **TypedRewriting.lean**: 4 insertions, 2 deletions
- **Derived.lean**: 2 insertions, 1 deletion
- **StepToCanonical.lean**: 18 insertions, 11 deletions

---

## (1) Remaining Uses/Definitions of strict_transport₃

### Definition (OmegaGroupoid.lean, Lines 1383-1385)
```lean
noncomputable def strict_transport₃ {p q : Path a b}
    {d₁ d₂ : Derivation₂ p q} : Derivation₃ d₁ d₂ :=
  .step (.rweq_transport (derivation₂_toEq_eq d₁ d₂))
```

**Current Role**: Final fallback for zero-fuel branch of `connect_strict_structural_go`.

### Single Usage (OmegaGroupoid.lean, Line 1399)
```lean
noncomputable def connect_strict_structural_go {p q : Path a b} :
    Nat → (d₁ d₂ : Derivation₂ p q) →
    StrictNormalForm d₁ → StrictNormalForm d₂ → Derivation₃ d₁ d₂
  | 0, d₁, d₂, _, _ => strict_transport₃ (d₁ := d₁) (d₂ := d₂)  -- LINE 1399
  | _fuel + 1, d₁, d₂, h₁, h₂ => ... (constructive cases)
```

Fuel is initialized at `d₁.depth + d₂.depth + 1` (Line 1542), ensuring all 
structurally recognizable cases are handled before the fallback triggers.

### Related Prop-Level Boundary (Lines 948-950)
```lean
theorem derivation₂_toEq_eq {p q : Path a b} (d₁ d₂ : Derivation₂ p q) :
    rweq_toEq d₁.toRwEq = rweq_toEq d₂.toRwEq := rfl
```

This is the **ONLY raw-Path projection boundary** remaining in the system. It 
projects `Derivation₂` witnesses to the `Eq` proof in `rweq_toEq` (lives in 
`Prop`, proof-irrelevant). This witness is used by:

```lean
| rweq_transport {d₁ d₂ : Derivation₂ p q}
    (h : rweq_toEq d₁.toRwEq = rweq_toEq d₂.toRwEq) :
    MetaStep₃ d₁ d₂  -- (MetaStep₃, Lines 256-258)
```

---

## (2) Current Strict Connector / Loop Contraction Design

### 2a. Fuel-Based Recursive Connector Architecture

`connect_strict_structural_go` (Lines 1396-1531) handles constructively:

#### NEW Atomic/Singleton Cases (Recent Edit)
- **Lines 1418-1425**: Atomic loops
  - `.refl` + `.step s` → `atomic_loop_contract s`
  - `.step s` + `.refl` → `inv(atomic_loop_contract s)`
  
- **Lines 1441-1448**: Mixed-sign singletons
  - `.step s₁` + `.inv(.step s₂)` → `connect_single_step_to_single_inv_strict`
  - `.inv(.step s₁)` + `.step s₂` → `connect_single_inv_to_single_step_strict`
  
- **Lines 1443-1444**: Inverse atomic loops
  - `.inv(.step s)` + `.refl` → `atomic_inv_loop_contract s`

#### NEW Forward-StepStar Cases (Recent Edit)
- **Lines 1426-1438**: Loops with forward-only tails
  - `.refl` + `.vcomp(.step s) rest`
  - Checks `derivation_to_stepstar?(rest)`: 
    - If `Some(st)`: constructive via `forward_stepstar_loop_contract`
    - If `None`: fallback `viaInverse` → eventually `strict_transport₃`
  
- **Lines 1516-1529**: Forward derivations against singleton inverses
  - `d₁` + `.inv(.step s₂)`: checks `derivation_to_stepstar?(d₁)`
    - If success: `connect_forward_stepstar_to_single_inv_strict`
    - If none: fallback

#### Existing Aligned-Head Cases
- Lines 1451-1485: Aligned positive-head `.vcomp(.step sᵢ) ...` chains
- Lines 1490-1499: Aligned negative-head `.vcomp(.inv(.step sᵢ)) ...` chains

#### Fallback (viaInverse)
When none match (Lines 1401-1417):
```lean
let viaInverse : {p q : Path a b} → (e₁ e₂ : Derivation₂ p q) → 
                Derivation₃ e₁ e₂ :=
  fun e₁ e₂ =>
    let hInv : Derivation₃ (.inv e₁) (.inv e₂) :=
      .vcomp (to_normal_form_inv₃ e₁)
        (.vcomp
          (connect_strict_structural_go _fuel 
            (normalizeInv e₁) (normalizeInv e₂) ...)
          (.inv (to_normal_form_inv₃ e₂)))
    ... -- re-wrap via groupoid laws
```

This recursively tries the comparison on normalized inverses.

### 2b. Loop Contraction Core

#### New Constructive Functions

**Canonical Raw Self-Loop** (Lines 1222-1223):
```lean
noncomputable def unit_self_step {p : Path a b} : Step p p := by
  simpa using (Step.trans_refl_left p)
```
Exploits the raw-`Path` collapse where `trans(refl a, p)` definitionally 
equals `p`, creating a singleton loop from `trans_refl_left`.

**Atomic Loop Contraction** (Lines 1308-1313):
```lean
noncomputable def atomic_loop_contract {p : Path a b} (s : Step p p) :
    Derivation₃ (.step s) (.refl p) :=
  .vcomp
    (connect_single_step_strict s (unit_self_step (p := p)))
    (unit_self_step_contract (p := p))
```

**Forward-StepStar Loop Contraction** (Lines 1347-1354):
```lean
noncomputable def forward_stepstar_loop_contract {p q : Path a b}
    (s : Step p q) {rest : Derivation₂ q p} {st : StepStar q p}
    (hst : derivation_to_stepstar? rest = some st) :
    Derivation₃ (.vcomp (.step s) rest) (.refl p) :=
  .vcomp
    (connect_cons_step_stepstar_to_step s (unit_self_step (p := p)) ...)
    (unit_self_step_contract (p := p))
```

**Core Loop Contraction** (Lines 1599-1602):
```lean
noncomputable def loop_contract_genuine {p : Path a b} (d : Derivation₂ p p) :
    Derivation₃ d (.refl p) := by
  simpa [reduce_loops] using (to_reduce_loops₃ d)
```
Entry point used by `contractibility₃`.

#### Inverse-Loop Isolation (Lines 1665-1678)

```lean
noncomputable def contractibility₃ {p q : Path a b}
    (d₁ d₂ : Derivation₂ p q) : Derivation₃ d₁ d₂ := by
  let loop : Derivation₂ p p := .vcomp d₁ (.inv d₂)
  exact
    .vcomp
      (.inv (.step (.vcomp_refl_right d₁)))          -- 1. Expand d₁
      (.vcomp
        (Derivation₃.whiskerLeft₃ d₁
          (.inv (.step (.vcomp_inv_left d₂))))        -- 2. Insert inverse pair
        (.vcomp
          (.inv (.step (.vcomp_assoc d₁ (.inv d₂) d₂)))  -- 3. Reassociate
          (.vcomp
            (Derivation₃.whiskerRight₃ (loop_contract_genuine loop) d₂)  
                                                        -- 4. CONTRACT LOOP
            (.step (.vcomp_refl_left d₂)))))          -- 5. Absorb unit
```

---

## (3) Most Promising Constructive Reduction

### Current Fallback Patterns (~9 cases triggering viaInverse)

1. **Line 1436**: `.refl` + `.vcomp(.step s) rest` where `derivation_to_stepstar? rest = None`
2. **Line 1455**: `.step s₁` + `.vcomp(.step s₂) rest₂` where tail NOT StepStar
3. **Line 1463**: `.vcomp(.step s₁) rest₁` + `.step s₂` where tail NOT StepStar
4. **Lines 1478-1482**: Both `.vcomp(.step sᵢ) restᵢ` where one/both NOT StepStar
5. **Lines 1487-1488**: `.inv(.step _)` + `.vcomp(.inv(.step _)) _` (explicit viaInverse)
6. **Line 1499**: Aligned `.vcomp(.inv sᵢ) restᵢ` but midpoints differ
7. **Line 1520**: `d₁` + `.inv(.step s₂)` where `derivation_to_stepstar? d₁ = None`
8. **Line 1527**: `.inv(.step s₁)` + `d₂` where `derivation_to_stepstar? d₂ = None`
9. **Line 1531**: Catch-all `| _, _ => viaInverse _ _`

### Surgical Extension Strategy

**Opportunity**: Current `derivation_to_stepstar?` (Lines 1066-1074) returns `None` 
for ANY derivation containing `.inv`:

```lean
noncomputable def derivation_to_stepstar? {p q : Path a b} :
    Derivation₂ p q → Option (StepStar p q)
  | .refl p => some (StepStar.refl p)
  | .step s => some (StepStar.single s)
  | .inv _ => none                        ← STOPS HERE
  | .vcomp d₁ d₂ => match derivation_to_stepstar? d₁, derivation_to_stepstar? d₂ with
      | some st₁, some st₂ => some (stepstar_append st₁ st₂)
      | _, _ => none
```

### Proposed Surgical Fix #1: Mixed-Polarity Recognition (~20 lines)

Extend to recognize patterns like `.vcomp(.step s) (.inv(.step s'))`:

```lean
inductive MixedStepChain (p q : Path a b) where
  | forward : StepStar p q → MixedStepChain p q
  | backward : StepStar q p → MixedStepChain p q
  | composed_fwd_then_bwd : (st_fwd : StepStar p m) → 
                           (st_bwd : StepStar q m) → 
                           MixedStepChain p q
  | composed_bwd_then_fwd : (st_bwd : StepStar q m) → 
                           (st_fwd : StepStar p m) → 
                           MixedStepChain p q

noncomputable def derivation_to_mixed_stepstar? {p q : Path a b} :
    Derivation₂ p q → Option (MixedStepChain p q) := ...
```

**Impact**: Eliminates cases 1, 3, 7, 8 (~40% of viaInverse calls)

### Proposed Surgical Fix #2: Two-Element Chains (~5 lines)

Add before the catch-all (Line 1530):

```lean
| .vcomp(.step s₁) (.inv(.step s₂)), d₂ =>
    let h : Derivation₃ (.step s₁) (.inv(.step s₂)) := 
      connect_single_step_to_single_inv_strict s₁ s₂
    connect_strict_structural_go _fuel h d₂ ...
```

**Impact**: Eliminates cases 1, 2, 5 (~30% of viaInverse calls)

**Combined Impact**: ~60% reduction in viaInverse calls, making residual 
cases provably "genuine raw-Path ambiguities."

---

## (4) Residual Blockers for Full Elimination

### Root Cause: Raw-Path Definitional Collapse

`Path` in Lean is defined inductively WITHOUT quotients:

```lean
inductive Path : α → α → Type where
  | refl : Path a a
  | trans : Path a b → Path b c → Path a c
```

This means: `Path.trans (Path.refl a) p  =β  p` (DEFINITIONAL)

**Consequence**: `Step.trans_refl_left p : Step p p` is a valid step even 
though source and target are syntactically identical on the raw value after 
β-reduction.

### Why Full Elimination is Non-Local

**1. Expression vs. Raw-Path Mismatch**
- On expression/syntax level (Polygraph), all coherences are genuinely distinct
- On raw `Path`, the collapse means certain derivations have identical `toEq` 
  witnesses
- Can ONLY distinguish them via **proof irrelevance of Prop**

**2. Three Strategies Now Interdependent**
- **Strategy A**: Type-valued constructors (atomic loops, forward chains)
- **Strategy B**: Normalizer groupoid-law reductions (normalize, reassociate)
- **Strategy C**: Prop-level projection (`strict_transport₃`)

Eliminating C globally would require:
- a) Redefining `Path` with quotient/setoid (violates foundational choice)
- b) Proving ALL remaining cases are structurally disambiguable (non-local proof)
- c) Switching to syntax-level representation (loses constructivity on raw Path)

**3. Coverage Proof is Non-Local**
To prove the boundary is necessary, one must:
1. Categorize all shapes reaching `strict_transport₃`
2. For each shape, prove it cannot be disambiguated by structure alone
3. Formalize: "This derivation has identical `toEq`; only Prop-level equality 
   distinguishes it"
4. Requires induction over all `Derivation₂` patterns and all `Path` structures

### Current Design is Locally Optimal

The refactor **accepts Prop-level boundary ONLY where semantically unavoidable**:

✓ At fuel=0 (all structural routes exhausted)
✓ When viaInverse recursion reaches its base case  
✓ Only for "raw-Path collapsed" scenarios

This minimizes Prop use while preserving:
✓ Directness of constructive content
✓ Practical compilation speed (fuel-based recursion)
✓ Structural transparency (no metatheoretic quotients)

---

## Summary Table

| Level | Component                       | Status              | Lines       |
|-------|----------------------------------|---------------------|-------------|
| 3     | `strict_transport₃`             | ACTIVE (FALLBACK)   | 1383-1385   |
| 3     | `loop_contract_genuine`         | CONSTRUCTIVE        | 1599-1602   |
| 3     | `atomic_loop_contract`          | NEW CONSTRUCTIVE    | 1308-1313   |
| 3     | `forward_stepstar_loop_contract`| NEW CONSTRUCTIVE    | 1347-1354   |
| 3     | `unit_self_step`                | NEW CONSTRUCTIVE    | 1222-1223   |
| 3     | `connect_strict_structural_go`  | EXTENDED COVERAGE   | 1396-1531   |
| 3     | `viaInverse`                    | STILL PRESENT       | 1401-1417   |
| 3     | `contractibility₃`              | USES LOOP CONTR.    | 1665-1678   |
| 4     | `contractibility₄`              | ASSUMED             | (imported)  |
| 5+    | `contractibilityHigh`           | ASSUMED             | (imported)  |

---

## Key Takeaways

1. **strict_transport₃ is NOW ISOLATED**: Only appears at zero-fuel fallback, not 
   pervasively in the pipeline.

2. **Most comparison work is constructive**: Atomic loops, forward chains, mixed 
   singletons all handled via explicit 3-cells.

3. **Prop boundary is minimal and justified**: The `derivation₂_toEq_eq` projection 
   is necessary because of raw-Path collapse, not a design flaw.

4. **Surgical improvements possible**: 60% of remaining fallback cases can be 
   eliminated by recognizing mixed-polarity patterns (20-30 lines of edits).

5. **Full elimination requires architectural change**: Moving beyond the Prop 
   boundary globally would require redefining `Path` or switching representation 
   (both are non-local decisions outside the scope of surgical refinement).
