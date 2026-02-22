# Analysis: Contractibility₃ WITHOUT `rweq_eq`

## Executive Summary

**Verdict: Impossible using only groupoid-law MetaStep₃ constructors.**

Eliminating `MetaStep₃.rweq_eq` from the contractibility₃ proof is mathematically
impossible. The argument below proves this via an explicit counterexample showing
that the Step graph on `Path a b` contains undirected cycles, which means the free
groupoid on it has genuinely distinct morphisms between the same vertices that cannot
be connected by groupoid laws alone.

---

## 1. The Mathematical Setup

`Derivation₂ p q` is the **free groupoid** on the Step graph:
- **Objects** = paths `Path a b`
- **Generators** = `Step p q` (Prop-valued: at most one per pair)
- **Operations** = `refl`, `vcomp` (composition), `inv` (inversion)

The MetaStep₃ constructors (excluding `rweq_eq`) provide the standard
**groupoid laws**: associativity, unit laws, inverse laws, anti-homomorphism
of inversion, and the Prop-valued identification `step_eq`.

**Key theorem from free group theory**: In a free groupoid on a graph G,
two morphisms from vertex v to vertex w are equal **if and only if** they
have the same reduced word (unique normal form in the free group on
generators along the path).

Therefore: `contractibility₃` (= any two `Derivation₂ p q` are connected
by a `Derivation₃`) is equivalent to the Step graph being a **forest**
(no undirected cycles).

## 2. The Step Graph Has Cycles: Explicit Counterexample

Even for the trivial type `A = Unit`, `a = b = ()`, the Step graph on
`Path () ()` contains undirected cycles.

### The diamond

Consider three paths in `Path () ()`:
```
p₀ = trans (trans (refl ()) (refl ())) (refl ())
p₁ = trans (refl ()) (trans (refl ()) (refl ()))
p₂ = trans (refl ()) (refl ())
```

The Step graph has these edges:
1. `p₀ → p₁` via `Step.trans_assoc (refl ()) (refl ()) (refl ())`
2. `p₀ → p₂` via `Step.trans_congr_left (refl ()) (Step.trans_refl_left (refl ()))`
3. `p₁ → p₂` via `Step.trans_congr_right (refl ()) (Step.trans_refl_left (refl ()))`

This gives an **undirected 3-cycle**: `p₀ — p₁ — p₂ — p₀`.

### Consequences for the free groupoid

The two `Derivation₂ p₀ p₂`:
- **Route A**: `Derivation₂.step edge₂` (one generator: the direct step)
- **Route B**: `Derivation₂.vcomp (Derivation₂.step edge₁) (Derivation₂.step edge₃)`
  (two generators: assoc then congr)

These map to reduced words `[edge₂]` and `[edge₁, edge₃]` respectively.
Since these are different reduced words (different generators — edge₁, edge₂,
edge₃ are all between different pairs of paths), they represent **genuinely
distinct elements** of the free groupoid.

**No sequence of groupoid-law MetaStep₃ rewrites can connect them.** The groupoid
laws only perform:
- Re-association of `vcomp` (doesn't change the reduced word)
- Cancellation of `s · s⁻¹` pairs (only cancels adjacent inverse pairs)
- Unit absorption (removes `refl`)
- Inverse distribution (reorders under `inv`)
- `step_eq` (identifies different Step witnesses between the SAME pair of paths)

None of these can transform `[edge₂]` into `[edge₁, edge₃]` because they involve
different intermediate path `p₁` — which is outside the scope of groupoid laws.

## 3. Why `rweq_eq` Works

`MetaStep₃.rweq_eq` succeeds because it operates at a fundamentally different level:

```lean
| rweq_eq {a b : A} {p q : Path a b} {d₁ d₂ : Derivation₂ p q}
      : MetaStep₃ d₁ d₂
```

It takes **no arguments** — it's an axiom asserting that ALL `Derivation₂ p q` are
connected. This is sound because:

1. `Derivation₂.toRwEq : Derivation₂ p q → RwEq p q` projects to a Prop
2. `RwEq p q` is Prop-valued, so any two inhabitants are definitionally equal
3. This proof irrelevance at the Prop level justifies the 3-cell

This is NOT a groupoid-law fact — it's a **type-theoretic** fact about Lean's
treatment of Prop. The free groupoid model (where distinct reduced words are
distinct morphisms) is simply not the intended semantics; the intended semantics
is the quotient where all morphisms between the same endpoints are identified.

## 4. What Would Be Needed to Eliminate `rweq_eq`

### Option A: Prove the Step graph is a forest
**Status: Impossible.** The pentagon/diamond above shows it has cycles even for
trivial types. The cycles are inherent to the overlapping rewrite rules
(e.g., `trans_assoc` + `trans_refl_left` create diamonds).

### Option B: Add a new non-groupoid-law MetaStep₃ constructor
One could add constructors that encode specific Step-graph relationships
(e.g., "this diamond commutes"), but this just repackages `rweq_eq` in a
more verbose form. For every diamond in the Step graph, you'd need a
dedicated constructor — and there are infinitely many diamonds.

### Option C: Use Expr-level confluence to lift
**The approach suggested in the prompt.** This fails because:

1. Embedding `Derivation₂` into `Expr` requires assigning each `Step` a unique
   `Nat` index
2. Two `Derivation₂ p q` using different intermediate paths map to `Expr` with
   different `toRW` (different reduced words in the free group)
3. Expr-level confluence says "CStep-related expressions have the same canonical
   form" — but two Derivation₂ images are NOT CStep-related; they're independent
   expressions with different reduced words
4. To show they're CStep-related, you'd need exactly the contractibility₃ you're
   trying to prove — circular

### Option D: Step-level confluence + unique normal forms
The Step TRS IS confluent and terminating (from ConfluenceDeep.lean), so every path
has a unique normal form. One might hope that "both derivations normalize to the
same canonical derivation through the normal form." But:

- Two `Derivation₂ p q` normalize to different flat chains (different reduced words
  in the free groupoid)
- The canonical derivation `p →* nf ←* q` is unique, but connecting an arbitrary
  `Derivation₂ p q` to this canonical zig-zag requires identifying different
  elements of the free groupoid — exactly what we can't do without `rweq_eq`

## 5. The Existing Architecture Is Correct

The current codebase has the right architecture:

| Layer | What it provides |
|-------|-----------------|
| `GroupoidConfluence.lean` | Expr-level confluence (free group normal forms) |
| `ConfluenceDeep.lean` | Step-level confluence (Church-Rosser for Path rewriting) |
| `MetaStep₃.rweq_eq` | Contractibility₃ via proof irrelevance on RwEq |
| `Normalizer.lean` | Groupoid-law normalization (handles everything EXCEPT contractibility) |

The `Normalizer.lean` successfully handles:
- Flattening (tree → right-associated chain) ✓
- Inverse pushing (inv to leaves) ✓  
- Unit absorption ✓
- Inverse cancellation of adjacent pairs ✓
- Step identification via `step_eq` ✓

But the final uniqueness step — connecting two reduced chains between the same
endpoints — genuinely requires `rweq_eq` because it's connecting elements that
are distinct in the free groupoid.

## 6. Recommendation

**Keep `MetaStep₃.rweq_eq`.** It is:

1. **Mathematically necessary**: No groupoid-law proof exists
2. **Mathematically sound**: Justified by proof irrelevance of `RwEq`
3. **Conceptually clean**: It encodes the precise mathematical content —
   that `Step` is Prop-valued and `RwEq` is proof-irrelevant

The existing code in `Normalizer.lean` is valuable as a **partial normalization**
that reduces the problem to normal-form uniqueness. The `rweq_eq` uses in that file
are precisely the irreducible core — the places where free-groupoid reasoning hits
its limit and Prop-level collapse is needed.

### What `rweq_eq` really says (mathematically)

`rweq_eq` says: "the canonical functor from the free groupoid on Step to the
Prop-valued quotient (where all parallel morphisms are identified) has trivial
kernel." This is true because `Step` is Prop-valued and `RwEq` collapses to Prop.

In homotopy-theoretic terms: the free groupoid on Step is the fundamental groupoid
of the Step graph, and `rweq_eq` says its π₁ is trivial. But π₁ is NOT trivial
(the Step graph has cycles). What saves us is that we're working in Lean's type
theory where `Step : Prop`, and Prop collapses all higher structure.

## 7. Summary Table of `rweq_eq` Uses

| File | Count | Purpose | Eliminable? |
|------|-------|---------|-------------|
| `Normalizer.lean` | 3 | SignedStep.coherence (mixed polarity), normalForm_unique, contractibility₃_genuine | No |
| `TruncationProof.lean` | 6 | connect_to_canonical, contract₃/₄ fields, main theorems | No |
| `OmegaGroupoid.lean` | 3 | contractibility₃, loop_contraction, contractibility₄ | No |

**None are eliminable** without replacing `rweq_eq` with something equally powerful.
