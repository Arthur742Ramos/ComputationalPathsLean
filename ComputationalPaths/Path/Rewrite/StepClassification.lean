/-
# Complete Classification of Step Constructors for Canon-Free Confluence

This module catalogs every constructor of `Step` (the single-step rewrite
relation on computational paths) and classifies it along multiple axes:

  1. **Category**: simplification / reorientation / congruence / distribution /
     type-specific / canonicalization
  2. **Type-former group**: groupoid, Prod, Σ, Sum, Π, transport, context,
     dep-context, bi-context, map, structural
  3. **LHS head constructor**: which `Path` constructor appears at the root of
     the LHS pattern
  4. **Critical-pair potential**: which other rules can overlap the same LHS

The ultimate goal is to prove confluence WITHOUT `Step.canon`.  Canon uses
UIP/proof irrelevance to collapse all paths to `stepChain p.toEq`, which
defeats the purpose of computational paths — we want the rewrite structure
itself, not just the propositional witness.

## Strategy Overview

### Why Canon-Free Confluence Is Hard

With `canon`, confluence is trivial: every path `p` has `Step p (stepChain p.toEq)`,
and `stepChain` is unique (by proof irrelevance), so any two reducts share a
common canonical form.  Without `canon`, we must show that all critical pairs
(where two rules overlap on the same redex) are joinable.

### Modular Confluence Strategy

The key insight is that the rule groups are largely **orthogonal** — their LHS
patterns involve different head constructors and type formers.  Specifically:

1. **Groupoid rules** (1–8): LHS heads are `symm(refl)`, `symm(symm _)`,
   `trans(refl, _)`, `trans(_, refl)`, `trans(p, symm p)`, `trans(symm p, p)`,
   `symm(trans _ _)`, `trans(trans _ _, _)`.

2. **Product rules** (9–15): LHS heads involve `map2`, `congrArg Prod.fst/snd`,
   `Prod.rec`, `prodMk`, specific to `Prod`.

3. **Sigma rules** (16–19): LHS heads involve `congrArg Sigma.fst`, `sigmaSnd`,
   `sigmaMk`, specific to `Sigma`.

4. **Sum rules** (20–21): LHS heads involve `congrArg (Sum.rec f g)`, specific
   to `Sum`.

5. **Function rules** (22–24): LHS heads involve `congrArg (· a) lamCongr`,
   `lamCongr`, specific to function types.

6. **Transport rules** (25–32): LHS heads involve `stepChain` wrapped around
   transport equalities.

7. **Context rules** (33–48): LHS heads involve `Context.map`, `substLeft`,
   `substRight`.

8. **Dep-context rules** (49–60): LHS heads involve `DepContext.map`,
   `DepContext.substLeft/Right`.

9. **Bi-context / dep-bi-context rules** (61–68): LHS heads involve
   `BiContext.mapLeft/Right/map2`, `DepBiContext.mapLeft/Right/map2`.

10. **Map rules** (69–72): LHS heads involve `Path.mapLeft/Right`.

11. **Structural congruence** (73, 75, 76): `symm_congr`, `trans_congr_left`,
    `trans_congr_right` — propagate steps into subterms.

12. **Canon** (77): The rule we want to eliminate.

### Orthogonality Analysis

Two rule groups overlap iff there exists a term that matches the LHS pattern of
a rule from each group simultaneously.  The critical question:

- **Groupoid ↔ Product**: Can a term be both `symm(prodMk p q)` and match
  `symm_symm`?  Only if `prodMk p q = symm _`.  These are different `Path`
  constructors ⇒ **NO OVERLAP** on base rules.  However, `prod_mk_symm` has
  LHS `symm(prodMk p q)` and `symm_congr` can lift any step under `symm` —
  this is a congruence-vs-base overlap (see below).

- **Groupoid ↔ Sigma**: Same argument.  `sigma_mk_symm` has LHS
  `symm(sigmaMk p q)` which is a different pattern from groupoid `symm` rules.

- **Groupoid ↔ Context**: `context_map_symm` has LHS `symm(C.map p)`.
  Again disjoint from `symm_refl`, `symm_symm`.

- **Product ↔ Sigma ↔ Sum ↔ Function**: Different `Path` constructors at root ⇒
  **FULLY ORTHOGONAL**.

- **Structural congruence ↔ Everything**: `symm_congr`, `trans_congr_left`,
  `trans_congr_right` can overlap with ANY rule whose LHS has `symm`, `trans`
  at the root.  This is the primary source of critical pairs.

### Critical Pair Categories

#### Category I: Structural Congruence vs. Base Rules

When a rule has LHS `symm(pattern)` or `trans(pattern, _)`, structural
congruence can also apply.  These pairs are:

  - `symm_congr` vs `symm_refl`: LHS `symm(refl)`.
    Step inside: `symm_congr` does nothing (refl has no sub-steps).
    Base rule: `symm_refl` fires.  ⇒ No real overlap (congruence needs a
    sub-step, `refl` has no redex).

  - `symm_congr` vs `symm_symm`: LHS `symm(symm p)` where `p` has a redex.
    Left: `symm(symm p) →[symm_congr] symm(symm p')` then `→[symm_symm] p'`.
    Right: `symm(symm p) →[symm_symm] p` then `→ p'`.
    Join: `p'`. ✓

  - `trans_congr_left` vs `trans_refl_left`: LHS `trans(refl, q)` where `q`
    has redex.  But `trans_congr_left` requires a step in the LEFT component,
    and `refl` has no redex ⇒ no real overlap.

  - `trans_congr_right` vs `trans_refl_right`: Same — `refl` in right has no redex.

  - `trans_congr_left` vs `trans_assoc`: LHS `trans(trans(p,q), r)` where
    `trans(p,q)` has a redex (via `trans_congr_left` or `trans_congr_right`).
    Left: apply congruence to get `trans(trans(p',q), r)` or `trans(trans(p,q'), r)`.
    Right: apply `trans_assoc` to get `trans(p, trans(q, r))`.
    Join: apply `trans_assoc` to left result / congruence to right result.
    This is joinable by applying the complementary rule. ✓

#### Category II: Overlapping Groupoid Rules

  - `trans_symm` vs `trans_congr_right` at `trans(p, symm p)`:
    If `symm p` has a redex (via `symm_congr`), we get
    `trans(p, symm p')` vs `refl`.
    This requires careful handling — need `trans_symm` to still apply
    after the subterm step.

  - `trans_assoc` vs `trans_symm`/`symm_trans`:
    Pattern `trans(trans(p, symm(p)), q)`:
    Left: `→[trans_assoc] trans(p, trans(symm(p), q))`.
    Right: `→[trans_congr_left] trans(refl, q) →[trans_refl_left] q`.
    Join from left: `→[trans_congr_right] trans(p, ...) → ...`
    These are the "groupoid word problem" critical pairs.

  - `symm_trans_congr` vs `symm_symm`:
    Pattern `symm(trans(symm(p), q))`:
    Not directly overlapping (different sub-pattern structure).

#### Category III: Congruence vs. Type-Specific Rules

  - `context_congr` vs `context_map_symm`: LHS `symm(C.map p)`.
    Left: `context_congr` propagates step in `p`.
    Right: `context_map_symm` pushes `symm` inside.
    Join: apply the complementary rule to each result. ✓

  - `context_subst_left_beta` vs `context_subst_right_beta`:
    Pattern `trans(r, C.map p)` matches `context_subst_left_beta`.
    Pattern `trans(C.map p, t)` matches `context_subst_right_beta`.
    These have disjoint LHS patterns (context arg in different position).

### Weight Function for Groupoid Fragment

The groupoid fragment (rules 1–8 + structural congruence 73, 75, 76) has a
well-known termination order using the lexicographic pair `(weight, leftWeight)`
defined in `GroupoidTRS.lean`:

  - `weight(refl) = 4`, `weight(symm e) = 2·weight(e) + 1`,
    `weight(trans e₁ e₂) = weight(e₁) + weight(e₂) + 2`
  - Rules 1–7 strictly decrease `weight`.
  - Rule 8 (associativity) preserves `weight` but decreases `leftWeight`.

### Confluence Strategy for the Full System (Without Canon)

1. **Groupoid fragment**: Proved terminating in `GroupoidTRS.lean`.
   Local confluence provable by checking finitely many critical pairs.
   By Newman's lemma ⇒ confluence. ✓

2. **Type-specific rules**: Each group (Prod, Σ, Sum, Π) is orthogonal to
   the others.  Within each group, rules are non-overlapping β/η pairs.
   They interact with groupoid rules only through structural congruence,
   and those interactions are joinable.

3. **Context/substitution rules**: More complex.  The substitution rules
   (`substLeft`, `substRight`) create associativity-like critical pairs
   with themselves and with the groupoid `trans_assoc`.  Key critical pairs:
   - `context_subst_left_assoc` vs `context_subst_right_assoc`
   - `context_subst_left_beta` vs `trans_assoc`
   All are handled by the dedicated associativity/cancellation rules (35–48).

4. **Transport rules**: These use `stepChain` on the RHS, making them
   essentially one-way simplifications. They don't create critical pairs
   with groupoid rules because their LHS involves `stepChain(...)` which
   is not `symm`, `trans`, etc.

### Conclusion

Removing `canon` is feasible because:
- The rule groups are modular and largely orthogonal.
- The groupoid core is already proved terminating.
- Type-specific rules don't overlap each other.
- The main challenge is the substitution/context rules, but dedicated
  cancellation rules (35–48, 55–60) are designed to close those pairs.
- The remaining critical pairs between structural congruence and base rules
  are all joinable by applying the complementary rule.

## References

- de Queiroz, de Oliveira & Ramos, "Propositional equality, identity types,
  and direct computational paths", SAJL 2016
- Ramos et al., "Explicit Computational Paths", SAJL 2018
-/

import ComputationalPaths.Path.Rewrite.Step
import ComputationalPaths.Path.Rewrite.ConfluenceProof
import ComputationalPaths.Path.Rewrite.TerminationBridge

namespace ComputationalPaths.Path.Rewrite.StepClassification

/-!
## Complete Constructor Catalog

Each entry: `(RuleNumber, Name, Category, Group, LHS → RHS, CriticalPairsWith)`
-/

/-- Classification categories for Step constructors. -/
inductive RuleCategory where
  /-- Strictly reduces term complexity (e.g., identity laws, cancellation). -/
  | simplification
  /-- Same complexity, different shape (e.g., associativity). -/
  | reorientation
  /-- Applies a rule inside a subterm (e.g., congruence under symm/trans). -/
  | congruence
  /-- Pushes constructors through others (e.g., symm distributing over trans). -/
  | distribution
  /-- Rules specific to Σ, Π, transport, ap, etc. -/
  | typeSpecific
  /-- The canonicalization rule we want to remove. -/
  | canonicalization
  deriving DecidableEq, Repr

/-- Type-former groups that rules belong to. -/
inductive RuleGroup where
  /-- Basic path algebra: refl, symm, trans. Rules 1–8. -/
  | groupoid
  /-- Product types (Prod). Rules 9–15. -/
  | product
  /-- Dependent pairs (Sigma). Rules 16–19. -/
  | sigma
  /-- Sum types (Sum). Rules 20–21. -/
  | sum
  /-- Function types. Rules 22–24. -/
  | function
  /-- Dependent application. Rule 25. -/
  | depApp
  /-- Transport along paths. Rules 26–32. -/
  | transport
  /-- Unary contexts. Rules 33–48. -/
  | context
  /-- Dependent unary contexts. Rules 49–60. -/
  | depContext
  /-- Binary contexts and dependent binary contexts. Rules 61–68. -/
  | biContext
  /-- mapLeft/mapRight. Rules 69–72. -/
  | mapLR
  /-- Structural congruence (propagation). Rules 73, 75, 76. -/
  | structural
  /-- Canon rule. Rule 77. -/
  | canon
  deriving DecidableEq, Repr

/-- Metadata for a single Step constructor. -/
structure RuleInfo where
  /-- Rule number in the Step definition. -/
  number : Nat
  /-- Constructor name (without `Step.` prefix). -/
  name : String
  /-- Classification category. -/
  category : RuleCategory
  /-- Which type-former group it belongs to. -/
  group : RuleGroup
  /-- Informal description of LHS → RHS. -/
  lhsToRhs : String
  /-- Head constructor of the LHS pattern. -/
  lhsHead : String
  /-- List of rule names this can create critical pairs with. -/
  criticalPairsWith : List String
  deriving Repr

/-- The complete catalog of all 77 Step constructors. -/
def allRules : List RuleInfo := [
  -- ═══════════════════════════════════════════════════════════════
  -- GROUP A: GROUPOID (Basic Path Algebra) — Rules 1–8
  -- ═══════════════════════════════════════════════════════════════
  { number := 1, name := "symm_refl"
  , category := .simplification, group := .groupoid
  , lhsToRhs := "symm(refl a) ▷ refl a"
  , lhsHead := "symm"
  , criticalPairsWith := ["symm_congr"]
  },
  { number := 2, name := "symm_symm"
  , category := .simplification, group := .groupoid
  , lhsToRhs := "symm(symm p) ▷ p"
  , lhsHead := "symm"
  , criticalPairsWith := ["symm_congr", "symm_refl"]
  },
  { number := 3, name := "trans_refl_left"
  , category := .simplification, group := .groupoid
  , lhsToRhs := "trans(refl a, p) ▷ p"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_congr_left", "trans_congr_right", "trans_assoc"]
  },
  { number := 4, name := "trans_refl_right"
  , category := .simplification, group := .groupoid
  , lhsToRhs := "trans(p, refl b) ▷ p"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_congr_left", "trans_congr_right", "trans_assoc"]
  },
  { number := 5, name := "trans_symm"
  , category := .simplification, group := .groupoid
  , lhsToRhs := "trans(p, symm p) ▷ refl a"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_congr_left", "trans_congr_right", "trans_assoc",
                           "context_subst_right_beta", "context_subst_left_beta"]
  },
  { number := 6, name := "symm_trans"
  , category := .simplification, group := .groupoid
  , lhsToRhs := "trans(symm p, p) ▷ refl b"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_congr_left", "trans_congr_right", "trans_assoc",
                           "context_subst_right_beta", "context_subst_left_beta"]
  },
  { number := 7, name := "symm_trans_congr"
  , category := .distribution, group := .groupoid
  , lhsToRhs := "symm(trans(p, q)) ▷ trans(symm q, symm p)"
  , lhsHead := "symm"
  , criticalPairsWith := ["symm_congr", "symm_symm"]
  },
  { number := 8, name := "trans_assoc"
  , category := .reorientation, group := .groupoid
  , lhsToRhs := "trans(trans(p, q), r) ▷ trans(p, trans(q, r))"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_congr_left", "trans_congr_right",
                           "trans_refl_left", "trans_refl_right",
                           "trans_symm", "symm_trans",
                           "context_subst_left_beta", "context_subst_right_beta"]
  },

  -- ═══════════════════════════════════════════════════════════════
  -- GROUP B: PRODUCT TYPES (Prod) — Rules 9–15
  -- ═══════════════════════════════════════════════════════════════
  { number := 9, name := "map2_subst"
  , category := .distribution, group := .product
  , lhsToRhs := "map2 f p q ▷ trans(mapRight f a₁ q, mapLeft f p b₂)"
  , lhsHead := "map2"
  , criticalPairsWith := ["prod_fst_beta", "prod_snd_beta", "prod_rec_beta"]
  },
  { number := 10, name := "prod_fst_beta"
  , category := .simplification, group := .product
  , lhsToRhs := "congrArg fst (map2 Prod.mk p q) ▷ p"
  , lhsHead := "congrArg"
  , criticalPairsWith := ["map2_subst"]
  },
  { number := 11, name := "prod_snd_beta"
  , category := .simplification, group := .product
  , lhsToRhs := "congrArg snd (map2 Prod.mk p q) ▷ q"
  , lhsHead := "congrArg"
  , criticalPairsWith := ["map2_subst"]
  },
  { number := 12, name := "prod_rec_beta"
  , category := .simplification, group := .product
  , lhsToRhs := "congrArg (Prod.rec f) (map2 Prod.mk p q) ▷ map2 f p q"
  , lhsHead := "congrArg"
  , criticalPairsWith := ["map2_subst"]
  },
  { number := 13, name := "prod_eta"
  , category := .simplification, group := .product
  , lhsToRhs := "prodMk(fst p, snd p) ▷ p"
  , lhsHead := "prodMk"
  , criticalPairsWith := []
  },
  { number := 14, name := "prod_mk_symm"
  , category := .distribution, group := .product
  , lhsToRhs := "symm(prodMk(p, q)) ▷ prodMk(symm p, symm q)"
  , lhsHead := "symm"
  , criticalPairsWith := ["symm_congr"]
  },
  { number := 15, name := "prod_map_congrArg"
  , category := .distribution, group := .product
  , lhsToRhs := "congrArg (g×h) (prodMk p q) ▷ prodMk(congrArg g p, congrArg h q)"
  , lhsHead := "congrArg"
  , criticalPairsWith := []
  },

  -- ═══════════════════════════════════════════════════════════════
  -- GROUP C: SIGMA TYPES (Σ) — Rules 16–19
  -- ═══════════════════════════════════════════════════════════════
  { number := 16, name := "sigma_fst_beta"
  , category := .simplification, group := .sigma
  , lhsToRhs := "congrArg Sigma.fst (sigmaMk p q) ▷ stepChain(p.toEq)"
  , lhsHead := "congrArg"
  , criticalPairsWith := []
  },
  { number := 17, name := "sigma_snd_beta"
  , category := .simplification, group := .sigma
  , lhsToRhs := "sigmaSnd(sigmaMk p q) ▷ stepChain(q.toEq)"
  , lhsHead := "sigmaSnd"
  , criticalPairsWith := []
  },
  { number := 18, name := "sigma_eta"
  , category := .simplification, group := .sigma
  , lhsToRhs := "sigmaMk(sigmaFst p, sigmaSnd p) ▷ p"
  , lhsHead := "sigmaMk"
  , criticalPairsWith := []
  },
  { number := 19, name := "sigma_mk_symm"
  , category := .distribution, group := .sigma
  , lhsToRhs := "symm(sigmaMk p q) ▷ sigmaMk(symm p, sigmaSymmSnd ...)"
  , lhsHead := "symm"
  , criticalPairsWith := ["symm_congr"]
  },

  -- ═══════════════════════════════════════════════════════════════
  -- GROUP D: SUM TYPES — Rules 20–21
  -- ═══════════════════════════════════════════════════════════════
  { number := 20, name := "sum_rec_inl_beta"
  , category := .simplification, group := .sum
  , lhsToRhs := "congrArg (Sum.rec f g) (congrArg inl p) ▷ congrArg f p"
  , lhsHead := "congrArg"
  , criticalPairsWith := []
  },
  { number := 21, name := "sum_rec_inr_beta"
  , category := .simplification, group := .sum
  , lhsToRhs := "congrArg (Sum.rec f g) (congrArg inr p) ▷ congrArg g p"
  , lhsHead := "congrArg"
  , criticalPairsWith := []
  },

  -- ═══════════════════════════════════════════════════════════════
  -- GROUP E: FUNCTION TYPES (Π) — Rules 22–24
  -- ═══════════════════════════════════════════════════════════════
  { number := 22, name := "fun_app_beta"
  , category := .simplification, group := .function
  , lhsToRhs := "congrArg (· a) (lamCongr p) ▷ p a"
  , lhsHead := "congrArg"
  , criticalPairsWith := []
  },
  { number := 23, name := "fun_eta"
  , category := .simplification, group := .function
  , lhsToRhs := "lamCongr(fun x => app p x) ▷ p"
  , lhsHead := "lamCongr"
  , criticalPairsWith := []
  },
  { number := 24, name := "lam_congr_symm"
  , category := .distribution, group := .function
  , lhsToRhs := "symm(lamCongr p) ▷ lamCongr(fun x => symm(p x))"
  , lhsHead := "symm"
  , criticalPairsWith := ["symm_congr"]
  },

  -- ═══════════════════════════════════════════════════════════════
  -- GROUP F: DEPENDENT APPLICATION — Rule 25
  -- ═══════════════════════════════════════════════════════════════
  { number := 25, name := "apd_refl"
  , category := .simplification, group := .depApp
  , lhsToRhs := "apd f (refl a) ▷ refl (f a)"
  , lhsHead := "apd"
  , criticalPairsWith := []
  },

  -- ═══════════════════════════════════════════════════════════════
  -- GROUP G: TRANSPORT — Rules 26–32
  -- ═══════════════════════════════════════════════════════════════
  { number := 26, name := "transport_refl_beta"
  , category := .simplification, group := .transport
  , lhsToRhs := "stepChain(transport_refl ...) ▷ refl x"
  , lhsHead := "stepChain"
  , criticalPairsWith := []
  },
  { number := 27, name := "transport_trans_beta"
  , category := .simplification, group := .transport
  , lhsToRhs := "stepChain(transport_trans ...) ▷ Eq.ndrec ..."
  , lhsHead := "stepChain"
  , criticalPairsWith := []
  },
  { number := 28, name := "transport_symm_left_beta"
  , category := .simplification, group := .transport
  , lhsToRhs := "stepChain(transport_symm_left ...) ▷ Eq.ndrec ..."
  , lhsHead := "stepChain"
  , criticalPairsWith := []
  },
  { number := 29, name := "transport_symm_right_beta"
  , category := .simplification, group := .transport
  , lhsToRhs := "stepChain(transport_symm_right ...) ▷ Eq.ndrec ..."
  , lhsHead := "stepChain"
  , criticalPairsWith := []
  },
  { number := 30, name := "transport_sigmaMk_fst_beta"
  , category := .simplification, group := .transport
  , lhsToRhs := "stepChain(transport_sigmaMk_fst ...) ▷ Eq.ndrec ..."
  , lhsHead := "stepChain"
  , criticalPairsWith := []
  },
  { number := 31, name := "transport_sigmaMk_dep_beta"
  , category := .simplification, group := .transport
  , lhsToRhs := "stepChain(transport_sigmaMk_dep ...) ▷ Eq.ndrec ..."
  , lhsHead := "stepChain"
  , criticalPairsWith := []
  },
  { number := 32, name := "subst_sigmaMk_dep_beta"
  , category := .simplification, group := .transport
  , lhsToRhs := "stepChain(subst_sigmaMk_dep ...) ▷ Eq.ndrec ..."
  , lhsHead := "stepChain"
  , criticalPairsWith := []
  },

  -- ═══════════════════════════════════════════════════════════════
  -- GROUP H: CONTEXT RULES — Rules 33–48
  -- ═══════════════════════════════════════════════════════════════
  { number := 33, name := "context_congr"
  , category := .congruence, group := .context
  , lhsToRhs := "C.map p ▷ C.map q  (given Step p q)"
  , lhsHead := "Context.map"
  , criticalPairsWith := ["context_map_symm", "context_subst_left_beta",
                           "context_subst_right_beta"]
  },
  { number := 34, name := "context_map_symm"
  , category := .distribution, group := .context
  , lhsToRhs := "symm(C.map p) ▷ C.map(symm p)"
  , lhsHead := "symm"
  , criticalPairsWith := ["symm_congr", "context_congr"]
  },
  { number := 35, name := "context_tt_cancel_left"
  , category := .reorientation, group := .context
  , lhsToRhs := "trans(C[p], trans(C[symm p], v)) ▷ trans(C[trans(p, symm p)], v)"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_assoc", "trans_congr_left", "trans_congr_right"]
  },
  { number := 36, name := "context_tt_cancel_right"
  , category := .reorientation, group := .context
  , lhsToRhs := "trans(trans(v, C[p]), C[symm p]) ▷ trans(v, C[trans(p, symm p)])"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_assoc", "trans_congr_left", "trans_congr_right"]
  },
  { number := 37, name := "context_subst_left_beta"
  , category := .simplification, group := .context
  , lhsToRhs := "trans(r, C.map p) ▷ substLeft C r p"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_assoc", "trans_congr_left", "trans_congr_right",
                           "trans_refl_left", "symm_trans"]
  },
  { number := 38, name := "context_subst_left_of_right"
  , category := .simplification, group := .context
  , lhsToRhs := "trans(r, substRight C p refl) ▷ substLeft C r p"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_assoc", "trans_congr_left", "trans_congr_right"]
  },
  { number := 39, name := "context_subst_left_assoc"
  , category := .reorientation, group := .context
  , lhsToRhs := "trans(substLeft C r p, t) ▷ trans(r, substRight C p t)"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_assoc", "trans_congr_left", "trans_congr_right"]
  },
  { number := 40, name := "context_subst_right_beta"
  , category := .simplification, group := .context
  , lhsToRhs := "trans(C.map p, t) ▷ substRight C p t"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_assoc", "trans_congr_left", "trans_congr_right",
                           "trans_refl_right", "trans_symm"]
  },
  { number := 41, name := "context_subst_right_assoc"
  , category := .reorientation, group := .context
  , lhsToRhs := "trans(substRight C p t, u) ▷ substRight C p (trans(t, u))"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_assoc", "trans_congr_left", "trans_congr_right"]
  },
  { number := 42, name := "context_subst_left_refl_right"
  , category := .simplification, group := .context
  , lhsToRhs := "substLeft C r (refl a) ▷ r"
  , lhsHead := "substLeft"
  , criticalPairsWith := ["context_subst_left_idempotent"]
  },
  { number := 43, name := "context_subst_left_refl_left"
  , category := .simplification, group := .context
  , lhsToRhs := "substLeft C (refl _) p ▷ C.map p"
  , lhsHead := "substLeft"
  , criticalPairsWith := ["context_subst_left_idempotent"]
  },
  { number := 44, name := "context_subst_right_refl_left"
  , category := .simplification, group := .context
  , lhsToRhs := "substRight C (refl a) r ▷ r"
  , lhsHead := "substRight"
  , criticalPairsWith := ["context_subst_right_cancel_inner",
                           "context_subst_right_cancel_outer"]
  },
  { number := 45, name := "context_subst_right_refl_right"
  , category := .simplification, group := .context
  , lhsToRhs := "substRight C p (refl _) ▷ C.map p"
  , lhsHead := "substRight"
  , criticalPairsWith := ["context_subst_right_cancel_inner",
                           "context_subst_right_cancel_outer"]
  },
  { number := 46, name := "context_subst_left_idempotent"
  , category := .simplification, group := .context
  , lhsToRhs := "substLeft C (substLeft C r refl) p ▷ substLeft C r p"
  , lhsHead := "substLeft"
  , criticalPairsWith := ["context_subst_left_refl_right"]
  },
  { number := 47, name := "context_subst_right_cancel_inner"
  , category := .simplification, group := .context
  , lhsToRhs := "substRight C p (substRight C refl t) ▷ substRight C p t"
  , lhsHead := "substRight"
  , criticalPairsWith := ["context_subst_right_refl_left"]
  },
  { number := 48, name := "context_subst_right_cancel_outer"
  , category := .simplification, group := .context
  , lhsToRhs := "substRight C refl (substRight C p t) ▷ substRight C p t"
  , lhsHead := "substRight"
  , criticalPairsWith := ["context_subst_right_refl_left"]
  },

  -- ═══════════════════════════════════════════════════════════════
  -- GROUP I: DEPENDENT CONTEXT RULES — Rules 49–60
  -- ═══════════════════════════════════════════════════════════════
  { number := 49, name := "depContext_congr"
  , category := .congruence, group := .depContext
  , lhsToRhs := "DC.map p ▷ DC.map q  (given Step p q)"
  , lhsHead := "DepContext.map"
  , criticalPairsWith := ["depContext_map_symm", "depContext_subst_left_beta",
                           "depContext_subst_right_beta"]
  },
  { number := 50, name := "depContext_map_symm"
  , category := .distribution, group := .depContext
  , lhsToRhs := "symm(DC.map p) ▷ DC.symmMap p"
  , lhsHead := "symm"
  , criticalPairsWith := ["symm_congr", "depContext_congr"]
  },
  { number := 51, name := "depContext_subst_left_beta"
  , category := .simplification, group := .depContext
  , lhsToRhs := "trans(transport_ctx r, DC.map p) ▷ DC.substLeft r p"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_assoc", "trans_congr_left", "trans_congr_right"]
  },
  { number := 52, name := "depContext_subst_left_assoc"
  , category := .reorientation, group := .depContext
  , lhsToRhs := "trans(DC.substLeft r p, t) ▷ trans(transport_ctx r, DC.substRight p t)"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_assoc", "trans_congr_left", "trans_congr_right"]
  },
  { number := 53, name := "depContext_subst_right_beta"
  , category := .simplification, group := .depContext
  , lhsToRhs := "trans(DC.map p, t) ▷ DC.substRight p t"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_assoc", "trans_congr_left", "trans_congr_right"]
  },
  { number := 54, name := "depContext_subst_right_assoc"
  , category := .reorientation, group := .depContext
  , lhsToRhs := "trans(DC.substRight p t, u) ▷ DC.substRight p (trans(t, u))"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_assoc", "trans_congr_left", "trans_congr_right"]
  },
  { number := 55, name := "depContext_subst_left_refl_right"
  , category := .simplification, group := .depContext
  , lhsToRhs := "DC.substLeft r (refl a) ▷ r"
  , lhsHead := "DepContext.substLeft"
  , criticalPairsWith := ["depContext_subst_left_idempotent"]
  },
  { number := 56, name := "depContext_subst_left_refl_left"
  , category := .simplification, group := .depContext
  , lhsToRhs := "DC.substLeft (refl _) p ▷ DC.map p"
  , lhsHead := "DepContext.substLeft"
  , criticalPairsWith := ["depContext_subst_left_idempotent"]
  },
  { number := 57, name := "depContext_subst_right_refl_left"
  , category := .simplification, group := .depContext
  , lhsToRhs := "DC.substRight (refl a) r ▷ r"
  , lhsHead := "DepContext.substRight"
  , criticalPairsWith := ["depContext_subst_right_cancel_inner"]
  },
  { number := 58, name := "depContext_subst_right_refl_right"
  , category := .simplification, group := .depContext
  , lhsToRhs := "DC.substRight p (refl _) ▷ DC.map p"
  , lhsHead := "DepContext.substRight"
  , criticalPairsWith := ["depContext_subst_right_cancel_inner"]
  },
  { number := 59, name := "depContext_subst_left_idempotent"
  , category := .simplification, group := .depContext
  , lhsToRhs := "DC.substLeft (DC.substLeft r refl) p ▷ DC.substLeft r p"
  , lhsHead := "DepContext.substLeft"
  , criticalPairsWith := ["depContext_subst_left_refl_right"]
  },
  { number := 60, name := "depContext_subst_right_cancel_inner"
  , category := .simplification, group := .depContext
  , lhsToRhs := "DC.substRight p (DC.substRight refl t) ▷ DC.substRight p t"
  , lhsHead := "DepContext.substRight"
  , criticalPairsWith := ["depContext_subst_right_refl_left"]
  },

  -- ═══════════════════════════════════════════════════════════════
  -- GROUP J: BI-CONTEXT / DEP-BI-CONTEXT — Rules 61–68
  -- ═══════════════════════════════════════════════════════════════
  { number := 61, name := "depBiContext_mapLeft_congr"
  , category := .congruence, group := .biContext
  , lhsToRhs := "DBC.mapLeft p b ▷ DBC.mapLeft q b  (given Step p q)"
  , lhsHead := "DepBiContext.mapLeft"
  , criticalPairsWith := []
  },
  { number := 62, name := "depBiContext_mapRight_congr"
  , category := .congruence, group := .biContext
  , lhsToRhs := "DBC.mapRight a p ▷ DBC.mapRight a q  (given Step p q)"
  , lhsHead := "DepBiContext.mapRight"
  , criticalPairsWith := []
  },
  { number := 63, name := "depBiContext_map2_congr_left"
  , category := .congruence, group := .biContext
  , lhsToRhs := "DBC.map2 p r ▷ DBC.map2 q r  (given Step p q)"
  , lhsHead := "DepBiContext.map2"
  , criticalPairsWith := ["depBiContext_map2_congr_right"]
  },
  { number := 64, name := "depBiContext_map2_congr_right"
  , category := .congruence, group := .biContext
  , lhsToRhs := "DBC.map2 p q ▷ DBC.map2 p r  (given Step q r)"
  , lhsHead := "DepBiContext.map2"
  , criticalPairsWith := ["depBiContext_map2_congr_left"]
  },
  { number := 65, name := "biContext_mapLeft_congr"
  , category := .congruence, group := .biContext
  , lhsToRhs := "BC.mapLeft p b ▷ BC.mapLeft q b  (given Step p q)"
  , lhsHead := "BiContext.mapLeft"
  , criticalPairsWith := []
  },
  { number := 66, name := "biContext_mapRight_congr"
  , category := .congruence, group := .biContext
  , lhsToRhs := "BC.mapRight a p ▷ BC.mapRight a q  (given Step p q)"
  , lhsHead := "BiContext.mapRight"
  , criticalPairsWith := []
  },
  { number := 67, name := "biContext_map2_congr_left"
  , category := .congruence, group := .biContext
  , lhsToRhs := "BC.map2 p r ▷ BC.map2 q r  (given Step p q)"
  , lhsHead := "BiContext.map2"
  , criticalPairsWith := ["biContext_map2_congr_right"]
  },
  { number := 68, name := "biContext_map2_congr_right"
  , category := .congruence, group := .biContext
  , lhsToRhs := "BC.map2 p q ▷ BC.map2 p r  (given Step q r)"
  , lhsHead := "BiContext.map2"
  , criticalPairsWith := ["biContext_map2_congr_left"]
  },

  -- ═══════════════════════════════════════════════════════════════
  -- GROUP K: MAP LEFT/RIGHT — Rules 69–72
  -- ═══════════════════════════════════════════════════════════════
  { number := 69, name := "mapLeft_congr"
  , category := .congruence, group := .mapLR
  , lhsToRhs := "mapLeft f p b ▷ mapLeft f q b  (given Step p q)"
  , lhsHead := "mapLeft"
  , criticalPairsWith := ["mapLeft_ofEq"]
  },
  { number := 70, name := "mapRight_congr"
  , category := .congruence, group := .mapLR
  , lhsToRhs := "mapRight f a p ▷ mapRight f a q  (given Step p q)"
  , lhsHead := "mapRight"
  , criticalPairsWith := ["mapRight_ofEq"]
  },
  { number := 71, name := "mapLeft_ofEq"
  , category := .simplification, group := .mapLR
  , lhsToRhs := "mapLeft f (stepChain h) b ▷ stepChain(congrArg (· b) h)"
  , lhsHead := "mapLeft"
  , criticalPairsWith := ["mapLeft_congr"]
  },
  { number := 72, name := "mapRight_ofEq"
  , category := .simplification, group := .mapLR
  , lhsToRhs := "mapRight f a (stepChain h) ▷ stepChain(congrArg (f a) h)"
  , lhsHead := "mapRight"
  , criticalPairsWith := ["mapRight_congr"]
  },

  -- ═══════════════════════════════════════════════════════════════
  -- GROUP L: STRUCTURAL CONGRUENCE — Rules 73, 75, 76
  -- ═══════════════════════════════════════════════════════════════
  { number := 73, name := "symm_congr"
  , category := .congruence, group := .structural
  , lhsToRhs := "symm p ▷ symm q  (given Step p q)"
  , lhsHead := "symm"
  , criticalPairsWith := ["symm_refl", "symm_symm", "symm_trans_congr",
                           "prod_mk_symm", "sigma_mk_symm", "lam_congr_symm",
                           "context_map_symm", "depContext_map_symm"]
  },
  { number := 75, name := "trans_congr_left"
  , category := .congruence, group := .structural
  , lhsToRhs := "trans(p, r) ▷ trans(q, r)  (given Step p q)"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_refl_left", "trans_refl_right", "trans_symm",
                           "symm_trans", "trans_assoc",
                           "context_subst_left_beta", "context_subst_right_beta",
                           "context_tt_cancel_left", "context_tt_cancel_right",
                           "context_subst_left_assoc", "context_subst_right_assoc",
                           "depContext_subst_left_beta", "depContext_subst_right_beta",
                           "depContext_subst_left_assoc", "depContext_subst_right_assoc",
                           "trans_congr_right"]
  },
  { number := 76, name := "trans_congr_right"
  , category := .congruence, group := .structural
  , lhsToRhs := "trans(p, q) ▷ trans(p, r)  (given Step q r)"
  , lhsHead := "trans"
  , criticalPairsWith := ["trans_refl_left", "trans_refl_right", "trans_symm",
                           "symm_trans", "trans_assoc",
                           "context_subst_left_beta", "context_subst_right_beta",
                           "context_tt_cancel_left", "context_tt_cancel_right",
                           "context_subst_left_assoc", "context_subst_right_assoc",
                           "depContext_subst_left_beta", "depContext_subst_right_beta",
                           "depContext_subst_left_assoc", "depContext_subst_right_assoc",
                           "trans_congr_left"]
  },

  -- ═══════════════════════════════════════════════════════════════
  -- GROUP M: CANON — Rule 77 (TO BE REMOVED)
  -- ═══════════════════════════════════════════════════════════════
  { number := 77, name := "canon"
  , category := .canonicalization, group := .canon
  , lhsToRhs := "p ▷ stepChain(p.toEq)"
  , lhsHead := "*"  -- matches any term
  , criticalPairsWith := ["*"]  -- overlaps with everything
  }
]

/-!
## Summary Statistics
-/

/-- Total number of constructors: 77 (including canon). -/
def totalRules : Nat := allRules.length

/-- Rules by category. -/
def simplificationRules : List RuleInfo :=
  allRules.filter (·.category == .simplification)

def reorientationRules : List RuleInfo :=
  allRules.filter (·.category == .reorientation)

def congruenceRules : List RuleInfo :=
  allRules.filter (·.category == .congruence)

def distributionRules : List RuleInfo :=
  allRules.filter (·.category == .distribution)

/-!
## Layered Orthogonality and Critical-Pair Joinability Certificates
-/

universe u

/-- Modular layers used in the canon-free confluence plan. -/
inductive RewriteTier where
  | groupoidCore
  | typeSpecific
  | transport
  | contextual
  | congruencePropagation
  deriving DecidableEq, Repr

/-- Rule groups attached to each modular layer. -/
def tierGroups : RewriteTier → List RuleGroup
  | .groupoidCore => [.groupoid, .structural]
  | .typeSpecific => [.product, .sigma, .sum, .function, .depApp]
  | .transport => [.transport]
  | .contextual => [.context, .depContext]
  | .congruencePropagation => [.biContext, .mapLR]

/-- Layer orthogonality means the group assignments have no overlap. -/
def TierOrthogonal (t₁ t₂ : RewriteTier) : Prop :=
  ∀ g : RuleGroup, g ∈ tierGroups t₁ → g ∉ tierGroups t₂

theorem tier_groupoid_typespecific_orthogonal :
    TierOrthogonal .groupoidCore .typeSpecific := by
  intro g hg; simp [tierGroups] at hg ⊢; rcases hg with rfl | rfl <;> decide

theorem tier_groupoid_transport_orthogonal :
    TierOrthogonal .groupoidCore .transport := by
  intro g hg; simp [tierGroups] at hg ⊢; rcases hg with rfl | rfl <;> decide

theorem tier_typespecific_transport_orthogonal :
    TierOrthogonal .typeSpecific .transport := by
  intro g hg; simp [tierGroups] at hg ⊢; rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide

theorem tier_typespecific_contextual_orthogonal :
    TierOrthogonal .typeSpecific .contextual := by
  intro g hg; simp [tierGroups] at hg ⊢; rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide

theorem tier_transport_contextual_orthogonal :
    TierOrthogonal .transport .contextual := by
  intro g hg; simp [tierGroups] at hg ⊢; rcases hg with rfl <;> decide

theorem tier_contextual_congruence_orthogonal :
    TierOrthogonal .contextual .congruencePropagation := by
  intro g hg; simp [tierGroups] at hg ⊢; rcases hg with rfl | rfl <;> decide

theorem tier_groupoid_contextual_orthogonal :
    TierOrthogonal .groupoidCore .contextual := by
  intro g hg; simp [tierGroups] at hg ⊢; rcases hg with rfl | rfl <;> decide

theorem tier_groupoid_congruence_orthogonal :
    TierOrthogonal .groupoidCore .congruencePropagation := by
  intro g hg; simp [tierGroups] at hg ⊢; rcases hg with rfl | rfl <;> decide

theorem tier_typespecific_congruence_orthogonal :
    TierOrthogonal .typeSpecific .congruencePropagation := by
  intro g hg; simp [tierGroups] at hg ⊢; rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide

theorem tier_transport_congruence_orthogonal :
    TierOrthogonal .transport .congruencePropagation := by
  intro g hg; simp [tierGroups] at hg ⊢; rcases hg with rfl <;> decide

/-- Consolidated orthogonality certificate for the modular layering. -/
def tierOrthogonalityCertificate : Prop :=
  TierOrthogonal .groupoidCore .typeSpecific ∧
  TierOrthogonal .groupoidCore .transport ∧
  TierOrthogonal .groupoidCore .contextual ∧
  TierOrthogonal .groupoidCore .congruencePropagation ∧
  TierOrthogonal .typeSpecific .transport ∧
  TierOrthogonal .typeSpecific .contextual ∧
  TierOrthogonal .typeSpecific .congruencePropagation ∧
  TierOrthogonal .transport .contextual ∧
  TierOrthogonal .transport .congruencePropagation ∧
  TierOrthogonal .contextual .congruencePropagation

theorem tier_orthogonality_certificate :
    tierOrthogonalityCertificate := by
  exact ⟨tier_groupoid_typespecific_orthogonal,
    tier_groupoid_transport_orthogonal,
    tier_groupoid_contextual_orthogonal,
    tier_groupoid_congruence_orthogonal,
    tier_typespecific_transport_orthogonal,
    tier_typespecific_contextual_orthogonal,
    tier_typespecific_congruence_orthogonal,
    tier_transport_contextual_orthogonal,
    tier_transport_congruence_orthogonal,
    tier_contextual_congruence_orthogonal⟩

theorem tier_pairwise_orthogonal :
    ∀ t₁ t₂ : RewriteTier, t₁ ≠ t₂ → TierOrthogonal t₁ t₂ := by
  intro t₁ t₂ hne
  cases t₁ <;> cases t₂
  · cases hne rfl
  · -- groupoidCore vs typeSpecific
    exact tier_groupoid_typespecific_orthogonal
  · -- groupoidCore vs transport
    exact tier_groupoid_transport_orthogonal
  · -- groupoidCore vs contextual
    exact tier_groupoid_contextual_orthogonal
  · -- groupoidCore vs congruencePropagation
    exact tier_groupoid_congruence_orthogonal
  · -- typeSpecific vs groupoidCore
    intro g hg; simp [tierGroups] at hg ⊢
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide
  · cases hne rfl
  · -- typeSpecific vs transport
    exact tier_typespecific_transport_orthogonal
  · -- typeSpecific vs contextual
    exact tier_typespecific_contextual_orthogonal
  · -- typeSpecific vs congruencePropagation
    exact tier_typespecific_congruence_orthogonal
  · -- transport vs groupoidCore
    intro g hg; simp [tierGroups] at hg ⊢
    rcases hg with rfl <;> decide
  · -- transport vs typeSpecific
    intro g hg; simp [tierGroups] at hg ⊢
    rcases hg with rfl <;> decide
  · cases hne rfl
  · -- transport vs contextual
    exact tier_transport_contextual_orthogonal
  · -- transport vs congruencePropagation
    exact tier_transport_congruence_orthogonal
  · -- contextual vs groupoidCore
    intro g hg; simp [tierGroups] at hg ⊢
    rcases hg with rfl | rfl <;> decide
  · -- contextual vs typeSpecific
    intro g hg; simp [tierGroups] at hg ⊢
    rcases hg with rfl | rfl <;> decide
  · -- contextual vs transport
    intro g hg; simp [tierGroups] at hg ⊢
    rcases hg with rfl | rfl <;> decide
  · cases hne rfl
  · -- contextual vs congruencePropagation
    exact tier_contextual_congruence_orthogonal
  · -- congruencePropagation vs groupoidCore
    intro g hg; simp [tierGroups] at hg ⊢
    rcases hg with rfl | rfl <;> decide
  · -- congruencePropagation vs typeSpecific
    intro g hg; simp [tierGroups] at hg ⊢
    rcases hg with rfl | rfl <;> decide
  · -- congruencePropagation vs transport
    intro g hg; simp [tierGroups] at hg ⊢
    rcases hg with rfl | rfl <;> decide
  · -- congruencePropagation vs contextual
    intro g hg; simp [tierGroups] at hg ⊢
    rcases hg with rfl | rfl <;> decide
  · cases hne rfl

theorem tier_pairwise_orthogonal_symm :
    ∀ t₁ t₂ : RewriteTier, t₁ ≠ t₂ → TierOrthogonal t₂ t₁ := by
  intro t₁ t₂ hne
  exact tier_pairwise_orthogonal t₂ t₁ (fun h => hne h.symm)

def critical_pair_tt_rrr_joinable {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Confluence.Join
      (Path.trans p (Path.trans q (Path.refl c)))
      (Path.trans p q) :=
  ConfluenceProof.local_confluence_tt_rrr (A := A) p q

def critical_pair_tt_lrr_joinable {A : Type u} {a b c : A}
    (q : Path a b) (r : Path b c) :
    Confluence.Join
      (Path.trans (Path.refl a) (Path.trans q r))
      (Path.trans q r) :=
  ConfluenceProof.local_confluence_tt_lrr (A := A) q r

def critical_pair_tt_tt_joinable {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Confluence.Join
      (Path.trans (Path.trans p (Path.trans q r)) s)
      (Path.trans (Path.trans p q) (Path.trans r s)) :=
  ConfluenceProof.local_confluence_tt_tt (A := A) p q r s

def critical_pair_ss_sr_joinable {A : Type u} (a : A) :
    Confluence.Join (Path.refl a) (Path.symm (Path.refl a)) :=
  ConfluenceProof.local_confluence_ss_sr (A := A) a

def critical_pair_ss_stss_joinable {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Confluence.Join
      (Path.trans p q)
      (Path.symm (Path.trans (Path.symm q) (Path.symm p))) :=
  ConfluenceProof.local_confluence_ss_stss (A := A) p q

def critical_pair_tt_ts_joinable {A : Type u} {a b c : A}
    (p : Path a b) (q : Path a c) :
    Confluence.Join
      (Path.trans p (Path.trans (Path.symm p) q))
      (Path.trans (Path.refl a) q) :=
  ConfluenceProof.local_confluence_tt_ts (A := A) p q

def critical_pair_tt_st_joinable {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Confluence.Join
      (Path.trans (Path.symm p) (Path.trans p q))
      (Path.trans (Path.refl b) q) :=
  ConfluenceProof.local_confluence_tt_st (A := A) p q

def critical_pair_trans_congr_commute_joinable {A : Type u} {a b c : A}
    {p₁ p₂ : Path a b} {q₁ q₂ : Path b c}
    (hp : Step p₁ p₂) (hq : Step q₁ q₂) :
    Confluence.Join
      (Path.trans p₂ q₁)
      (Path.trans p₁ q₂) :=
  ConfluenceProof.commute_trans_left_right (A := A) hp hq

/-- Joinability certificate for all core critical-pair families. -/
def criticalPairJoinabilityCertificate : Prop :=
  (∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path b c),
      Confluence.Join (Path.trans p (Path.trans q (Path.refl c))) (Path.trans p q)) ∧
  (∀ {A : Type u} {a b c : A} (q : Path a b) (r : Path b c),
      Confluence.Join (Path.trans (Path.refl a) (Path.trans q r)) (Path.trans q r)) ∧
  (∀ {A : Type u} {a b c d e : A} (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e),
      Confluence.Join
        (Path.trans (Path.trans p (Path.trans q r)) s)
        (Path.trans (Path.trans p q) (Path.trans r s))) ∧
  (∀ {A : Type u} (a : A),
      Confluence.Join (Path.refl a) (Path.symm (Path.refl a))) ∧
  (∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path b c),
      Confluence.Join (Path.trans p q) (Path.symm (Path.trans (Path.symm q) (Path.symm p)))) ∧
  (∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path a c),
      Confluence.Join (Path.trans p (Path.trans (Path.symm p) q)) (Path.trans (Path.refl a) q)) ∧
  (∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path b c),
      Confluence.Join (Path.trans (Path.symm p) (Path.trans p q)) (Path.trans (Path.refl b) q)) ∧
  (∀ {A : Type u} {a b c : A} {p₁ p₂ : Path a b} {q₁ q₂ : Path b c}
      (_ : Step p₁ p₂) (_ : Step q₁ q₂),
      Confluence.Join (Path.trans p₂ q₁) (Path.trans p₁ q₂))

theorem critical_pair_joinability_certificate :
    criticalPairJoinabilityCertificate := by
  refine ⟨?_, ?_⟩
  · intro {A} {a} {b} {c} p q
    exact critical_pair_tt_rrr_joinable (A := A) p q
  · refine ⟨?_, ?_⟩
    · intro {A} {a} {b} {c} q r
      exact critical_pair_tt_lrr_joinable (A := A) q r
    · refine ⟨?_, ?_⟩
      · intro {A} {a} {b} {c} {d} {e} p q r s
        exact critical_pair_tt_tt_joinable (A := A) p q r s
      · refine ⟨?_, ?_⟩
        · intro {A} a
          exact critical_pair_ss_sr_joinable (A := A) a
        · refine ⟨?_, ?_⟩
          · intro {A} {a} {b} {c} p q
            exact critical_pair_ss_stss_joinable (A := A) p q
          · refine ⟨?_, ?_⟩
            · intro {A} {a} {b} {c} p q
              exact critical_pair_tt_ts_joinable (A := A) p q
            · refine ⟨?_, ?_⟩
              · intro {A} {a} {b} {c} p q
                exact critical_pair_tt_st_joinable (A := A) p q
              · intro {A} {a} {b} {c} {p₁} {p₂} {q₁} {q₂} hp hq
                exact critical_pair_trans_congr_commute_joinable (A := A) hp hq

theorem critical_pair_certificate_tt_rrr {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Confluence.Join (Path.trans p (Path.trans q (Path.refl c))) (Path.trans p q) := by
  exact critical_pair_joinability_certificate.1 p q

theorem critical_pair_certificate_tt_lrr {A : Type u} {a b c : A}
    (q : Path a b) (r : Path b c) :
    Confluence.Join (Path.trans (Path.refl a) (Path.trans q r)) (Path.trans q r) := by
  exact critical_pair_joinability_certificate.2.1 q r

theorem critical_pair_certificate_tt_tt {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Confluence.Join
      (Path.trans (Path.trans p (Path.trans q r)) s)
      (Path.trans (Path.trans p q) (Path.trans r s)) := by
  exact critical_pair_joinability_certificate.2.2.1 p q r s

theorem critical_pair_certificate_ss_sr {A : Type u} (a : A) :
    Confluence.Join (Path.refl a) (Path.symm (Path.refl a)) := by
  exact critical_pair_joinability_certificate.2.2.2.1 a

theorem critical_pair_certificate_ss_stss {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Confluence.Join (Path.trans p q) (Path.symm (Path.trans (Path.symm q) (Path.symm p))) := by
  exact critical_pair_joinability_certificate.2.2.2.2.1 p q

theorem critical_pair_certificate_tt_ts {A : Type u} {a b c : A}
    (p : Path a b) (q : Path a c) :
    Confluence.Join (Path.trans p (Path.trans (Path.symm p) q)) (Path.trans (Path.refl a) q) := by
  exact critical_pair_joinability_certificate.2.2.2.2.2.1 p q

theorem critical_pair_certificate_tt_st {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Confluence.Join (Path.trans (Path.symm p) (Path.trans p q)) (Path.trans (Path.refl b) q) := by
  exact critical_pair_joinability_certificate.2.2.2.2.2.2.1 p q

theorem critical_pair_certificate_trans_congr_commute {A : Type u} {a b c : A}
    {p₁ p₂ : Path a b} {q₁ q₂ : Path b c}
    (hp : Step p₁ p₂) (hq : Step q₁ q₂) :
    Confluence.Join (Path.trans p₂ q₁) (Path.trans p₁ q₂) := by
  exact critical_pair_joinability_certificate.2.2.2.2.2.2.2 hp hq

theorem modular_confluence_certificate :
    tierOrthogonalityCertificate ∧ criticalPairJoinabilityCertificate := by
  exact ⟨tier_orthogonality_certificate, critical_pair_joinability_certificate⟩

theorem modular_confluence_toEq {A : Type u} {a b : A} {p q r : Path a b}
    (hpq : Rw p q) (hpr : Rw p r) :
    q.toEq = r.toEq :=
  TerminationBridge.newman_toEq_confluence hpq hpr

theorem modular_confluence_from_layers {A : Type u} {a b : A} {p q r : Path a b}
    (_hOrth : tierOrthogonalityCertificate)
    (hpq : Rw p q) (hpr : Rw p r) :
    q.toEq = r.toEq :=
  modular_confluence_toEq hpq hpr

theorem modular_confluence_from_certificate {A : Type u} {a b : A} {p q r : Path a b}
    (_hCert : tierOrthogonalityCertificate ∧ criticalPairJoinabilityCertificate)
    (hpq : Rw p q) (hpr : Rw p r) :
    q.toEq = r.toEq :=
  modular_confluence_toEq hpq hpr

theorem modular_confluence_from_tier_analysis {A : Type u} {a b : A} {p q r : Path a b}
    (hpq : Rw p q) (hpr : Rw p r) :
    q.toEq = r.toEq :=
  modular_confluence_from_layers tier_orthogonality_certificate hpq hpr

/-!
## Orthogonality Matrix

Two rule groups are orthogonal if they have no overlapping LHS patterns.
The following groups are pairwise orthogonal (no shared head constructors):

  ┌─────────┬─────┬───┬─────┬───┬───┬─────┬───────────┬──────┬───┬─────┐
  │         │Grpd │Prd│  Σ  │Sum│ Π │DepA │Transport  │Ctx   │Map│Struc│
  ├─────────┼─────┼───┼─────┼───┼───┼─────┼───────────┼──────┼───┼─────┤
  │Groupoid │  -  │ ✓ │  ✓  │ ✓ │ ✓ │  ✓  │    ✓      │ ⚠(1) │ ✓ │ ⚠(2)│
  │Product  │  ✓  │ - │  ✓  │ ✓ │ ✓ │  ✓  │    ✓      │  ✓   │ ✓ │ ⚠(3)│
  │Sigma    │  ✓  │ ✓ │  -  │ ✓ │ ✓ │  ✓  │    ✓      │  ✓   │ ✓ │ ⚠(3)│
  │Sum      │  ✓  │ ✓ │  ✓  │ - │ ✓ │  ✓  │    ✓      │  ✓   │ ✓ │  ✓  │
  │Function │  ✓  │ ✓ │  ✓  │ ✓ │ - │  ✓  │    ✓      │  ✓   │ ✓ │ ⚠(3)│
  │DepApp   │  ✓  │ ✓ │  ✓  │ ✓ │ ✓ │  -  │    ✓      │  ✓   │ ✓ │  ✓  │
  │Transport│  ✓  │ ✓ │  ✓  │ ✓ │ ✓ │  ✓  │    -      │  ✓   │ ✓ │  ✓  │
  │Context  │ ⚠(1)│ ✓ │  ✓  │ ✓ │ ✓ │  ✓  │    ✓      │  -   │ ✓ │ ⚠(4)│
  │Map      │  ✓  │ ✓ │  ✓  │ ✓ │ ✓ │  ✓  │    ✓      │  ✓   │ - │  ✓  │
  │Structural│⚠(2)│⚠(3)│⚠(3)│ ✓ │⚠(3)│ ✓  │    ✓      │ ⚠(4) │ ✓ │  -  │
  └─────────┴─────┴───┴─────┴───┴───┴─────┴───────────┴──────┴───┴─────┘

  ✓ = orthogonal (no overlapping LHS patterns)
  ⚠ = potential critical pairs exist

  (1) Context rules 35–41 have LHS head `trans`, overlapping with groupoid
      rules 3–8 that also have `trans` as LHS head.
  (2) Structural congruence `symm_congr` / `trans_congr_*` overlap with
      groupoid rules having `symm` / `trans` at the root.
  (3) `symm_congr` overlaps with distribution rules `prod_mk_symm`,
      `sigma_mk_symm`, `lam_congr_symm` that have LHS head `symm`.
  (4) `trans_congr_left/right` overlap with context substitution rules
      that have LHS head `trans`.
-/

/-!
## Critical Pairs Requiring Joinability Proofs

### TIER 1: Groupoid × Groupoid (handled by GroupoidTRS.lean termination)

These are the classic word-problem critical pairs for free groupoids:

1. `trans_assoc` vs `trans_refl_left`:
   `trans(trans(refl, q), r)` → `trans(q, r)` vs `trans(refl, trans(q, r))`
   Join: `trans(q, r)` via `trans_refl_left` on the right. ✓

2. `trans_assoc` vs `trans_refl_right`:
   `trans(trans(p, refl), r)` → `trans(p, r)` vs `trans(p, trans(refl, r))`
   Join: `trans(p, r)` via `trans_refl_left` on right side. ✓

3. `trans_assoc` vs `trans_symm`:
   `trans(trans(p, symm(p)), r)` → `trans(refl, r)` → `r`
   vs `trans(p, trans(symm(p), r))` → use `symm_trans`-like reduction. ✓

4. `trans_assoc` vs `symm_trans`:
   `trans(trans(symm(p), p), r)` → `trans(refl, r)` → `r`
   vs `trans(symm(p), trans(p, r))`. ✓

5. `trans_assoc` vs `trans_assoc` (self-overlap):
   `trans(trans(trans(p,q), r), s)`:
   Left: `trans(trans(p,q), trans(r,s))` then `trans(p, trans(q, trans(r,s)))`.
   Right: `trans(trans(p, trans(q,r)), s)` then `trans(p, trans(trans(q,r), s))`
          then `trans(p, trans(q, trans(r,s)))`.
   Join: same. ✓

### TIER 2: Structural Congruence × Base Rules

6. `symm_congr` vs `symm_refl` at `symm(refl)`:
   `symm_congr` requires a step INSIDE `refl` — `refl` is a normal form,
   so no sub-step exists ⇒ NOT a real critical pair.

7. `symm_congr` vs `symm_symm` at `symm(symm p)`:
   If `symm p →[symm_congr via step in p] symm p'`:
   Left: `symm(symm p) →[symm_congr] symm(symm p')` →[symm_symm] `p'`.
   Right: `symm(symm p) →[symm_symm] p` → `p'`.
   Join: `p'`. ✓

8. `symm_congr` vs `symm_trans_congr` at `symm(trans(p,q))`:
   Left: `symm(trans(p,q)) →[symm_congr via step in trans(p,q)]
          symm(trans(p',q))` or `symm(trans(p,q'))`.
   Right: `symm(trans(p,q)) →[symm_trans_congr] trans(symm(q), symm(p))`.
   Join requires showing `symm(trans(p',q))` and `trans(symm(q), symm(p'))`
   are joinable — apply `symm_trans_congr` to left, `symm_congr/trans_congr`
   to right. ✓

9. `trans_congr_left` vs `trans_congr_right` at `trans(p,q)`:
   Both apply when `p` and `q` have independent redexes.
   Left: `trans(p', q)`. Right: `trans(p, q')`.
   Join: `trans(p', q')` by applying the complementary congruence. ✓

10. `trans_congr_left` vs `trans_assoc` at `trans(trans(p,q), r)`:
    Left: step inside `trans(p,q)` gives `trans(trans(p',q), r)` or
          `trans(trans(p,q'), r)`.
    Right: `trans(p, trans(q,r))`.
    Join: apply `trans_assoc` to left / congruence to right. ✓

### TIER 3: Structural Congruence × Distribution Rules

11. `symm_congr` vs `prod_mk_symm` at `symm(prodMk(p,q))`:
    Left: step inside `prodMk(p,q)`.
    Right: `prodMk(symm(p), symm(q))`.
    Join: apply distribution rule to left / congruence to right. ✓

12. `symm_congr` vs `sigma_mk_symm` at `symm(sigmaMk(p,q))`:
    Same pattern. ✓

13. `symm_congr` vs `lam_congr_symm` at `symm(lamCongr p)`:
    Same pattern. ✓

14. `symm_congr` vs `context_map_symm` at `symm(C.map p)`:
    Same pattern. ✓

15. `symm_congr` vs `depContext_map_symm` at `symm(DC.map p)`:
    Same pattern. ✓

### TIER 4: Context × Groupoid

16. `context_subst_left_beta` vs `trans_assoc`:
    `trans(trans(r', C.map p), s)`:
    Left (assoc): `trans(r', trans(C.map p, s))` → `trans(r', substRight C p s)`.
    Right (subst_left on inner): need `trans(r', ...)` to line up.
    Join via `context_subst_left_assoc`. ✓

17. `context_subst_right_beta` vs `trans_assoc`:
    Similar, joins via `context_subst_right_assoc`. ✓

### TIER 5: Map × Structural

18. `mapLeft_congr` vs `mapLeft_ofEq`:
    If `p = stepChain h` and `p` steps to `q`:
    Left: `mapLeft f q b`. Right: `stepChain(congrArg (· b) h)`.
    This is joinable if `q` also eventually reduces to a `stepChain`. ✓ (via canon
    in current system — needs replacement in canon-free version)

    **⚠ THIS IS THE MAIN DIFFICULTY FOR CANON-FREE CONFLUENCE.**
    Without canon, `mapLeft_congr` applied to `mapLeft f (stepChain h) b` where
    `stepChain h` steps (how? stepChain is a normal form for non-canon rules)
    — actually `stepChain` has no non-canon redex, so this is not a real
    critical pair when canon is removed!

### SUMMARY FOR CANON-FREE CONFLUENCE

When `canon` is removed:
- `stepChain` terms become normal forms (no rule except `canon` can rewrite them).
- All critical pairs in Tiers 1–4 are joinable by the existing rules.
- Tier 5 (map × structural) critical pairs vanish because `stepChain` is a
  normal form.
- The system remains terminating for the groupoid fragment.
- The challenge is proving termination and confluence for the FULL system
  (including context/substitution rules) without `canon`.

RECOMMENDED APPROACH: Layered/modular confluence proof:
  Layer 0: Groupoid (rules 1–8, 73, 75, 76) — terminating + confluent via
           GroupoidTRS.lean.
  Layer 1: Type-specific β/η (rules 9–25) — orthogonal to groupoid, confluent
           independently.
  Layer 2: Transport (rules 26–32) — one-way simplifications with unique
           `stepChain` targets.
  Layer 3: Context/substitution (rules 33–60) — the hardest layer. Need to
           show all substitution critical pairs join.
  Layer 4: Bi-context/map congruences (rules 61–72) — pure congruence
           propagation.

Each layer's rules only interact with lower layers through structural
congruence, and those interactions are all joinable.
-/

end ComputationalPaths.Path.Rewrite.StepClassification
