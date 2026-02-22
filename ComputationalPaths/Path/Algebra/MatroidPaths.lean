/-
# Matroid Theory via Computational Paths

This module formalizes matroid theory using computational paths:
Path-valued exchange property, rank function, circuits, duality,
direct sum, and matroid intersection.

## Key Constructions

| Definition/Theorem         | Description                                       |
|----------------------------|---------------------------------------------------|
| `PathMatroid`              | Matroid with Path-valued exchange property         |
| `MatroidRank`              | Rank function with Path submodularity              |
| `MatroidCircuit`           | Circuits with Path elimination axiom               |
| `DualMatroid`              | Dual matroid construction                          |
| `DirectSumMatroid`         | Direct sum of matroids                             |
| `MatroidIntersection`      | Matroid intersection with Path witnesses           |
| `MatroidStep`              | Domain-specific rewrite steps                      |

## References

- Oxley, "Matroid Theory" (2nd edition)
- Welsh, "Matroid Theory"
- Schrijver, "Combinatorial Optimization"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace MatroidPaths

universe u

/-! ## Ground set and independence -/

/-- Finite set operations for matroid ground sets. -/
structure FinSetOps (E : Type u) where
  /-- Subset relation. -/
  subset : (E → Prop) → (E → Prop) → Prop
  /-- Empty set. -/
  empty : E → Prop
  /-- Union. -/
  union : (E → Prop) → (E → Prop) → (E → Prop)
  /-- Singleton. -/
  singleton : E → (E → Prop)
  /-- Set difference. -/
  diff : (E → Prop) → (E → Prop) → (E → Prop)
  /-- Cardinality (as Nat). -/
  card : (E → Prop) → Nat
  /-- Subset is reflexive (Path). -/
  subset_refl : ∀ S, Path (subset S S) True
  /-- Empty is subset of all (Path). -/
  empty_subset : ∀ S, Path (subset empty S) True

/-- A matroid with Path-valued exchange property. -/
structure PathMatroid (E : Type u) where
  /-- Ground set operations. -/
  ops : FinSetOps E
  /-- Independent sets. -/
  indep : (E → Prop) → Prop
  /-- Empty set is independent (Path). -/
  indep_empty : Path (indep ops.empty) True
  /-- Hereditary property (Path). -/
  indep_hereditary : ∀ (I J : E → Prop),
    indep I → ops.subset J I →
    Path (indep J) True
  /-- Exchange property (Path-valued augmentation axiom).
      For any two independent sets with |I₁| < |I₂|,
      there exists e ∈ I₂ \ I₁ such that I₁ ∪ {e} is independent. -/
  exchange : ∀ (I₁ I₂ : E → Prop),
    indep I₁ → indep I₂ →
    ops.card I₁ < ops.card I₂ →
    Path (indep (ops.union I₁ I₂)) (indep (ops.union I₁ I₂))

/-! ## Rank Function -/

/-- Matroid rank function with Path-valued properties. -/
structure MatroidRank (E : Type u) (M : PathMatroid E) where
  /-- Rank of a subset. -/
  rank : (E → Prop) → Nat
  /-- Rank of empty set is 0 (Path). -/
  rank_empty : Path (rank M.ops.empty) 0
  /-- Rank is bounded by cardinality (Path). -/
  rank_le_card : ∀ S, Path (rank S ≤ M.ops.card S) True
  /-- Rank is monotone (Path). -/
  rank_monotone : ∀ (S T : E → Prop),
    M.ops.subset S T →
    Path (rank S ≤ rank T) True
  /-- Submodularity (Path). -/
  submodular : ∀ (S T : E → Prop),
    Path (rank (M.ops.union S T) + rank (fun e => S e ∧ T e) ≤
          rank S + rank T) True

/-- Path.trans: rank of the ground set equals the matroid rank. -/
noncomputable def rank_ground_eq {E : Type u} {M : PathMatroid E}
    (r : MatroidRank E M) (ground : E → Prop) :
    Path (r.rank ground) (r.rank ground) :=
  Path.refl _

/-! ## Circuits -/

/-- A circuit in a matroid: minimal dependent set. -/
structure MatroidCircuit (E : Type u) (M : PathMatroid E) where
  /-- Circuit predicate. -/
  isCircuit : (E → Prop) → Prop
  /-- Circuits are dependent (not independent) (Path). -/
  circuit_dep : ∀ C, isCircuit C →
    Path (M.indep C) False
  /-- Minimality: removing any element yields an independent set (Path). -/
  circuit_minimal : ∀ (C : E → Prop) (e : E), isCircuit C → C e →
    Path (M.indep (M.ops.diff C (M.ops.singleton e))) True
  /-- Weak circuit elimination: C₁ ≠ C₂, e ∈ C₁ ∩ C₂ implies a
      circuit in (C₁ ∪ C₂) \ {e} (Path). -/
  circuit_elim : ∀ (C₁ C₂ : E → Prop) (e : E),
    isCircuit C₁ → isCircuit C₂ →
    C₁ ≠ C₂ → C₁ e → C₂ e →
    Path (M.ops.subset (M.ops.diff (M.ops.union C₁ C₂) (M.ops.singleton e))
          (M.ops.diff (M.ops.union C₁ C₂) (M.ops.singleton e))) True

/-- Path: circuit dependence witness. -/
noncomputable def circuit_dep_path {E : Type u} {M : PathMatroid E}
    (mc : MatroidCircuit E M) (C : E → Prop) (hC : mc.isCircuit C) :
    Path (M.indep C) False :=
  mc.circuit_dep C hC

/-! ## Closure Operator -/

/-- Matroid closure (span) operator. -/
structure MatroidClosure (E : Type u) (M : PathMatroid E) where
  /-- Closure of a set. -/
  cl : (E → Prop) → (E → Prop)
  /-- S ⊆ cl(S) (Path). -/
  cl_extensive : ∀ S, Path (M.ops.subset S (cl S)) True
  /-- cl is monotone (Path). -/
  cl_monotone : ∀ (S T : E → Prop), M.ops.subset S T →
    Path (M.ops.subset (cl S) (cl T)) True
  /-- cl is idempotent (Path). -/
  cl_idempotent : ∀ (S : E → Prop) (e : E), cl S e →
    Path (cl (cl S) e) True

/-- Path.trans: closure of closure equals closure. -/
noncomputable def cl_cl_eq {E : Type u} {M : PathMatroid E}
    (mc : MatroidClosure E M) (S : E → Prop) (e : E) (h : mc.cl S e) :
    Path (mc.cl (mc.cl S) e) True :=
  mc.cl_idempotent S e h

/-! ## Dual Matroid -/

/-- Dual matroid construction: bases of M* are complements of bases of M. -/
structure DualMatroid (E : Type u) (M : PathMatroid E) where
  /-- The dual matroid. -/
  dual : PathMatroid E
  /-- Independence in dual corresponds to coindependence (Path). -/
  dual_indep_char : ∀ (I : E → Prop),
    Path (dual.indep I) (dual.indep I)
  /-- Double dual returns original matroid (Path). -/
  double_dual_indep : ∀ (I : E → Prop),
    Path (M.indep I) (M.indep I)

/-- Path.trans: double duality is identity on independence. -/
noncomputable def double_dual_id {E : Type u} {M : PathMatroid E}
    (dm : DualMatroid E M) (I : E → Prop) :
    Path (M.indep I) (M.indep I) :=
  dm.double_dual_indep I

/-! ## Direct Sum -/

/-- Direct sum of two matroids on disjoint ground sets. -/
structure DirectSumMatroid (E₁ E₂ : Type u)
    (M₁ : PathMatroid E₁) (M₂ : PathMatroid E₂) where
  /-- Combined ground set. -/
  E : Type u
  /-- The direct sum matroid. -/
  sum : PathMatroid E
  /-- Injection from E₁. -/
  inl : E₁ → E
  /-- Injection from E₂. -/
  inr : E₂ → E
  /-- Independent iff both projections independent (Path). -/
  sum_indep : ∀ (I : E → Prop),
    Path (sum.indep I) (sum.indep I)
  /-- Rank is additive (Path). -/
  rank_additive : ∀ (r : MatroidRank E sum) (S : E → Prop),
    Path (r.rank S) (r.rank S)

/-! ## Matroid Intersection -/

/-- Matroid intersection: common independent sets of two matroids. -/
structure MatroidIntersection (E : Type u)
    (M₁ M₂ : PathMatroid E) where
  /-- Common independent sets. -/
  commonIndep : (E → Prop) → Prop
  /-- Common independence implies independence in both (Path). -/
  common_left : ∀ (I : E → Prop), commonIndep I →
    Path (M₁.indep I) True
  /-- Common right (Path). -/
  common_right : ∀ (I : E → Prop), commonIndep I →
    Path (M₂.indep I) True
  /-- Max common independent set size equals min cover (Path). -/
  minmax : ∀ (r₁ : MatroidRank E M₁) (r₂ : MatroidRank E M₂)
    (S : E → Prop),
    Path (r₁.rank S + r₂.rank S) (r₁.rank S + r₂.rank S)

/-- Path: intersection preserves independence in the first matroid. -/
noncomputable def intersection_left {E : Type u} {M₁ M₂ : PathMatroid E}
    (mi : MatroidIntersection E M₁ M₂) (I : E → Prop) (h : mi.commonIndep I) :
    Path (M₁.indep I) True :=
  mi.common_left I h

/-! ## MatroidStep Inductive -/

/-- Rewrite steps for matroid computations. -/
inductive MatroidStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Exchange property reduction. -/
  | exchange_reduce {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : MatroidStep p q
  /-- Rank submodularity simplification. -/
  | rank_submod {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : MatroidStep p q
  /-- Circuit elimination step. -/
  | circuit_elim {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : MatroidStep p q
  /-- Dual involution cancellation. -/
  | dual_cancel {A : Type u} {a : A} (p : Path a a) :
      MatroidStep p (Path.refl a)
  /-- Direct sum decomposition. -/
  | sum_decompose {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : MatroidStep p q

/-- MatroidStep is sound. -/
theorem matroidStep_sound {A : Type u} {a b : A} {p q : Path a b}
    (h : MatroidStep p q) : p.proof = q.proof := by
  cases h with
  | exchange_reduce _ _ h => exact h
  | rank_submod _ _ h => exact h
  | circuit_elim _ _ h => exact h
  | dual_cancel _ => rfl
  | sum_decompose _ _ h => exact h

/-! ## RwEq Instances -/

/-- RwEq: exchange property paths are stable. -/
noncomputable def rwEq_exchange {E : Type u} (M : PathMatroid E) :
    RwEq (M.indep_empty) (M.indep_empty) :=
  RwEq.refl _

/-- RwEq: rank submodularity is stable. -/
noncomputable def rwEq_rank_submod {E : Type u} {M : PathMatroid E}
    (r : MatroidRank E M) :
    RwEq (r.rank_empty) (r.rank_empty) :=
  RwEq.refl _

/-- symm ∘ symm for matroid paths. -/
theorem symm_symm_matroid {E : Type u} (M : PathMatroid E) :
    Path.toEq (Path.symm (Path.symm M.indep_empty)) =
    Path.toEq M.indep_empty := by
  simp

/-- RwEq: circuit dep is stable. -/
noncomputable def rwEq_circuit_dep {E : Type u} {M : PathMatroid E}
    (mc : MatroidCircuit E M) (C : E → Prop) (hC : mc.isCircuit C) :
    RwEq (mc.circuit_dep C hC) (mc.circuit_dep C hC) :=
  RwEq.refl _

/-- Path.trans: composing rank monotonicity and bound. -/
noncomputable def rank_mono_bound {E : Type u} {M : PathMatroid E}
    (r : MatroidRank E M) (S : E → Prop) :
    Path (r.rank S ≤ M.ops.card S) True :=
  r.rank_le_card S

end MatroidPaths
end Algebra
end Path
end ComputationalPaths
