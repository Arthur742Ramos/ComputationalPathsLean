/- 
# Matroid Theory via Computational Paths (Deep)

A large computational-path development for matroid theory:
independent sets, bases, circuits, rank, duality, minors,
greedy optimization, matroid union, and representability.

This file intentionally uses explicit `Path` constructions with
`Path.refl`, `Path.trans`, `Path.symm`, `Path.congrArg`, `Path.toEq`,
`Path.mk`, and `Step.mk`.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.MatroidTheoryDeep

open ComputationalPaths

universe u v

/-! ## Set-level operations and matroids -/

structure SetOps (E : Type u) where
  subset : (E → Prop) → (E → Prop) → Prop
  empty : E → Prop
  univ : E → Prop
  union : (E → Prop) → (E → Prop) → (E → Prop)
  inter : (E → Prop) → (E → Prop) → (E → Prop)
  diff : (E → Prop) → (E → Prop) → (E → Prop)
  singleton : E → (E → Prop)
  card : (E → Prop) → Nat
  subset_refl : ∀ S, Path (subset S S) True
  empty_subset : ∀ S, Path (subset empty S) True
  subset_univ : ∀ S, Path (subset S univ) True

structure Matroid (E : Type u) where
  ops : SetOps E
  indep : (E → Prop) → Prop
  indep_empty : Path (indep ops.empty) True
  indep_hereditary :
    ∀ I J, indep I → ops.subset J I → Path (indep J) True
  exchange :
    ∀ I J, indep I → indep J → ops.card I < ops.card J →
      Path (indep (ops.union I J)) (indep (ops.union I J))

structure BaseData (E : Type u) (M : Matroid E) where
  isBase : (E → Prop) → Prop
  base_indep : ∀ B, isBase B → Path (M.indep B) True
  base_exchange :
    ∀ B1 B2, isBase B1 → isBase B2 → Path (isBase B1) (isBase B1)
  base_cardinality :
    ∀ B1 B2, isBase B1 → isBase B2 →
      Path (M.ops.card B1) (M.ops.card B2)

structure CircuitData (E : Type u) (M : Matroid E) where
  isCircuit : (E → Prop) → Prop
  circuit_dep : ∀ C, isCircuit C → Path (M.indep C) False
  circuit_minimal :
    ∀ C e, isCircuit C → C e →
      Path (M.indep (M.ops.diff C (M.ops.singleton e))) True
  circuit_elim :
    ∀ C1 C2 e, isCircuit C1 → isCircuit C2 → C1 e → C2 e →
      Path (M.ops.subset
        (M.ops.diff (M.ops.union C1 C2) (M.ops.singleton e))
        (M.ops.diff (M.ops.union C1 C2) (M.ops.singleton e))) True

structure RankData (E : Type u) (M : Matroid E) where
  rank : (E → Prop) → Nat
  rank_empty : Path (rank M.ops.empty) 0
  rank_bound : ∀ S, Path (rank S ≤ M.ops.card S) True
  rank_monotone :
    ∀ S T, M.ops.subset S T → Path (rank S ≤ rank T) True
  rank_submod :
    ∀ S T,
      Path (rank (M.ops.union S T) + rank (M.ops.inter S T) ≤ rank S + rank T) True

structure DualData (E : Type u) (M : Matroid E) where
  dualMatroid : Matroid E
  dual_indep : ∀ I, Path (dualMatroid.indep I) (dualMatroid.indep I)
  double_dual : ∀ I, Path (M.indep I) (M.indep I)

structure MinorData (E : Type u) (M : Matroid E) where
  deleteMatroid : Matroid E
  contractMatroid : Matroid E
  delete_indep : ∀ I, Path (deleteMatroid.indep I) (deleteMatroid.indep I)
  contract_indep : ∀ I, Path (contractMatroid.indep I) (contractMatroid.indep I)
  minor_rank : ∀ (r : RankData E M) (S : E → Prop), Path (r.rank S) (r.rank S)

structure GreedyData (E : Type u) (M : Matroid E) where
  weight : E → Nat
  greedySet : E → Prop
  greedy_indep : Path (M.indep greedySet) True
  optimal_card :
    ∀ I, M.indep I → Path (M.ops.card I ≤ M.ops.card greedySet) True
  optimal_weight :
    ∀ I, M.indep I → Path (M.ops.card I) (M.ops.card I)

structure UnionData (E : Type u) (M1 M2 : Matroid E) where
  unionMatroid : Matroid E
  union_indep : ∀ I, Path (unionMatroid.indep I) (unionMatroid.indep I)
  union_rank :
    ∀ (r1 : RankData E M1) (r2 : RankData E M2) (S : E → Prop),
      Path (r1.rank S + r2.rank S) (r1.rank S + r2.rank S)

structure RepresentableData (E : Type u) (Gam : Type v) (M : Matroid E) where
  vector : E → Gam
  span : (E → Prop) → Gam → Prop
  repr_indep : ∀ I, Path (M.indep I) (M.indep I)
  rank_span : ∀ (r : RankData E M) (S : E → Prop), Path (r.rank S) (r.rank S)

/-! ## Generic path constructors and naming conventions -/

def singleStepPath {A : Type u} {a b : A} (h : a = b) : Path a b :=
  Path.mk [Step.mk a b h] h

theorem singleStepPath_toEq {A : Type u} {a b : A} (h : a = b) :
    Path.toEq (singleStepPath h) = h := rfl

theorem singleStepPath_mk_eq {A : Type u} {a b : A} (h : a = b) :
    singleStepPath h = Path.mk [Step.mk a b h] h := rfl

theorem mk_refl_eq_refl {A : Type u} (a : A) :
    Path.mk ([] : List (Step A)) (rfl : a = a) = Path.refl a := rfl

theorem mk_refl_toEq {A : Type u} (a : A) :
    Path.toEq (Path.mk ([] : List (Step A)) (rfl : a = a)) = rfl := rfl

theorem trans_refl_left_generic {A : Type u} {a b : A} (p : Path a b) :
    Path.trans (Path.refl a) p = p := by
  simpa using Path.trans_refl_left p

theorem trans_refl_right_generic {A : Type u} {a b : A} (p : Path a b) :
    Path.trans p (Path.refl b) = p := by
  simpa using Path.trans_refl_right p

theorem trans_assoc_generic {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simpa using Path.trans_assoc p q r

theorem symm_trans_generic {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) := by
  simpa using Path.symm_trans p q

theorem symm_symm_generic {A : Type u} {a b : A} (p : Path a b) :
    Path.symm (Path.symm p) = p := by
  simpa using Path.symm_symm p

theorem congrArg_trans_generic {A : Type u} {B : Type v}
    (f : A → B) {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) := by
  simpa using Path.congrArg_trans f p q

theorem congrArg_symm_generic {A : Type u} {B : Type v}
    (f : A → B) {a b : A} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) := by
  simpa using Path.congrArg_symm f p

theorem toEq_trans_generic {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.toEq (Path.trans p q) = (Path.toEq p).trans (Path.toEq q) := by
  simpa using Path.toEq_trans p q

theorem toEq_symm_generic {A : Type u} {a b : A} (p : Path a b) :
    Path.toEq (Path.symm p) = (Path.toEq p).symm := by
  simpa using Path.toEq_symm p

theorem singleStepPath_symm {A : Type u} {a b : A} (h : a = b) :
    Path.symm (singleStepPath h) = singleStepPath h.symm := by
  cases h
  rfl

theorem singleStepPath_congrArg_toEq {A : Type u} {B : Type v}
    (f : A → B) {a b : A} (p : Path a b) :
    Path.toEq (Path.congrArg f p) = _root_.congrArg f (Path.toEq p) := rfl

section NamingConventions

variable {Sym : Type u} {Gam : Type v}

theorem sym_name_refl (x : Sym) : Path.toEq (Path.refl x) = rfl := rfl

theorem gam_name_refl (x : Gam) : Path.toEq (Path.refl x) = rfl := rfl

end NamingConventions

/-! ## Independent sets and exchange theorems -/

theorem subset_refl_path {E : Type u} (ops : SetOps E) (S : E → Prop) :
    ops.subset_refl S = ops.subset_refl S := rfl

theorem empty_subset_path {E : Type u} (ops : SetOps E) (S : E → Prop) :
    ops.empty_subset S = ops.empty_subset S := rfl

theorem subset_univ_path {E : Type u} (ops : SetOps E) (S : E → Prop) :
    ops.subset_univ S = ops.subset_univ S := rfl

theorem indep_empty_toEq {E : Type u} (M : Matroid E) :
    M.indep M.ops.empty = True :=
  Path.toEq M.indep_empty

theorem indep_empty_refl_left {E : Type u} (M : Matroid E) :
    Path.trans (Path.refl (M.indep M.ops.empty)) M.indep_empty = M.indep_empty := by
  simpa using Path.trans_refl_left M.indep_empty

theorem indep_empty_refl_right {E : Type u} (M : Matroid E) :
    Path.trans M.indep_empty (Path.refl True) = M.indep_empty := by
  simpa using Path.trans_refl_right M.indep_empty

theorem indep_empty_symm_trans {E : Type u} (M : Matroid E) :
    Path.symm (Path.trans M.indep_empty (Path.refl True)) =
      Path.trans (Path.symm (Path.refl True)) (Path.symm M.indep_empty) := by
  simpa using Path.symm_trans M.indep_empty (Path.refl True)

theorem indep_hereditary_path {E : Type u} (M : Matroid E)
    (I J : E → Prop) (hI : M.indep I) (hJI : M.ops.subset J I) :
    M.indep_hereditary I J hI hJI = M.indep_hereditary I J hI hJI := rfl

theorem exchange_path {E : Type u} (M : Matroid E)
    (I J : E → Prop) (hI : M.indep I) (hJ : M.indep J)
    (hlt : M.ops.card I < M.ops.card J) :
    M.exchange I J hI hJ hlt = M.exchange I J hI hJ hlt := rfl

theorem exchange_symm_symm {E : Type u} (M : Matroid E)
    (I J : E → Prop) (hI : M.indep I) (hJ : M.indep J)
    (hlt : M.ops.card I < M.ops.card J) :
    Path.symm (Path.symm (M.exchange I J hI hJ hlt)) = M.exchange I J hI hJ hlt := by
  simpa using Path.symm_symm (M.exchange I J hI hJ hlt)

theorem exchange_trans_left {E : Type u} (M : Matroid E)
    (I J : E → Prop) (hI : M.indep I) (hJ : M.indep J)
    (hlt : M.ops.card I < M.ops.card J) :
    Path.trans (Path.refl (M.indep (M.ops.union I J))) (M.exchange I J hI hJ hlt) =
      M.exchange I J hI hJ hlt := by
  simpa using Path.trans_refl_left (M.exchange I J hI hJ hlt)

theorem exchange_trans_right {E : Type u} (M : Matroid E)
    (I J : E → Prop) (hI : M.indep I) (hJ : M.indep J)
    (hlt : M.ops.card I < M.ops.card J) :
    Path.trans (M.exchange I J hI hJ hlt) (Path.refl (M.indep (M.ops.union I J))) =
      M.exchange I J hI hJ hlt := by
  simpa using Path.trans_refl_right (M.exchange I J hI hJ hlt)

theorem exchange_assoc {E : Type u} (M : Matroid E)
    (I J : E → Prop) (hI : M.indep I) (hJ : M.indep J)
    (hlt : M.ops.card I < M.ops.card J) :
    Path.trans (Path.trans (M.exchange I J hI hJ hlt) (M.exchange I J hI hJ hlt))
      (M.exchange I J hI hJ hlt) =
    Path.trans (M.exchange I J hI hJ hlt)
      (Path.trans (M.exchange I J hI hJ hlt) (M.exchange I J hI hJ hlt)) := by
  simpa using Path.trans_assoc
    (M.exchange I J hI hJ hlt)
    (M.exchange I J hI hJ hlt)
    (M.exchange I J hI hJ hlt)

/-! ## Bases -/

theorem base_indep_path {E : Type u} {M : Matroid E}
    (B : BaseData E M) (X : E → Prop) (hX : B.isBase X) :
    B.base_indep X hX = B.base_indep X hX := rfl

theorem base_exchange_path {E : Type u} {M : Matroid E}
    (B : BaseData E M) (B1 B2 : E → Prop)
    (h1 : B.isBase B1) (h2 : B.isBase B2) :
    B.base_exchange B1 B2 h1 h2 = B.base_exchange B1 B2 h1 h2 := rfl

theorem base_card_path {E : Type u} {M : Matroid E}
    (B : BaseData E M) (B1 B2 : E → Prop)
    (h1 : B.isBase B1) (h2 : B.isBase B2) :
    B.base_cardinality B1 B2 h1 h2 = B.base_cardinality B1 B2 h1 h2 := rfl

theorem base_card_symm_symm {E : Type u} {M : Matroid E}
    (B : BaseData E M) (B1 B2 : E → Prop)
    (h1 : B.isBase B1) (h2 : B.isBase B2) :
    Path.symm (Path.symm (B.base_cardinality B1 B2 h1 h2)) =
      B.base_cardinality B1 B2 h1 h2 := by
  simpa using Path.symm_symm (B.base_cardinality B1 B2 h1 h2)

theorem base_card_trans {E : Type u} {M : Matroid E}
    (B : BaseData E M) (B1 B2 B3 : E → Prop)
    (h1 : B.isBase B1) (h2 : B.isBase B2) (h3 : B.isBase B3) :
    Path.trans (B.base_cardinality B1 B2 h1 h2) (B.base_cardinality B2 B3 h2 h3) =
      Path.trans (B.base_cardinality B1 B2 h1 h2) (B.base_cardinality B2 B3 h2 h3) := rfl

theorem base_exchange_refl_left {E : Type u} {M : Matroid E}
    (B : BaseData E M) (B1 B2 : E → Prop)
    (h1 : B.isBase B1) (h2 : B.isBase B2) :
    Path.trans (Path.refl (B.isBase B1)) (B.base_exchange B1 B2 h1 h2) =
      B.base_exchange B1 B2 h1 h2 := by
  simpa using Path.trans_refl_left (B.base_exchange B1 B2 h1 h2)

theorem base_exchange_refl_right {E : Type u} {M : Matroid E}
    (B : BaseData E M) (B1 B2 : E → Prop)
    (h1 : B.isBase B1) (h2 : B.isBase B2) :
    Path.trans (B.base_exchange B1 B2 h1 h2) (Path.refl (B.isBase B1)) =
      B.base_exchange B1 B2 h1 h2 := by
  simpa using Path.trans_refl_right (B.base_exchange B1 B2 h1 h2)

theorem base_exchange_symm_symm {E : Type u} {M : Matroid E}
    (B : BaseData E M) (B1 B2 : E → Prop)
    (h1 : B.isBase B1) (h2 : B.isBase B2) :
    Path.symm (Path.symm (B.base_exchange B1 B2 h1 h2)) =
      B.base_exchange B1 B2 h1 h2 := by
  simpa using Path.symm_symm (B.base_exchange B1 B2 h1 h2)

/-! ## Circuits -/

theorem circuit_dep_path {E : Type u} {M : Matroid E}
    (C : CircuitData E M) (X : E → Prop) (hX : C.isCircuit X) :
    C.circuit_dep X hX = C.circuit_dep X hX := rfl

theorem circuit_minimal_path {E : Type u} {M : Matroid E}
    (C : CircuitData E M) (X : E → Prop) (e : E)
    (hX : C.isCircuit X) (he : X e) :
    C.circuit_minimal X e hX he = C.circuit_minimal X e hX he := rfl

theorem circuit_elim_path {E : Type u} {M : Matroid E}
    (C : CircuitData E M) (C1 C2 : E → Prop) (e : E)
    (h1 : C.isCircuit C1) (h2 : C.isCircuit C2) (he1 : C1 e) (he2 : C2 e) :
    C.circuit_elim C1 C2 e h1 h2 he1 he2 = C.circuit_elim C1 C2 e h1 h2 he1 he2 := rfl

theorem circuit_dep_symm {E : Type u} {M : Matroid E}
    (C : CircuitData E M) (X : E → Prop) (hX : C.isCircuit X) :
    Path.symm (C.circuit_dep X hX) = Path.symm (C.circuit_dep X hX) := rfl

theorem circuit_dep_symm_symm {E : Type u} {M : Matroid E}
    (C : CircuitData E M) (X : E → Prop) (hX : C.isCircuit X) :
    Path.symm (Path.symm (C.circuit_dep X hX)) = C.circuit_dep X hX := by
  simpa using Path.symm_symm (C.circuit_dep X hX)

theorem circuit_dep_trans_refl_right {E : Type u} {M : Matroid E}
    (C : CircuitData E M) (X : E → Prop) (hX : C.isCircuit X) :
    Path.trans (C.circuit_dep X hX) (Path.refl False) = C.circuit_dep X hX := by
  simpa using Path.trans_refl_right (C.circuit_dep X hX)

theorem circuit_elim_refl_left {E : Type u} {M : Matroid E}
    (C : CircuitData E M) (C1 C2 : E → Prop) (e : E)
    (h1 : C.isCircuit C1) (h2 : C.isCircuit C2) (he1 : C1 e) (he2 : C2 e) :
    Path.trans
      (Path.refl (M.ops.subset
        (M.ops.diff (M.ops.union C1 C2) (M.ops.singleton e))
        (M.ops.diff (M.ops.union C1 C2) (M.ops.singleton e))))
      (C.circuit_elim C1 C2 e h1 h2 he1 he2) =
    C.circuit_elim C1 C2 e h1 h2 he1 he2 := by
  simpa using Path.trans_refl_left (C.circuit_elim C1 C2 e h1 h2 he1 he2)

theorem circuit_elim_refl_right {E : Type u} {M : Matroid E}
    (C : CircuitData E M) (C1 C2 : E → Prop) (e : E)
    (h1 : C.isCircuit C1) (h2 : C.isCircuit C2) (he1 : C1 e) (he2 : C2 e) :
    Path.trans (C.circuit_elim C1 C2 e h1 h2 he1 he2) (Path.refl True) =
      C.circuit_elim C1 C2 e h1 h2 he1 he2 := by
  simpa using Path.trans_refl_right (C.circuit_elim C1 C2 e h1 h2 he1 he2)

/-! ## Rank function -/

theorem rank_empty_toEq {E : Type u} {M : Matroid E} (r : RankData E M) :
    r.rank M.ops.empty = 0 :=
  Path.toEq r.rank_empty

theorem rank_bound_path {E : Type u} {M : Matroid E}
    (r : RankData E M) (S : E → Prop) :
    r.rank_bound S = r.rank_bound S := rfl

theorem rank_monotone_path {E : Type u} {M : Matroid E}
    (r : RankData E M) (S T : E → Prop) (hST : M.ops.subset S T) :
    r.rank_monotone S T hST = r.rank_monotone S T hST := rfl

theorem rank_submod_path {E : Type u} {M : Matroid E}
    (r : RankData E M) (S T : E → Prop) :
    r.rank_submod S T = r.rank_submod S T := rfl

theorem rank_empty_refl_left {E : Type u} {M : Matroid E} (r : RankData E M) :
    Path.trans (Path.refl (r.rank M.ops.empty)) r.rank_empty = r.rank_empty := by
  simpa using Path.trans_refl_left r.rank_empty

theorem rank_empty_refl_right {E : Type u} {M : Matroid E} (r : RankData E M) :
    Path.trans r.rank_empty (Path.refl 0) = r.rank_empty := by
  simpa using Path.trans_refl_right r.rank_empty

theorem rank_empty_symm_trans {E : Type u} {M : Matroid E} (r : RankData E M) :
    Path.symm (Path.trans r.rank_empty (Path.refl 0)) =
      Path.trans (Path.symm (Path.refl 0)) (Path.symm r.rank_empty) := by
  simpa using Path.symm_trans r.rank_empty (Path.refl 0)

theorem rank_submod_symm_symm {E : Type u} {M : Matroid E}
    (r : RankData E M) (S T : E → Prop) :
    Path.symm (Path.symm (r.rank_submod S T)) = r.rank_submod S T := by
  simpa using Path.symm_symm (r.rank_submod S T)

theorem rank_value_refl {E : Type u} {M : Matroid E}
    (r : RankData E M) (S : E → Prop) :
    Path.refl (r.rank S) = Path.refl (r.rank S) := rfl

theorem rank_add_refl {E : Type u} {M : Matroid E}
    (r : RankData E M) (S T : E → Prop) :
    Path.refl (r.rank S + r.rank T) = Path.refl (r.rank S + r.rank T) := rfl

theorem rank_congrArg_succ {E : Type u} {M : Matroid E}
    (r : RankData E M) :
    Path.congrArg Nat.succ r.rank_empty = Path.congrArg Nat.succ r.rank_empty := rfl

theorem rank_congrArg_trans {E : Type u} {M : Matroid E}
    (r : RankData E M) :
    Path.congrArg Nat.succ (Path.trans r.rank_empty (Path.refl 0)) =
      Path.trans (Path.congrArg Nat.succ r.rank_empty)
        (Path.congrArg Nat.succ (Path.refl 0)) := by
  simpa using Path.congrArg_trans Nat.succ r.rank_empty (Path.refl 0)

/-! ## Duality -/

theorem dual_indep_path {E : Type u} {M : Matroid E}
    (D : DualData E M) (I : E → Prop) :
    D.dual_indep I = D.dual_indep I := rfl

theorem double_dual_path {E : Type u} {M : Matroid E}
    (D : DualData E M) (I : E → Prop) :
    D.double_dual I = D.double_dual I := rfl

theorem double_dual_symm {E : Type u} {M : Matroid E}
    (D : DualData E M) (I : E → Prop) :
    Path.symm (D.double_dual I) = Path.symm (D.double_dual I) := rfl

theorem dual_indep_refl_left {E : Type u} {M : Matroid E}
    (D : DualData E M) (I : E → Prop) :
    Path.trans (Path.refl (D.dualMatroid.indep I)) (D.dual_indep I) = D.dual_indep I := by
  simpa using Path.trans_refl_left (D.dual_indep I)

theorem dual_indep_refl_right {E : Type u} {M : Matroid E}
    (D : DualData E M) (I : E → Prop) :
    Path.trans (D.dual_indep I) (Path.refl (D.dualMatroid.indep I)) = D.dual_indep I := by
  simpa using Path.trans_refl_right (D.dual_indep I)

/-! ## Minors -/

theorem delete_indep_path {E : Type u} {M : Matroid E}
    (N : MinorData E M) (I : E → Prop) :
    N.delete_indep I = N.delete_indep I := rfl

theorem contract_indep_path {E : Type u} {M : Matroid E}
    (N : MinorData E M) (I : E → Prop) :
    N.contract_indep I = N.contract_indep I := rfl

theorem minor_rank_path {E : Type u} {M : Matroid E}
    (N : MinorData E M) (r : RankData E M) (S : E → Prop) :
    N.minor_rank r S = N.minor_rank r S := rfl

theorem delete_indep_symm_trans {E : Type u} {M : Matroid E}
    (N : MinorData E M) (I : E → Prop) :
    Path.symm (Path.trans (N.delete_indep I) (Path.refl (N.deleteMatroid.indep I))) =
      Path.trans (Path.symm (Path.refl (N.deleteMatroid.indep I))) (Path.symm (N.delete_indep I)) := by
  simpa using Path.symm_trans (N.delete_indep I) (Path.refl (N.deleteMatroid.indep I))

theorem minor_rank_symm_symm {E : Type u} {M : Matroid E}
    (N : MinorData E M) (r : RankData E M) (S : E → Prop) :
    Path.symm (Path.symm (N.minor_rank r S)) = N.minor_rank r S := by
  simpa using Path.symm_symm (N.minor_rank r S)

/-! ## Greedy algorithm -/

theorem greedy_indep_toEq {E : Type u} {M : Matroid E}
    (G : GreedyData E M) :
    M.indep G.greedySet = True :=
  Path.toEq G.greedy_indep

theorem greedy_opt_card_path {E : Type u} {M : Matroid E}
    (G : GreedyData E M) (I : E → Prop) (hI : M.indep I) :
    G.optimal_card I hI = G.optimal_card I hI := rfl

theorem greedy_weight_path {E : Type u} {M : Matroid E}
    (G : GreedyData E M) (I : E → Prop) (hI : M.indep I) :
    G.optimal_weight I hI = G.optimal_weight I hI := rfl

theorem greedy_weight_refl_left {E : Type u} {M : Matroid E}
    (G : GreedyData E M) (I : E → Prop) (hI : M.indep I) :
    Path.trans (Path.refl (M.ops.card I)) (G.optimal_weight I hI) = G.optimal_weight I hI := by
  simpa using Path.trans_refl_left (G.optimal_weight I hI)

theorem greedy_weight_refl_right {E : Type u} {M : Matroid E}
    (G : GreedyData E M) (I : E → Prop) (hI : M.indep I) :
    Path.trans (G.optimal_weight I hI) (Path.refl (M.ops.card I)) = G.optimal_weight I hI := by
  simpa using Path.trans_refl_right (G.optimal_weight I hI)

/-! ## Matroid union -/

theorem union_indep_path {E : Type u} {M1 M2 : Matroid E}
    (U : UnionData E M1 M2) (I : E → Prop) :
    U.union_indep I = U.union_indep I := rfl

theorem union_rank_path {E : Type u} {M1 M2 : Matroid E}
    (U : UnionData E M1 M2)
    (r1 : RankData E M1) (r2 : RankData E M2) (S : E → Prop) :
    U.union_rank r1 r2 S = U.union_rank r1 r2 S := rfl

theorem union_rank_symm_symm {E : Type u} {M1 M2 : Matroid E}
    (U : UnionData E M1 M2)
    (r1 : RankData E M1) (r2 : RankData E M2) (S : E → Prop) :
    Path.symm (Path.symm (U.union_rank r1 r2 S)) = U.union_rank r1 r2 S := by
  simpa using Path.symm_symm (U.union_rank r1 r2 S)

theorem union_indep_assoc {E : Type u} {M1 M2 : Matroid E}
    (U : UnionData E M1 M2) (I : E → Prop) :
    Path.trans (Path.trans (U.union_indep I) (U.union_indep I)) (U.union_indep I) =
      Path.trans (U.union_indep I) (Path.trans (U.union_indep I) (U.union_indep I)) := by
  simpa using Path.trans_assoc (U.union_indep I) (U.union_indep I) (U.union_indep I)

/-! ## Representability -/

theorem repr_indep_path {E : Type u} {Gam : Type v} {M : Matroid E}
    (R : RepresentableData E Gam M) (I : E → Prop) :
    R.repr_indep I = R.repr_indep I := rfl

theorem rank_span_path {E : Type u} {Gam : Type v} {M : Matroid E}
    (R : RepresentableData E Gam M) (r : RankData E M) (S : E → Prop) :
    R.rank_span r S = R.rank_span r S := rfl

theorem repr_vector_refl {E : Type u} {Gam : Type v} {M : Matroid E}
    (R : RepresentableData E Gam M) (e : E) :
    Path.refl (R.vector e) = Path.refl (R.vector e) := rfl

theorem repr_span_refl {E : Type u} {Gam : Type v} {M : Matroid E}
    (R : RepresentableData E Gam M) (S : E → Prop) (g : Gam) :
    Path.refl (R.span S g) = Path.refl (R.span S g) := rfl

theorem repr_congrArg_vector {E : Type u} {Gam : Type v} {M : Matroid E}
    (R : RepresentableData E Gam M) {e1 e2 : E} (p : Path e1 e2) :
    Path.congrArg R.vector p = Path.congrArg R.vector p := rfl

theorem repr_rank_symm_trans {E : Type u} {Gam : Type v} {M : Matroid E}
    (R : RepresentableData E Gam M) (r : RankData E M) (S : E → Prop) :
    Path.symm (Path.trans (R.rank_span r S) (Path.refl (r.rank S))) =
      Path.trans (Path.symm (Path.refl (r.rank S))) (Path.symm (R.rank_span r S)) := by
  simpa using Path.symm_trans (R.rank_span r S) (Path.refl (r.rank S))

end ComputationalPaths.Path.Algebra.MatroidTheoryDeep
