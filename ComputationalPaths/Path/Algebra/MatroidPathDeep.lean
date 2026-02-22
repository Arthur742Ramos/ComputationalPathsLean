/-
  ComputationalPaths/Path/Algebra/MatroidPathDeep.lean

  Matroid Theory via Computational Paths
  =======================================

  Matroid theory modeled via rank functions, closure operators, and
  structural operations, with all identities witnessed by computational Paths.

  Path operates on Type u, so we model matroid operations through their
  concrete outputs (Nat ranks, set-valued closures, structure-valued data)
  rather than through Prop-valued predicates.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.MatroidPathDeep

open ComputationalPaths.Path

universe u v

-- ============================================================================
-- § 1. Matroid via Rank Functions
-- ============================================================================

/-- A rank function on subsets of a finite ground set -/
structure RankFn (n : Nat) where
  rank : (Fin n → Bool) → Nat
  rank_empty : rank (fun _ => false) = 0
  rank_le_card : ∀ S, rank S ≤ n
  rank_mono : ∀ S T, (∀ i, S i = true → T i = true) → rank S ≤ rank T

/-- Closure operator returning a set -/
structure ClosureOp (n : Nat) where
  cl : (Fin n → Bool) → (Fin n → Bool)
  extensive : ∀ S i, S i = true → cl S i = true
  monotone : ∀ S T, (∀ i, S i = true → T i = true) → ∀ i, cl S i = true → cl T i = true
  idempotent : ∀ S, cl (cl S) = cl S

/-- A matroid combining rank and closure -/
structure MatroidOps (n : Nat) where
  rankFn : RankFn n
  closureOp : ClosureOp n

-- ============================================================================
-- § 2. Rank Function Paths
-- ============================================================================

-- 1: Rank of empty set
noncomputable def rank_empty_path (n : Nat) (r : RankFn n) :
    Path (r.rank (fun _ => false)) 0 :=
  Path.mk [Step.mk _ _ r.rank_empty] r.rank_empty

-- 2: Rank empty composed with successor
noncomputable def rank_empty_succ (n : Nat) (r : RankFn n) :
    Path (Nat.succ (r.rank (fun _ => false))) (Nat.succ 0) :=
  Path.congrArg Nat.succ (rank_empty_path n r)

-- 3: Rank empty composed with addition
noncomputable def rank_empty_add (n : Nat) (r : RankFn n) (k : Nat) :
    Path (r.rank (fun _ => false) + k) (0 + k) :=
  Path.congrArg (· + k) (rank_empty_path n r)

-- 4: Double successor of rank empty
noncomputable def rank_empty_succ_succ (n : Nat) (r : RankFn n) :
    Path (Nat.succ (Nat.succ (r.rank (fun _ => false)))) (Nat.succ (Nat.succ 0)) :=
  Path.congrArg Nat.succ (rank_empty_succ n r)

-- 5: Rank of same set via two rank functions
noncomputable def rank_transfer (n : Nat) (r1 r2 : RankFn n) (S : Fin n → Bool)
    (h : r1.rank S = r2.rank S) :
    Path (r1.rank S) (r2.rank S) :=
  Path.mk [Step.mk _ _ h] h

-- 6: Rank transfer composed with function
noncomputable def rank_transfer_map (n : Nat) (r1 r2 : RankFn n) (S : Fin n → Bool)
    (h : r1.rank S = r2.rank S) (f : Nat → Nat) :
    Path (f (r1.rank S)) (f (r2.rank S)) :=
  Path.congrArg f (rank_transfer n r1 r2 S h)

-- ============================================================================
-- § 3. Closure Operator Paths
-- ============================================================================

-- 7: Closure idempotency
noncomputable def closure_idem (n : Nat) (c : ClosureOp n) (S : Fin n → Bool) :
    Path (c.cl (c.cl S)) (c.cl S) :=
  Path.mk [Step.mk _ _ (c.idempotent S)] (c.idempotent S)

-- 8: Triple closure
noncomputable def closure_triple (n : Nat) (c : ClosureOp n) (S : Fin n → Bool) :
    Path (c.cl (c.cl (c.cl S))) (c.cl S) :=
  Path.trans
    (Path.congrArg c.cl (closure_idem n c S))
    (closure_idem n c S)

-- 9: Quadruple closure
noncomputable def closure_quad (n : Nat) (c : ClosureOp n) (S : Fin n → Bool) :
    Path (c.cl (c.cl (c.cl (c.cl S)))) (c.cl S) :=
  Path.trans
    (Path.congrArg c.cl (closure_triple n c S))
    (closure_idem n c S)

-- 10: Quintuple closure
noncomputable def closure_quint (n : Nat) (c : ClosureOp n) (S : Fin n → Bool) :
    Path (c.cl (c.cl (c.cl (c.cl (c.cl S))))) (c.cl S) :=
  Path.trans
    (Path.congrArg c.cl (closure_quad n c S))
    (closure_idem n c S)

-- 11: Closure as functor
noncomputable def closure_map (n : Nat) (c : ClosureOp n) (S T : Fin n → Bool)
    (p : Path S T) : Path (c.cl S) (c.cl T) :=
  Path.congrArg c.cl p

-- 12: Double closure map
noncomputable def closure_map_double (n : Nat) (c : ClosureOp n) (S T : Fin n → Bool)
    (p : Path S T) : Path (c.cl (c.cl S)) (c.cl (c.cl T)) :=
  Path.congrArg c.cl (closure_map n c S T p)

-- 13: Pointwise closure identity
noncomputable def closure_pointwise_idem (n : Nat) (c : ClosureOp n) :
    Path (fun S => c.cl (c.cl S)) (fun S => c.cl S) :=
  Path.mk [Step.mk _ _ (funext (fun S => c.idempotent S))] (funext (fun S => c.idempotent S))

-- ============================================================================
-- § 4. Flat Paths (fixed points of closure)
-- ============================================================================

-- 14: Flat closure identity
noncomputable def flat_cl_identity (n : Nat) (c : ClosureOp n) (F : Fin n → Bool)
    (hF : c.cl F = F) : Path (c.cl F) F :=
  Path.mk [Step.mk _ _ hF] hF

-- 15: Flat double application
noncomputable def flat_double (n : Nat) (c : ClosureOp n) (F : Fin n → Bool)
    (hF : c.cl F = F) : Path (c.cl (c.cl F)) F :=
  Path.trans (closure_idem n c F) (flat_cl_identity n c F hF)

-- 16: Flat triple application
noncomputable def flat_triple (n : Nat) (c : ClosureOp n) (F : Fin n → Bool)
    (hF : c.cl F = F) : Path (c.cl (c.cl (c.cl F))) F :=
  Path.trans (closure_triple n c F) (flat_cl_identity n c F hF)

-- ============================================================================
-- § 5. Matroid Duality via Rank
-- ============================================================================

/-- Dual rank function: r*(S) = |S| - r(E) + r(complement(S)) -/
structure DualRankData (n : Nat) where
  primal : RankFn n
  dual : RankFn n
  complement : (Fin n → Bool) → (Fin n → Bool)
  compl_invol : ∀ S, complement (complement S) = S

-- 17: Complement involution
noncomputable def compl_invol_path (n : Nat) (d : DualRankData n) (S : Fin n → Bool) :
    Path (d.complement (d.complement S)) S :=
  Path.mk [Step.mk _ _ (d.compl_invol S)] (d.compl_invol S)

-- 18: Double complement via congrArg
noncomputable def compl_double_map (n : Nat) (d : DualRankData n) (S : Fin n → Bool) :
    Path (d.complement (d.complement (d.complement (d.complement S)))) S :=
  Path.trans
    (Path.congrArg d.complement (Path.congrArg d.complement (compl_invol_path n d S)))
    (compl_invol_path n d S)

-- 19: Biduality for rank
noncomputable def biduality_rank (n : Nat) (d : DualRankData n) (S : Fin n → Bool)
    (h : d.dual.rank (d.complement S) = d.primal.rank S) :
    Path (d.dual.rank (d.complement S)) (d.primal.rank S) :=
  Path.mk [Step.mk _ _ h] h

-- 20: Biduality composed with successor
noncomputable def biduality_rank_succ (n : Nat) (d : DualRankData n) (S : Fin n → Bool)
    (h : d.dual.rank (d.complement S) = d.primal.rank S) :
    Path (Nat.succ (d.dual.rank (d.complement S))) (Nat.succ (d.primal.rank S)) :=
  Path.congrArg Nat.succ (biduality_rank n d S h)

-- ============================================================================
-- § 6. Direct Sum Rank
-- ============================================================================

/-- Direct sum: rank of disjoint union is sum of ranks -/
structure DirectSumRank (n m : Nat) where
  r1 : RankFn n
  r2 : RankFn m
  combined_rank : (Fin n → Bool) → (Fin m → Bool) → Nat
  additivity : ∀ S T, combined_rank S T = r1.rank S + r2.rank T

-- 21: Direct sum additivity
noncomputable def direct_sum_add (n m : Nat) (ds : DirectSumRank n m)
    (S : Fin n → Bool) (T : Fin m → Bool) :
    Path (ds.combined_rank S T) (ds.r1.rank S + ds.r2.rank T) :=
  Path.mk [Step.mk _ _ (ds.additivity S T)] (ds.additivity S T)

-- 22: Direct sum empty sets
noncomputable def direct_sum_empty (n m : Nat) (ds : DirectSumRank n m) :
    Path (ds.combined_rank (fun _ => false) (fun _ => false))
         (ds.r1.rank (fun _ => false) + ds.r2.rank (fun _ => false)) :=
  direct_sum_add n m ds (fun _ => false) (fun _ => false)

-- 23: Direct sum empty with rank_empty
noncomputable def direct_sum_empty_zero (n m : Nat) (ds : DirectSumRank n m) :
    Path (ds.r1.rank (fun _ => false) + ds.r2.rank (fun _ => false)) (0 + 0) :=
  have h : ds.r1.rank (fun _ => false) + ds.r2.rank (fun _ => false) = 0 + 0 := by
    rw [ds.r1.rank_empty, ds.r2.rank_empty]
  Path.mk [Step.mk _ _ h] h

-- 24: Full direct sum empty chain
noncomputable def direct_sum_full_empty (n m : Nat) (ds : DirectSumRank n m) :
    Path (ds.combined_rank (fun _ => false) (fun _ => false)) (0 + 0) :=
  Path.trans (direct_sum_empty n m ds) (direct_sum_empty_zero n m ds)

-- ============================================================================
-- § 7. Minor Operations: Deletion and Contraction
-- ============================================================================

/-- Deletion: restrict rank to a subset -/
structure DeletionData (n : Nat) where
  original : RankFn n
  restricted : RankFn n
  delete_mask : Fin n → Bool
  rank_agree : ∀ S, (∀ i, S i = true → delete_mask i = true) →
    restricted.rank S = original.rank S

/-- Contraction data -/
structure ContractionData (n : Nat) where
  original : RankFn n
  contracted : RankFn n
  contract_set : Fin n → Bool
  rank_shift : ∀ S, contracted.rank S = original.rank S - original.rank contract_set

-- 25: Deletion rank agreement
noncomputable def deletion_rank_agree (n : Nat) (d : DeletionData n) (S : Fin n → Bool)
    (h : ∀ i, S i = true → d.delete_mask i = true) :
    Path (d.restricted.rank S) (d.original.rank S) :=
  Path.mk [Step.mk _ _ (d.rank_agree S h)] (d.rank_agree S h)

-- 26: Contraction rank shift
noncomputable def contraction_rank_shift (n : Nat) (c : ContractionData n) (S : Fin n → Bool) :
    Path (c.contracted.rank S) (c.original.rank S - c.original.rank c.contract_set) :=
  Path.mk [Step.mk _ _ (c.rank_shift S)] (c.rank_shift S)

-- 27: Deletion of empty preserves zero rank
noncomputable def deletion_empty (n : Nat) (d : DeletionData n) :
    Path (d.restricted.rank (fun _ => false)) 0 :=
  Path.mk [Step.mk _ _ d.restricted.rank_empty] d.restricted.rank_empty

-- 28: Original empty rank via deletion
noncomputable def deletion_original_empty (n : Nat) (d : DeletionData n) :
    Path (d.original.rank (fun _ => false)) 0 :=
  Path.mk [Step.mk _ _ d.original.rank_empty] d.original.rank_empty

-- ============================================================================
-- § 8. Tutte Polynomial Structure
-- ============================================================================

/-- Tutte polynomial as a pair of evaluations -/
structure TutteEval where
  tx : Nat
  ty : Nat

-- 29: Tutte evaluation at specific point
noncomputable def tutte_at_point (t : TutteEval) (hx : t.tx = 1) :
    Path t.tx 1 :=
  Path.mk [Step.mk _ _ hx] hx

-- 30: Tutte pair path
noncomputable def tutte_pair (t : TutteEval) (hx : t.tx = 1) (hy : t.ty = 2) :
    Path (t.tx, t.ty) (1, 2) :=
  have h : (t.tx, t.ty) = (1, 2) := by rw [hx, hy]
  Path.mk [Step.mk _ _ h] h

-- 31: Tutte x via congrArg
noncomputable def tutte_x_map (t : TutteEval) (f : Nat → Nat) (hx : t.tx = 1) :
    Path (f t.tx) (f 1) :=
  Path.congrArg f (tutte_at_point t hx)

-- ============================================================================
-- § 9. Greedy Algorithm Structure
-- ============================================================================

/-- Greedy solution data: weights and an optimal basis -/
structure GreedySolution (n : Nat) where
  weights : Fin n → Nat
  optimal_value : Nat
  greedy_value : Nat
  optimality : greedy_value = optimal_value

-- 32: Greedy optimality as path
noncomputable def greedy_optimal (n : Nat) (g : GreedySolution n) :
    Path g.greedy_value g.optimal_value :=
  Path.mk [Step.mk _ _ g.optimality] g.optimality

-- 33: Greedy composed with successor
noncomputable def greedy_optimal_succ (n : Nat) (g : GreedySolution n) :
    Path (Nat.succ g.greedy_value) (Nat.succ g.optimal_value) :=
  Path.congrArg Nat.succ (greedy_optimal n g)

-- 34: Greedy value doubled
noncomputable def greedy_optimal_double (n : Nat) (g : GreedySolution n) :
    Path (g.greedy_value + g.greedy_value) (g.optimal_value + g.optimal_value) :=
  have h : g.greedy_value + g.greedy_value = g.optimal_value + g.optimal_value := by
    rw [g.optimality]
  Path.mk [Step.mk _ _ h] h

-- ============================================================================
-- § 10. Matroid Intersection
-- ============================================================================

/-- Matroid intersection: common rank bound -/
structure IntersectionData (n : Nat) where
  r1 : RankFn n
  r2 : RankFn n
  common_rank : (Fin n → Bool) → Nat
  bound : ∀ S, common_rank S ≤ min (r1.rank S) (r2.rank S)

-- 35: Intersection rank identity
noncomputable def intersection_rank_id (n : Nat) (d : IntersectionData n)
    (S T : Fin n → Bool) (h : d.common_rank S = d.common_rank T) :
    Path (d.common_rank S) (d.common_rank T) :=
  Path.mk [Step.mk _ _ h] h

-- 36: Intersection rank via congrArg
noncomputable def intersection_rank_map (n : Nat) (d : IntersectionData n)
    (S T : Fin n → Bool) (h : d.common_rank S = d.common_rank T) (f : Nat → Nat) :
    Path (f (d.common_rank S)) (f (d.common_rank T)) :=
  Path.congrArg f (intersection_rank_id n d S T h)

-- ============================================================================
-- § 11. Representable Matroids
-- ============================================================================

/-- A matroid represented by column vectors: rank = linear rank -/
structure ReprMatroid (n k : Nat) where
  matrix : Fin n → Fin k → Nat
  rank_of : (Fin n → Bool) → Nat

-- 37: Representation rank identity
noncomputable def repr_rank_id (n k : Nat) (r1 r2 : ReprMatroid n k)
    (S : Fin n → Bool) (h : r1.rank_of S = r2.rank_of S) :
    Path (r1.rank_of S) (r2.rank_of S) :=
  Path.mk [Step.mk _ _ h] h

-- ============================================================================
-- § 12. Graphic Matroids
-- ============================================================================

/-- Graph structure -/
structure Graph where
  vertices : Nat
  edges : Nat
  edgeRank : (Fin edges → Bool) → Nat
  rank_empty : edgeRank (fun _ => false) = 0

-- 38: Graphic matroid empty rank
noncomputable def graphic_empty (g : Graph) :
    Path (g.edgeRank (fun _ => false)) 0 :=
  Path.mk [Step.mk _ _ g.rank_empty] g.rank_empty

-- 39: Graphic composed with succ
noncomputable def graphic_empty_succ (g : Graph) :
    Path (Nat.succ (g.edgeRank (fun _ => false))) (Nat.succ 0) :=
  Path.congrArg Nat.succ (graphic_empty g)

-- ============================================================================
-- § 13. Cryptomorphism Coherence (Equality-Level)
-- ============================================================================

-- 40: Closure idem is symmetric to itself (symm of symm)
theorem closure_idem_symm_symm (n : Nat) (c : ClosureOp n) (S : Fin n → Bool) :
    Path.symm (Path.symm (closure_idem n c S)) = closure_idem n c S :=
  symm_symm _

-- 41: Triple closure via trans_assoc
theorem closure_triple_assoc (n : Nat) (c : ClosureOp n) (S : Fin n → Bool)
    (p : Path (c.cl (c.cl (c.cl S))) (c.cl (c.cl S)))
    (q : Path (c.cl (c.cl S)) (c.cl S))
    (r : Path (c.cl S) S) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

-- 42: Trans with refl left
theorem closure_trans_refl_left (n : Nat) (c : ClosureOp n) (S : Fin n → Bool) :
    Path.trans (Path.refl _) (closure_idem n c S) = closure_idem n c S :=
  trans_refl_left _

-- 43: Trans with refl right
theorem closure_trans_refl_right (n : Nat) (c : ClosureOp n) (S : Fin n → Bool) :
    Path.trans (closure_idem n c S) (Path.refl _) = closure_idem n c S :=
  trans_refl_right _

-- 44: Symm of refl
theorem rank_symm_refl (n : Nat) (r : RankFn n) (S : Fin n → Bool) :
    Path.symm (Path.refl (r.rank S)) = Path.refl (r.rank S) :=
  symm_refl _

-- 45: CongrArg distributes over trans for rank
theorem rank_congrArg_trans (n : Nat) (f : Nat → Nat) (r : RankFn n)
    (S T U : Fin n → Bool)
    (p : Path (r.rank S) (r.rank T))
    (q : Path (r.rank T) (r.rank U)) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  congrArg_trans f p q

-- 46: CongrArg distributes over symm for rank
theorem rank_congrArg_symm (n : Nat) (f : Nat → Nat) (r : RankFn n)
    (S T : Fin n → Bool) (p : Path (r.rank S) (r.rank T)) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  congrArg_symm f p

-- 47: Symm distributes over trans (anti-homomorphism)
theorem rank_symm_trans (n : Nat) (r : RankFn n)
    (S T U : Fin n → Bool)
    (p : Path (r.rank S) (r.rank T))
    (q : Path (r.rank T) (r.rank U)) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

-- 48: Symm involution for complement paths
theorem compl_symm_invol (n : Nat) (d : DualRankData n) (S : Fin n → Bool) :
    Path.symm (Path.symm (compl_invol_path n d S)) = compl_invol_path n d S :=
  symm_symm _

-- 49: Greedy optimality symm_symm
theorem greedy_symm_invol (n : Nat) (g : GreedySolution n) :
    Path.symm (Path.symm (greedy_optimal n g)) = greedy_optimal n g :=
  symm_symm _

-- 50: Trans_refl for rank_empty
theorem rank_empty_trans_refl (n : Nat) (r : RankFn n) :
    Path.trans (rank_empty_path n r) (Path.refl 0) = rank_empty_path n r :=
  trans_refl_right _

-- ============================================================================
-- § 14. Advanced Path Compositions
-- ============================================================================

-- 51: Deletion then original empty chain
noncomputable def deletion_chain_empty (n : Nat) (d : DeletionData n)
    (h : ∀ i, (fun _ : Fin n => false) i = true → d.delete_mask i = true) :
    Path (d.restricted.rank (fun _ => false)) (d.original.rank (fun _ => false)) :=
  deletion_rank_agree n d (fun _ => false) h

-- 52: Full deletion empty chain to zero
noncomputable def deletion_full_chain (n : Nat) (d : DeletionData n)
    (h : ∀ i, (fun _ : Fin n => false) i = true → d.delete_mask i = true) :
    Path (d.restricted.rank (fun _ => false)) 0 :=
  Path.trans
    (deletion_rank_agree n d (fun _ => false) h)
    (deletion_original_empty n d)

-- 53: Biduality rank chain
noncomputable def biduality_chain (n : Nat) (d : DualRankData n) (S : Fin n → Bool)
    (h1 : d.dual.rank (d.complement S) = d.primal.rank S)
    (h2 : d.primal.rank S = d.dual.rank (d.complement S)) :
    Path (d.dual.rank (d.complement S)) (d.dual.rank (d.complement S)) :=
  Path.trans (biduality_rank n d S h1) (Path.mk [Step.mk _ _ h2] h2)

-- 54: CongrArg chain: f(g(rank(empty))) = f(g(0))
noncomputable def rank_double_map (n : Nat) (r : RankFn n) (f g : Nat → Nat) :
    Path (f (g (r.rank (fun _ => false)))) (f (g 0)) :=
  Path.congrArg f (Path.congrArg g (rank_empty_path n r))

-- 55: Direct sum full chain with congrArg
noncomputable def direct_sum_chain (n m : Nat) (ds : DirectSumRank n m) :
    Path (Nat.succ (ds.combined_rank (fun _ => false) (fun _ => false)))
         (Nat.succ (0 + 0)) :=
  Path.congrArg Nat.succ (direct_sum_full_empty n m ds)

-- ============================================================================
-- § 15. More Coherence
-- ============================================================================

-- 56: Flat path toEq roundtrip
theorem flat_roundtrip (n : Nat) (c : ClosureOp n) (F : Fin n → Bool)
    (hF : c.cl F = F) :
    (Path.trans (flat_cl_identity n c F hF) (Path.symm (flat_cl_identity n c F hF))).toEq =
    rfl := by
  simp

-- 57: Closure idem toEq roundtrip
theorem closure_idem_roundtrip (n : Nat) (c : ClosureOp n) (S : Fin n → Bool) :
    (Path.trans (closure_idem n c S) (Path.symm (closure_idem n c S))).toEq =
    rfl := by
  simp

-- 58: Greedy optimality toEq roundtrip
theorem greedy_roundtrip (n : Nat) (g : GreedySolution n) :
    (Path.trans (greedy_optimal n g) (Path.symm (greedy_optimal n g))).toEq =
    rfl := by
  simp

-- 59: Complement involution toEq roundtrip
theorem compl_roundtrip (n : Nat) (d : DualRankData n) (S : Fin n → Bool) :
    (Path.trans (compl_invol_path n d S) (Path.symm (compl_invol_path n d S))).toEq =
    rfl := by
  simp

-- 60: Four-fold trans associativity for rank
theorem rank_four_assoc (_n : Nat)
    {a b c d e : Nat}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans (Path.trans p q) r) s =
    Path.trans p (Path.trans q (Path.trans r s)) := by
  rw [trans_assoc (Path.trans p q) r s, trans_assoc p q (Path.trans r s)]

end ComputationalPaths.Path.Algebra.MatroidPathDeep
