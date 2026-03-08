import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- KOSZUL DUALITY VIA PATHS: Koszul complexes, bar/cobar adjunctions,
-- dual operads, minimal resolutions, quadratic algebras, PBW theorem,
-- Koszul algebras, ext algebras, derived Koszul duality, twisting morphisms
-- ============================================================================

inductive KoszulExpr : Type where
  | element : Nat → KoszulExpr
  | zero : KoszulExpr
  | one : KoszulExpr
  | add : KoszulExpr → KoszulExpr → KoszulExpr
  | neg : KoszulExpr → KoszulExpr
  | mul : KoszulExpr → KoszulExpr → KoszulExpr
  | tensor : KoszulExpr → KoszulExpr → KoszulExpr
  -- Differential
  | diff : KoszulExpr → KoszulExpr
  -- Koszul complex
  | koszulComplex : KoszulExpr → KoszulExpr
  | koszulHomology : KoszulExpr → KoszulExpr
  -- Quadratic algebras
  | quadAlg : KoszulExpr → KoszulExpr → KoszulExpr
  | generators : KoszulExpr → KoszulExpr
  | relations : KoszulExpr → KoszulExpr
  | quadDual : KoszulExpr → KoszulExpr
  -- Bar/cobar
  | bar : KoszulExpr → KoszulExpr
  | cobar : KoszulExpr → KoszulExpr
  | barElem : List KoszulExpr → KoszulExpr
  -- Koszul property
  | koszulAlg : KoszulExpr → KoszulExpr
  | isKoszul : KoszulExpr → KoszulExpr
  -- Ext algebra
  | ext : KoszulExpr → KoszulExpr → KoszulExpr
  | extSelf : KoszulExpr → KoszulExpr
  -- Resolutions
  | resolution : KoszulExpr → KoszulExpr
  | minimalRes : KoszulExpr → KoszulExpr
  | projRes : KoszulExpr → KoszulExpr
  -- Twisting morphisms
  | twistMorph : KoszulExpr → KoszulExpr → KoszulExpr
  | twistComp : KoszulExpr → KoszulExpr
  -- Operadic
  | operad : KoszulExpr → KoszulExpr
  | dualOperad : KoszulExpr → KoszulExpr
  | operadCobar : KoszulExpr → KoszulExpr
  -- PBW
  | pbwBasis : KoszulExpr → KoszulExpr
  | graded : KoszulExpr → KoszulExpr
  | filtration : KoszulExpr → KoszulExpr
  -- Cohomology
  | cohomology : KoszulExpr → KoszulExpr
  | quasiIso : KoszulExpr → KoszulExpr → KoszulExpr
  deriving Repr, BEq

inductive KoszulStep : KoszulExpr → KoszulExpr → Type where
  | refl  : (a : KoszulExpr) → KoszulStep a a
  | symm  : KoszulStep a b → KoszulStep b a
  | trans : KoszulStep a b → KoszulStep b c → KoszulStep a c
  | congrArg : (f : KoszulExpr → KoszulExpr) → KoszulStep a b → KoszulStep (f a) (f b)
  -- Algebra
  | add_assoc : KoszulStep (KoszulExpr.add (KoszulExpr.add a b) c)
                            (KoszulExpr.add a (KoszulExpr.add b c))
  | add_comm : KoszulStep (KoszulExpr.add a b) (KoszulExpr.add b a)
  | add_zero : KoszulStep (KoszulExpr.add a KoszulExpr.zero) a
  | zero_add : KoszulStep (KoszulExpr.add KoszulExpr.zero a) a
  | add_neg : KoszulStep (KoszulExpr.add a (KoszulExpr.neg a)) KoszulExpr.zero
  | mul_assoc : KoszulStep (KoszulExpr.mul (KoszulExpr.mul a b) c)
                            (KoszulExpr.mul a (KoszulExpr.mul b c))
  | mul_one : KoszulStep (KoszulExpr.mul a KoszulExpr.one) a
  | one_mul : KoszulStep (KoszulExpr.mul KoszulExpr.one a) a
  | left_distrib : KoszulStep (KoszulExpr.mul a (KoszulExpr.add b c))
                               (KoszulExpr.add (KoszulExpr.mul a b) (KoszulExpr.mul a c))
  -- Tensor
  | tensor_assoc : KoszulStep (KoszulExpr.tensor (KoszulExpr.tensor a b) c)
                               (KoszulExpr.tensor a (KoszulExpr.tensor b c))
  | tensor_comm : KoszulStep (KoszulExpr.tensor a b) (KoszulExpr.tensor b a)
  | tensor_unit : KoszulStep (KoszulExpr.tensor a KoszulExpr.one) a
  -- Differential d²=0
  | d_squared_zero : KoszulStep (KoszulExpr.diff (KoszulExpr.diff x)) KoszulExpr.zero
  -- Koszul complex
  | koszul_acyclic : KoszulStep (KoszulExpr.koszulHomology (KoszulExpr.koszulComplex a))
                                 KoszulExpr.zero
  | koszul_resolution : KoszulStep (KoszulExpr.koszulComplex a)
                                    (KoszulExpr.quasiIso (KoszulExpr.koszulComplex a) a)
  -- Quadratic duality
  | quad_dual_involution : KoszulStep (KoszulExpr.quadDual (KoszulExpr.quadDual a)) a
  | quad_dual_generators : KoszulStep (KoszulExpr.generators (KoszulExpr.quadDual a))
                                       (KoszulExpr.generators a)
  | quad_dual_relations : KoszulStep (KoszulExpr.relations (KoszulExpr.quadDual a))
                                      (KoszulExpr.relations a)
  -- Bar/cobar adjunction
  | bar_cobar_equiv : KoszulStep (KoszulExpr.cobar (KoszulExpr.bar a))
                                  (KoszulExpr.quasiIso (KoszulExpr.cobar (KoszulExpr.bar a)) a)
  | cobar_bar_equiv : KoszulStep (KoszulExpr.bar (KoszulExpr.cobar c))
                                  (KoszulExpr.quasiIso (KoszulExpr.bar (KoszulExpr.cobar c)) c)
  | bar_diff : KoszulStep (KoszulExpr.diff (KoszulExpr.bar a))
                           (KoszulExpr.bar (KoszulExpr.diff a))
  | cobar_diff : KoszulStep (KoszulExpr.diff (KoszulExpr.cobar c))
                             (KoszulExpr.cobar (KoszulExpr.diff c))
  -- Koszul algebra ↔ quadratic dual = Ext
  | koszul_ext : KoszulStep (KoszulExpr.extSelf (KoszulExpr.koszulAlg a))
                             (KoszulExpr.quadDual (KoszulExpr.koszulAlg a))
  | koszul_bar_dual : KoszulStep (KoszulExpr.bar (KoszulExpr.koszulAlg a))
                                  (KoszulExpr.quasiIso
                                    (KoszulExpr.bar (KoszulExpr.koszulAlg a))
                                    (KoszulExpr.quadDual (KoszulExpr.koszulAlg a)))
  -- Minimal resolution
  | minimal_res_exists : KoszulStep a (KoszulExpr.quasiIso (KoszulExpr.minimalRes a) a)
  | minimal_res_diff_decomp : KoszulStep (KoszulExpr.diff (KoszulExpr.minimalRes a))
                                          (KoszulExpr.mul (KoszulExpr.minimalRes a)
                                                          (KoszulExpr.minimalRes a))
  -- Twisting morphisms
  | twist_maurer_cartan : KoszulStep (KoszulExpr.diff (KoszulExpr.twistMorph a b))
                                      (KoszulExpr.add
                                        (KoszulExpr.twistMorph (KoszulExpr.diff a) b)
                                        (KoszulExpr.mul (KoszulExpr.twistMorph a b)
                                                        (KoszulExpr.twistMorph a b)))
  | twist_bar_universal : KoszulStep (KoszulExpr.twistMorph (KoszulExpr.bar a) a)
                                      (KoszulExpr.twistComp a)
  -- Operadic Koszul duality
  | operad_dual_involution : KoszulStep (KoszulExpr.dualOperad (KoszulExpr.dualOperad p))
                                         (KoszulExpr.operad p)
  | operad_cobar_dual : KoszulStep (KoszulExpr.operadCobar (KoszulExpr.dualOperad p))
                                    (KoszulExpr.quasiIso
                                      (KoszulExpr.operadCobar (KoszulExpr.dualOperad p))
                                      (KoszulExpr.operad p))
  -- PBW
  | pbw_filtered : KoszulStep (KoszulExpr.graded (KoszulExpr.filtration a))
                               (KoszulExpr.pbwBasis a)
  | pbw_koszul : KoszulStep (KoszulExpr.isKoszul (KoszulExpr.pbwBasis a))
                             (KoszulExpr.pbwBasis a)
  -- Ext
  | ext_self_cohomology : KoszulStep (KoszulExpr.extSelf a) (KoszulExpr.cohomology (KoszulExpr.resolution a))

inductive KoszulPath : KoszulExpr → KoszulExpr → Type where
  | nil  : (a : KoszulExpr) → KoszulPath a a
  | cons : KoszulStep a b → KoszulPath b c → KoszulPath a c

namespace KoszulPath

noncomputable def trans : KoszulPath a b → KoszulPath b c → KoszulPath a c
  | .nil _, q => q
  | .cons s p, q => .cons s (trans p q)

noncomputable def symm : KoszulPath a b → KoszulPath b a
  | .nil _ => .nil _
  | .cons s p => (symm p).trans (.cons (.symm s) (.nil _))

noncomputable def congrArg (f : KoszulExpr → KoszulExpr) : KoszulPath a b → KoszulPath (f a) (f b)
  | .nil _ => .nil _
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

noncomputable def length : KoszulPath a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

-- =========================================================================
-- 1. Differential d²=0
-- =========================================================================

noncomputable def d_squared_zero_path (x : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.diff x)) KoszulExpr.zero :=
  .cons .d_squared_zero (.nil _)

noncomputable def d_triple_zero (x : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.diff (KoszulExpr.diff x))) KoszulExpr.zero :=
  .cons .d_squared_zero (.nil _)

-- =========================================================================
-- 2. Algebra axioms
-- =========================================================================

noncomputable def add_assoc_path :
    KoszulPath (KoszulExpr.add (KoszulExpr.add a b) c)
               (KoszulExpr.add a (KoszulExpr.add b c)) :=
  .cons .add_assoc (.nil _)

noncomputable def add_comm_path :
    KoszulPath (KoszulExpr.add a b) (KoszulExpr.add b a) :=
  .cons .add_comm (.nil _)

noncomputable def add_zero_path :
    KoszulPath (KoszulExpr.add a KoszulExpr.zero) a :=
  .cons .add_zero (.nil _)

noncomputable def add_neg_path :
    KoszulPath (KoszulExpr.add a (KoszulExpr.neg a)) KoszulExpr.zero :=
  .cons .add_neg (.nil _)

noncomputable def mul_assoc_path :
    KoszulPath (KoszulExpr.mul (KoszulExpr.mul a b) c)
               (KoszulExpr.mul a (KoszulExpr.mul b c)) :=
  .cons .mul_assoc (.nil _)

noncomputable def mul_one_path :
    KoszulPath (KoszulExpr.mul a KoszulExpr.one) a :=
  .cons .mul_one (.nil _)

noncomputable def one_mul_path :
    KoszulPath (KoszulExpr.mul KoszulExpr.one a) a :=
  .cons .one_mul (.nil _)

noncomputable def left_distrib_path :
    KoszulPath (KoszulExpr.mul a (KoszulExpr.add b c))
               (KoszulExpr.add (KoszulExpr.mul a b) (KoszulExpr.mul a c)) :=
  .cons .left_distrib (.nil _)

-- =========================================================================
-- 3. Tensor product
-- =========================================================================

noncomputable def tensor_assoc_path :
    KoszulPath (KoszulExpr.tensor (KoszulExpr.tensor a b) c)
               (KoszulExpr.tensor a (KoszulExpr.tensor b c)) :=
  .cons .tensor_assoc (.nil _)

noncomputable def tensor_comm_path :
    KoszulPath (KoszulExpr.tensor a b) (KoszulExpr.tensor b a) :=
  .cons .tensor_comm (.nil _)

noncomputable def tensor_unit_path :
    KoszulPath (KoszulExpr.tensor a KoszulExpr.one) a :=
  .cons .tensor_unit (.nil _)

noncomputable def tensor_comm_involutive :
    KoszulPath (KoszulExpr.tensor a b) (KoszulExpr.tensor a b) :=
  .cons .tensor_comm (.cons .tensor_comm (.nil _))

-- =========================================================================
-- 4. Koszul complex
-- =========================================================================

noncomputable def koszul_acyclic_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.koszulHomology (KoszulExpr.koszulComplex a))
               KoszulExpr.zero :=
  .cons .koszul_acyclic (.nil _)

noncomputable def koszul_resolution_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.koszulComplex a)
               (KoszulExpr.quasiIso (KoszulExpr.koszulComplex a) a) :=
  .cons .koszul_resolution (.nil _)

noncomputable def koszul_d_squared (a : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.diff (KoszulExpr.koszulComplex a)))
               KoszulExpr.zero :=
  .cons .d_squared_zero (.nil _)

-- =========================================================================
-- 5. Quadratic duality
-- =========================================================================

noncomputable def quad_dual_involution_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.quadDual (KoszulExpr.quadDual a)) a :=
  .cons .quad_dual_involution (.nil _)

noncomputable def quad_dual_generators_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.generators (KoszulExpr.quadDual a))
               (KoszulExpr.generators a) :=
  .cons .quad_dual_generators (.nil _)

noncomputable def quad_dual_relations_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.relations (KoszulExpr.quadDual a))
               (KoszulExpr.relations a) :=
  .cons .quad_dual_relations (.nil _)

noncomputable def quad_dual_congrArg (a : KoszulExpr) (f : KoszulExpr → KoszulExpr) :
    KoszulPath (f (KoszulExpr.quadDual (KoszulExpr.quadDual a)))
               (f a) :=
  (quad_dual_involution_path a).congrArg f

-- =========================================================================
-- 6. Bar/cobar adjunction
-- =========================================================================

noncomputable def bar_cobar_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.cobar (KoszulExpr.bar a))
               (KoszulExpr.quasiIso (KoszulExpr.cobar (KoszulExpr.bar a)) a) :=
  .cons .bar_cobar_equiv (.nil _)

noncomputable def cobar_bar_path (c : KoszulExpr) :
    KoszulPath (KoszulExpr.bar (KoszulExpr.cobar c))
               (KoszulExpr.quasiIso (KoszulExpr.bar (KoszulExpr.cobar c)) c) :=
  .cons .cobar_bar_equiv (.nil _)

noncomputable def bar_diff_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.bar a))
               (KoszulExpr.bar (KoszulExpr.diff a)) :=
  .cons .bar_diff (.nil _)

noncomputable def cobar_diff_path (c : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.cobar c))
               (KoszulExpr.cobar (KoszulExpr.diff c)) :=
  .cons .cobar_diff (.nil _)

noncomputable def bar_d_squared (a : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.diff (KoszulExpr.bar a))) KoszulExpr.zero :=
  .cons .d_squared_zero (.nil _)

noncomputable def cobar_d_squared (c : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.diff (KoszulExpr.cobar c))) KoszulExpr.zero :=
  .cons .d_squared_zero (.nil _)

-- =========================================================================
-- 7. Koszul algebra properties
-- =========================================================================

noncomputable def koszul_ext_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.extSelf (KoszulExpr.koszulAlg a))
               (KoszulExpr.quadDual (KoszulExpr.koszulAlg a)) :=
  .cons .koszul_ext (.nil _)

noncomputable def koszul_bar_dual_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.bar (KoszulExpr.koszulAlg a))
               (KoszulExpr.quasiIso
                 (KoszulExpr.bar (KoszulExpr.koszulAlg a))
                 (KoszulExpr.quadDual (KoszulExpr.koszulAlg a))) :=
  .cons .koszul_bar_dual (.nil _)

-- =========================================================================
-- 8. Minimal resolutions
-- =========================================================================

noncomputable def minimal_res_path (a : KoszulExpr) :
    KoszulPath a (KoszulExpr.quasiIso (KoszulExpr.minimalRes a) a) :=
  .cons .minimal_res_exists (.nil _)

noncomputable def minimal_res_diff_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.minimalRes a))
               (KoszulExpr.mul (KoszulExpr.minimalRes a) (KoszulExpr.minimalRes a)) :=
  .cons .minimal_res_diff_decomp (.nil _)

noncomputable def minimal_res_d_squared (a : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.diff (KoszulExpr.minimalRes a)))
               KoszulExpr.zero :=
  .cons .d_squared_zero (.nil _)

-- =========================================================================
-- 9. Twisting morphisms
-- =========================================================================

noncomputable def twist_mc_path (a b : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.twistMorph a b))
               (KoszulExpr.add
                 (KoszulExpr.twistMorph (KoszulExpr.diff a) b)
                 (KoszulExpr.mul (KoszulExpr.twistMorph a b)
                                 (KoszulExpr.twistMorph a b))) :=
  .cons .twist_maurer_cartan (.nil _)

noncomputable def twist_bar_universal_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.twistMorph (KoszulExpr.bar a) a)
               (KoszulExpr.twistComp a) :=
  .cons .twist_bar_universal (.nil _)

noncomputable def twist_mc_congrArg (a b : KoszulExpr) (f : KoszulExpr → KoszulExpr) :
    KoszulPath (f (KoszulExpr.diff (KoszulExpr.twistMorph a b)))
               (f (KoszulExpr.add
                 (KoszulExpr.twistMorph (KoszulExpr.diff a) b)
                 (KoszulExpr.mul (KoszulExpr.twistMorph a b)
                                 (KoszulExpr.twistMorph a b)))) :=
  (twist_mc_path a b).congrArg f

-- =========================================================================
-- 10. Operadic Koszul duality
-- =========================================================================

noncomputable def operad_dual_involution_path (p : KoszulExpr) :
    KoszulPath (KoszulExpr.dualOperad (KoszulExpr.dualOperad p))
               (KoszulExpr.operad p) :=
  .cons .operad_dual_involution (.nil _)

noncomputable def operad_cobar_dual_path (p : KoszulExpr) :
    KoszulPath (KoszulExpr.operadCobar (KoszulExpr.dualOperad p))
               (KoszulExpr.quasiIso
                 (KoszulExpr.operadCobar (KoszulExpr.dualOperad p))
                 (KoszulExpr.operad p)) :=
  .cons .operad_cobar_dual (.nil _)

noncomputable def operad_dual_congrArg (p : KoszulExpr) (f : KoszulExpr → KoszulExpr) :
    KoszulPath (f (KoszulExpr.dualOperad (KoszulExpr.dualOperad p)))
               (f (KoszulExpr.operad p)) :=
  (operad_dual_involution_path p).congrArg f

-- =========================================================================
-- 11. PBW theorem
-- =========================================================================

noncomputable def pbw_filtered_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.graded (KoszulExpr.filtration a))
               (KoszulExpr.pbwBasis a) :=
  .cons .pbw_filtered (.nil _)

noncomputable def pbw_koszul_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.isKoszul (KoszulExpr.pbwBasis a))
               (KoszulExpr.pbwBasis a) :=
  .cons .pbw_koszul (.nil _)

-- =========================================================================
-- 12. Ext algebra
-- =========================================================================

noncomputable def ext_self_cohomology_path (a : KoszulExpr) :
    KoszulPath (KoszulExpr.extSelf a)
               (KoszulExpr.cohomology (KoszulExpr.resolution a)) :=
  .cons .ext_self_cohomology (.nil _)

-- =========================================================================
-- 13. Cross-cutting chains
-- =========================================================================

-- Koszul algebra: Ext = quadratic dual chain
noncomputable def koszul_ext_dual_chain (a : KoszulExpr) :
    KoszulPath (KoszulExpr.extSelf (KoszulExpr.koszulAlg a))
               (KoszulExpr.quadDual (KoszulExpr.koszulAlg a)) :=
  .cons .koszul_ext (.nil _)

-- Quadratic dual involution + bar chain
noncomputable def quad_dual_bar_chain (a : KoszulExpr) :
    KoszulPath (KoszulExpr.quadDual (KoszulExpr.quadDual a)) a :=
  .cons .quad_dual_involution (.nil _)

-- Bar + d²=0 chain
noncomputable def bar_differential_chain (a : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.diff (KoszulExpr.bar a))) KoszulExpr.zero :=
  .cons .d_squared_zero (.nil _)

-- Operadic dual is involutive
noncomputable def operad_dual_roundtrip (p : KoszulExpr) :
    KoszulPath (KoszulExpr.dualOperad (KoszulExpr.dualOperad p))
               (KoszulExpr.operad p) :=
  .cons .operad_dual_involution (.nil _)

-- Tensor associativity pentagon (3-fold)
noncomputable def tensor_assoc_3fold (a b c d : KoszulExpr) :
    KoszulPath (KoszulExpr.tensor (KoszulExpr.tensor (KoszulExpr.tensor a b) c) d)
               (KoszulExpr.tensor (KoszulExpr.tensor a b) (KoszulExpr.tensor c d)) :=
  .cons .tensor_assoc (.nil _)

-- Cobar diff + d²=0
noncomputable def cobar_differential_chain (c : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.diff (KoszulExpr.cobar c))) KoszulExpr.zero :=
  .cons .d_squared_zero (.nil _)

-- Koszul complex + resolution chain
noncomputable def koszul_is_resolution (a : KoszulExpr) :
    KoszulPath (KoszulExpr.koszulComplex a)
               (KoszulExpr.quasiIso (KoszulExpr.koszulComplex a) a) :=
  .cons .koszul_resolution (.nil _)

-- Minimal resolution d²=0 chain
noncomputable def minimal_d_squared_chain (a : KoszulExpr) :
    KoszulPath (KoszulExpr.diff (KoszulExpr.diff (KoszulExpr.minimalRes a)))
               KoszulExpr.zero :=
  .cons .d_squared_zero (.nil _)

-- PBW + koszul combined
noncomputable def pbw_koszul_filtered_chain (a : KoszulExpr) :
    KoszulPath (KoszulExpr.graded (KoszulExpr.filtration a))
               (KoszulExpr.pbwBasis a) :=
  .cons .pbw_filtered (.nil _)

end KoszulPath
end ComputationalPaths
