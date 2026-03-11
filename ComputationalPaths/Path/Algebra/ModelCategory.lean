/-
# ModelCategory

Model categories via computational paths.

This public module surfaces representative constructions from
`ModelCategoryDeep` under the `ComputationalPaths.Path.Algebra.ModelCategory`
namespace. Since the deep module is already imported by the path umbrella, this
wrapper improves discoverability without changing the underlying semantics.
-/

import ComputationalPaths.Path.Algebra.ModelCategoryDeep

namespace ComputationalPaths.Path.Algebra.ModelCategory

/-! ## Representative model-category paths -/

@[inline] noncomputable def trivFib_is_fib_path
    (mc : ComputationalPaths.Path.Algebra.ModelCategoryDeep.ModelCat)
    (f : Nat) (h : mc.isTrivFib f = true) :=
  ComputationalPaths.Path.Algebra.ModelCategoryDeep.trivFib_is_fib_path mc f h

theorem trivFib_is_fib_path_length
    (mc : ComputationalPaths.Path.Algebra.ModelCategoryDeep.ModelCat)
    (f : Nat) (h : mc.isTrivFib f = true) :
    _root_.ComputationalPaths.Path.length (trivFib_is_fib_path mc f h) = 1 := by
  simp [trivFib_is_fib_path,
    ComputationalPaths.Path.Algebra.ModelCategoryDeep.trivFib_is_fib_path]

@[inline] noncomputable def fib_weq_trivFib_path
    (mc : ComputationalPaths.Path.Algebra.ModelCategoryDeep.ModelCat)
    (f : Nat) (hf : mc.isFib f = true) (hw : mc.isWeq f = true) :=
  ComputationalPaths.Path.Algebra.ModelCategoryDeep.fib_weq_trivFib_path mc f hf hw

theorem fib_weq_trivFib_path_length
    (mc : ComputationalPaths.Path.Algebra.ModelCategoryDeep.ModelCat)
    (f : Nat) (hf : mc.isFib f = true) (hw : mc.isWeq f = true) :
    _root_.ComputationalPaths.Path.length (fib_weq_trivFib_path mc f hf hw) = 1 := by
  simp [fib_weq_trivFib_path,
    ComputationalPaths.Path.Algebra.ModelCategoryDeep.fib_weq_trivFib_path]

@[inline] noncomputable def cof_trivfib_sum_path
    (fact : ComputationalPaths.Path.Algebra.ModelCategoryDeep.CofTrivFibFact) :=
  ComputationalPaths.Path.Algebra.ModelCategoryDeep.cof_trivfib_sum_path fact

theorem cof_trivfib_sum_path_length
    (fact : ComputationalPaths.Path.Algebra.ModelCategoryDeep.CofTrivFibFact) :
    _root_.ComputationalPaths.Path.length (cof_trivfib_sum_path fact) = 1 := by
  simp [cof_trivfib_sum_path,
    ComputationalPaths.Path.Algebra.ModelCategoryDeep.cof_trivfib_sum_path]

@[inline] noncomputable def two_of_three_compose_path
    (tot : ComputationalPaths.Path.Algebra.ModelCategoryDeep.TwoOfThree) :=
  ComputationalPaths.Path.Algebra.ModelCategoryDeep.two_of_three_compose_path tot

theorem two_of_three_compose_path_length
    (tot : ComputationalPaths.Path.Algebra.ModelCategoryDeep.TwoOfThree) :
    _root_.ComputationalPaths.Path.length (two_of_three_compose_path tot) = 1 := by
  simp [two_of_three_compose_path,
    ComputationalPaths.Path.Algebra.ModelCategoryDeep.two_of_three_compose_path]

@[inline] noncomputable def trivFib_fib_weq_chain
    (mc : ComputationalPaths.Path.Algebra.ModelCategoryDeep.ModelCat)
    (f : Nat) (h : mc.isTrivFib f = true) :=
  ComputationalPaths.Path.Algebra.ModelCategoryDeep.trivFib_fib_weq_chain mc f h

theorem trivFib_fib_weq_chain_length
    (mc : ComputationalPaths.Path.Algebra.ModelCategoryDeep.ModelCat)
    (f : Nat) (h : mc.isTrivFib f = true) :
    _root_.ComputationalPaths.Path.length (trivFib_fib_weq_chain mc f h) = 2 := by
  simp [trivFib_fib_weq_chain,
    ComputationalPaths.Path.Algebra.ModelCategoryDeep.trivFib_fib_weq_chain,
    ComputationalPaths.Path.Algebra.ModelCategoryDeep.trivFib_is_fib_path,
    ComputationalPaths.Path.Algebra.ModelCategoryDeep.trivFib_is_weq_path]

@[inline] noncomputable def quillen_adj_sym_path
    (qp : ComputationalPaths.Path.Algebra.ModelCategoryDeep.QuillenPair) (n : Nat) :=
  ComputationalPaths.Path.Algebra.ModelCategoryDeep.quillen_adj_sym_path qp n

theorem quillen_adj_sym_path_length
    (qp : ComputationalPaths.Path.Algebra.ModelCategoryDeep.QuillenPair) (n : Nat) :
    _root_.ComputationalPaths.Path.length (quillen_adj_sym_path qp n) = 1 := by
  simp [quillen_adj_sym_path,
    ComputationalPaths.Path.Algebra.ModelCategoryDeep.quillen_adj_sym_path,
    ComputationalPaths.Path.Algebra.ModelCategoryDeep.quillen_adj_path]

@[inline] noncomputable def cofgen_total_comm_path
    (cg : ComputationalPaths.Path.Algebra.ModelCategoryDeep.CofGenData) :=
  ComputationalPaths.Path.Algebra.ModelCategoryDeep.cofgen_total_comm_path cg

theorem cofgen_total_comm_path_length
    (cg : ComputationalPaths.Path.Algebra.ModelCategoryDeep.CofGenData) :
    _root_.ComputationalPaths.Path.length (cofgen_total_comm_path cg) = 2 := by
  simp [cofgen_total_comm_path,
    ComputationalPaths.Path.Algebra.ModelCategoryDeep.cofgen_total_comm_path,
    ComputationalPaths.Path.Algebra.ModelCategoryDeep.cofgen_total_path,
    ComputationalPaths.Path.Algebra.ModelCategoryDeep.cofgen_comm_path]

@[inline] noncomputable def homotopy_trans_arith_path (a b c : Nat) :=
  ComputationalPaths.Path.Algebra.ModelCategoryDeep.homotopy_trans_arith_path a b c

theorem homotopy_trans_arith_path_length (a b c : Nat) :
    _root_.ComputationalPaths.Path.length (homotopy_trans_arith_path a b c) = 1 := by
  simp [homotopy_trans_arith_path,
    ComputationalPaths.Path.Algebra.ModelCategoryDeep.homotopy_trans_arith_path]

@[inline] noncomputable def model_id_weq_path
    (mc : ComputationalPaths.Path.Algebra.ModelCategoryDeep.ModelCat)
    (n : Nat) (h : mc.isWeq n = true) :=
  ComputationalPaths.Path.Algebra.ModelCategoryDeep.model_id_weq_path mc n h

theorem model_id_weq_path_length
    (mc : ComputationalPaths.Path.Algebra.ModelCategoryDeep.ModelCat)
    (n : Nat) (h : mc.isWeq n = true) :
    _root_.ComputationalPaths.Path.length (model_id_weq_path mc n h) = 1 := by
  simp [model_id_weq_path,
    ComputationalPaths.Path.Algebra.ModelCategoryDeep.model_id_weq_path]

end ComputationalPaths.Path.Algebra.ModelCategory
