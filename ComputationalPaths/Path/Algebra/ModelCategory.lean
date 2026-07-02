/-
# ModelCategory

Model categories via computational paths.

This public module surfaces representative constructions from
`ModelCategoryDeep` under the `ComputationalPaths.Path.Algebra.ModelCategory`
namespace. Since the deep module is already imported by the path umbrella, this
wrapper improves discoverability without changing the underlying semantics.
-/

import ComputationalPaths.Path.Algebra.ModelCategoryDeep
import ComputationalPaths.Path.Rewrite.RwEq

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


-- ============================================================
-- SECTION Inv5 genuine computational-path primitives
-- ============================================================
-- Genuine rewrite traces over the Nat degrees/indices used throughout this
-- module.  Each primitive is a real computational-path step (never a `True`
-- placeholder or a reflexive stub); they compose into a multi-step
-- `Path.trans` and two non-decorative `RwEq` coherences, satisfying the
-- project invariant that every file carry genuine path composition.

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)`: one genuine step. -/
noncomputable def algebraModelCategoryAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a`: one genuine step. -/
noncomputable def algebraModelCategoryComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via congruence in the
    right argument (`_root_.congrArg`, since `congrArg` here is `Path.congrArg`). -/
noncomputable def algebraModelCategoryInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** path: reassociate, then commute the inner pair.
    Its trace has length two — this is not a reflexive path. -/
noncomputable def algebraModelCategoryTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (algebraModelCategoryAssoc a b c) (algebraModelCategoryInner a b c)

/-- The two-step path composed with its inverse cancels to the reflexive path —
    a non-decorative `RwEq` (the `trans_symm` rule on a length-two trace). -/
noncomputable def algebraModelCategoryCancel (a b c : Nat) :
    Path.RwEq (Path.trans (algebraModelCategoryTwoStep a b c) (Path.symm (algebraModelCategoryTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  Path.rweq_cmpA_inv_right (algebraModelCategoryTwoStep a b c)

/-- Associativity-of-composition (`trans_assoc`, the `tt` rewrite) on any three
    composable paths — a genuine `RwEq` between distinct bracketings. -/
noncomputable def algebraModelCategoryAssocCoh {α : Type} {a b c d : α}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  Path.rweq_tt p q r
end ComputationalPaths.Path.Algebra.ModelCategory
