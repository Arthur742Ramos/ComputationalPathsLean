/-
# KoszulDuality

Koszul duality via computational paths.

This public wrapper surfaces representative constructions from
`KoszulDualityDeep` into the `ComputationalPaths.Path.Algebra.KoszulDuality`
namespace, turning the previous placeholder into a usable public interface.
-/

import ComputationalPaths.Path.Algebra.KoszulDualityDeep

namespace ComputationalPaths.Path.Algebra.KoszulDuality

open ComputationalPaths

/-! ## Representative Koszul-duality paths -/

@[inline] noncomputable def d_squared_zero_path
    (x : ComputationalPaths.KoszulExpr) :=
  ComputationalPaths.KoszulPath.d_squared_zero_path x

theorem d_squared_zero_path_length (x : ComputationalPaths.KoszulExpr) :
    ComputationalPaths.KoszulPath.length (d_squared_zero_path x) = 1 := rfl

@[inline] noncomputable def tensor_comm_involutive
    (a b : ComputationalPaths.KoszulExpr) :=
  ComputationalPaths.KoszulPath.tensor_comm_involutive (a := a) (b := b)

theorem tensor_comm_involutive_length
    (a b : ComputationalPaths.KoszulExpr) :
    ComputationalPaths.KoszulPath.length (tensor_comm_involutive a b) = 2 := rfl

@[inline] noncomputable def quad_dual_involution_path
    (a : ComputationalPaths.KoszulExpr) :=
  ComputationalPaths.KoszulPath.quad_dual_involution_path a

theorem quad_dual_involution_path_length
    (a : ComputationalPaths.KoszulExpr) :
    ComputationalPaths.KoszulPath.length (quad_dual_involution_path a) = 1 := rfl

@[inline] noncomputable def bar_cobar_path
    (a : ComputationalPaths.KoszulExpr) :=
  ComputationalPaths.KoszulPath.bar_cobar_path a

theorem bar_cobar_path_length (a : ComputationalPaths.KoszulExpr) :
    ComputationalPaths.KoszulPath.length (bar_cobar_path a) = 1 := rfl

@[inline] noncomputable def koszul_bar_dual_path
    (a : ComputationalPaths.KoszulExpr) :=
  ComputationalPaths.KoszulPath.koszul_bar_dual_path a

theorem koszul_bar_dual_path_length
    (a : ComputationalPaths.KoszulExpr) :
    ComputationalPaths.KoszulPath.length (koszul_bar_dual_path a) = 1 := rfl

@[inline] noncomputable def twist_mc_congrArg
    (a b : ComputationalPaths.KoszulExpr)
    (f : ComputationalPaths.KoszulExpr → ComputationalPaths.KoszulExpr) :=
  ComputationalPaths.KoszulPath.twist_mc_congrArg a b f

theorem twist_mc_congrArg_length
    (a b : ComputationalPaths.KoszulExpr)
    (f : ComputationalPaths.KoszulExpr → ComputationalPaths.KoszulExpr) :
    ComputationalPaths.KoszulPath.length (twist_mc_congrArg a b f) = 1 := rfl

@[inline] noncomputable def minimal_res_path
    (a : ComputationalPaths.KoszulExpr) :=
  ComputationalPaths.KoszulPath.minimal_res_path a

theorem minimal_res_path_length (a : ComputationalPaths.KoszulExpr) :
    ComputationalPaths.KoszulPath.length (minimal_res_path a) = 1 := rfl

@[inline] noncomputable def operad_dual_involution_path
    (p : ComputationalPaths.KoszulExpr) :=
  ComputationalPaths.KoszulPath.operad_dual_involution_path p

theorem operad_dual_involution_path_length
    (p : ComputationalPaths.KoszulExpr) :
    ComputationalPaths.KoszulPath.length (operad_dual_involution_path p) = 1 := rfl

@[inline] noncomputable def ext_self_cohomology_path
    (a : ComputationalPaths.KoszulExpr) :=
  ComputationalPaths.KoszulPath.ext_self_cohomology_path a

theorem ext_self_cohomology_path_length
    (a : ComputationalPaths.KoszulExpr) :
    ComputationalPaths.KoszulPath.length (ext_self_cohomology_path a) = 1 := rfl

end ComputationalPaths.Path.Algebra.KoszulDuality
