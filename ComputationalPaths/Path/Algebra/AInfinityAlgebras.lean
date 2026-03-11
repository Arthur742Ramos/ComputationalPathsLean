/-
# AInfinityAlgebras

A-infinity algebra structures via computational paths.

This public wrapper re-exports representative constructions from
`AInfinityAlgebrasDeep` into the `ComputationalPaths.Path.Algebra.AInfinityAlgebras`
namespace so the module is no longer an empty scaffold.
-/

import ComputationalPaths.Path.Algebra.AInfinityAlgebrasDeep

namespace ComputationalPaths.Path.Algebra.AInfinityAlgebras

open ComputationalPaths

/-! ## Representative A-infinity paths -/

@[inline] noncomputable def m1_squared_zero_path (x : ComputationalPaths.AInfExpr) :=
  ComputationalPaths.AInfPath.m1_squared_zero_path x

theorem m1_squared_zero_path_length (x : ComputationalPaths.AInfExpr) :
    ComputationalPaths.AInfPath.length (m1_squared_zero_path x) = 1 := rfl

@[inline] noncomputable def stasheff_3_path
    (x y : ComputationalPaths.AInfExpr) :=
  ComputationalPaths.AInfPath.stasheff_3_path x y

theorem stasheff_3_path_length (x y : ComputationalPaths.AInfExpr) :
    ComputationalPaths.AInfPath.length (stasheff_3_path x y) = 1 := rfl

@[inline] noncomputable def mn_1_squared_zero (x : ComputationalPaths.AInfExpr) :=
  ComputationalPaths.AInfPath.mn_1_squared_zero x

theorem mn_1_squared_zero_length (x : ComputationalPaths.AInfExpr) :
    ComputationalPaths.AInfPath.length (mn_1_squared_zero x) = 3 := rfl

@[inline] noncomputable def transfer_homotopy_identity_path
    (x : ComputationalPaths.AInfExpr) :=
  ComputationalPaths.AInfPath.transfer_homotopy_identity_path x

theorem transfer_homotopy_identity_path_length
    (x : ComputationalPaths.AInfExpr) :
    ComputationalPaths.AInfPath.length (transfer_homotopy_identity_path x) = 1 := rfl

@[inline] noncomputable def massey_indeterminacy_path
    (a b c : ComputationalPaths.AInfExpr) :=
  ComputationalPaths.AInfPath.massey_indeterminacy_path a b c

theorem massey_indeterminacy_path_length
    (a b c : ComputationalPaths.AInfExpr) :
    ComputationalPaths.AInfPath.length (massey_indeterminacy_path a b c) = 1 := rfl

@[inline] noncomputable def bar_cobar_equiv_path
    (a : ComputationalPaths.AInfExpr) :=
  ComputationalPaths.AInfPath.bar_cobar_equiv_path a

theorem bar_cobar_equiv_path_length (a : ComputationalPaths.AInfExpr) :
    ComputationalPaths.AInfPath.length (bar_cobar_equiv_path a) = 1 := rfl

@[inline] noncomputable def formality_path
    (a : ComputationalPaths.AInfExpr) :=
  ComputationalPaths.AInfPath.formality_path a

theorem formality_path_length (a : ComputationalPaths.AInfExpr) :
    ComputationalPaths.AInfPath.length (formality_path a) = 1 := rfl

@[inline] noncomputable def minimal_exists_path
    (a : ComputationalPaths.AInfExpr) :=
  ComputationalPaths.AInfPath.minimal_exists_path a

theorem minimal_exists_path_length (a : ComputationalPaths.AInfExpr) :
    ComputationalPaths.AInfPath.length (minimal_exists_path a) = 1 := rfl

end ComputationalPaths.Path.Algebra.AInfinityAlgebras
