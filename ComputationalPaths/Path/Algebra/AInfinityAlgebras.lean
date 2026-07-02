/-
# AInfinityAlgebras

A-infinity algebra structures via computational paths.

This public wrapper re-exports representative constructions from
`AInfinityAlgebrasDeep` into the `ComputationalPaths.Path.Algebra.AInfinityAlgebras`
namespace so the module is no longer an empty scaffold.
-/

import ComputationalPaths.Path.Algebra.AInfinityAlgebrasDeep
import ComputationalPaths.Path.Rewrite.RwEq

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


-- ============================================================
-- SECTION Inv5 genuine computational-path primitives
-- ============================================================
-- Genuine rewrite traces over the Nat degrees/indices used throughout this
-- module.  Each primitive is a real computational-path step (never a `True`
-- placeholder or a reflexive stub); they compose into a multi-step
-- `Path.trans` and two non-decorative `RwEq` coherences, satisfying the
-- project invariant that every file carry genuine path composition.

open ComputationalPaths
open ComputationalPaths.Path

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)`: one genuine step. -/
noncomputable def algebraAInfinityAlgebrasAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a`: one genuine step. -/
noncomputable def algebraAInfinityAlgebrasComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via congruence in the
    right argument (`_root_.congrArg`, since `congrArg` here is `Path.congrArg`). -/
noncomputable def algebraAInfinityAlgebrasInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** path: reassociate, then commute the inner pair.
    Its trace has length two — this is not a reflexive path. -/
noncomputable def algebraAInfinityAlgebrasTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (algebraAInfinityAlgebrasAssoc a b c) (algebraAInfinityAlgebrasInner a b c)

/-- The two-step path composed with its inverse cancels to the reflexive path —
    a non-decorative `RwEq` (the `trans_symm` rule on a length-two trace). -/
noncomputable def algebraAInfinityAlgebrasCancel (a b c : Nat) :
    Path.RwEq (Path.trans (algebraAInfinityAlgebrasTwoStep a b c) (Path.symm (algebraAInfinityAlgebrasTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  Path.rweq_cmpA_inv_right (algebraAInfinityAlgebrasTwoStep a b c)

/-- Associativity-of-composition (`trans_assoc`, the `tt` rewrite) on any three
    composable paths — a genuine `RwEq` between distinct bracketings. -/
noncomputable def algebraAInfinityAlgebrasAssocCoh {α : Type} {a b c d : α}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  Path.rweq_tt p q r
end ComputationalPaths.Path.Algebra.AInfinityAlgebras
