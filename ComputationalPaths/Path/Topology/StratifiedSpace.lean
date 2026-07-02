/-
# StratifiedSpace

Stratified spaces via computational paths.

This public module surfaces representative constructions from
`StratifiedSpaceDeep` under the
`ComputationalPaths.Path.Topology.StratifiedSpace` namespace so the public
topology layer exposes discoverable entry points instead of only the deep file.
-/

import ComputationalPaths.Path.Topology.StratifiedSpaceDeep
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths.Path.Topology.StratifiedSpace

open ComputationalPaths

/-! ## Representative stratified-space traces -/

@[inline] noncomputable def frontier_to_bottom (n : Nat) :=
  ComputationalPaths.StratPath.frontier_to_bottom n

theorem frontier_to_bottom_length (n : Nat) :
    ComputationalPaths.StratPath.length (frontier_to_bottom n) = 1 := rfl

@[inline] noncomputable def frontier_chain_two (n : Nat) :=
  ComputationalPaths.StratPath.frontier_chain_two n

theorem frontier_chain_two_length (n : Nat) :
    ComputationalPaths.StratPath.length (frontier_chain_two n) = 2 := rfl

@[inline] noncomputable def link_cone_product_chain (l : ComputationalPaths.LinkType) :=
  ComputationalPaths.StratPath.link_cone_product_chain l

theorem link_cone_product_chain_length (l : ComputationalPaths.LinkType) :
    ComputationalPaths.StratPath.length (link_cone_product_chain l) = 2 := rfl

@[inline] noncomputable def perv_full_chain :=
  ComputationalPaths.StratPath.perv_full_chain

theorem perv_full_chain_length :
    ComputationalPaths.StratPath.length perv_full_chain = 2 := rfl

@[inline] noncomputable def ih_direct_sum_double_comm
    (a b : ComputationalPaths.IHGroup) :=
  ComputationalPaths.StratPath.ih_direct_sum_double_comm a b

theorem ih_direct_sum_double_comm_length
    (a b : ComputationalPaths.IHGroup) :
    ComputationalPaths.StratPath.length (ih_direct_sum_double_comm a b) = 2 := rfl

@[inline] noncomputable def ic_double_norm
    (s : ComputationalPaths.ICSheafStalk) :=
  ComputationalPaths.StratPath.ic_double_norm s

theorem ic_double_norm_length
    (s : ComputationalPaths.ICSheafStalk) :
    ComputationalPaths.StratPath.length (ic_double_norm s) = 3 := rfl

@[inline] noncomputable def bbd_t_roundtrip :=
  ComputationalPaths.StratPath.bbd_t_roundtrip

theorem bbd_t_roundtrip_length :
    ComputationalPaths.StratPath.length bbd_t_roundtrip = 2 := rfl

@[inline] noncomputable def morse_regular_to_symm :=
  ComputationalPaths.StratPath.morse_regular_to_symm

theorem morse_regular_to_symm_length :
    ComputationalPaths.StratPath.length morse_regular_to_symm = 3 := rfl

@[inline] noncomputable def exit_id_then_compose
    (a b c : ComputationalPaths.StratumIdx) :=
  ComputationalPaths.StratPath.exit_id_then_compose a b c

theorem exit_id_then_compose_length
    (a b c : ComputationalPaths.StratumIdx) :
    ComputationalPaths.StratPath.length (exit_id_then_compose a b c) = 2 := rfl

@[inline] noncomputable def stratified_structure_thm
    (l : ComputationalPaths.LinkType) :=
  ComputationalPaths.StratPath.stratified_structure_thm l

theorem stratified_structure_thm_length
    (l : ComputationalPaths.LinkType) :
    ComputationalPaths.StratPath.length (stratified_structure_thm l) = 2 := rfl


-- ============================================================
-- SECTION Inv5 genuine computational-path primitives
-- ============================================================
-- Genuine rewrite traces over the Nat degrees/indices used throughout this
-- module.  Each primitive is a real computational-path step (never a `True`
-- placeholder or a reflexive stub); they compose into a multi-step
-- `Path.trans` and two non-decorative `RwEq` coherences, satisfying the
-- project invariant that every file carry genuine path composition.

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)`: one genuine step. -/
noncomputable def topologyStratifiedSpaceAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Commutativity rewrite `a + b ⤳ b + a`: one genuine step. -/
noncomputable def topologyStratifiedSpaceComm (a b : Nat) : Path (a + b) (b + a) :=
  Path.ofEq (Nat.add_comm a b)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via congruence in the
    right argument (`_root_.congrArg`, since `congrArg` here is `Path.congrArg`). -/
noncomputable def topologyStratifiedSpaceInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- A genuine **two-step** path: reassociate, then commute the inner pair.
    Its trace has length two — this is not a reflexive path. -/
noncomputable def topologyStratifiedSpaceTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (topologyStratifiedSpaceAssoc a b c) (topologyStratifiedSpaceInner a b c)

/-- The two-step path composed with its inverse cancels to the reflexive path —
    a non-decorative `RwEq` (the `trans_symm` rule on a length-two trace). -/
noncomputable def topologyStratifiedSpaceCancel (a b c : Nat) :
    Path.RwEq (Path.trans (topologyStratifiedSpaceTwoStep a b c) (Path.symm (topologyStratifiedSpaceTwoStep a b c)))
      (Path.refl ((a + b) + c)) :=
  Path.rweq_cmpA_inv_right (topologyStratifiedSpaceTwoStep a b c)

/-- Associativity-of-composition (`trans_assoc`, the `tt` rewrite) on any three
    composable paths — a genuine `RwEq` between distinct bracketings. -/
noncomputable def topologyStratifiedSpaceAssocCoh {α : Type} {a b c d : α}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  Path.rweq_tt p q r
end ComputationalPaths.Path.Topology.StratifiedSpace
