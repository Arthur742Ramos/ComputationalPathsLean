/-
# StratifiedSpace

Stratified spaces via computational paths.

This public module surfaces representative constructions from
`StratifiedSpaceDeep` under the
`ComputationalPaths.Path.Topology.StratifiedSpace` namespace so the public
topology layer exposes discoverable entry points instead of only the deep file.
-/

import ComputationalPaths.Path.Topology.StratifiedSpaceDeep

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

end ComputationalPaths.Path.Topology.StratifiedSpace
