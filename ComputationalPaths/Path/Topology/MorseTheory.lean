/-
# MorseTheory

Morse theory via computational paths.

This public module exposes representative computational-path constructions from
`MorseTheoryDeep` in the `ComputationalPaths.Path.Topology.MorseTheory`
namespace. The deep module already belongs to the public import graph, so these
definitions focus on giving users a coherent, discoverable surface.
-/

import ComputationalPaths.Path.Topology.MorseTheoryDeep

namespace ComputationalPaths.Path.Topology.MorseTheory

open ComputationalPaths

universe u

/-! ## Representative Morse-theoretic paths -/

private theorem atomic_path_length {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A)
    {a b : A}
    (s : ComputationalPaths.MorseTheoryDeep.MorseAlg.MorseStep (M := M) a b) :
    _root_.ComputationalPaths.Path.length
      (ComputationalPaths.MorseTheoryDeep.MorseAlg.MorseStep.toPath (M := M) s) = 1 := by
  cases s <;> rfl

@[inline] noncomputable def crit_flow_fixed_path {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A) (p : A) :=
  ComputationalPaths.MorseTheoryDeep.MorseAlg.crit_flow_fixed_path (M := M) p

theorem crit_flow_fixed_path_length {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A) (p : A) :
    _root_.ComputationalPaths.Path.length (crit_flow_fixed_path M p) = 1 := by
  simpa [crit_flow_fixed_path,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.crit_flow_fixed_path] using
      atomic_path_length (M := M)
        (s := ComputationalPaths.MorseTheoryDeep.MorseAlg.MorseStep.flow_crit_fixed (M := M) p)

@[inline] noncomputable def flow_flow_crit_to_crit {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A) (p : A) :=
  ComputationalPaths.MorseTheoryDeep.MorseAlg.flow_flow_crit_to_crit (M := M) p

theorem flow_flow_crit_to_crit_length {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A) (p : A) :
    _root_.ComputationalPaths.Path.length (flow_flow_crit_to_crit M p) = 2 := by
  simp [flow_flow_crit_to_crit,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.flow_flow_crit_to_crit,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.flow_idempotent_on_crit_path,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.crit_flow_fixed_path,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.MorseStep.toPath]

@[inline] noncomputable def attach_unit_twice {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A) (p : A) :=
  ComputationalPaths.MorseTheoryDeep.MorseAlg.attach_unit_twice (M := M) p

theorem attach_unit_twice_length {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A) (p : A) :
    _root_.ComputationalPaths.Path.length (attach_unit_twice M p) = 2 := by
  simp [attach_unit_twice,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.attach_unit_twice,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.attach_unit_path,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.MorseStep.toPath]

@[inline] noncomputable def cell_cell_attach_3step {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A) (p q : A) :=
  ComputationalPaths.MorseTheoryDeep.MorseAlg.cell_cell_attach_3step (M := M) p q

theorem cell_cell_attach_3step_length {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A) (p q : A) :
    _root_.ComputationalPaths.Path.length (cell_cell_attach_3step M p q) = 2 := by
  simp [cell_cell_attach_3step,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.cell_cell_attach_3step,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.cell_idem_path,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.cell_attach_path,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.MorseStep.toPath]

@[inline] noncomputable def euler_to_crit {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A) (p : A) :=
  ComputationalPaths.MorseTheoryDeep.MorseAlg.euler_to_crit (M := M) p

theorem euler_to_crit_length {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A) (p : A) :
    _root_.ComputationalPaths.Path.length (euler_to_crit M p) = 2 := by
  simp [euler_to_crit,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.euler_to_crit,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.euler_to_betti,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.betti_to_crit,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.MorseStep.toPath]

@[inline] noncomputable def handle_cancel_3step {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A) (p q : A) :=
  ComputationalPaths.MorseTheoryDeep.MorseAlg.handle_cancel_3step (M := M) p q

theorem handle_cancel_3step_length {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A) (p q : A) :
    _root_.ComputationalPaths.Path.length (handle_cancel_3step M p q) = 2 := by
  simp [handle_cancel_3step,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.handle_cancel_3step,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.attach_assoc_path,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.attach_unit_path,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.MorseStep.toPath]

@[inline] noncomputable def bdry_nested_to_base {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A) (p : A) :=
  ComputationalPaths.MorseTheoryDeep.MorseAlg.bdry_nested_to_base (M := M) p

theorem bdry_nested_to_base_length {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A) (p : A) :
    _root_.ComputationalPaths.Path.length (bdry_nested_to_base M p) = 2 := by
  simp [bdry_nested_to_base,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.bdry_nested_to_base,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.bdry_nested_congrArg,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.crit_flow_fixed_path,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.bdry_squared_path,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.MorseStep.toPath]

@[inline] noncomputable def euler_cobord_id {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A) (p : A) :=
  ComputationalPaths.MorseTheoryDeep.MorseAlg.euler_cobord_id (M := M) p

theorem euler_cobord_id_length {A : Type u}
    (M : ComputationalPaths.MorseTheoryDeep.MorseAlg A) (p : A) :
    _root_.ComputationalPaths.Path.length (euler_cobord_id M p) = 3 := by
  simp [euler_cobord_id,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.euler_cobord_id,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.cobord_id_path,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.euler_to_crit,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.euler_to_betti,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.betti_to_crit,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.MorseStep.toPath]

@[inline] noncomputable def trivialAlg :=
  ComputationalPaths.MorseTheoryDeep.Instances.trivial

@[inline] noncomputable def trivial_attach_unit_loop (p : PUnit) :=
  ComputationalPaths.MorseTheoryDeep.MorseAlg.attach_unit_loop (M := trivialAlg) p

theorem trivial_attach_unit_loop_length (p : PUnit) :
    _root_.ComputationalPaths.Path.length (trivial_attach_unit_loop p) = 2 := by
  simp [trivial_attach_unit_loop, trivialAlg,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.attach_unit_loop,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.attach_unit_path,
    ComputationalPaths.MorseTheoryDeep.MorseAlg.MorseStep.toPath]

end ComputationalPaths.Path.Topology.MorseTheory
