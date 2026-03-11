/-
# PersistentHomology

Persistent homology via computational paths.

This public wrapper re-exports representative persistent-homology traces from
`PersistentHomologyDeep` into the
`ComputationalPaths.Path.Topology.PersistentHomology` namespace.
-/

import ComputationalPaths.Path.Topology.PersistentHomologyDeep

namespace ComputationalPaths.Path.Topology.PersistentHomology

open ComputationalPaths

universe u

/-! ## Representative persistent-homology traces -/

@[inline] noncomputable def ph_filt_chain {A : Sort u}
    (sub : A → A) (a : A) :=
  ComputationalPaths.ph_filt_chain sub a

theorem ph_filt_chain_length {A : Sort u}
    (sub : A → A) (a : A) :
    ComputationalPaths.PHPath.length (ph_filt_chain sub a) = 2 := rfl

@[inline] noncomputable def ph_birth_death_cycle {A : Sort u}
    (b d : A → A) (a : A) :=
  ComputationalPaths.ph_birth_death_cycle b d a

theorem ph_birth_death_cycle_length {A : Sort u}
    (b d : A → A) (a : A) :
    ComputationalPaths.PHPath.length (ph_birth_death_cycle b d a) = 2 := rfl

@[inline] noncomputable def ph_barcode_filt {A : Sort u}
    (dec inc : A → A) (a : A) :=
  ComputationalPaths.ph_barcode_filt dec inc a

theorem ph_barcode_filt_length {A : Sort u}
    (dec inc : A → A) (a : A) :
    ComputationalPaths.PHPath.length (ph_barcode_filt dec inc a) = 2 := rfl

@[inline] noncomputable def ph_bottleneck_triangle {A : Sort u}
    (d max : A → A → A) (a b c : A) :=
  ComputationalPaths.ph_bottleneck_triangle d max a b c

theorem ph_bottleneck_triangle_length {A : Sort u}
    (d max : A → A → A) (a b c : A) :
    ComputationalPaths.PHPath.length (ph_bottleneck_triangle d max a b c) = 1 := rfl

@[inline] noncomputable def ph_bd_barcode {A : Sort u}
    (b d bar : A → A) (a : A) :=
  ComputationalPaths.ph_bd_barcode b d bar a

theorem ph_bd_barcode_length {A : Sort u}
    (b d bar : A → A) (a : A) :
    ComputationalPaths.PHPath.length (ph_bd_barcode b d bar a) = 2 := rfl

@[inline] noncomputable def ph_pipeline {A : Sort u}
    (rips bar dec : A → A) (a : A) :=
  ComputationalPaths.ph_pipeline rips bar dec a

theorem ph_pipeline_length {A : Sort u}
    (rips bar dec : A → A) (a : A) :
    ComputationalPaths.PHPath.length (ph_pipeline rips bar dec a) = 2 := rfl

@[inline] noncomputable def ph_stability_chain {A : Sort u}
    (il bn : A → A → A) (f : A → A) (a b : A) :=
  ComputationalPaths.ph_stability_chain il bn f a b

theorem ph_stability_chain_length {A : Sort u}
    (il bn : A → A → A) (f : A → A) (a b : A) :
    ComputationalPaths.PHPath.length (ph_stability_chain il bn f a b) = 1 := rfl

@[inline] noncomputable def ph_diagram_from_filt {A : Sort u}
    (inc dec : A → A) (a : A) :=
  ComputationalPaths.ph_diagram_from_filt inc dec a

theorem ph_diagram_from_filt_length {A : Sort u}
    (inc dec : A → A) (a : A) :
    ComputationalPaths.PHPath.length (ph_diagram_from_filt inc dec a) = 2 := rfl

@[inline] noncomputable def ph_interleaving_rips_cech {A : Sort u}
    (il : A → A → A) (rips cech : A → A) (a : A) :=
  ComputationalPaths.ph_interleaving_rips_cech il rips cech a

theorem ph_interleaving_rips_cech_length {A : Sort u}
    (il : A → A → A) (rips cech : A → A) (a : A) :
    ComputationalPaths.PHPath.length (ph_interleaving_rips_cech il rips cech a) = 1 := rfl

end ComputationalPaths.Path.Topology.PersistentHomology
