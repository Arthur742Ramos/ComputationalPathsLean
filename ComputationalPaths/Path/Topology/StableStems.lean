/-
# StableStems

Stable stems via computational paths.

This public wrapper re-exports representative stable-stem traces from
`StableStemsDeep` into the `ComputationalPaths.Path.Topology.StableStems`
namespace, replacing the previous placeholder with a usable interface.
-/

import ComputationalPaths.Path.Topology.StableStemsDeep

namespace ComputationalPaths.Path.Topology.StableStems

open ComputationalPaths

universe u

/-! ## Representative stable-stem traces -/

@[inline] noncomputable def stem_double_susp {A : Sort u} (sigma : A → A) (a : A) :=
  ComputationalPaths.stem_double_susp sigma a

theorem stem_double_susp_length {A : Sort u} (sigma : A → A) (a : A) :
    ComputationalPaths.StemPath.length (stem_double_susp sigma a) = 2 := rfl

@[inline] noncomputable def j_roundtrip {A : Sort u} (j : A → A) (a : A) :=
  ComputationalPaths.j_roundtrip j a

theorem j_roundtrip_length {A : Sort u} (j : A → A) (a : A) :
    ComputationalPaths.StemPath.length (j_roundtrip j a) = 2 := rfl

@[inline] noncomputable def greek_chain {A : Sort u} (alpha_ beta_ gamma_ : A → A) (a : A) :=
  ComputationalPaths.greek_chain alpha_ beta_ gamma_ a

theorem greek_chain_length {A : Sort u} (alpha_ beta_ gamma_ : A → A) (a : A) :
    ComputationalPaths.StemPath.length (greek_chain alpha_ beta_ gamma_ a) = 1 := rfl

@[inline] noncomputable def toda_juggling_path {A : Sort u}
    (toda : A → A → A → A) (f : A → A) (a b c : A) :=
  ComputationalPaths.toda_juggling_path toda f a b c

theorem toda_juggling_path_length {A : Sort u}
    (toda : A → A → A → A) (f : A → A) (a b c : A) :
    ComputationalPaths.StemPath.length (toda_juggling_path toda f a b c) = 1 := rfl

@[inline] noncomputable def adams_psi_compose_path {A : Sort u}
    (psi₁ psi₂ : A → A) (a : A) :=
  ComputationalPaths.adams_psi_compose_path psi₁ psi₂ a

theorem adams_psi_compose_path_length {A : Sort u}
    (psi₁ psi₂ : A → A) (a : A) :
    ComputationalPaths.StemPath.length (adams_psi_compose_path psi₁ psi₂ a) = 1 := rfl

@[inline] noncomputable def kervaire_double {A : Sort u} (kerv : A → A) (a : A) :=
  ComputationalPaths.kervaire_double kerv a

theorem kervaire_double_length {A : Sort u} (kerv : A → A) (a : A) :
    ComputationalPaths.StemPath.length (kervaire_double kerv a) = 2 := rfl

@[inline] noncomputable def stem_full_pipeline {A : Sort u}
    (sigma stab j : A → A) (a : A) :=
  ComputationalPaths.stem_full_pipeline sigma stab j a

theorem stem_full_pipeline_length {A : Sort u}
    (sigma stab j : A → A) (a : A) :
    ComputationalPaths.StemPath.length (stem_full_pipeline sigma stab j a) = 2 := rfl

@[inline] noncomputable def hurewicz_kervaire {A : Sort u}
    (h kerv : A → A) (a : A) :=
  ComputationalPaths.hurewicz_kervaire h kerv a

theorem hurewicz_kervaire_length {A : Sort u}
    (h kerv : A → A) (a : A) :
    ComputationalPaths.StemPath.length (hurewicz_kervaire h kerv a) = 1 := rfl

@[inline] noncomputable def chromatic_tower {A : Sort u}
    (v lvl alpha_ : A → A) (a : A) :=
  ComputationalPaths.chromatic_tower v lvl alpha_ a

theorem chromatic_tower_length {A : Sort u}
    (v lvl alpha_ : A → A) (a : A) :
    ComputationalPaths.StemPath.length (chromatic_tower v lvl alpha_ a) = 1 := rfl

end ComputationalPaths.Path.Topology.StableStems
