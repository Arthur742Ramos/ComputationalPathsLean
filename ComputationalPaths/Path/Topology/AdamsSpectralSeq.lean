/-
# AdamsSpectralSeq

Adams spectral-sequence traces via computational paths.

This public wrapper surfaces representative constructions from
`AdamsSpectralSeqDeep` under the `ComputationalPaths.Path.Topology.AdamsSpectralSeq`
namespace, replacing the previous placeholder with usable spectral-sequence
interfaces and small length facts about the resulting traces.
-/

import ComputationalPaths.Path.Topology.AdamsSpectralSeqDeep

namespace ComputationalPaths.Path.Topology.AdamsSpectralSeq

open ComputationalPaths

universe u

/-! ## Representative Adams spectral-sequence paths -/

@[inline] noncomputable def filt_compose_path {A : Sort u} (f g : A → A) (a : A) :=
  ComputationalPaths.filt_compose_path f g a

theorem filt_compose_path_length {A : Sort u} (f g : A → A) (a : A) :
    ComputationalPaths.AdamsPath.length (filt_compose_path f g a) = 1 := rfl

@[inline] noncomputable def d2_square_zero_path {A : Sort u} (d : A → A) (a : A) :=
  ComputationalPaths.d2_square_zero_path d a

theorem d2_square_zero_path_length {A : Sort u} (d : A → A) (a : A) :
    ComputationalPaths.AdamsPath.length (d2_square_zero_path d a) = 1 := rfl

@[inline] noncomputable def convergence_roundtrip {A : Sort u}
    (lim filt : A → A) (a : A) :=
  ComputationalPaths.convergence_roundtrip lim filt a

theorem convergence_roundtrip_length {A : Sort u}
    (lim filt : A → A) (a : A) :
    ComputationalPaths.AdamsPath.length (convergence_roundtrip lim filt a) = 2 := rfl

@[inline] noncomputable def double_periodicity {A : Sort u} (v : A → A) (a : A) :=
  ComputationalPaths.double_periodicity v a

theorem double_periodicity_length {A : Sort u} (v : A → A) (a : A) :
    ComputationalPaths.AdamsPath.length (double_periodicity v a) = 1 := rfl

@[inline] noncomputable def stem_computation {A : Sort u} (lim e : A → A) (a : A) :=
  ComputationalPaths.stem_computation lim e a

theorem stem_computation_length {A : Sort u} (lim e : A → A) (a : A) :
    ComputationalPaths.AdamsPath.length (stem_computation lim e a) = 2 := rfl

@[inline] noncomputable def filt_conv_compose {A : Sort u}
    (filt lim : A → A) (a : A) :=
  ComputationalPaths.filt_conv_compose filt lim a

theorem filt_conv_compose_length {A : Sort u}
    (filt lim : A → A) (a : A) :
    ComputationalPaths.AdamsPath.length (filt_conv_compose filt lim a) = 2 := rfl

@[inline] noncomputable def adams_full_chain {A : Sort u}
    (d ext lim e : A → A) (a : A) :=
  ComputationalPaths.adams_full_chain d ext lim e a

theorem adams_full_chain_length {A : Sort u}
    (d ext lim e : A → A) (a : A) :
    ComputationalPaths.AdamsPath.length (adams_full_chain d ext lim e a) = 2 := rfl

@[inline] noncomputable def adams_periodicity {A : Sort u}
    (v ext lim : A → A) (a : A) :=
  ComputationalPaths.adams_periodicity v ext lim a

theorem adams_periodicity_length {A : Sort u}
    (v ext lim : A → A) (a : A) :
    ComputationalPaths.AdamsPath.length (adams_periodicity v ext lim a) = 1 := rfl

end ComputationalPaths.Path.Topology.AdamsSpectralSeq
