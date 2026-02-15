/-
# Signal Processing via Computational Paths

This module models signal processing concepts using computational paths:
signals as sequences, convolution, filtering, frequency domain analysis,
sampling, and Z-transform aspects.

## References

- Oppenheim & Willsky, "Signals and Systems"
- Proakis & Manolakis, "Digital Signal Processing"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace SignalPaths

universe u v

open ComputationalPaths.Path

/-! ## Signals and Samples -/

/-- A discrete signal sample: value at a time index. -/
structure SignalSample where
  timeIndex : Nat
  value : Nat

/-- Signal equivalence data: two signals agree at a sample point. -/
structure SignalEquivData where
  sample1 : Nat
  sample2 : Nat
  equivPath : Path sample1 sample2

/-- Signal equivalence path trans refl. -/
theorem signalEquiv_trans_refl (d : SignalEquivData) :
    Path.trans d.equivPath (Path.refl d.sample2) = d.equivPath := by
  simp

/-- Signal equivalence path refl trans. -/
theorem signalEquiv_refl_trans (d : SignalEquivData) :
    Path.trans (Path.refl d.sample1) d.equivPath = d.equivPath := by
  simp

/-- RwEq: signal equiv trans refl. -/
theorem signalEquiv_rweq_trans_refl (d : SignalEquivData) :
    RwEq
      (Path.trans d.equivPath (Path.refl d.sample2))
      d.equivPath :=
  rweq_of_step (Step.trans_refl_right d.equivPath)

/-- RwEq: signal equiv symm_symm. -/
theorem signalEquiv_rweq_symm_symm (d : SignalEquivData) :
    RwEq
      (Path.symm (Path.symm d.equivPath))
      d.equivPath :=
  rweq_of_step (Step.symm_symm d.equivPath)

/-! ## Convolution -/

/-- Convolution data: (x * h)[n] = Σ x[k]h[n-k]. -/
structure ConvolutionData where
  outputVal : Nat
  sumVal : Nat
  convPath : Path outputVal sumVal

/-- Convolution path trans refl. -/
theorem conv_trans_refl (d : ConvolutionData) :
    Path.trans d.convPath (Path.refl d.sumVal) = d.convPath := by
  simp

/-- RwEq: convolution inv cancel right. -/
theorem conv_rweq_inv_right (d : ConvolutionData) :
    RwEq
      (Path.trans d.convPath (Path.symm d.convPath))
      (Path.refl d.outputVal) :=
  rweq_cmpA_inv_right d.convPath

/-- RwEq: convolution symm_symm. -/
theorem conv_rweq_symm_symm (d : ConvolutionData) :
    RwEq
      (Path.symm (Path.symm d.convPath))
      d.convPath :=
  rweq_of_step (Step.symm_symm d.convPath)

/-- Convolution composition: (x*h1)*h2 = x*(h1*h2) as path associativity. -/
theorem conv_assoc {a b c d : Nat}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp

/-! ## Filtering -/

/-- Filter data: y[n] = H(x)[n] witnessed as a path. -/
structure FilterData where
  inputVal : Nat
  outputVal : Nat
  filterPath : Path inputVal outputVal

/-- Filter path trans refl. -/
theorem filter_trans_refl (d : FilterData) :
    Path.trans d.filterPath (Path.refl d.outputVal) = d.filterPath := by
  simp

/-- RwEq: filter refl trans. -/
theorem filter_rweq_refl_trans (d : FilterData) :
    RwEq
      (Path.trans (Path.refl d.inputVal) d.filterPath)
      d.filterPath :=
  rweq_of_step (Step.trans_refl_left d.filterPath)

/-- RwEq: filter inv cancel right. -/
theorem filter_rweq_inv_right (d : FilterData) :
    RwEq
      (Path.trans d.filterPath (Path.symm d.filterPath))
      (Path.refl d.inputVal) :=
  rweq_cmpA_inv_right d.filterPath

/-- Cascade of two filters composes via path trans. -/
def filterCascade {a b c : Nat} (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- Filter cascade is associative. -/
theorem filterCascade_assoc {a b c d : Nat}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    filterCascade (filterCascade p q) r =
    filterCascade p (filterCascade q r) := by
  simp [filterCascade]

/-! ## Frequency Domain -/

/-- Frequency domain data: X(ω) relates to x[n] via transform. -/
structure FreqData where
  timeDomVal : Nat
  freqDomVal : Nat
  transformPath : Path timeDomVal freqDomVal

/-- Transform path trans refl. -/
theorem freq_trans_refl (d : FreqData) :
    Path.trans d.transformPath (Path.refl d.freqDomVal) = d.transformPath := by
  simp

/-- RwEq: transform symm_symm. -/
theorem freq_rweq_symm_symm (d : FreqData) :
    RwEq
      (Path.symm (Path.symm d.transformPath))
      d.transformPath :=
  rweq_of_step (Step.symm_symm d.transformPath)

/-- RwEq: transform inv cancel right. -/
theorem freq_rweq_inv_right (d : FreqData) :
    RwEq
      (Path.trans d.transformPath (Path.symm d.transformPath))
      (Path.refl d.timeDomVal) :=
  rweq_cmpA_inv_right d.transformPath

/-! ## Sampling -/

/-- Sampling data: sampled signal relates to continuous via path. -/
structure SamplingData where
  continuousVal : Nat
  sampledVal : Nat
  samplingPath : Path continuousVal sampledVal

/-- Sampling path trans refl. -/
theorem sampling_trans_refl (d : SamplingData) :
    Path.trans d.samplingPath (Path.refl d.sampledVal) = d.samplingPath := by
  simp

/-- RwEq: sampling inv cancel left. -/
theorem sampling_rweq_inv_left (d : SamplingData) :
    RwEq
      (Path.trans (Path.symm d.samplingPath) d.samplingPath)
      (Path.refl d.sampledVal) :=
  rweq_cmpA_inv_left d.samplingPath

/-- RwEq: sampling symm_symm. -/
theorem sampling_rweq_symm_symm (d : SamplingData) :
    RwEq
      (Path.symm (Path.symm d.samplingPath))
      d.samplingPath :=
  rweq_of_step (Step.symm_symm d.samplingPath)

/-! ## Z-Transform Aspects -/

/-- Z-transform data: X(z) = Σ x[n]z^(-n). -/
structure ZTransformData where
  seqVal : Nat
  zVal : Nat
  zPath : Path seqVal zVal

/-- Z-transform path trans refl. -/
theorem ztransform_trans_refl (d : ZTransformData) :
    Path.trans d.zPath (Path.refl d.zVal) = d.zPath := by
  simp

/-- RwEq: Z-transform inv cancel right. -/
theorem ztransform_rweq_inv_right (d : ZTransformData) :
    RwEq
      (Path.trans d.zPath (Path.symm d.zPath))
      (Path.refl d.seqVal) :=
  rweq_cmpA_inv_right d.zPath

/-! ## congrArg for Signal Transforms -/

/-- Applying a signal transform to a path via congrArg. -/
theorem congrArg_signal {A B : Type u} (f : A → B)
    {x y : A} (p : Path x y) :
    Path.congrArg f (Path.trans p (Path.refl y)) =
    Path.congrArg f p := by
  simp

/-- congrArg preserves filter cascade composition. -/
theorem congrArg_filterCascade {A B : Type u} (f : A → B)
    {x y z : A} (p : Path x y) (q : Path y z) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) := by
  simp

/-- congrArg preserves signal symm. -/
theorem congrArg_signal_symm {A B : Type u} (f : A → B)
    {x y : A} (p : Path x y) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) := by
  simp

end SignalPaths
end Computation
end Path
end ComputationalPaths
