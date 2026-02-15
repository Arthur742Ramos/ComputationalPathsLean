/-
# Signal Processing via Computational Paths

Signals as sequences, convolution, filtering, frequency domain transforms,
modulation, sampling, quantization, noise, spectral analysis—all modeled
through computational paths.

## References

- Oppenheim & Willsky, "Signals and Systems"
- Haykin, "Communication Systems"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace SignalPaths

universe u v

open ComputationalPaths.Path

/-! ## Signal Samples -/

/-- A signal sample connecting two time-indexed values. -/
structure SignalSample where
  valAt : Nat
  valNext : Nat
  samplePath : Path valAt valNext

/-- Compose two signal samples in sequence. -/
def sampleCompose {a b c : Nat}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- Sample composition is associative. -/
theorem sampleCompose_assoc {a b c d : Nat}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    sampleCompose (sampleCompose p q) r = sampleCompose p (sampleCompose q r) := by
  simp [sampleCompose]

/-- Sample compose with refl right. -/
theorem sampleCompose_refl_right {a b : Nat} (p : Path a b) :
    sampleCompose p (Path.refl b) = p := by
  simp [sampleCompose]

/-- Sample compose with refl left. -/
theorem sampleCompose_refl_left {a b : Nat} (p : Path a b) :
    sampleCompose (Path.refl a) p = p := by
  simp [sampleCompose]

/-! ## Convolution -/

/-- Convolution data: output sample from convolving two signals. -/
structure ConvolutionData where
  inputVal : Nat
  kernelVal : Nat
  outputVal : Nat
  convPath : Path inputVal outputVal

/-- Convolution path trans refl. -/
theorem conv_trans_refl (d : ConvolutionData) :
    Path.trans d.convPath (Path.refl d.outputVal) = d.convPath := by
  simp

/-- RwEq: convolution inv cancel right. -/
theorem conv_rweq_inv_right (d : ConvolutionData) :
    RwEq
      (Path.trans d.convPath (Path.symm d.convPath))
      (Path.refl d.inputVal) :=
  rweq_cmpA_inv_right d.convPath

/-- RwEq: convolution symm_symm. -/
theorem conv_rweq_symm_symm (d : ConvolutionData) :
    RwEq (Path.symm (Path.symm d.convPath)) d.convPath :=
  rweq_of_step (Step.symm_symm d.convPath)

/-! ## Filtering -/

/-- Filter data: input passes through filter to produce output. -/
structure FilterData where
  inputSample : Nat
  outputSample : Nat
  filterPath : Path inputSample outputSample

/-- Filter path trans refl. -/
theorem filter_trans_refl (d : FilterData) :
    Path.trans d.filterPath (Path.refl d.outputSample) = d.filterPath := by
  simp

/-- RwEq: filter refl trans. -/
theorem filter_rweq_refl_trans (d : FilterData) :
    RwEq
      (Path.trans (Path.refl d.inputSample) d.filterPath)
      d.filterPath :=
  rweq_of_step (Step.trans_refl_left d.filterPath)

/-- RwEq: filter inv cancel left. -/
theorem filter_rweq_inv_left (d : FilterData) :
    RwEq
      (Path.trans (Path.symm d.filterPath) d.filterPath)
      (Path.refl d.outputSample) :=
  rweq_cmpA_inv_left d.filterPath

/-- Cascading two filters in series. -/
def filterCascade (d1 d2 : FilterData)
    (h : d1.outputSample = d2.inputSample) : Path d1.inputSample d2.outputSample :=
  Path.trans d1.filterPath (Path.trans (Path.ofEq h) d2.filterPath)

/-! ## Frequency Domain -/

/-- Frequency domain data: time domain relates to frequency domain. -/
structure FrequencyData where
  timeDomainVal : Nat
  freqDomainVal : Nat
  transformPath : Path timeDomainVal freqDomainVal

/-- The inverse transform path. -/
def inverseTransform (d : FrequencyData) : Path d.freqDomainVal d.timeDomainVal :=
  Path.symm d.transformPath

/-- Round-trip transform cancels (forward then inverse). -/
theorem freq_roundtrip_rweq (d : FrequencyData) :
    RwEq
      (Path.trans d.transformPath (inverseTransform d))
      (Path.refl d.timeDomainVal) :=
  rweq_cmpA_inv_right d.transformPath

/-- Round-trip inverse then forward cancels. -/
theorem freq_roundtrip_inv_rweq (d : FrequencyData) :
    RwEq
      (Path.trans (inverseTransform d) d.transformPath)
      (Path.refl d.freqDomainVal) :=
  rweq_cmpA_inv_left d.transformPath

/-- RwEq: transform symm_symm. -/
theorem freq_rweq_symm_symm (d : FrequencyData) :
    RwEq (Path.symm (Path.symm d.transformPath)) d.transformPath :=
  rweq_of_step (Step.symm_symm d.transformPath)

/-! ## Modulation -/

/-- Modulation data: baseband signal modulated to carrier. -/
structure ModulationData where
  basebandVal : Nat
  modulatedVal : Nat
  modPath : Path basebandVal modulatedVal

/-- Demodulation path. -/
def demodulate (d : ModulationData) : Path d.modulatedVal d.basebandVal :=
  Path.symm d.modPath

/-- Modulate then demodulate cancels. -/
theorem mod_demod_rweq (d : ModulationData) :
    RwEq
      (Path.trans d.modPath (demodulate d))
      (Path.refl d.basebandVal) :=
  rweq_cmpA_inv_right d.modPath

/-- Modulation path trans refl. -/
theorem mod_trans_refl (d : ModulationData) :
    Path.trans d.modPath (Path.refl d.modulatedVal) = d.modPath := by
  simp

/-! ## Sampling -/

/-- Sampling data: continuous value sampled to discrete. -/
structure SamplingData where
  continuousVal : Nat
  discreteVal : Nat
  samplePath : Path continuousVal discreteVal

/-- RwEq: sampling trans refl. -/
theorem sampling_rweq_trans_refl (d : SamplingData) :
    RwEq
      (Path.trans d.samplePath (Path.refl d.discreteVal))
      d.samplePath :=
  rweq_of_step (Step.trans_refl_right d.samplePath)

/-- RwEq: sampling inv cancel right. -/
theorem sampling_rweq_inv_right (d : SamplingData) :
    RwEq
      (Path.trans d.samplePath (Path.symm d.samplePath))
      (Path.refl d.continuousVal) :=
  rweq_cmpA_inv_right d.samplePath

/-! ## Quantization -/

/-- Quantization data: continuous sample quantized to discrete level. -/
structure QuantizationData where
  analogVal : Nat
  quantizedVal : Nat
  quantPath : Path analogVal quantizedVal

/-- Quantization error path (quantized minus analog). -/
theorem quant_rweq_symm_symm (d : QuantizationData) :
    RwEq (Path.symm (Path.symm d.quantPath)) d.quantPath :=
  rweq_of_step (Step.symm_symm d.quantPath)

/-- Quantization trans refl. -/
theorem quant_trans_refl (d : QuantizationData) :
    Path.trans d.quantPath (Path.refl d.quantizedVal) = d.quantPath := by
  simp

/-! ## Noise Channel -/

/-- Noise channel data: signal passes through noisy channel. -/
structure NoiseChannelData where
  cleanVal : Nat
  noisyVal : Nat
  noisePath : Path cleanVal noisyVal

/-- RwEq: noise channel inv cancel. -/
theorem noise_rweq_inv_right (d : NoiseChannelData) :
    RwEq
      (Path.trans d.noisePath (Path.symm d.noisePath))
      (Path.refl d.cleanVal) :=
  rweq_cmpA_inv_right d.noisePath

/-- RwEq: noise refl trans. -/
theorem noise_rweq_refl_trans (d : NoiseChannelData) :
    RwEq
      (Path.trans (Path.refl d.cleanVal) d.noisePath)
      d.noisePath :=
  rweq_of_step (Step.trans_refl_left d.noisePath)

/-! ## congrArg for Signal Paths -/

/-- Applying a signal transform f to a path via congrArg. -/
theorem congrArg_signal (f : Nat → Nat)
    {a b : Nat} (p : Path a b) :
    Path.congrArg f (Path.trans p (Path.refl b)) =
    Path.congrArg f p := by
  simp

/-- congrArg preserves sample composition. -/
theorem congrArg_sampleCompose (f : Nat → Nat)
    {a b c : Nat} (p : Path a b) (q : Path b c) :
    Path.congrArg f (sampleCompose p q) =
    sampleCompose (Path.congrArg f p) (Path.congrArg f q) := by
  simp [sampleCompose]

/-- congrArg preserves symm of signal paths. -/
theorem congrArg_signal_symm (f : Nat → Nat)
    {a b : Nat} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) := by
  simp

/-! ## Signal Iteration -/

/-- Iterate a signal processing step n times. -/
def signalIterate {a : Nat} (p : Path a a) : Nat → Path a a
  | 0 => Path.refl a
  | n + 1 => Path.trans (signalIterate p n) p

/-- Signal iterate zero is refl. -/
theorem signalIterate_zero {a : Nat} (p : Path a a) :
    signalIterate p 0 = Path.refl a := rfl

/-- RwEq: signal iterate 1 simplifies. -/
theorem signalIterate_one_rweq {a : Nat} (p : Path a a) :
    RwEq (signalIterate p 1) p :=
  rweq_of_step (Step.trans_refl_left p)

end SignalPaths
end Computation
end Path
end ComputationalPaths
