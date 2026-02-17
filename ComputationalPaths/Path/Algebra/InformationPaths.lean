/-
# Information Theory via Computational Paths

This module models information-theoretic concepts using computational paths:
entropy as path measure, mutual information, data processing inequality
aspects, Kullback-Leibler divergence properties, source coding, and
channel capacity.

## References

- Cover & Thomas, "Elements of Information Theory"
- Shannon, "A Mathematical Theory of Communication"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace InformationPaths

universe u v

open ComputationalPaths.Path

/-! ## Entropy as Path Measure -/

/-- Entropy data for a discrete distribution. -/
structure EntropyData where
  distribution : List Nat   -- probability weights
  entropyVal : Nat           -- H(X) (scaled)
  totalWeight : Nat
  normPath : Path (distribution.foldl (· + ·) 0) totalWeight

/-- Two entropy data are equivalent if they have the same entropy value. -/
def entropyEquiv (d1 d2 : EntropyData) : Prop :=
  d1.entropyVal = d2.entropyVal

/-- Entropy equivalence is reflexive. -/
theorem entropyEquiv_refl (d : EntropyData) : entropyEquiv d d := rfl

/-- Entropy equivalence is symmetric. -/
theorem entropyEquiv_symm {d1 d2 : EntropyData}
    (h : entropyEquiv d1 d2) : entropyEquiv d2 d1 := h.symm

/-- Entropy equivalence is transitive. -/
theorem entropyEquiv_trans {d1 d2 d3 : EntropyData}
    (h1 : entropyEquiv d1 d2) (h2 : entropyEquiv d2 d3) :
    entropyEquiv d1 d3 := h1.trans h2

/-- Path from entropy equivalence. -/
def entropyEquiv_path {d1 d2 : EntropyData}
    (h : entropyEquiv d1 d2) : Path d1.entropyVal d2.entropyVal :=
  Path.mk [Step.mk _ _ h] h

/-- Normalization path trans refl. -/
theorem entropy_norm_trans_refl (d : EntropyData) :
    Path.trans d.normPath (Path.refl d.totalWeight) = d.normPath := by
  simp

/-- RwEq: entropy norm trans refl. -/
theorem entropy_rweq_trans_refl (d : EntropyData) :
    RwEq
      (Path.trans d.normPath (Path.refl d.totalWeight))
      d.normPath :=
  rweq_of_step (Step.trans_refl_right d.normPath)

/-- RwEq: entropy norm inv cancel right. -/
theorem entropy_rweq_inv_right (d : EntropyData) :
    RwEq
      (Path.trans d.normPath (Path.symm d.normPath))
      (Path.refl (d.distribution.foldl (· + ·) 0)) :=
  rweq_cmpA_inv_right d.normPath

/-- RwEq: entropy norm symm_symm. -/
theorem entropy_rweq_symm_symm (d : EntropyData) :
    RwEq
      (Path.symm (Path.symm d.normPath))
      d.normPath :=
  rweq_of_step (Step.symm_symm d.normPath)

/-! ## Joint and Conditional Entropy -/

/-- Joint entropy data: H(X,Y). -/
structure JointEntropyData where
  jointEntropy : Nat
  marginalX : Nat
  marginalY : Nat
  condEntropy : Nat  -- H(Y|X)
  chainPath : Path jointEntropy (marginalX + condEntropy)

/-- Chain rule path trans refl. -/
theorem chain_trans_refl (d : JointEntropyData) :
    Path.trans d.chainPath (Path.refl (d.marginalX + d.condEntropy)) =
    d.chainPath := by
  simp

/-- RwEq: chain rule trans refl. -/
theorem chain_rweq_trans_refl (d : JointEntropyData) :
    RwEq
      (Path.trans d.chainPath (Path.refl (d.marginalX + d.condEntropy)))
      d.chainPath :=
  rweq_of_step (Step.trans_refl_right d.chainPath)

/-- RwEq: chain rule inv cancel. -/
theorem chain_rweq_inv_right (d : JointEntropyData) :
    RwEq
      (Path.trans d.chainPath (Path.symm d.chainPath))
      (Path.refl d.jointEntropy) :=
  rweq_cmpA_inv_right d.chainPath

/-- RwEq: chain rule refl trans. -/
theorem chain_rweq_refl_trans (d : JointEntropyData) :
    RwEq
      (Path.trans (Path.refl d.jointEntropy) d.chainPath)
      d.chainPath :=
  rweq_of_step (Step.trans_refl_left d.chainPath)

/-! ## Mutual Information -/

/-- Mutual information data: I(X;Y) = H(X) + H(Y) - H(X,Y). -/
structure MutualInfoData where
  entropyX : Nat
  entropyY : Nat
  jointEntropy : Nat
  mutualInfo : Nat
  sumEntropies : Nat
  sumPath : Path sumEntropies (entropyX + entropyY)
  miPath : Path (mutualInfo + jointEntropy) sumEntropies

/-- Mutual information path composition. -/
def mi_composed_path (d : MutualInfoData) :
    Path (d.mutualInfo + d.jointEntropy) (d.entropyX + d.entropyY) :=
  Path.trans d.miPath d.sumPath

/-- MI composed path trans refl. -/
theorem mi_trans_refl (d : MutualInfoData) :
    Path.trans d.miPath (Path.refl d.sumEntropies) = d.miPath := by
  simp

/-- MI symmetry distributes over composition. -/
theorem mi_symm_trans (d : MutualInfoData) :
    Path.symm (mi_composed_path d) =
    Path.trans (Path.symm d.sumPath) (Path.symm d.miPath) := by
  simp [mi_composed_path]

/-- RwEq: MI path trans refl. -/
theorem mi_rweq_trans_refl (d : MutualInfoData) :
    RwEq
      (Path.trans d.miPath (Path.refl d.sumEntropies))
      d.miPath :=
  rweq_of_step (Step.trans_refl_right d.miPath)

/-- RwEq: MI path inv cancel. -/
theorem mi_rweq_inv_right (d : MutualInfoData) :
    RwEq
      (Path.trans d.miPath (Path.symm d.miPath))
      (Path.refl (d.mutualInfo + d.jointEntropy)) :=
  rweq_cmpA_inv_right d.miPath

/-- RwEq: MI symm_symm. -/
theorem mi_rweq_symm_symm (d : MutualInfoData) :
    RwEq
      (Path.symm (Path.symm d.miPath))
      d.miPath :=
  rweq_of_step (Step.symm_symm d.miPath)

/-! ## KL Divergence -/

/-- KL divergence data: D(P||Q) with path witness. -/
structure KLDivData where
  klVal : Nat
  crossEntropy : Nat
  entropyP : Nat
  klPath : Path klVal (crossEntropy + entropyP)

/-- KL divergence path trans refl. -/
theorem kl_trans_refl (d : KLDivData) :
    Path.trans d.klPath (Path.refl (d.crossEntropy + d.entropyP)) =
    d.klPath := by
  simp

/-- RwEq: KL divergence trans refl. -/
theorem kl_rweq_trans_refl (d : KLDivData) :
    RwEq
      (Path.trans d.klPath (Path.refl (d.crossEntropy + d.entropyP)))
      d.klPath :=
  rweq_of_step (Step.trans_refl_right d.klPath)

/-- RwEq: KL divergence inv cancel. -/
theorem kl_rweq_inv_right (d : KLDivData) :
    RwEq
      (Path.trans d.klPath (Path.symm d.klPath))
      (Path.refl d.klVal) :=
  rweq_cmpA_inv_right d.klPath

/-- RwEq: KL divergence inv cancel left. -/
theorem kl_rweq_inv_left (d : KLDivData) :
    RwEq
      (Path.trans (Path.symm d.klPath) d.klPath)
      (Path.refl (d.crossEntropy + d.entropyP)) :=
  rweq_cmpA_inv_left d.klPath

/-- RwEq: KL symm_symm. -/
theorem kl_rweq_symm_symm (d : KLDivData) :
    RwEq
      (Path.symm (Path.symm d.klPath))
      d.klPath :=
  rweq_of_step (Step.symm_symm d.klPath)

/-! ## Data Processing Inequality -/

/-- Data processing data: for Markov chain X → Y → Z, I(X;Z) ≤ I(X;Y). -/
structure DataProcessingData where
  miXY : Nat
  miXZ : Nat
  gap : Nat
  dpPath : Path (miXZ + gap) miXY

/-- Data processing path trans refl. -/
theorem dp_trans_refl (d : DataProcessingData) :
    Path.trans d.dpPath (Path.refl d.miXY) = d.dpPath := by
  simp

/-- RwEq: data processing trans refl. -/
theorem dp_rweq_trans_refl (d : DataProcessingData) :
    RwEq
      (Path.trans d.dpPath (Path.refl d.miXY))
      d.dpPath :=
  rweq_of_step (Step.trans_refl_right d.dpPath)

/-- RwEq: data processing inv cancel. -/
theorem dp_rweq_inv_right (d : DataProcessingData) :
    RwEq
      (Path.trans d.dpPath (Path.symm d.dpPath))
      (Path.refl (d.miXZ + d.gap)) :=
  rweq_cmpA_inv_right d.dpPath

/-! ## Source Coding -/

/-- Source coding data: rate ≥ entropy for lossless coding. -/
structure SourceCodingData where
  rate : Nat
  entropy : Nat
  slack : Nat
  codingPath : Path rate (entropy + slack)

/-- Source coding path trans refl. -/
theorem coding_trans_refl (d : SourceCodingData) :
    Path.trans d.codingPath (Path.refl (d.entropy + d.slack)) =
    d.codingPath := by
  simp

/-- RwEq: source coding trans refl. -/
theorem coding_rweq_trans_refl (d : SourceCodingData) :
    RwEq
      (Path.trans d.codingPath (Path.refl (d.entropy + d.slack)))
      d.codingPath :=
  rweq_of_step (Step.trans_refl_right d.codingPath)

/-- RwEq: source coding inv cancel. -/
theorem coding_rweq_inv_right (d : SourceCodingData) :
    RwEq
      (Path.trans d.codingPath (Path.symm d.codingPath))
      (Path.refl d.rate) :=
  rweq_cmpA_inv_right d.codingPath

/-! ## CongrArg and Transport -/

/-- CongrArg for distribution sums. -/
theorem dist_congrArg {d1 d2 : List Nat}
    (h : d1 = d2) : d1.foldl (· + ·) 0 = d2.foldl (· + ·) 0 :=
  _root_.congrArg (fun l => l.foldl (· + ·) 0) h

/-- Path from congrArg on distributions. -/
def dist_congrArg_path {d1 d2 : List Nat}
    (h : d1 = d2) : Path (d1.foldl (· + ·) 0) (d2.foldl (· + ·) 0) :=
  Path.mk [Step.mk _ _ (_root_.congrArg (fun l => l.foldl (· + ·) 0) h)]
    (_root_.congrArg (fun l => l.foldl (· + ·) 0) h)

/-- Transport for entropy-indexed data. -/
def entropy_transport {P : Nat → Type v} {n1 n2 : Nat}
    (h : n1 = n2) (x : P n1) : P n2 :=
  Path.transport (Path.mk [Step.mk _ _ h] h) x

/-- Transport along refl is identity. -/
theorem entropy_transport_refl {P : Nat → Type v} (n : Nat) (x : P n) :
    entropy_transport (rfl : n = n) x = x := rfl

/-! ## Path Composition for Information -/

/-- Associativity for information path composition. -/
theorem info_path_assoc {a b c d : Nat}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp

/-- CongrArg through addition for information quantities. -/
def info_congrArg_add {a b : Nat} (c : Nat) (p : Path a b) :
    Path (a + c) (b + c) :=
  Path.congrArg (· + c) p

/-! ## Trivial Instances -/

/-- Trivial entropy data. -/
def trivialEntropy : EntropyData where
  distribution := [1]
  entropyVal := 0
  totalWeight := 1
  normPath := Path.refl 1

/-- Trivial joint entropy data. -/
def trivialJointEntropy : JointEntropyData where
  jointEntropy := 2
  marginalX := 1
  marginalY := 1
  condEntropy := 1
  chainPath := Path.refl 2

/-- Trivial mutual information. -/
def trivialMI : MutualInfoData where
  entropyX := 1
  entropyY := 1
  jointEntropy := 1
  mutualInfo := 1
  sumEntropies := 2
  sumPath := Path.refl 2
  miPath := Path.refl 2

/-- Trivial KL divergence. -/
def trivialKL : KLDivData where
  klVal := 0
  crossEntropy := 0
  entropyP := 0
  klPath := Path.refl 0

/-- Trivial source coding. -/
def trivialCoding : SourceCodingData where
  rate := 2
  entropy := 1
  slack := 1
  codingPath := Path.refl 2

end InformationPaths
end Algebra
end Path
end ComputationalPaths
