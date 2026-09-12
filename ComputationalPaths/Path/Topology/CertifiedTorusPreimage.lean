import ComputationalPaths.Path.Algebra.CertifiedIntegerMatrixPreimage
import ComputationalPaths.Path.Topology.FiniteTorusWinding

/-!
# Certified preimages of finite-torus loop classes

This module connects the topology-independent certified integer-matrix solver
to the concrete finite-torus winding classifier.
-/

namespace ComputationalPaths.Path.GeometricTopology.CertifiedTorusPreimage

open Matrix
open FiniteTorusWinding
open ComputationalPaths.Path.Algebra.CertifiedIntegerMatrixPreimage

namespace Torus

/-- The computed vector specifies an actual loop. For canonical standard
representatives its image equals the target loop pointwise, not just up to
homotopy. -/
theorem candidate_loop {m n : ℕ} (A : Mat m n) (c : Certificate m n)
    (h : c.Valid A) (z : Vec m) (hz : c.Feasible z) :
    ((standardLoop (c.candidate z)).map (matrixMap A).continuous).cast
      (matrixMap_base A).symm (matrixMap_base A).symm = standardLoop z := by
  change
    ((standardLoop (c.candidate z)).map
      (matrixMap (fun i j => A i j)).continuous).cast
        (matrixMap_base (fun i j => A i j)).symm
        (matrixMap_base (fun i j => A i j)).symm = standardLoop z
  rw [matrixMap_standardLoop]
  exact congrArg standardLoop (c.candidate_correct A h z hz)

/-- The target is the actual standard-loop homotopy class of the input vector.
This is not a pointwise lifting problem for paths under a covering map. -/
theorem preimage_iff {m n : ℕ} (A : Mat m n) (z : Vec m) (q : LoopQuot n) :
    matrixMapQuotientMap A q = decode z ↔ A.mulVec (encode q) = z := by
  change
    matrixMapQuotientMap (fun i j => A i j) q = decode z ↔
      Matrix.mulVec (fun i j => A i j) (encode q) = z
  constructor
  · intro h
    have he := congrArg encode h
    rw [encode_matrixMapQuotientMap, encode_decode] at he
    exact he
  · intro h
    apply (equivIntVector m).injective
    change
      encode (matrixMapQuotientMap (fun i j => A i j) q) =
        encode (decode z)
    rw [encode_matrixMapQuotientMap, encode_decode]
    exact h

theorem exists_preimage_iff {m n : ℕ} (A : Mat m n) (z : Vec m) :
    (∃ q, matrixMapQuotientMap A q = decode z) ↔ ∃ x, A.mulVec x = z := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨encode q, (preimage_iff A z q).mp hq⟩
  · rintro ⟨x, hx⟩
    refine ⟨decode x, (preimage_iff A z (decode x)).mpr ?_⟩
    simpa only [encode_decode] using hx

/-- All topological preimage classes are the decoded affine kernel lattice. -/
theorem all_preimages {m n : ℕ} (A : Mat m n) (c : Certificate m n)
    (h : c.Valid A) (z : Vec m) (hz : c.Feasible z) (q : LoopQuot n) :
    matrixMapQuotientMap A q = decode z ↔
      ∃ v, q = decode (c.candidate z + c.kernelGenerator.mulVec v) := by
  rw [preimage_iff, c.all_solutions A h z hz]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, (decode_encode q).symm.trans (congrArg decode hv)⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, encode_decode _⟩

def TopologicallyCorrect {m n : ℕ} (A : Mat m n) (c : Certificate m n)
    (z : Vec m) : Outcome m n → Prop
  | .invalid => ¬ c.Valid A
  | .solved x => c.Valid A ∧ matrixMapQuotientMap A (decode x) = decode z ∧
      ∀ q, matrixMapQuotientMap A q = decode z ↔
        ∃ v, q = decode (x + c.kernelGenerator.mulVec v)
  | .obstructed i => c.Valid A ∧ ¬ c.d i ∣ c.transformed z i ∧
      ¬ ∃ q, matrixMapQuotientMap A q = decode z

/-- Flagship endpoint: the executed answer is correct for the fixed topological
semantics, including all solutions and explicit negative witnesses. -/
theorem solve_topologically_correct {m n : ℕ} (A : Mat m n)
    (c : Certificate m n) (z : Vec m) : TopologicallyCorrect A c z (solve A c z) := by
  have hs := solve_correct A c z
  cases he : solve A c z with
  | invalid => simpa [he, Outcome.Correct, TopologicallyCorrect] using hs
  | solved x =>
    rw [he] at hs
    obtain ⟨hc, hx, hall⟩ := hs
    refine ⟨hc, (preimage_iff A z (decode x)).mpr ?_, ?_⟩
    · simpa only [encode_decode] using hx
    · intro q
      rw [preimage_iff, hall]
      constructor
      · rintro ⟨v, hv⟩
        exact ⟨v, (decode_encode q).symm.trans (congrArg decode hv)⟩
      · rintro ⟨v, rfl⟩
        exact ⟨v, encode_decode _⟩
  | obstructed i =>
    rw [he] at hs
    exact ⟨hs.1, hs.2.1, fun hq => hs.2.2 ((exists_preimage_iff A z).mp hq)⟩

end Torus

end ComputationalPaths.Path.GeometricTopology.CertifiedTorusPreimage
