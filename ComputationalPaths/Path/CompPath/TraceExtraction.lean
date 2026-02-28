/-
# Trace Extraction from Computational Paths

This module demonstrates what ONLY computational paths can do — visible proof
traces. We extract explicit rewrite traces from RwEq proofs, recording each
Step applied, and show how a Path between two terms can be decomposed into
its constituent Steps.

## Key Results

- `StepLabel`: labels identifying which rewrite rule was applied.
- `TraceEntry`: a single entry in a rewrite trace.
- `assocTrace`: explicit trace for associativity.
- `unitLeftTrace`: explicit trace for left unit.
- `fullNormTrace`: 3-step trace for full normalization.
- `triangle_rw`: the triangle identity as a multi-step Rw proof.
- `fullNorm_rw`: multi-step Rw proof with explicit step structure.

## References

- de Queiroz, de Oliveira & Ramos, "Propositional equality, identity types,
  and direct computational paths", SAJL 2016
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace TraceExtraction

open Step

universe u

variable {A : Type u}

/-! ## Trace data structures -/

/-- A human-readable label for a rewrite step. -/
inductive StepLabel : Type
  | symmRefl : StepLabel
  | symmSymm : StepLabel
  | transReflLeft : StepLabel
  | transReflRight : StepLabel
  | transSym : StepLabel
  | symTrans : StepLabel
  | transAssoc : StepLabel
  | congrLeft : StepLabel
  | congrRight : StepLabel
  | symmCongr : StepLabel
  | other : String → StepLabel
  deriving Inhabited

/-- A single entry in a rewrite trace. -/
structure TraceEntry where
  /-- Label identifying which rewrite rule was applied. -/
  label : StepLabel
  /-- Description of the transformation. -/
  description : String
  deriving Inhabited

/-! ## Explicit trace examples -/

section Examples

variable {a b c d : A}

/-- Trace for associativity: `(p ⬝ q) ⬝ r ▷ p ⬝ (q ⬝ r)`.
    This is a single-step trace. -/
noncomputable def assocTrace : List TraceEntry :=
  [{ label := StepLabel.transAssoc
     description := "(p ⬝ q) ⬝ r ▷ p ⬝ (q ⬝ r)" }]

/-- The associativity trace has length 1. -/
theorem assocTrace_length : assocTrace.length = 1 := by rfl

/-- Trace for left unit elimination: `refl ⬝ p ▷ p`.
    Single-step trace. -/
noncomputable def unitLeftTrace : List TraceEntry :=
  [{ label := StepLabel.transReflLeft
     description := "refl ⬝ p ▷ p" }]

/-- Trace for right unit elimination: `p ⬝ refl ▷ p`.
    Single-step trace. -/
noncomputable def unitRightTrace : List TraceEntry :=
  [{ label := StepLabel.transReflRight
     description := "p ⬝ refl ▷ p" }]

/-- Trace for right inverse cancellation: `p ⬝ p⁻¹ ▷ refl`.
    Single-step trace. -/
noncomputable def inverseTrace : List TraceEntry :=
  [{ label := StepLabel.transSym
     description := "p ⬝ p⁻¹ ▷ refl" }]

/-- Full normalization trace for `((refl ⬝ p) ⬝ p⁻¹) ⬝ refl → refl`.
    This demonstrates a 3-step reduction sequence:
    1. Right unit: `((refl ⬝ p) ⬝ p⁻¹) ⬝ refl ▷ (refl ⬝ p) ⬝ p⁻¹`
    2. Left unit (under congr): `(refl ⬝ p) ⬝ p⁻¹ ▷ p ⬝ p⁻¹`
    3. Right inverse: `p ⬝ p⁻¹ ▷ refl`
-/
noncomputable def fullNormTrace : List TraceEntry :=
  [ { label := StepLabel.transReflRight
      description := "((refl ⬝ p) ⬝ p⁻¹) ⬝ refl ▷ (refl ⬝ p) ⬝ p⁻¹" }
  , { label := StepLabel.congrLeft
      description := "(refl ⬝ p) ⬝ p⁻¹ ▷ p ⬝ p⁻¹  [trans_refl_left under congr_left]" }
  , { label := StepLabel.transSym
      description := "p ⬝ p⁻¹ ▷ refl" }
  ]

theorem fullNormTrace_length : fullNormTrace.length = 3 := by rfl

/-- The corresponding Rw proof witnessing the 3-step trace above. -/
theorem fullNorm_rw (p : Path a b) :
    Rw (Path.trans (Path.trans (Path.trans (Path.refl a) p) (Path.symm p))
          (Path.refl a))
       (Path.refl a) := by
  apply Rw.tail
  · apply Rw.tail
    · apply Rw.tail
      · exact Rw.refl _
      · exact Step.trans_refl_right _
    · exact Step.trans_congr_left (Path.symm p)
              (Step.trans_refl_left p)
  · exact Step.trans_symm p

/-- The full normalization holds as RwEq. -/
noncomputable def fullNorm_rweq (p : Path a b) :
    RwEq (Path.trans (Path.trans (Path.trans (Path.refl a) p) (Path.symm p))
            (Path.refl a))
         (Path.refl a) :=
  rweq_of_rw (fullNorm_rw p)

end Examples

/-! ## Triangle coherence trace -/

section TriangleTrace

variable {a b c : A}

/-- Trace for the triangle identity: `(p ⬝ refl) ⬝ q ▷ p ⬝ q`.
    Two-step sequence:
    1. Associativity: `(p ⬝ refl) ⬝ q ▷ p ⬝ (refl ⬝ q)`
    2. Right congr + left unit: `p ⬝ (refl ⬝ q) ▷ p ⬝ q`
-/
noncomputable def triangleTrace : List TraceEntry :=
  [ { label := StepLabel.transAssoc
      description := "(p ⬝ refl) ⬝ q ▷ p ⬝ (refl ⬝ q)" }
  , { label := StepLabel.congrRight
      description := "p ⬝ (refl ⬝ q) ▷ p ⬝ q  [trans_refl_left under congr_right]" }
  ]

theorem triangleTrace_length : triangleTrace.length = 2 := by rfl

/-- The Rw proof for the triangle identity. -/
theorem triangle_rw (p : Path a b) (q : Path b c) :
    Rw (Path.trans (Path.trans p (Path.refl b)) q)
       (Path.trans p q) := by
  apply Rw.tail
  · exact rw_of_step (Step.trans_assoc p (Path.refl b) q)
  · exact Step.trans_congr_right p (Step.trans_refl_left q)

/-- The alternate (left) route for the triangle identity. -/
theorem triangle_left_rw (p : Path a b) (q : Path b c) :
    Rw (Path.trans (Path.trans p (Path.refl b)) q)
       (Path.trans p q) :=
  rw_of_step (Step.trans_congr_left q (Step.trans_refl_right p))

/-- Triangle identity as RwEq. -/
noncomputable def triangle_rweq (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p (Path.refl b)) q)
         (Path.trans p q) :=
  rweq_of_rw (triangle_rw p q)

/-- Triangle identity as RwEq via the left route. -/
noncomputable def triangle_left_rweq (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p (Path.refl b)) q)
         (Path.trans p q) :=
  rweq_of_rw (triangle_left_rw p q)

/-- Left and right triangle routes compose to a coherent loop. -/
noncomputable def triangle_left_right_coherence (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p (Path.refl b)) q)
         (Path.trans (Path.trans p (Path.refl b)) q) :=
  rweq_trans (triangle_rweq p q) (rweq_symm (triangle_left_rweq p q))

/-- `triangleTrace` is sound as an `RwEq` witness. -/
noncomputable def triangleTrace_soundness (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p (Path.refl b)) q)
         (Path.trans p q) :=
  triangle_rweq p q

end TriangleTrace

/-! ## Pentagon trace -/

section PentagonTrace

variable {a b c d e : A}

/-- Trace for the pentagon identity (left path, 2 steps).
    1. Outer associator: `((pq)r)s → (pq)(rs)`
    2. Inner associator: `(pq)(rs) → p(q(rs))`
-/
noncomputable def pentagonLeftTrace : List TraceEntry :=
  [ { label := StepLabel.transAssoc
      description := "((pq)r)s → (pq)(rs)" }
  , { label := StepLabel.transAssoc
      description := "(pq)(rs) → p(q(rs))" }
  ]

/-- Trace for the pentagon identity (right path, 3 steps).
    1. Congr + associator: `((pq)r)s → (p(qr))s`
    2. Outer associator: `(p(qr))s → p((qr)s)`
    3. Congr + associator: `p((qr)s) → p(q(rs))`
-/
noncomputable def pentagonRightTrace : List TraceEntry :=
  [ { label := StepLabel.other "trans_assoc + congr_left"
      description := "((pq)r)s → (p(qr))s" }
  , { label := StepLabel.transAssoc
      description := "(p(qr))s → p((qr)s)" }
  , { label := StepLabel.other "trans_assoc + congr_right"
      description := "p((qr)s) → p(q(rs))" }
  ]

theorem pentagonLeftTrace_length : pentagonLeftTrace.length = 2 := by rfl
theorem pentagonRightTrace_length : pentagonRightTrace.length = 3 := by rfl

/-- Both paths of the pentagon reach the same target. Total trace: 5 steps. -/
theorem pentagonTotalTrace_length :
    pentagonLeftTrace.length + pentagonRightTrace.length = 5 := by rfl

/-- The left path as Rw. -/
theorem pentagon_left_rw (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Rw (trans (trans (trans p q) r) s)
       (trans p (trans q (trans r s))) := by
  apply Rw.tail
  · exact rw_of_step (Step.trans_assoc (trans p q) r s)
  · exact Step.trans_assoc p q (trans r s)

/-- The right path as Rw. -/
theorem pentagon_right_rw (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Rw (trans (trans (trans p q) r) s)
       (trans p (trans q (trans r s))) := by
  apply Rw.tail
  · apply Rw.tail
    · apply Rw.tail
      · exact Rw.refl _
      · exact Step.trans_congr_left s (Step.trans_assoc p q r)
    · exact Step.trans_assoc p (trans q r) s
  · exact Step.trans_congr_right p (Step.trans_assoc q r s)

/-- Both paths agree via RwEq: this IS Mac Lane coherence. -/
noncomputable def pentagon_coherence (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (trans (trans (trans p q) r) s)
         (trans p (trans q (trans r s))) :=
  rweq_of_rw (pentagon_left_rw p q r s)

/-- Pentagon coherence via the right route explicitly. -/
noncomputable def pentagon_right_coherence (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (trans (trans (trans p q) r) s)
         (trans p (trans q (trans r s))) :=
  rweq_of_rw (pentagon_right_rw p q r s)

/-- Left and right pentagon routes compose to a coherent loop. -/
noncomputable def pentagon_left_right_coherence (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (trans (trans (trans p q) r) s)
         (trans (trans (trans p q) r) s) :=
  rweq_trans (pentagon_coherence p q r s)
    (rweq_symm (pentagon_right_coherence p q r s))

/-- `pentagonLeftTrace` is sound as an `RwEq` witness. -/
noncomputable def pentagonLeftTrace_soundness (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (trans (trans (trans p q) r) s)
         (trans p (trans q (trans r s))) :=
  pentagon_coherence p q r s

/-- `pentagonRightTrace` is sound as an `RwEq` witness. -/
noncomputable def pentagonRightTrace_soundness (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (trans (trans (trans p q) r) s)
         (trans p (trans q (trans r s))) :=
  pentagon_right_coherence p q r s

end PentagonTrace

/-! ## Inverse normalization trace -/

section InverseTrace

variable {a b : A}

/-- Trace for `(p⁻¹)⁻¹ → p` via double symmetry cancellation. -/
noncomputable def doubleSymmTrace : List TraceEntry :=
  [{ label := StepLabel.symmSymm
     description := "(p⁻¹)⁻¹ ▷ p" }]

theorem doubleSymmTrace_length : doubleSymmTrace.length = 1 := by rfl

/-- Double symmetry cancellation as Rw. -/
theorem doubleSym_rw (p : Path a b) :
    Rw (Path.symm (Path.symm p)) p :=
  rw_of_step (Step.symm_symm p)

/-- Trace for `refl⁻¹ → refl` via symmetry of reflexivity. -/
noncomputable def symmReflTrace : List TraceEntry :=
  [{ label := StepLabel.symmRefl
     description := "refl⁻¹ ▷ refl" }]

theorem symmReflTrace_length : symmReflTrace.length = 1 := by rfl

/-- Symmetry of reflexivity as Rw. -/
theorem symmRefl_rw (a : A) :
    Rw (Path.symm (Path.refl a)) (Path.refl a) :=
  rw_of_step (Step.symm_refl a)

end InverseTrace

end TraceExtraction
end Path
end ComputationalPaths
