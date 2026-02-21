import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Noncommutative geometry paths: spectral triples

This module packages spectral-triple style coherence data as computational
paths with explicit `Path.Step` witnesses and derived `RwEq` normalizations.
-/

namespace ComputationalPaths
namespace NCG
namespace SpectralTriplesPaths

open Path

universe u

/-- Path-level spectral triple data with explicit step witnesses. -/
structure SpectralTriplePathData (H A : Type u) where
  zeroVec : H
  oneAlg : A
  repr : A → H → H
  dirac : H → H
  grading : H → H
  chargeConj : H → H
  commutator : A → H → H
  reprOnePath : ∀ v : H, Path (repr oneAlg v) v
  reprOneStep :
    ∀ v : H,
      Path.Step (Path.trans (reprOnePath v) (Path.refl v)) (reprOnePath v)
  commutatorZeroPath : ∀ a : A, Path (commutator a zeroVec) zeroVec
  commutatorZeroStep :
    ∀ a : A,
      Path.Step
        (Path.trans (commutatorZeroPath a) (Path.refl zeroVec))
        (commutatorZeroPath a)
  gradingSquarePath : ∀ v : H, Path (grading (grading v)) v
  gradingSquareStep :
    ∀ v : H,
      Path.Step
        (Path.trans (gradingSquarePath v) (Path.refl v))
        (gradingSquarePath v)
  chargeConjSquarePath : ∀ v : H, Path (chargeConj (chargeConj v)) v
  chargeConjSquareStep :
    ∀ v : H,
      Path.Step
        (Path.trans (chargeConjSquarePath v) (Path.refl v))
        (chargeConjSquarePath v)
  realityPath : ∀ v : H, Path (chargeConj (grading v)) (grading (chargeConj v))
  realityStep :
    ∀ v : H,
      Path.Step
        (Path.trans (realityPath v) (Path.refl (grading (chargeConj v))))
        (realityPath v)

namespace SpectralTriplePathData

variable {H A : Type u} (S : SpectralTriplePathData H A)

noncomputable def reprOne_rweq (v : H) :
    RwEq (Path.trans (S.reprOnePath v) (Path.refl v)) (S.reprOnePath v) :=
  rweq_of_step (S.reprOneStep v)

noncomputable def commutatorZero_rweq (a : A) :
    RwEq
      (Path.trans (S.commutatorZeroPath a) (Path.refl S.zeroVec))
      (S.commutatorZeroPath a) :=
  rweq_of_step (S.commutatorZeroStep a)

noncomputable def gradingSquare_rweq (v : H) :
    RwEq
      (Path.trans (S.gradingSquarePath v) (Path.refl v))
      (S.gradingSquarePath v) :=
  rweq_of_step (S.gradingSquareStep v)

noncomputable def chargeConjSquare_rweq (v : H) :
    RwEq
      (Path.trans (S.chargeConjSquarePath v) (Path.refl v))
      (S.chargeConjSquarePath v) :=
  rweq_of_step (S.chargeConjSquareStep v)

noncomputable def reality_rweq (v : H) :
    RwEq
      (Path.trans (S.realityPath v) (Path.refl (S.grading (S.chargeConj v))))
      (S.realityPath v) :=
  rweq_of_step (S.realityStep v)

/-- Two-step normalization for `gradingSquarePath` with duplicated unit tails. -/
noncomputable def gradingSquare_two_refl_rweq (v : H) :
    RwEq
      (Path.trans
        (Path.trans (S.gradingSquarePath v) (Path.refl v))
        (Path.refl v))
      (S.gradingSquarePath v) := by
  exact rweq_trans
    (rweq_of_step
      (Path.Step.trans_assoc
        (S.gradingSquarePath v)
        (Path.refl v)
        (Path.refl v)))
    (rweq_trans
      (rweq_trans_congr_right
        (S.gradingSquarePath v)
        (rweq_cmpA_refl_left (Path.refl v)))
      (S.gradingSquare_rweq v))

/-- Roundtrip along the reality path and its inverse. -/
def reality_roundtrip (v : H) :
    Path (S.chargeConj (S.grading v)) (S.chargeConj (S.grading v)) :=
  Path.trans (S.realityPath v) (Path.symm (S.realityPath v))

noncomputable def reality_roundtrip_rweq (v : H) :
    RwEq (S.reality_roundtrip v) (Path.refl (S.chargeConj (S.grading v))) :=
  rweq_cmpA_inv_right (S.realityPath v)

end SpectralTriplePathData

/-- Canonical identity-like spectral data with explicit Step witnesses. -/
def identitySpectralTriplePathData (H A : Type u) [Inhabited H] [Inhabited A] :
    SpectralTriplePathData H A where
  zeroVec := default
  oneAlg := default
  repr := fun _ v => v
  dirac := fun v => v
  grading := fun v => v
  chargeConj := fun v => v
  commutator := fun _ _ => default
  reprOnePath := fun v => Path.refl v
  reprOneStep := fun v => Path.Step.trans_refl_right (Path.refl v)
  commutatorZeroPath := fun _ => Path.refl default
  commutatorZeroStep := fun _ => Path.Step.trans_refl_right (Path.refl default)
  gradingSquarePath := fun v => Path.refl v
  gradingSquareStep := fun v => Path.Step.trans_refl_right (Path.refl v)
  chargeConjSquarePath := fun v => Path.refl v
  chargeConjSquareStep := fun v => Path.Step.trans_refl_right (Path.refl v)
  realityPath := fun v => Path.refl v
  realityStep := fun v => Path.Step.trans_refl_right (Path.refl v)

/-- In the identity model, reality roundtrip normalizes to reflexivity. -/
noncomputable def identity_reality_roundtrip_rweq
    (H A : Type u) [Inhabited H] [Inhabited A] (v : H) :
    RwEq
      (Path.trans (Path.refl v) (Path.symm (Path.refl v)))
      (Path.refl v) :=
  (identitySpectralTriplePathData H A).reality_roundtrip_rweq v

end SpectralTriplesPaths
end NCG
end ComputationalPaths

