/-
# Fundamental group of the torus via explicit computational paths

This file keeps the torus argument entirely at the path level:

1. `T² = S¹ × S¹` is handled by explicit path pairs (`Path.prodMk`, `Path.fst`, `Path.snd`).
2. Eckmann-Hilton interchange is witnessed directly by `Step.map2_subst`.
3. The commutator `[a,b] = 1` is reduced by an explicit `Step` chain.
4. Generator independence is expressed as componentwise independence of path pairs.
-/

import CompPaths.Core
import ComputationalPaths.Path.CompPath.Torus

set_option maxHeartbeats 2000000

namespace ComputationalPaths
namespace Path
namespace CompPath

/-! ## Torus paths as explicit pairs -/

abbrev TorusPathPair : Type :=
  Path (A := Circle) circleBase circleBase × Path (A := Circle) circleBase circleBase

noncomputable def torusPairToLoop : TorusPathPair → torusLoopSpace
  | (p, q) => Path.prodMk p q

noncomputable def torusLoopToPair : torusLoopSpace → TorusPathPair :=
  fun p => (Path.fst p, Path.snd p)

theorem torusPairToLoop_fst (p q : Path (A := Circle) circleBase circleBase) :
    RwEq (Path.fst (torusPairToLoop (p, q))) p := by
  simpa [torusPairToLoop] using
    (rweq_fst_prodMk (α := Circle) (β := Circle) (p := p) (q := q))

theorem torusPairToLoop_snd (p q : Path (A := Circle) circleBase circleBase) :
    RwEq (Path.snd (torusPairToLoop (p, q))) q := by
  simpa [torusPairToLoop] using
    (rweq_snd_prodMk (α := Circle) (β := Circle) (p := p) (q := q))

theorem torusLoop_pair_eta (p : torusLoopSpace) :
    RwEq (torusPairToLoop (torusLoopToPair p)) p := by
  simpa [torusPairToLoop, torusLoopToPair] using
    (rweq_prod_eta (α := Circle) (β := Circle) (p := p))

/-! ## Eckmann-Hilton interchange from `Step` constructors -/

noncomputable def horizontalAxis (p : Path (A := Circle) circleBase circleBase) :
    torusLoopSpace :=
  Path.mapLeft (A := Circle) (B := Circle) (C := Torus) Prod.mk p circleBase

noncomputable def verticalAxis (q : Path (A := Circle) circleBase circleBase) :
    torusLoopSpace :=
  Path.mapRight (A := Circle) (B := Circle) (C := Torus) Prod.mk circleBase q

noncomputable def horizontalThenVertical
    (p q : Path (A := Circle) circleBase circleBase) : torusLoopSpace :=
  Path.trans (horizontalAxis p) (verticalAxis q)

noncomputable def verticalThenHorizontal
    (p q : Path (A := Circle) circleBase circleBase) : torusLoopSpace :=
  Path.trans (verticalAxis q) (horizontalAxis p)

/-- Explicit interchange step:
`horizontalThenVertical p q` rewrites to `verticalThenHorizontal p q`
by the primitive constructor `Step.map2_subst`. -/
noncomputable def torusInterchangeStep
    (p q : Path (A := Circle) circleBase circleBase) :
    Step (horizontalThenVertical p q) (verticalThenHorizontal p q) := by
  change
    Step
      (Path.map2 (A := Circle) (B := Circle) (C := Torus) Prod.mk p q)
      (Path.trans
        (Path.mapRight (A := Circle) (B := Circle) (C := Torus) Prod.mk circleBase q)
        (Path.mapLeft (A := Circle) (B := Circle) (C := Torus) Prod.mk p circleBase))
  exact
    Step.map2_subst
      (A := Torus) (A₁ := Circle) (B := Circle) (f := Prod.mk) (p := p) (q := q)

noncomputable def torusInterchangeRwEq
    (p q : Path (A := Circle) circleBase circleBase) :
    RwEq (horizontalThenVertical p q) (verticalThenHorizontal p q) :=
  rweq_of_step (torusInterchangeStep p q)

noncomputable def torusLoop1_to_horizontalAxis :
    RwEq torusLoop1 (horizontalAxis circleLoop) := by
  unfold torusLoop1 horizontalAxis Path.prodMk Path.map2
  simpa using
    (rweq_cmpA_refl_right
      (Path.mapLeft (A := Circle) (B := Circle) (C := Torus) Prod.mk circleLoop circleBase))

noncomputable def torusLoop2_to_verticalAxis :
    RwEq torusLoop2 (verticalAxis circleLoop) := by
  unfold torusLoop2 verticalAxis Path.prodMk Path.map2
  simpa using
    (rweq_cmpA_refl_left
      (Path.mapRight (A := Circle) (B := Circle) (C := Torus) Prod.mk circleBase circleLoop))

/-- The generator loops commute by the interchange witness chain. -/
noncomputable def torusGeneratorsCommuteRwEq :
    RwEq (Path.trans torusLoop1 torusLoop2) (Path.trans torusLoop2 torusLoop1) := by
  have h_left :
      RwEq (Path.trans torusLoop1 torusLoop2)
        (Path.trans (horizontalAxis circleLoop) (verticalAxis circleLoop)) :=
    rweq_trans_congr torusLoop1_to_horizontalAxis torusLoop2_to_verticalAxis
  have h_mid :
      RwEq (Path.trans (horizontalAxis circleLoop) (verticalAxis circleLoop))
        (Path.trans (verticalAxis circleLoop) (horizontalAxis circleLoop)) :=
    torusInterchangeRwEq circleLoop circleLoop
  have h_right :
      RwEq (Path.trans (verticalAxis circleLoop) (horizontalAxis circleLoop))
        (Path.trans torusLoop2 torusLoop1) :=
    rweq_trans_congr (rweq_symm torusLoop2_to_verticalAxis) (rweq_symm torusLoop1_to_horizontalAxis)
  exact rweq_trans h_left (rweq_trans h_mid h_right)

/-! ## Commutator cancellation via explicit `Step` chains -/

noncomputable def torusCommutatorExplicit : torusLoopSpace :=
  Path.trans
    (Path.trans (Path.trans torusLoop1 torusLoop2) (Path.symm torusLoop1))
    (Path.symm torusLoop2)

private noncomputable def commutatorReflRightRw {A : Type} {a : A}
    (p : LoopSpace A a) :
    Rw
      (Path.trans (Path.trans (Path.trans p (Path.refl a)) (Path.symm p))
        (Path.symm (Path.refl a)))
      (Path.refl a) := by
  apply rw_trans
  · exact rw_of_step (Step.trans_congr_right
      (Path.trans (Path.trans p (Path.refl a)) (Path.symm p))
      (Step.symm_refl a))
  apply rw_trans
  · exact rw_of_step (Step.trans_refl_right _)
  apply rw_trans
  · exact rw_of_step (Step.trans_congr_left (Path.symm p) (Step.trans_refl_right p))
  exact rw_of_step (Step.trans_symm p)

private noncomputable def commutatorReflLeftRw {A : Type} {a : A}
    (p : LoopSpace A a) :
    Rw
      (Path.trans (Path.trans (Path.trans (Path.refl a) p) (Path.symm (Path.refl a)))
        (Path.symm p))
      (Path.refl a) := by
  apply rw_trans
  · exact rw_of_step (Step.trans_congr_left (Path.symm p)
      (Step.trans_congr_right (Path.trans (Path.refl a) p) (Step.symm_refl a)))
  apply rw_trans
  · exact rw_of_step (Step.trans_congr_left (Path.symm p)
      (Step.trans_refl_right (Path.trans (Path.refl a) p)))
  apply rw_trans
  · exact rw_of_step (Step.trans_congr_left (Path.symm p)
      (Step.trans_refl_left p))
  exact rw_of_step (Step.trans_symm p)

private noncomputable def commutatorReflRightRwEq {A : Type} {a : A}
    (p : LoopSpace A a) :
    RwEq
      (Path.trans (Path.trans (Path.trans p (Path.refl a)) (Path.symm p))
        (Path.symm (Path.refl a)))
      (Path.refl a) :=
  rweq_of_rw (commutatorReflRightRw p)

private noncomputable def commutatorReflLeftRwEq {A : Type} {a : A}
    (p : LoopSpace A a) :
    RwEq
      (Path.trans (Path.trans (Path.trans (Path.refl a) p) (Path.symm (Path.refl a)))
        (Path.symm p))
      (Path.refl a) :=
  rweq_of_rw (commutatorReflLeftRw p)

noncomputable def torusCommutator_fst_refl :
    RwEq (Path.fst torusCommutatorExplicit) (Path.refl circleBase) := by
  unfold torusCommutatorExplicit
  simp only [Path.fst, congrArg_trans, congrArg_symm]
  apply rweq_trans
  · apply rweq_trans_congr
    · apply rweq_trans_congr
      · apply rweq_trans_congr
        · exact rweq_fst_prodMk circleLoop (Path.refl circleBase)
        · exact rweq_fst_prodMk (Path.refl circleBase) circleLoop
      · exact rweq_symm_congr (rweq_fst_prodMk circleLoop (Path.refl circleBase))
    · exact rweq_symm_congr (rweq_fst_prodMk (Path.refl circleBase) circleLoop)
  · exact commutatorReflRightRwEq circleLoop

noncomputable def torusCommutator_snd_refl :
    RwEq (Path.snd torusCommutatorExplicit) (Path.refl circleBase) := by
  unfold torusCommutatorExplicit
  simp only [Path.snd, congrArg_trans, congrArg_symm]
  apply rweq_trans
  · apply rweq_trans_congr
    · apply rweq_trans_congr
      · apply rweq_trans_congr
        · exact rweq_snd_prodMk circleLoop (Path.refl circleBase)
        · exact rweq_snd_prodMk (Path.refl circleBase) circleLoop
      · exact rweq_symm_congr (rweq_snd_prodMk circleLoop (Path.refl circleBase))
    · exact rweq_symm_congr (rweq_snd_prodMk (Path.refl circleBase) circleLoop)
  · exact commutatorReflLeftRwEq circleLoop

/-- Explicit commutator reduction `[a,b] = 1` at the torus path level. -/
noncomputable def torusCommutator_trivial_path :
    RwEq torusCommutatorExplicit (Path.refl torusBase) := by
  have h_eta :
      RwEq torusCommutatorExplicit
        (Path.prodMk (Path.fst torusCommutatorExplicit) (Path.snd torusCommutatorExplicit)) :=
    rweq_symm (rweq_prod_eta torusCommutatorExplicit)
  have h_prod :
      RwEq (Path.prodMk (Path.fst torusCommutatorExplicit) (Path.snd torusCommutatorExplicit))
        (Path.prodMk (Path.refl circleBase) (Path.refl circleBase)) :=
    rweq_map2_of_rweq (f := Prod.mk) torusCommutator_fst_refl torusCommutator_snd_refl
  have h_refl :
      Path.prodMk (Path.refl circleBase) (Path.refl circleBase) = Path.refl torusBase :=
    Path.prodMk_refl_refl circleBase circleBase
  exact rweq_trans h_eta (rweq_trans h_prod (rweq_of_eq h_refl))

/-! ## Generator independence at the path level -/

theorem torusPathPair_independence
    {p₁ p₂ q₁ q₂ : Path (A := Circle) circleBase circleBase}
    (h : RwEq (Path.prodMk p₁ q₁) (Path.prodMk p₂ q₂)) :
    RwEq p₁ p₂ × RwEq q₁ q₂ := by
  have hfst :
      RwEq (Path.fst (Path.prodMk p₁ q₁)) (Path.fst (Path.prodMk p₂ q₂)) := by
    simpa [Path.fst] using
      (rweq_congrArg_of_rweq (A := Torus) (f := Prod.fst) h)
  have hsnd :
      RwEq (Path.snd (Path.prodMk p₁ q₁)) (Path.snd (Path.prodMk p₂ q₂)) := by
    simpa [Path.snd] using
      (rweq_congrArg_of_rweq (A := Torus) (f := Prod.snd) h)
  constructor
  · exact
      rweq_trans (rweq_symm (rweq_fst_prodMk p₁ q₁))
        (rweq_trans hfst (rweq_fst_prodMk p₂ q₂))
  · exact
      rweq_trans (rweq_symm (rweq_snd_prodMk p₁ q₁))
        (rweq_trans hsnd (rweq_snd_prodMk p₂ q₂))

/-- If the two torus generators were identified, both circle axes would collapse. -/
theorem torusGenerator_independence_path
    (h : RwEq torusLoop1 torusLoop2) :
    RwEq circleLoop (Path.refl circleBase) ∧
    RwEq (Path.refl circleBase) circleLoop := by
  simpa [torusLoop1, torusLoop2] using
    (torusPathPair_independence
      (p₁ := circleLoop) (q₁ := Path.refl circleBase)
      (p₂ := Path.refl circleBase) (q₂ := circleLoop) h)

end CompPath
end Path
end ComputationalPaths
