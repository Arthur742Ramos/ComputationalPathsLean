/-
# Deep Step Reduction Analysis

Shows specific Step reductions using actual Step constructors from the rewrite
system, composes multiple Steps into reduction sequences via StepStar, and
proves normalization properties for specific path expressions.

Every theorem uses actual `Step` constructors (symm_refl, symm_symm,
trans_refl_left, trans_assoc, trans_cancel_left, symm_congr, etc.)
and `StepStar` sequences.
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.Step

namespace ComputationalPaths.Path.StepReductionDeep

open ComputationalPaths.Path

universe u

variable {A : Type u} {a b c d e : A}

/-! ## 1. Single-step reductions witnessed by Step constructors -/

/-- symm(refl a) reduces to refl a in one Step. -/
theorem symm_refl_step (a : A) :
    Step (Path.symm (Path.refl a)) (Path.refl a) :=
  Step.symm_refl a

/-- symm(symm(p)) reduces to p in one Step. -/
theorem symm_symm_step (p : Path a b) :
    Step (Path.symm (Path.symm p)) p :=
  Step.symm_symm p

/-- trans(refl, p) reduces to p in one Step. -/
theorem trans_refl_left_step (p : Path a b) :
    Step (Path.trans (Path.refl a) p) p :=
  Step.trans_refl_left p

/-- trans(p, refl) reduces to p in one Step. -/
theorem trans_refl_right_step (p : Path a b) :
    Step (Path.trans p (Path.refl b)) p :=
  Step.trans_refl_right p

/-- trans(p, symm(p)) reduces to refl in one Step. -/
theorem trans_symm_step (p : Path a b) :
    Step (Path.trans p (Path.symm p)) (Path.refl a) :=
  Step.trans_symm p

/-- symm(p) ∘ p reduces to refl in one Step. -/
theorem symm_trans_step (p : Path a b) :
    Step (Path.trans (Path.symm p) p) (Path.refl b) :=
  Step.symm_trans p

/-- (p ∘ q) ∘ r reduces to p ∘ (q ∘ r) in one Step. -/
theorem trans_assoc_step (p : Path a b) (q : Path b c) (r : Path c d) :
    Step (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  Step.trans_assoc p q r

/-- symm(p ∘ q) reduces to symm(q) ∘ symm(p) in one Step. -/
theorem symm_trans_congr_step (p : Path a b) (q : Path b c) :
    Step (Path.symm (Path.trans p q)) (Path.trans (Path.symm q) (Path.symm p)) :=
  Step.symm_trans_congr p q

/-- p ∘ (symm(p) ∘ q) reduces to q (left cancellation) in one Step. -/
theorem trans_cancel_left_step (p : Path a b) (q : Path a c) :
    Step (Path.trans p (Path.trans (Path.symm p) q)) q :=
  Step.trans_cancel_left p q

/-- symm(p) ∘ (p ∘ q) reduces to q (right cancellation) in one Step. -/
theorem trans_cancel_right_step (p : Path a b) (q : Path b c) :
    Step (Path.trans (Path.symm p) (Path.trans p q)) q :=
  Step.trans_cancel_right p q

/-! ## 2. Congruence-propagated Steps -/

/-- If p ▷ q then symm(p) ▷ symm(q) via Step.symm_congr. -/
theorem symm_congr_step {p q : Path a b} (h : Step p q) :
    Step (Path.symm p) (Path.symm q) :=
  Step.symm_congr h

/-- If p ▷ q then trans(p, r) ▷ trans(q, r) via Step.trans_congr_left. -/
theorem trans_congr_left_step {p q : Path a b} (r : Path b c) (h : Step p q) :
    Step (Path.trans p r) (Path.trans q r) :=
  Step.trans_congr_left r h

/-- If q ▷ r then trans(p, q) ▷ trans(p, r) via Step.trans_congr_right. -/
theorem trans_congr_right_step (p : Path a b) {q r : Path b c} (h : Step q r) :
    Step (Path.trans p q) (Path.trans p r) :=
  Step.trans_congr_right p h

/-! ## 3. Multi-step reductions via StepStar -/

/-- symm(symm(refl a)) →* refl a in two steps: symm_symm then done. -/
theorem symm_symm_refl_reduces (a : A) :
    StepStar (Path.symm (Path.symm (Path.refl a))) (Path.refl a) :=
  StepStar.single (Step.symm_symm (Path.refl a))

/-- trans(refl, trans(refl, p)) →* p in two steps. -/
theorem trans_refl_trans_refl_reduces (p : Path a b) :
    StepStar (Path.trans (Path.refl a) (Path.trans (Path.refl a) p)) p :=
  StepStar.two
    (Step.trans_refl_left (Path.trans (Path.refl a) p))
    (Step.trans_refl_left p)

/-- trans(trans(p, refl), refl) →* p in two steps. -/
theorem trans_p_refl_refl_reduces (p : Path a b) :
    StepStar (Path.trans (Path.trans p (Path.refl b)) (Path.refl b)) p :=
  StepStar.two
    (Step.trans_refl_right (Path.trans p (Path.refl b)))
    (Step.trans_refl_right p)

/-- symm(refl) ∘ p →* p in two steps: reduce symm(refl) to refl, then left-unit. -/
theorem symm_refl_trans_reduces (p : Path a b) :
    StepStar (Path.trans (Path.symm (Path.refl a)) p) p :=
  StepStar.two
    (Step.trans_congr_left p (Step.symm_refl a))
    (Step.trans_refl_left p)

/-- p ∘ symm(refl) →* p in two steps. -/
theorem trans_symm_refl_reduces (p : Path a b) :
    StepStar (Path.trans p (Path.symm (Path.refl b))) p :=
  StepStar.two
    (Step.trans_congr_right p (Step.symm_refl b))
    (Step.trans_refl_right p)

/-- symm(symm(p)) ∘ symm(symm(q)) →* p ∘ q in two steps. -/
theorem symm_symm_trans_reduces (p : Path a b) (q : Path b c) :
    StepStar
      (Path.trans (Path.symm (Path.symm p)) (Path.symm (Path.symm q)))
      (Path.trans p q) :=
  StepStar.two
    (Step.trans_congr_left (Path.symm (Path.symm q)) (Step.symm_symm p))
    (Step.trans_congr_right p (Step.symm_symm q))

/-- ((p ∘ q) ∘ r) ∘ s →* p ∘ (q ∘ (r ∘ s)) in two steps (full right-association). -/
theorem full_right_assoc_reduces (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    StepStar
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  StepStar.two
    (Step.trans_assoc (Path.trans p q) r s)
    (Step.trans_assoc p q (Path.trans r s))

/-! ## 4. Deeper multi-step chains -/

/-- symm(refl ∘ p) →* symm(p) in two steps: first trans_refl_left under symm_congr. -/
theorem symm_trans_refl_left_reduces (p : Path a b) :
    StepStar (Path.symm (Path.trans (Path.refl a) p)) (Path.symm p) :=
  StepStar.single (Step.symm_congr (Step.trans_refl_left p))

/-- symm(p ∘ refl) →* symm(p) in one step via symm_congr. -/
theorem symm_trans_refl_right_reduces (p : Path a b) :
    StepStar (Path.symm (Path.trans p (Path.refl b))) (Path.symm p) :=
  StepStar.single (Step.symm_congr (Step.trans_refl_right p))

/-- symm(symm(p ∘ q)) →* p ∘ q in one step. -/
theorem symm_symm_trans_step (p : Path a b) (q : Path b c) :
    StepStar (Path.symm (Path.symm (Path.trans p q))) (Path.trans p q) :=
  StepStar.single (Step.symm_symm (Path.trans p q))

/-- trans(p, trans(symm(p), trans(symm(q), q))) →* refl via cancel left,
    then →* refl via symm_trans. Two steps total. -/
theorem cancel_then_inverse_reduces (p : Path a b) (q : Path c a) :
    StepStar
      (Path.trans p (Path.trans (Path.symm p) (Path.trans (Path.symm q) q)))
      (Path.refl a) :=
  StepStar.two
    (Step.trans_cancel_left p (Path.trans (Path.symm q) q))
    (Step.symm_trans q)

/-- symm(p ∘ symm(p)) →* symm(refl) →* refl in two steps. -/
theorem symm_of_trans_symm_reduces (p : Path a b) :
    StepStar (Path.symm (Path.trans p (Path.symm p))) (Path.refl a) :=
  StepStar.two
    (Step.symm_congr (Step.trans_symm p))
    (Step.symm_refl a)

/-- symm(symm(p) ∘ p) →* symm(refl) →* refl in two steps. -/
theorem symm_of_symm_trans_reduces (p : Path a b) :
    StepStar (Path.symm (Path.trans (Path.symm p) p)) (Path.refl b) :=
  StepStar.two
    (Step.symm_congr (Step.symm_trans p))
    (Step.symm_refl b)

/-! ## 5. Normalization for specific fragments -/

/-- Any refl-padded path reduces to the path itself. -/
theorem refl_padding_normalizes (p : Path a b) :
    StepStar (Path.trans (Path.refl a) (Path.trans p (Path.refl b))) p :=
  StepStar.two
    (Step.trans_refl_left (Path.trans p (Path.refl b)))
    (Step.trans_refl_right p)

/-- Double symm on both sides of a trans normalizes. -/
theorem double_symm_in_trans_normalizes (p : Path a b) (q : Path b c) :
    StepStar
      (Path.trans (Path.symm (Path.symm p)) (Path.symm (Path.symm q)))
      (Path.trans p q) :=
  symm_symm_trans_reduces p q

/-- symm(symm(refl a)) →* refl a via symm_symm. -/
theorem symm_symm_refl_normalizes (a : A) :
    StepStar (Path.symm (Path.symm (Path.refl a))) (Path.refl a) :=
  StepStar.single (Step.symm_symm (Path.refl a))

/-- Left-nested triple composition right-associates in two steps. -/
theorem triple_assoc_normalizes (p : Path a b) (q : Path b c) (r : Path c d) :
    StepStar
      (Path.trans (Path.trans p q) r)
      (Path.trans p (Path.trans q r)) :=
  StepStar.single (Step.trans_assoc p q r)

/-! ## 6. Step preservation under congruences -/

/-- A single step under symm_congr followed by another step. -/
theorem symm_congr_chain {p q r : Path a b}
    (h1 : Step p q) (h2 : Step q r) :
    StepStar (Path.symm p) (Path.symm r) :=
  StepStar.two (Step.symm_congr h1) (Step.symm_congr h2)

/-- Two left-congruence steps in sequence. -/
theorem trans_congr_left_chain {p q r : Path a b} (s : Path b c)
    (h1 : Step p q) (h2 : Step q r) :
    StepStar (Path.trans p s) (Path.trans r s) :=
  StepStar.two (Step.trans_congr_left s h1) (Step.trans_congr_left s h2)

/-- Two right-congruence steps in sequence. -/
theorem trans_congr_right_chain (p : Path a b) {q r s : Path b c}
    (h1 : Step q r) (h2 : Step r s) :
    StepStar (Path.trans p q) (Path.trans p s) :=
  StepStar.two (Step.trans_congr_right p h1) (Step.trans_congr_right p h2)

/-- Reduce both sides of a trans via left then right congruence. -/
theorem trans_both_congr {p p' : Path a b} {q q' : Path b c}
    (hp : Step p p') (hq : Step q q') :
    StepStar (Path.trans p q) (Path.trans p' q') :=
  StepStar.two
    (Step.trans_congr_left q hp)
    (Step.trans_congr_right p' hq)

/-! ## 7. Complex reduction witnesses -/

/-- (refl ∘ p) ∘ (symm(p) ∘ refl) →* refl via multiple rules.
    Steps: congr_left(trans_refl_left) → congr_right(trans_refl_right) → trans_symm -/
theorem unit_inverse_reduces (p : Path a b) :
    StepStar
      (Path.trans (Path.trans (Path.refl a) p) (Path.trans (Path.symm p) (Path.refl a)))
      (Path.refl a) :=
  StepStar.tail
    (StepStar.two
      (Step.trans_congr_left _ (Step.trans_refl_left p))
      (Step.trans_congr_right p (Step.trans_refl_right (Path.symm p))))
    (Step.trans_symm p)

/-- symm(p ∘ q) ∘ (p ∘ q) →* refl in one step. -/
theorem symm_trans_of_compound (p : Path a b) (q : Path b c) :
    Step (Path.trans (Path.symm (Path.trans p q)) (Path.trans p q)) (Path.refl c) :=
  Step.symm_trans (Path.trans p q)

/-- (p ∘ q) ∘ symm(p ∘ q) →* refl in one step. -/
theorem trans_symm_of_compound (p : Path a b) (q : Path b c) :
    Step (Path.trans (Path.trans p q) (Path.symm (Path.trans p q))) (Path.refl a) :=
  Step.trans_symm (Path.trans p q)

/-- Nested cancellation: p ∘ (symm(p) ∘ (q ∘ (symm(q) ∘ r))) →* r. -/
theorem nested_cancel_reduces (p : Path a b) (q : Path a c) (r : Path a d) :
    StepStar
      (Path.trans p (Path.trans (Path.symm p) (Path.trans q (Path.trans (Path.symm q) r))))
      r :=
  StepStar.two
    (Step.trans_cancel_left p (Path.trans q (Path.trans (Path.symm q) r)))
    (Step.trans_cancel_left q r)

/-! ## 8. Interaction of structural rules -/

/-- symm_congr applied to trans_refl_left produces a valid Step. -/
theorem symm_of_trans_refl_left_step (p : Path a b) :
    Step (Path.symm (Path.trans (Path.refl a) p)) (Path.symm p) :=
  Step.symm_congr (Step.trans_refl_left p)

/-- symm_congr applied to trans_refl_right produces a valid Step. -/
theorem symm_of_trans_refl_right_step (p : Path a b) :
    Step (Path.symm (Path.trans p (Path.refl b))) (Path.symm p) :=
  Step.symm_congr (Step.trans_refl_right p)

/-- Left-congruence applied to symm_refl. -/
theorem trans_symm_refl_congr_left (q : Path a b) :
    Step (Path.trans (Path.symm (Path.refl a)) q) (Path.trans (Path.refl a) q) :=
  Step.trans_congr_left q (Step.symm_refl a)

/-- Right-congruence applied to symm_refl. -/
theorem trans_p_symm_refl_congr_right (p : Path a b) :
    Step (Path.trans p (Path.symm (Path.refl b))) (Path.trans p (Path.refl b)) :=
  Step.trans_congr_right p (Step.symm_refl b)

end ComputationalPaths.Path.StepReductionDeep
