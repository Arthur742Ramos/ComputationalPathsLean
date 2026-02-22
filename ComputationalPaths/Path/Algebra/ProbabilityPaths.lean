/-
# Probability Theory via Computational Paths

This module models probability theory using computational paths:
probability measures as path-valued functions, Bayes' rule as path
composition, conditional probability, independence as path factoring,
expectation linearity, and law of total probability.

## References

- Kolmogorov, "Foundations of the Theory of Probability"
- Billingsley, "Probability and Measure"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace ProbabilityPaths

universe u v

open ComputationalPaths.Path

/-! ## Events -/

/-- An event in a probability space. -/
structure Event (Ω : Type u) where
  pred : Ω → Prop

/-- The certain event. -/
noncomputable def Event.certain (Ω : Type u) : Event Ω := ⟨fun _ => True⟩

/-- The impossible event. -/
noncomputable def Event.impossible (Ω : Type u) : Event Ω := ⟨fun _ => False⟩

/-- Complement of an event. -/
noncomputable def Event.compl {Ω : Type u} (A : Event Ω) : Event Ω :=
  ⟨fun ω => ¬A.pred ω⟩

/-- Intersection of events. -/
noncomputable def Event.inter {Ω : Type u} (A B : Event Ω) : Event Ω :=
  ⟨fun ω => A.pred ω ∧ B.pred ω⟩

/-- Union of events. -/
noncomputable def Event.union {Ω : Type u} (A B : Event Ω) : Event Ω :=
  ⟨fun ω => A.pred ω ∨ B.pred ω⟩

/-! ## Probability Measure Paths -/

/-- A probability measure assignment with path witnesses. -/
structure MeasurePath (Ω : Type u) where
  prob : Event Ω → Nat
  totalProb : Nat
  normPath : Path (prob (Event.certain Ω)) totalProb

/-- Two measure paths are equivalent when they agree on all events. -/
noncomputable def measurePathEquiv {Ω : Type u} (m1 m2 : MeasurePath Ω) : Prop :=
  ∀ e : Event Ω, m1.prob e = m2.prob e

/-- Measure path equivalence is reflexive. -/
theorem measurePathEquiv_refl {Ω : Type u} (m : MeasurePath Ω) :
    measurePathEquiv m m :=
  fun _ => rfl

/-- Measure path equivalence is symmetric. -/
theorem measurePathEquiv_symm {Ω : Type u}
    {m1 m2 : MeasurePath Ω} (h : measurePathEquiv m1 m2) :
    measurePathEquiv m2 m1 :=
  fun e => (h e).symm

/-- Measure path equivalence is transitive. -/
theorem measurePathEquiv_trans {Ω : Type u}
    {m1 m2 m3 : MeasurePath Ω}
    (h1 : measurePathEquiv m1 m2) (h2 : measurePathEquiv m2 m3) :
    measurePathEquiv m1 m3 :=
  fun e => (h1 e).trans (h2 e)

/-- CongrArg for probability: equal events have equal probability. -/
theorem prob_congrArg {Ω : Type u} (m : MeasurePath Ω) {e1 e2 : Event Ω}
    (h : e1 = e2) : m.prob e1 = m.prob e2 :=
  _root_.congrArg m.prob h

/-- Path from congrArg on probability. -/
noncomputable def prob_congrArg_path {Ω : Type u} (m : MeasurePath Ω) {e1 e2 : Event Ω}
    (h : e1 = e2) : Path (m.prob e1) (m.prob e2) :=
  Path.mk [Step.mk _ _ (_root_.congrArg m.prob h)] (_root_.congrArg m.prob h)

/-- Transport of probability data along event equality. -/
noncomputable def prob_transport {Ω : Type u} {P : Event Ω → Type v}
    {e1 e2 : Event Ω} (h : e1 = e2) (x : P e1) : P e2 :=
  Path.transport (Path.mk [Step.mk _ _ h] h) x

/-- Transport along refl is identity. -/
theorem prob_transport_refl {Ω : Type u} {P : Event Ω → Type v}
    (e : Event Ω) (x : P e) :
    prob_transport (rfl : e = e) x = x := rfl

/-- Normalization path trans refl. -/
theorem norm_path_trans_refl {Ω : Type u} (m : MeasurePath Ω) :
    Path.trans m.normPath (Path.refl m.totalProb) = m.normPath := by
  simp

/-- Normalization path refl trans. -/
theorem norm_path_refl_trans {Ω : Type u} (m : MeasurePath Ω) :
    Path.trans (Path.refl (m.prob (Event.certain Ω))) m.normPath = m.normPath := by
  simp

/-- RwEq: normalization path trans refl step. -/
noncomputable def norm_rweq_trans_refl {Ω : Type u} (m : MeasurePath Ω) :
    RwEq
      (Path.trans m.normPath (Path.refl m.totalProb))
      m.normPath :=
  rweq_of_step (Step.trans_refl_right m.normPath)

/-- RwEq: normalization path refl trans step. -/
noncomputable def norm_rweq_refl_trans {Ω : Type u} (m : MeasurePath Ω) :
    RwEq
      (Path.trans (Path.refl (m.prob (Event.certain Ω))) m.normPath)
      m.normPath :=
  rweq_of_step (Step.trans_refl_left m.normPath)

/-- RwEq: normalization path inv cancel right. -/
noncomputable def norm_rweq_inv_right {Ω : Type u} (m : MeasurePath Ω) :
    RwEq
      (Path.trans m.normPath (Path.symm m.normPath))
      (Path.refl (m.prob (Event.certain Ω))) :=
  rweq_cmpA_inv_right m.normPath

/-- RwEq: normalization path inv cancel left. -/
noncomputable def norm_rweq_inv_left {Ω : Type u} (m : MeasurePath Ω) :
    RwEq
      (Path.trans (Path.symm m.normPath) m.normPath)
      (Path.refl m.totalProb) :=
  rweq_cmpA_inv_left m.normPath

/-- RwEq: symm_symm for normalization path. -/
noncomputable def norm_rweq_symm_symm {Ω : Type u} (m : MeasurePath Ω) :
    RwEq
      (Path.symm (Path.symm m.normPath))
      m.normPath :=
  rweq_of_step (Step.symm_symm m.normPath)

/-! ## Conditional Probability -/

/-- Conditional probability data with path witness. -/
structure CondProb (Ω : Type u) where
  probAB : Nat
  condVal : Nat
  bayesPath : Path condVal probAB

/-- Bayes rule data connecting P(A|B)·P(B) and P(B|A)·P(A) via joint. -/
structure BayesData (Ω : Type u) where
  probAB : Nat
  condValAB : Nat
  condValBA : Nat
  pathAB : Path condValAB probAB
  pathBA : Path condValBA probAB

/-- Bayes composition: a path from condValAB to condValBA. -/
noncomputable def bayes_compose {Ω : Type u} (bd : BayesData Ω) :
    Path bd.condValAB bd.condValBA :=
  Path.trans bd.pathAB (Path.symm bd.pathBA)

/-- Bayes composition trans refl. -/
theorem bayes_trans_refl {Ω : Type u} (bd : BayesData Ω) :
    Path.trans bd.pathAB (Path.refl bd.probAB) = bd.pathAB := by
  simp

/-- Bayes composition refl trans. -/
theorem bayes_refl_trans {Ω : Type u} (bd : BayesData Ω) :
    Path.trans (Path.refl bd.condValAB) bd.pathAB = bd.pathAB := by
  simp

/-- RwEq: pathAB inverse cancel right. -/
noncomputable def bayes_rweq_inv_right {Ω : Type u} (bd : BayesData Ω) :
    RwEq
      (Path.trans bd.pathAB (Path.symm bd.pathAB))
      (Path.refl bd.condValAB) :=
  rweq_cmpA_inv_right bd.pathAB

/-- RwEq: pathAB inverse cancel left. -/
noncomputable def bayes_rweq_inv_left {Ω : Type u} (bd : BayesData Ω) :
    RwEq
      (Path.trans (Path.symm bd.pathAB) bd.pathAB)
      (Path.refl bd.probAB) :=
  rweq_cmpA_inv_left bd.pathAB

/-- RwEq: pathAB trans refl. -/
noncomputable def bayes_rweq_trans_refl {Ω : Type u} (bd : BayesData Ω) :
    RwEq
      (Path.trans bd.pathAB (Path.refl bd.probAB))
      bd.pathAB :=
  rweq_of_step (Step.trans_refl_right bd.pathAB)

/-- RwEq: pathAB refl trans. -/
noncomputable def bayes_rweq_refl_trans {Ω : Type u} (bd : BayesData Ω) :
    RwEq
      (Path.trans (Path.refl bd.condValAB) bd.pathAB)
      bd.pathAB :=
  rweq_of_step (Step.trans_refl_left bd.pathAB)

/-- RwEq: pathAB symm_symm. -/
noncomputable def bayes_rweq_symm_symm {Ω : Type u} (bd : BayesData Ω) :
    RwEq
      (Path.symm (Path.symm bd.pathAB))
      bd.pathAB :=
  rweq_of_step (Step.symm_symm bd.pathAB)

/-- RwEq: pathBA inverse cancel right. -/
noncomputable def bayes_rweq_BA_inv_right {Ω : Type u} (bd : BayesData Ω) :
    RwEq
      (Path.trans bd.pathBA (Path.symm bd.pathBA))
      (Path.refl bd.condValBA) :=
  rweq_cmpA_inv_right bd.pathBA

/-! ## Independence as Path Factoring -/

/-- Independence witness: joint probability factors through product. -/
structure IndepData (Ω : Type u) where
  probA : Nat
  probB : Nat
  probAB : Nat
  product : Nat
  prodPath : Path product (probA * probB)
  indepPath : Path probAB product

/-- Independence factor: composed path from joint to product of marginals. -/
noncomputable def indep_factor_path {Ω : Type u} (d : IndepData Ω) :
    Path d.probAB (d.probA * d.probB) :=
  Path.trans d.indepPath d.prodPath

/-- Independence factor trans refl. -/
theorem indep_factor_refl {Ω : Type u} (d : IndepData Ω) :
    Path.trans d.indepPath (Path.refl d.product) = d.indepPath := by
  simp

/-- Symmetry distributes over independence composition. -/
theorem indep_symm_trans {Ω : Type u} (d : IndepData Ω) :
    Path.symm (indep_factor_path d) =
    Path.trans (Path.symm d.prodPath) (Path.symm d.indepPath) := by
  simp [indep_factor_path]

/-- RwEq: indepPath inv cancel right. -/
noncomputable def indep_rweq_inv_right {Ω : Type u} (d : IndepData Ω) :
    RwEq
      (Path.trans d.indepPath (Path.symm d.indepPath))
      (Path.refl d.probAB) :=
  rweq_cmpA_inv_right d.indepPath

/-- RwEq: indepPath inv cancel left. -/
noncomputable def indep_rweq_inv_left {Ω : Type u} (d : IndepData Ω) :
    RwEq
      (Path.trans (Path.symm d.indepPath) d.indepPath)
      (Path.refl d.product) :=
  rweq_cmpA_inv_left d.indepPath

/-- RwEq: indepPath symm_symm. -/
noncomputable def indep_rweq_symm_symm {Ω : Type u} (d : IndepData Ω) :
    RwEq
      (Path.symm (Path.symm d.indepPath))
      d.indepPath :=
  rweq_of_step (Step.symm_symm d.indepPath)

/-- RwEq: prodPath trans refl. -/
noncomputable def indep_rweq_prod_trans_refl {Ω : Type u} (d : IndepData Ω) :
    RwEq
      (Path.trans d.prodPath (Path.refl (d.probA * d.probB)))
      d.prodPath :=
  rweq_of_step (Step.trans_refl_right d.prodPath)

/-! ## Expectation via Paths -/

/-- Expectation data: weighted sum with path witness. -/
structure ExpectationData where
  expectation : Nat
  weightedSum : Nat
  sumPath : Path expectation weightedSum

/-- Linearity data: constant expectation. -/
structure LinearExpData where
  expectation : Nat
  constProduct : Nat
  constExpPath : Path expectation constProduct

/-- Expectation sum path trans refl. -/
theorem expect_trans_refl (d : ExpectationData) :
    Path.trans d.sumPath (Path.refl d.weightedSum) = d.sumPath := by
  simp

/-- RwEq: expectation inv cancel right. -/
noncomputable def expect_rweq_inv_right (d : ExpectationData) :
    RwEq
      (Path.trans d.sumPath (Path.symm d.sumPath))
      (Path.refl d.expectation) :=
  rweq_cmpA_inv_right d.sumPath

/-- RwEq: expectation inv cancel left. -/
noncomputable def expect_rweq_inv_left (d : ExpectationData) :
    RwEq
      (Path.trans (Path.symm d.sumPath) d.sumPath)
      (Path.refl d.weightedSum) :=
  rweq_cmpA_inv_left d.sumPath

/-- RwEq: expectation trans refl step. -/
noncomputable def expect_rweq_trans_refl (d : ExpectationData) :
    RwEq
      (Path.trans d.sumPath (Path.refl d.weightedSum))
      d.sumPath :=
  rweq_of_step (Step.trans_refl_right d.sumPath)

/-- RwEq: linear exp trans refl. -/
noncomputable def linear_rweq_trans_refl (d : LinearExpData) :
    RwEq
      (Path.trans d.constExpPath (Path.refl d.constProduct))
      d.constExpPath :=
  rweq_of_step (Step.trans_refl_right d.constExpPath)

/-- RwEq: linear exp symm_symm. -/
noncomputable def linear_rweq_symm_symm (d : LinearExpData) :
    RwEq
      (Path.symm (Path.symm d.constExpPath))
      d.constExpPath :=
  rweq_of_step (Step.symm_symm d.constExpPath)

/-! ## Law of Total Probability -/

/-- Total probability path data. -/
structure TotalProbData (Ω : Type u) where
  probA : Nat
  weightedSum : Nat
  totalProbPath : Path probA weightedSum

/-- Total probability trans refl. -/
theorem total_prob_trans_refl {Ω : Type u} (d : TotalProbData Ω) :
    Path.trans d.totalProbPath (Path.refl d.weightedSum) =
    d.totalProbPath := by
  simp

/-- RwEq: total prob inv cancel right. -/
noncomputable def total_prob_rweq_inv_right {Ω : Type u} (d : TotalProbData Ω) :
    RwEq
      (Path.trans d.totalProbPath (Path.symm d.totalProbPath))
      (Path.refl d.probA) :=
  rweq_cmpA_inv_right d.totalProbPath

/-- RwEq: total prob inv cancel left. -/
noncomputable def total_prob_rweq_inv_left {Ω : Type u} (d : TotalProbData Ω) :
    RwEq
      (Path.trans (Path.symm d.totalProbPath) d.totalProbPath)
      (Path.refl d.weightedSum) :=
  rweq_cmpA_inv_left d.totalProbPath

/-- RwEq: total prob trans refl step. -/
noncomputable def total_prob_rweq_trans_refl {Ω : Type u} (d : TotalProbData Ω) :
    RwEq
      (Path.trans d.totalProbPath (Path.refl d.weightedSum))
      d.totalProbPath :=
  rweq_of_step (Step.trans_refl_right d.totalProbPath)

/-- RwEq: total prob symm_symm. -/
noncomputable def total_prob_rweq_symm_symm {Ω : Type u} (d : TotalProbData Ω) :
    RwEq
      (Path.symm (Path.symm d.totalProbPath))
      d.totalProbPath :=
  rweq_of_step (Step.symm_symm d.totalProbPath)

/-! ## Composition of Probability Paths -/

/-- Associativity of probability path composition. -/
theorem prob_path_assoc {a b c d : Nat}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp

/-- Probability path congrArg through a function. -/
noncomputable def prob_map_path {a b : Nat} (f : Nat → Nat) (p : Path a b) :
    Path (f a) (f b) :=
  Path.congrArg f p

/-- Probability path map preserves refl. -/
theorem prob_map_refl (f : Nat → Nat) (a : Nat) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  simp

/-! ## Trivial Instances -/

/-- Trivial measure path on Unit. -/
noncomputable def trivialMeasurePath : MeasurePath Unit where
  prob := fun _ => 1
  totalProb := 1
  normPath := Path.refl 1

/-- Trivial Bayes data. -/
noncomputable def trivialBayesData : BayesData Unit where
  probAB := 1
  condValAB := 1
  condValBA := 1
  pathAB := Path.refl 1
  pathBA := Path.refl 1

/-- Trivial independence data. -/
noncomputable def trivialIndepData : IndepData Unit where
  probA := 1
  probB := 1
  probAB := 1
  product := 1
  prodPath := Path.mk [Step.mk _ _ (by norm_num)] (by norm_num)
  indepPath := Path.refl 1

/-- Trivial expectation data. -/
noncomputable def trivialExpData : ExpectationData where
  expectation := 5
  weightedSum := 5
  sumPath := Path.refl 5

/-- Trivial total probability data. -/
noncomputable def trivialTotalProb : TotalProbData Unit where
  probA := 3
  weightedSum := 3
  totalProbPath := Path.refl 3

end ProbabilityPaths
end Algebra
end Path
end ComputationalPaths
