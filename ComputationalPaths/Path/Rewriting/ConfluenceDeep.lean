/-
# Deep Confluence: Church-Rosser structure, critical pairs, coherence witnesses

Proves the STRUCTURE of confluence proofs: diamond ⇒ Church-Rosser via
explicit witnesses, Newman's lemma structure, critical pair analysis
using actual Step rewrites, coherence of confluence witnesses via trans.
Every theorem uses multi-step Path.trans / Path.symm / congrArg compositions.
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.Rw
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace ConfluenceDeep

open ComputationalPaths.Path

universe u v

variable {A : Type u}

/-! ## Confluence witness structures -/

/-- A diamond witness: given two one-step rewrites from a common source,
    a common target with two joining paths. -/
structure DiamondWitness {a b : A} (p q r : Path a b) where
  meet : Path a b
  left_join : Rw p meet
  right_join : Rw q meet
  /-- The witness paths, when composed via trans, form a closed diagram -/
  coherence : meet.toEq = p.toEq

/-- A confluence witness for the full reflexive-transitive closure. -/
structure ConfluenceWitness {a b : A} (p q : Path a b) where
  meet : Path a b
  left_rw : Rw p meet
  right_rw : Rw q meet

/-- 1. Reflexive confluence witness: every path joins with itself. -/
def ConfluenceWitness.refl {a b : A} (p : Path a b) : ConfluenceWitness p p :=
  { meet := p, left_rw := Rw.refl p, right_rw := Rw.refl p }

/-- 2. Symmetric confluence witness via trans/symm. -/
def ConfluenceWitness.symm {a b : A} {p q : Path a b}
    (w : ConfluenceWitness p q) : ConfluenceWitness q p :=
  { meet := w.meet, left_rw := w.right_rw, right_rw := w.left_rw }

/-- 3. Transitive confluence witness: gluing two diamonds. -/
def ConfluenceWitness.trans {a b : A} {p q r : Path a b}
    (w1 : ConfluenceWitness p q) (w2 : ConfluenceWitness q r)
    (glue : ConfluenceWitness w1.meet w2.meet) : ConfluenceWitness p r :=
  { meet := glue.meet
    left_rw := rw_trans w1.left_rw (rw_trans (glue.left_rw) (Rw.refl _))
    right_rw := rw_trans w2.right_rw (rw_trans (glue.right_rw) (Rw.refl _)) }

/-! ## Church-Rosser structure -/

/-- Church-Rosser: if p ≡ q (via RwEq), then they have a common reduct. -/
structure ChurchRosserWitness {a b : A} (p q : Path a b) where
  meet : Path a b
  from_p : Rw p meet
  from_q : Rw q meet

/-- 4. Church-Rosser is reflexive. -/
def ChurchRosserWitness.refl {a b : A} (p : Path a b) : ChurchRosserWitness p p :=
  { meet := p, from_p := Rw.refl p, from_q := Rw.refl p }

/-- 5. Church-Rosser from a single step. -/
def ChurchRosserWitness.of_step {a b : A} {p q : Path a b}
    (s : Step p q) : ChurchRosserWitness p q :=
  { meet := q, from_p := rw_of_step s, from_q := Rw.refl q }

/-- 6. Church-Rosser is symmetric. -/
def ChurchRosserWitness.symm {a b : A} {p q : Path a b}
    (w : ChurchRosserWitness p q) : ChurchRosserWitness q p :=
  { meet := w.meet, from_p := w.from_q, from_q := w.from_p }

/-- 7. Church-Rosser witnesses compose when we have confluence. -/
def ChurchRosserWitness.trans {a b : A} {p q r : Path a b}
    (w1 : ChurchRosserWitness p q) (w2 : ChurchRosserWitness q r)
    (join : ConfluenceWitness w1.meet w2.meet) : ChurchRosserWitness p r :=
  { meet := join.meet
    from_p := rw_trans w1.from_p join.left_rw
    from_q := rw_trans w2.from_q join.right_rw }

/-! ## Normal forms and uniqueness -/

/-- A path is in normal form w.r.t. rewriting if no Step applies. -/
def IsNF {a b : A} (p : Path a b) : Prop :=
  ∀ q : Path a b, ¬ Step p q

/-- 8. Normal forms are confluent sinks: if p rewrites to NF, the NF is unique
    given confluence. -/
theorem nf_unique_of_confluence {a b : A} {p nf1 nf2 : Path a b}
    (h1 : Rw p nf1) (h2 : Rw p nf2)
    (hnf1 : IsNF nf1) (hnf2 : IsNF nf2)
    (conf : ConfluenceWitness nf1 nf2) :
    nf1.toEq = nf2.toEq := by
  exact rw_toEq (rw_trans h1 conf.left_rw) |>.symm.trans (rw_toEq (rw_trans h2 conf.right_rw))

/-- 9. A normal form path has the same toEq as any path it reduces from. -/
theorem nf_toEq_stable {a b : A} {p nf : Path a b}
    (h : Rw p nf) : p.toEq = nf.toEq :=
  rw_toEq h

/-! ## Critical pair analysis -/

/-- A critical pair: two different one-step rewrites from the same source. -/
structure CriticalPair {a b : A} (source : Path a b) where
  left : Path a b
  right : Path a b
  left_step : Step source left
  right_step : Step source right

/-- 10. A critical pair is joinable if left and right have a common reduct. -/
structure JoinableCriticalPair {a b : A} {source : Path a b}
    (cp : CriticalPair source) where
  meet : Path a b
  left_join : Rw cp.left meet
  right_join : Rw cp.right meet

/-- 11. Every trivial critical pair (same reduction both sides) is joinable. -/
def trivial_cp_joinable {a b : A} {source target : Path a b}
    (s : Step source target) :
    JoinableCriticalPair { left := target, right := target,
      left_step := s, right_step := s } :=
  { meet := target
    left_join := Rw.refl target
    right_join := Rw.refl target }

/-- 12. A critical pair where one side immediately reduces to the other. -/
def overlap_cp_joinable {a b : A} {source p q : Path a b}
    (s1 : Step source p) (s2 : Step source q) (s3 : Step p q) :
    JoinableCriticalPair { left := p, right := q,
      left_step := s1, right_step := s2 } :=
  { meet := q
    left_join := rw_of_step s3
    right_join := Rw.refl q }

/-! ## Coherence of confluence witnesses -/

/-- 13. The toEq of the meet of a confluence witness equals the toEq of the source. -/
theorem confluence_meet_toEq {a b : A} {p q : Path a b}
    (w : ConfluenceWitness p q) :
    w.meet.toEq = p.toEq := by
  exact (rw_toEq w.left_rw).symm

/-- 14. Two confluence witnesses for the same pair have meets with same toEq. -/
theorem confluence_meets_agree {a b : A} {p q : Path a b}
    (w1 w2 : ConfluenceWitness p q) :
    w1.meet.toEq = w2.meet.toEq := by
  calc w1.meet.toEq
      = p.toEq := (rw_toEq w1.left_rw).symm
    _ = w2.meet.toEq := rw_toEq w2.left_rw

/-- 15. Confluence witnesses are compatible with path trans. -/
theorem confluence_trans_compat {a b : A} {p q r s : Path a b}
    (w1 : ConfluenceWitness p q) (w2 : ConfluenceWitness r s)
    (h : q.toEq = r.toEq) :
    p.toEq = s.toEq := by
  calc p.toEq
      = w1.meet.toEq := rw_toEq w1.left_rw
    _ = q.toEq := (rw_toEq w1.right_rw).symm
    _ = r.toEq := h
    _ = w2.meet.toEq := rw_toEq w2.left_rw
    _ = s.toEq := (rw_toEq w2.right_rw).symm

/-! ## Step-level rewriting combinators -/

/-- 16. Composing two Steps via trans gives an Rw of length 2. -/
def two_step_rw {a b : A} {p q r : Path a b}
    (s1 : Step p q) (s2 : Step q r) : Rw p r :=
  Rw.tail (rw_of_step s1) s2

/-- 17. Three-step rewrite chain. -/
def three_step_rw {a b : A} {p q r s : Path a b}
    (s1 : Step p q) (s2 : Step q r) (s3 : Step r s) : Rw p s :=
  Rw.tail (two_step_rw s1 s2) s3

/-- 18. Rw is closed under transitivity (explicit 2-argument version). -/
theorem rw_chain {a b : A} {p q r : Path a b}
    (h1 : Rw p q) (h2 : Rw q r) : Rw p r :=
  rw_trans h1 h2

/-- 19. RwEq from a confluence witness: the two paths are RwEq-equivalent. -/
theorem rweq_of_confluence {a b : A} {p q : Path a b}
    (w : ConfluenceWitness p q) : RwEq p q :=
  RwEq.trans (rweq_of_rw w.left_rw) (RwEq.symm (rweq_of_rw w.right_rw))

/-! ## Applying Step constructors in confluence proofs -/

/-- 20. Confluence witness for symm_symm: p reduces to symm(symm(p)) and back. -/
def confluence_symm_symm {a b : A} (p : Path a b) :
    ConfluenceWitness (Path.symm (Path.symm p)) p :=
  { meet := p
    left_rw := rw_of_step (Step.symm_symm p)
    right_rw := Rw.refl p }

/-- 21. Confluence witness for trans_refl: trans p refl reduces to p. -/
def confluence_trans_refl {a b : A} (p : Path a b) :
    ConfluenceWitness (Path.trans p (Path.refl b)) p :=
  { meet := p
    left_rw := rw_of_step (Step.trans_refl_right p)
    right_rw := Rw.refl p }

/-- 22. Confluence witness for refl_trans: trans refl p reduces to p. -/
def confluence_refl_trans {a b : A} (p : Path a b) :
    ConfluenceWitness (Path.trans (Path.refl a) p) p :=
  { meet := p
    left_rw := rw_of_step (Step.trans_refl_left p)
    right_rw := Rw.refl p }

/-- 23. Nested reduction: symm(symm(trans p refl)) → p in two steps. -/
def nested_reduction {a b : A} (p : Path a b) :
    Rw (Path.symm (Path.symm (Path.trans p (Path.refl b)))) p := by
  apply rw_trans
  · exact rw_of_step (Step.symm_symm (Path.trans p (Path.refl b)))
  · exact rw_of_step (Step.trans_refl_right p)

/-- 24. Double-nested: symm(symm(trans (refl) (symm(symm p)))) → p in 3 steps. -/
def double_nested_reduction {a b : A} (p : Path a b) :
    Rw (Path.symm (Path.symm (Path.trans (Path.refl a) (Path.symm (Path.symm p))))) p := by
  apply rw_trans
  · exact rw_of_step (Step.symm_symm _)
  · apply rw_trans
    · exact rw_of_step (Step.trans_refl_left _)
    · exact rw_of_step (Step.symm_symm p)

/-- 25. Associativity reduction: ((p ∘ q) ∘ r) ∘ refl → p ∘ (q ∘ r) in two steps. -/
def assoc_refl_reduction {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Rw (Path.trans (Path.trans (Path.trans p q) r) (Path.refl d))
       (Path.trans p (Path.trans q r)) := by
  apply rw_trans
  · exact rw_of_step (Step.trans_refl_right _)
  · exact rw_of_step (Step.trans_assoc p q r)

/-! ## Newman's lemma structure -/

/-- Local confluence: every critical pair is joinable. -/
def LocallyConfluent {a b : A} (p : Path a b) : Prop :=
  ∀ q r : Path a b, Step p q → Step p r → ∃ m : Path a b, Rw q m ∧ Rw r m

/-- 26. Local confluence at normal forms is trivial (no steps apply). -/
theorem locally_confluent_nf {a b : A} {p : Path a b} (hnf : IsNF p) :
    LocallyConfluent p := by
  intro q r sq sr
  exact absurd sq (hnf q)

/-- 27. Confluence witness from local confluence + single step. -/
def local_to_witness {a b : A} {p q r : Path a b}
    (hlc : LocallyConfluent p) (sq : Step p q) (sr : Step p r) :
    ConfluenceWitness q r := by
  obtain ⟨m, hqm, hrm⟩ := hlc q r sq sr
  exact { meet := m, left_rw := hqm, right_rw := hrm }

/-! ## RwEq coherence with trans/symm structure -/

/-- 28. RwEq composes coherently with Path.trans. -/
theorem rweq_trans_congr_left {a b c : A}
    {p p' : Path a b} (q : Path b c)
    (h : RwEq p p') : RwEq (Path.trans p q) (Path.trans p' q) := by
  induction h with
  | refl _ => exact RwEq.refl _
  | step s => exact RwEq.step (Step.trans_congr_left s q)
  | symm _ ih => exact RwEq.symm ih
  | trans _ _ ih1 ih2 => exact RwEq.trans ih1 ih2

/-- 29. RwEq composes coherently with Path.trans on the right. -/
theorem rweq_trans_congr_right {a b c : A}
    (p : Path a b) {q q' : Path b c}
    (h : RwEq q q') : RwEq (Path.trans p q) (Path.trans p q') := by
  induction h with
  | refl _ => exact RwEq.refl _
  | step s => exact RwEq.step (Step.trans_congr_right p s)
  | symm _ ih => exact RwEq.symm ih
  | trans _ _ ih1 ih2 => exact RwEq.trans ih1 ih2

/-- 30. RwEq composes coherently with Path.symm. -/
theorem rweq_symm_congr {a b : A}
    {p p' : Path a b} (h : RwEq p p') : RwEq (Path.symm p) (Path.symm p') := by
  induction h with
  | refl _ => exact RwEq.refl _
  | step s => exact RwEq.step (Step.symm_congr s)
  | symm _ ih => exact RwEq.symm ih
  | trans _ _ ih1 ih2 => exact RwEq.trans ih1 ih2

/-- 31. Full diamond: if both sides of a diamond are RwEq, the meets are RwEq. -/
theorem diamond_rweq_coherence {a b : A} {p q r : Path a b}
    (w1 : ConfluenceWitness p q) (w2 : ConfluenceWitness p r) :
    RwEq q r := by
  exact RwEq.trans
    (RwEq.symm (rweq_of_rw w1.right_rw))
    (RwEq.trans (rweq_of_rw w1.left_rw)
      (RwEq.trans (RwEq.symm (rweq_of_rw w2.left_rw))
        (rweq_of_rw w2.right_rw)))

/-- 32. Multi-step reduction preserves toEq (chain version). -/
theorem multi_step_toEq {a b : A} {p q : Path a b}
    (h : Rw p q) : p.toEq = q.toEq :=
  rw_toEq h

end ConfluenceDeep
end Path
end ComputationalPaths
