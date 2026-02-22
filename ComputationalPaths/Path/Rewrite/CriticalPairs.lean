import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.Rw
namespace ComputationalPaths.Path.Rewriting

open ComputationalPaths
open ComputationalPaths.Path

universe u

/-!
# Critical-pair catalogue for computational-path rewriting

This module exposes the concrete local-confluence payload for the computational
paths rewrite system:

1. a paper-indexed catalogue of the 78 rewrite rules;
2. a complete enumeration of critical-pair overlap schemas currently realized
   in `Path.Rewrite.Step`;
3. case-by-case joinability witnesses, each reducing to an explicit
   multi-step proof from the rewrite kernel.
-/

/-- Paper-indexed rule catalogue (1..78).

`trans_congr` is the historical rule 74; in Lean it is represented by the pair
`trans_congr_left` / `trans_congr_right` constructors. -/
inductive StepRule where
  | symm_refl
  | symm_symm
  | trans_refl_left
  | trans_refl_right
  | trans_symm
  | symm_trans
  | symm_trans_congr
  | trans_assoc
  | map2_subst
  | prod_fst_beta
  | prod_snd_beta
  | prod_rec_beta
  | prod_eta
  | prod_mk_symm
  | prod_map_congrArg
  | sigma_fst_beta
  | sigma_snd_beta
  | sigma_eta
  | sigma_mk_symm
  | sum_rec_inl_beta
  | sum_rec_inr_beta
  | fun_app_beta
  | fun_eta
  | lam_congr_symm
  | apd_refl
  | transport_refl_beta
  | transport_trans_beta
  | transport_symm_left_beta
  | transport_symm_right_beta
  | transport_sigmaMk_fst_beta
  | transport_sigmaMk_dep_beta
  | subst_sigmaMk_dep_beta
  | context_congr
  | context_map_symm
  | context_tt_cancel_left
  | context_tt_cancel_right
  | context_subst_left_beta
  | context_subst_left_of_right
  | context_subst_left_assoc
  | context_subst_right_beta
  | context_subst_right_assoc
  | context_subst_left_refl_right
  | context_subst_left_refl_left
  | context_subst_right_refl_left
  | context_subst_right_refl_right
  | context_subst_left_idempotent
  | context_subst_right_cancel_inner
  | context_subst_right_cancel_outer
  | depContext_congr
  | depContext_map_symm
  | depContext_subst_left_beta
  | depContext_subst_left_assoc
  | depContext_subst_right_beta
  | depContext_subst_right_assoc
  | depContext_subst_left_refl_right
  | depContext_subst_left_refl_left
  | depContext_subst_right_refl_left
  | depContext_subst_right_refl_right
  | depContext_subst_left_idempotent
  | depContext_subst_right_cancel_inner
  | depBiContext_mapLeft_congr
  | depBiContext_mapRight_congr
  | depBiContext_map2_congr_left
  | depBiContext_map2_congr_right
  | biContext_mapLeft_congr
  | biContext_mapRight_congr
  | biContext_map2_congr_left
  | biContext_map2_congr_right
  | mapLeft_congr
  | mapRight_congr
  | mapLeft_ofEq
  | mapRight_ofEq
  | symm_congr
  | trans_congr
  | trans_congr_left
  | trans_congr_right
  | trans_cancel_left
  | trans_cancel_right
deriving DecidableEq, Repr

def allStepRules : List StepRule := [
  .symm_refl, .symm_symm, .trans_refl_left, .trans_refl_right, .trans_symm, .symm_trans,
  .symm_trans_congr, .trans_assoc, .map2_subst, .prod_fst_beta, .prod_snd_beta,
  .prod_rec_beta, .prod_eta, .prod_mk_symm, .prod_map_congrArg, .sigma_fst_beta,
  .sigma_snd_beta, .sigma_eta, .sigma_mk_symm, .sum_rec_inl_beta, .sum_rec_inr_beta,
  .fun_app_beta, .fun_eta, .lam_congr_symm, .apd_refl, .transport_refl_beta,
  .transport_trans_beta, .transport_symm_left_beta, .transport_symm_right_beta,
  .transport_sigmaMk_fst_beta, .transport_sigmaMk_dep_beta, .subst_sigmaMk_dep_beta,
  .context_congr, .context_map_symm, .context_tt_cancel_left, .context_tt_cancel_right,
  .context_subst_left_beta, .context_subst_left_of_right, .context_subst_left_assoc,
  .context_subst_right_beta, .context_subst_right_assoc, .context_subst_left_refl_right,
  .context_subst_left_refl_left, .context_subst_right_refl_left, .context_subst_right_refl_right,
  .context_subst_left_idempotent, .context_subst_right_cancel_inner, .context_subst_right_cancel_outer,
  .depContext_congr, .depContext_map_symm, .depContext_subst_left_beta, .depContext_subst_left_assoc,
  .depContext_subst_right_beta, .depContext_subst_right_assoc, .depContext_subst_left_refl_right,
  .depContext_subst_left_refl_left, .depContext_subst_right_refl_left, .depContext_subst_right_refl_right,
  .depContext_subst_left_idempotent, .depContext_subst_right_cancel_inner, .depBiContext_mapLeft_congr,
  .depBiContext_mapRight_congr, .depBiContext_map2_congr_left, .depBiContext_map2_congr_right,
  .biContext_mapLeft_congr, .biContext_mapRight_congr, .biContext_map2_congr_left, .biContext_map2_congr_right,
  .mapLeft_congr, .mapRight_congr, .mapLeft_ofEq, .mapRight_ofEq, .symm_congr, .trans_congr,
  .trans_congr_left, .trans_congr_right, .trans_cancel_left, .trans_cancel_right
]

theorem allStepRules_count : allStepRules.length = 78 := by
  decide

theorem allStepRules_complete : ∀ r : StepRule, r ∈ allStepRules := by
  intro r
  cases r <;> simp [allStepRules]

/-- Enumerated critical-pair overlap schemas. -/
inductive CriticalPairCase where
  | trans_assoc_trans_refl_left
  | trans_assoc_trans_refl_right
  | trans_assoc_trans_symm
  | trans_assoc_symm_trans
  | trans_assoc_trans_assoc
  | symm_congr_symm_symm
  | symm_congr_symm_trans_congr_left
  | symm_congr_symm_trans_congr_right
  | trans_congr_left_right
  | trans_congr_left_trans_assoc
  | trans_congr_right_trans_assoc
  | trans_assoc_trans_refl_inner_right
  | symm_symm_symm_refl
  | symm_symm_symm_trans_congr
  | symm_trans_congr_trans_refl_left
  | symm_trans_congr_trans_refl_right
  | trans_cancel_left_trans_refl_left_inner
  | trans_cancel_right_symm_refl
  | trans_assoc_trans_cancel_left
  | trans_assoc_trans_cancel_right
  | symm_trans_congr_symm_symm_left
  | symm_trans_congr_symm_symm_right
  | trans_cancel_left_trans_refl_right
  | trans_cancel_right_trans_refl_right
  | trans_cancel_left_trans_refl_left
  | trans_cancel_right_trans_refl_left
  | trans_refl_left_trans_assoc
  | trans_refl_right_trans_assoc
  | trans_symm_trans_assoc
  | symm_trans_trans_assoc
  | symm_congr_trans_assoc
  | symm_congr_trans_symm
  | symm_congr_symm_trans
deriving DecidableEq, Repr

def allCriticalPairs : List CriticalPairCase := [
  .trans_assoc_trans_refl_left,
  .trans_assoc_trans_refl_right,
  .trans_assoc_trans_symm,
  .trans_assoc_symm_trans,
  .trans_assoc_trans_assoc,
  .symm_congr_symm_symm,
  .symm_congr_symm_trans_congr_left,
  .symm_congr_symm_trans_congr_right,
  .trans_congr_left_right,
  .trans_congr_left_trans_assoc,
  .trans_congr_right_trans_assoc,
  .trans_assoc_trans_refl_inner_right,
  .symm_symm_symm_refl,
  .symm_symm_symm_trans_congr,
  .symm_trans_congr_trans_refl_left,
  .symm_trans_congr_trans_refl_right,
  .trans_cancel_left_trans_refl_left_inner,
  .trans_cancel_right_symm_refl,
  .trans_assoc_trans_cancel_left,
  .trans_assoc_trans_cancel_right,
  .symm_trans_congr_symm_symm_left,
  .symm_trans_congr_symm_symm_right,
  .trans_cancel_left_trans_refl_right,
  .trans_cancel_right_trans_refl_right,
  .trans_cancel_left_trans_refl_left,
  .trans_cancel_right_trans_refl_left,
  .trans_refl_left_trans_assoc,
  .trans_refl_right_trans_assoc,
  .trans_symm_trans_assoc,
  .symm_trans_trans_assoc,
  .symm_congr_trans_assoc,
  .symm_congr_trans_symm,
  .symm_congr_symm_trans
]

theorem allCriticalPairs_count : allCriticalPairs.length = 33 := by
  decide

theorem allCriticalPairs_complete : ∀ c : CriticalPairCase, c ∈ allCriticalPairs := by
  intro c
  cases c <;> simp [allCriticalPairs]

/-- The pair of rewrite rules producing the given overlap schema. -/
def CriticalPairCase.rules : CriticalPairCase → StepRule × StepRule
  | .trans_assoc_trans_refl_left => (.trans_assoc, .trans_refl_left)
  | .trans_assoc_trans_refl_right => (.trans_assoc, .trans_refl_left)
  | .trans_assoc_trans_symm => (.trans_assoc, .trans_symm)
  | .trans_assoc_symm_trans => (.trans_assoc, .symm_trans)
  | .trans_assoc_trans_assoc => (.trans_assoc, .trans_assoc)
  | .symm_congr_symm_symm => (.symm_congr, .symm_symm)
  | .symm_congr_symm_trans_congr_left => (.symm_congr, .symm_trans_congr)
  | .symm_congr_symm_trans_congr_right => (.symm_congr, .symm_trans_congr)
  | .trans_congr_left_right => (.trans_congr_left, .trans_congr_right)
  | .trans_congr_left_trans_assoc => (.trans_congr_left, .trans_assoc)
  | .trans_congr_right_trans_assoc => (.trans_congr_right, .trans_assoc)
  | .trans_assoc_trans_refl_inner_right => (.trans_assoc, .trans_refl_right)
  | .symm_symm_symm_refl => (.symm_symm, .symm_refl)
  | .symm_symm_symm_trans_congr => (.symm_symm, .symm_trans_congr)
  | .symm_trans_congr_trans_refl_left => (.symm_trans_congr, .trans_refl_right)
  | .symm_trans_congr_trans_refl_right => (.symm_trans_congr, .trans_refl_left)
  | .trans_cancel_left_trans_refl_left_inner => (.trans_cancel_left, .trans_refl_left)
  | .trans_cancel_right_symm_refl => (.trans_cancel_right, .symm_refl)
  | .trans_assoc_trans_cancel_left => (.trans_assoc, .trans_cancel_left)
  | .trans_assoc_trans_cancel_right => (.trans_assoc, .trans_cancel_right)
  | .symm_trans_congr_symm_symm_left => (.symm_trans_congr, .symm_symm)
  | .symm_trans_congr_symm_symm_right => (.symm_trans_congr, .symm_symm)
  | .trans_cancel_left_trans_refl_right => (.trans_cancel_left, .trans_refl_right)
  | .trans_cancel_right_trans_refl_right => (.trans_cancel_right, .trans_refl_right)
  | .trans_cancel_left_trans_refl_left => (.trans_cancel_left, .trans_refl_left)
  | .trans_cancel_right_trans_refl_left => (.trans_cancel_right, .trans_refl_left)
  | .trans_refl_left_trans_assoc => (.trans_refl_left, .trans_assoc)
  | .trans_refl_right_trans_assoc => (.trans_refl_right, .trans_assoc)
  | .trans_symm_trans_assoc => (.trans_symm, .trans_assoc)
  | .symm_trans_trans_assoc => (.symm_trans, .trans_assoc)
  | .symm_congr_trans_assoc => (.symm_congr, .trans_assoc)
  | .symm_congr_trans_symm => (.symm_congr, .trans_symm)
  | .symm_congr_symm_trans => (.symm_congr, .symm_trans)

theorem CriticalPairCase.rules_in_catalogue (c : CriticalPairCase) :
    c.rules.1 ∈ allStepRules ∧ c.rules.2 ∈ allStepRules := by
  exact ⟨allStepRules_complete c.rules.1, allStepRules_complete c.rules.2⟩

def JoinableRw {A : Type u} {a b : A} (p q : Path a b) : Prop :=
  ∃ r, Rw p r ∧ Rw q r

local notation "Step.Joinable" => JoinableRw

theorem joinable_symm {A : Type u} {a b : A} {p q : Path a b} :
    Step.Joinable p q → Step.Joinable q p := by
  intro h
  rcases h with ⟨r, hp, hq⟩
  exact ⟨r, hq, hp⟩

@[simp] theorem rw_single {A : Type u} {a b : A}
    {p q : Path a b} (h : Step p q) : Rw p q := by
  have _ : RwEq p q := rweq_of_step h
  exact Rw.tail (Rw.refl p) h

@[simp] theorem rw_two {A : Type u} {a b : A}
    {p q r : Path a b} (h₁ : Step p q) (h₂ : Step q r) : Rw p r :=
  Rw.tail (rw_single h₁) h₂

@[simp] theorem rw_three {A : Type u} {a b : A}
    {p q r s : Path a b}
    (h₁ : Step p q) (h₂ : Step q r) (h₃ : Step r s) : Rw p s :=
  Rw.tail (rw_two h₁ h₂) h₃

/-- Target joinability statement for each critical-pair schema. -/
def CriticalPairCase.Statement : CriticalPairCase → Prop
  | .trans_assoc_trans_refl_left =>
      ∀ {A : Type u} {a b c : A} (p : Path a b) (r : Path b c),
        Step.Joinable (Path.trans (Path.refl a) (Path.trans p r)) (Path.trans p r)
  | .trans_assoc_trans_refl_right =>
      ∀ {A : Type u} {a b c : A} (p : Path a b) (r : Path b c),
        Step.Joinable (Path.trans p (Path.trans (Path.refl b) r)) (Path.trans p r)
  | .trans_assoc_trans_symm =>
      ∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path a c),
        Step.Joinable (Path.trans p (Path.trans (Path.symm p) q)) (Path.trans (Path.refl a) q)
  | .trans_assoc_symm_trans =>
      ∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path b c),
        Step.Joinable (Path.trans (Path.symm p) (Path.trans p q)) (Path.trans (Path.refl b) q)
  | .trans_assoc_trans_assoc =>
      ∀ {A : Type u} {a b c d e : A}
        (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e),
        Step.Joinable
          (Path.trans (Path.trans p (Path.trans q r)) s)
          (Path.trans (Path.trans p q) (Path.trans r s))
  | .symm_congr_symm_symm =>
      ∀ {A : Type u} {a b : A} {p p' : Path a b}
        (hp : Step p p'),
        Step.Joinable (Path.symm (Path.symm p')) p
  | .symm_congr_symm_trans_congr_left =>
      ∀ {A : Type u} {a b c : A} {p p' : Path a b} {q : Path b c}
        (hp : Step p p'),
        Step.Joinable
          (Path.symm (Path.trans p' q))
          (Path.trans (Path.symm q) (Path.symm p))
  | .symm_congr_symm_trans_congr_right =>
      ∀ {A : Type u} {a b c : A} {p : Path a b} {q q' : Path b c}
        (hq : Step q q'),
        Step.Joinable
          (Path.symm (Path.trans p q'))
          (Path.trans (Path.symm q) (Path.symm p))
  | .trans_congr_left_right =>
      ∀ {A : Type u} {a b c : A} {p p' : Path a b} {q q' : Path b c}
        (hp : Step p p') (hq : Step q q'),
        Step.Joinable (Path.trans p' q) (Path.trans p q')
  | .trans_congr_left_trans_assoc =>
      ∀ {A : Type u} {a b c d : A}
        {p p' : Path a b} {q : Path b c} {r : Path c d}
        (hp : Step p p'),
        Step.Joinable
          (Path.trans (Path.trans p' q) r)
          (Path.trans p (Path.trans q r))
  | .trans_congr_right_trans_assoc =>
      ∀ {A : Type u} {a b c d : A}
        {p : Path a b} {q q' : Path b c} {r : Path c d}
        (hq : Step q q'),
        Step.Joinable
          (Path.trans (Path.trans p q') r)
          (Path.trans p (Path.trans q r))
  | .trans_assoc_trans_refl_inner_right =>
      ∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path b c),
        Step.Joinable (Path.trans p (Path.trans q (Path.refl c))) (Path.trans p q)
  | .symm_symm_symm_refl =>
      ∀ {A : Type u} (a : A),
        Step.Joinable (Path.refl a) (Path.symm (Path.refl a))
  | .symm_symm_symm_trans_congr =>
      ∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path b c),
        Step.Joinable
          (Path.trans p q)
          (Path.symm (Path.trans (Path.symm q) (Path.symm p)))
  | .symm_trans_congr_trans_refl_left =>
      ∀ {A : Type u} {a b : A} (p : Path a b),
        Step.Joinable
          (Path.symm p)
          (Path.trans (Path.symm p) (Path.symm (Path.refl a)))
  | .symm_trans_congr_trans_refl_right =>
      ∀ {A : Type u} {a b : A} (p : Path a b),
        Step.Joinable
          (Path.symm p)
          (Path.trans (Path.symm (Path.refl b)) (Path.symm p))
  | .trans_cancel_left_trans_refl_left_inner =>
      ∀ {A : Type u} {a c : A} (q : Path a c),
        Step.Joinable q (Path.trans (Path.symm (Path.refl a)) q)
  | .trans_cancel_right_symm_refl =>
      ∀ {A : Type u} {a c : A} (q : Path a c),
        Step.Joinable q (Path.trans (Path.refl a) (Path.trans (Path.refl a) q))
  | .trans_assoc_trans_cancel_left =>
      ∀ {A : Type u} {a b c d : A}
        (p : Path a b) (q : Path a c) (r : Path c d),
        Step.Joinable
          (Path.trans q r)
          (Path.trans p (Path.trans (Path.trans (Path.symm p) q) r))
  | .trans_assoc_trans_cancel_right =>
      ∀ {A : Type u} {a b c d : A}
        (p : Path a b) (q : Path b c) (r : Path c d),
        Step.Joinable
          (Path.trans q r)
          (Path.trans (Path.symm p) (Path.trans (Path.trans p q) r))
  | .symm_trans_congr_symm_symm_left =>
      ∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path b c),
        Step.Joinable
          (Path.symm (Path.trans p q))
          (Path.trans (Path.symm q) (Path.symm (Path.symm (Path.symm p))))
  | .symm_trans_congr_symm_symm_right =>
      ∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path b c),
        Step.Joinable
          (Path.symm (Path.trans p q))
          (Path.trans (Path.symm (Path.symm (Path.symm q))) (Path.symm p))
  | .trans_cancel_left_trans_refl_right =>
      ∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path a c),
        Step.Joinable
          (Path.trans q (Path.refl c))
          (Path.trans p (Path.trans (Path.symm p) q))
  | .trans_cancel_right_trans_refl_right =>
      ∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path b c),
        Step.Joinable
          (Path.trans q (Path.refl c))
          (Path.trans (Path.symm p) (Path.trans p q))
  | .trans_cancel_left_trans_refl_left =>
      ∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path a c),
        Step.Joinable
          (Path.trans (Path.refl a) q)
          (Path.trans p (Path.trans (Path.symm p) q))
  | .trans_cancel_right_trans_refl_left =>
      ∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path b c),
        Step.Joinable
          (Path.trans (Path.refl b) q)
          (Path.trans (Path.symm p) (Path.trans p q))
  | .trans_refl_left_trans_assoc =>
      ∀ {A : Type u} {a b c : A} (p : Path a b) (r : Path b c),
        Step.Joinable
          (Path.trans p r)
          (Path.trans (Path.refl a) (Path.trans p r))
  | .trans_refl_right_trans_assoc =>
      ∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path b c),
        Step.Joinable
          (Path.trans p q)
          (Path.trans p (Path.trans q (Path.refl c)))
  | .trans_symm_trans_assoc =>
      ∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path a c),
        Step.Joinable
          (Path.trans (Path.refl a) q)
          (Path.trans p (Path.trans (Path.symm p) q))
  | .symm_trans_trans_assoc =>
      ∀ {A : Type u} {a b c : A} (p : Path a b) (q : Path b c),
        Step.Joinable
          (Path.trans (Path.refl b) q)
          (Path.trans (Path.symm p) (Path.trans p q))
  | .symm_congr_trans_assoc =>
      ∀ {A : Type u} {a b c d : A}
        (p : Path a b) (q : Path b c) (r : Path c d),
        Step.Joinable
          (Path.trans (Path.symm r) (Path.symm (Path.trans p q)))
          (Path.symm (Path.trans p (Path.trans q r)))
  | .symm_congr_trans_symm =>
      ∀ {A : Type u} {a b : A} (p : Path a b),
        Step.Joinable
          (Path.symm (Path.refl a))
          (Path.trans (Path.symm (Path.symm p)) (Path.symm p))
  | .symm_congr_symm_trans =>
      ∀ {A : Type u} {a b : A} (p : Path a b),
        Step.Joinable
          (Path.symm (Path.refl b))
          (Path.trans (Path.symm p) (Path.symm (Path.symm p)))

theorem critical_pair_trans_assoc_trans_refl_left_joinable
    {A : Type u} {a b c : A} (p : Path a b) (r : Path b c) :
    Step.Joinable
      (Path.trans (Path.refl a) (Path.trans p r))
      (Path.trans p r) := by
  refine ⟨Path.trans p r, ?_, ?_⟩
  · exact rw_single (Step.trans_refl_left (Path.trans p r))
  · exact Rw.refl (Path.trans p r)

theorem critical_pair_trans_assoc_trans_refl_right_joinable
    {A : Type u} {a b c : A} (p : Path a b) (r : Path b c) :
    Step.Joinable
      (Path.trans p (Path.trans (Path.refl b) r))
      (Path.trans p r) := by
  refine ⟨Path.trans p r, ?_, ?_⟩
  · exact rw_single
      (Step.trans_congr_right p (Step.trans_refl_left r))
  · exact Rw.refl (Path.trans p r)

theorem critical_pair_trans_assoc_trans_symm_joinable
    {A : Type u} {a b c : A} (p : Path a b) (q : Path a c) :
    Step.Joinable
      (Path.trans p (Path.trans (Path.symm p) q))
      (Path.trans (Path.refl a) q) := by
  refine ⟨q, ?_, ?_⟩
  · exact rw_single (Step.trans_cancel_left p q)
  · exact rw_single (Step.trans_refl_left q)

theorem critical_pair_trans_assoc_symm_trans_joinable
    {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.trans (Path.symm p) (Path.trans p q))
      (Path.trans (Path.refl b) q) := by
  refine ⟨q, ?_, ?_⟩
  · exact rw_single (Step.trans_cancel_right p q)
  · exact rw_single (Step.trans_refl_left q)

theorem critical_pair_trans_assoc_trans_assoc_joinable
    {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Step.Joinable
      (Path.trans (Path.trans p (Path.trans q r)) s)
      (Path.trans (Path.trans p q) (Path.trans r s)) := by
  refine ⟨Path.trans p (Path.trans q (Path.trans r s)), ?_, ?_⟩
  · exact rw_two
      (Step.trans_assoc p (Path.trans q r) s)
      (Step.trans_congr_right p (Step.trans_assoc q r s))
  · exact rw_single (Step.trans_assoc p q (Path.trans r s))

theorem critical_pair_symm_congr_symm_symm_joinable
    {A : Type u} {a b : A} {p p' : Path a b}
    (hp : Step p p') :
    Step.Joinable
      (Path.symm (Path.symm p'))
      p := by
  refine ⟨p', ?_, ?_⟩
  · exact rw_single (Step.symm_symm p')
  · exact rw_single hp

theorem critical_pair_symm_congr_symm_trans_congr_left_joinable
    {A : Type u} {a b c : A} {p p' : Path a b} {q : Path b c}
    (hp : Step p p') :
    Step.Joinable
      (Path.symm (Path.trans p' q))
      (Path.trans (Path.symm q) (Path.symm p)) := by
  refine ⟨Path.trans (Path.symm q) (Path.symm p'), ?_, ?_⟩
  · exact rw_single (Step.symm_trans_congr p' q)
  · exact rw_single
      (Step.trans_congr_right (Path.symm q) (Step.symm_congr hp))

theorem critical_pair_symm_congr_symm_trans_congr_right_joinable
    {A : Type u} {a b c : A} {p : Path a b} {q q' : Path b c}
    (hq : Step q q') :
    Step.Joinable
      (Path.symm (Path.trans p q'))
      (Path.trans (Path.symm q) (Path.symm p)) := by
  refine ⟨Path.trans (Path.symm q') (Path.symm p), ?_, ?_⟩
  · exact rw_single (Step.symm_trans_congr p q')
  · exact rw_single
      (Step.trans_congr_left (Path.symm p) (Step.symm_congr hq))

theorem critical_pair_trans_congr_left_right_joinable
    {A : Type u} {a b c : A} {p p' : Path a b} {q q' : Path b c}
    (hp : Step p p') (hq : Step q q') :
    Step.Joinable
      (Path.trans p' q)
      (Path.trans p q') := by
  refine ⟨Path.trans p' q', ?_, ?_⟩
  · exact rw_single (Step.trans_congr_right p' hq)
  · exact rw_single (Step.trans_congr_left q' hp)

theorem critical_pair_trans_congr_left_trans_assoc_joinable
    {A : Type u} {a b c d : A}
    {p p' : Path a b} {q : Path b c} {r : Path c d}
    (hp : Step p p') :
    Step.Joinable
      (Path.trans (Path.trans p' q) r)
      (Path.trans p (Path.trans q r)) := by
  refine ⟨Path.trans p' (Path.trans q r), ?_, ?_⟩
  · exact rw_single (Step.trans_assoc p' q r)
  · exact rw_single (Step.trans_congr_left (Path.trans q r) hp)

theorem critical_pair_trans_congr_right_trans_assoc_joinable
    {A : Type u} {a b c d : A}
    {p : Path a b} {q q' : Path b c} {r : Path c d}
    (hq : Step q q') :
    Step.Joinable
      (Path.trans (Path.trans p q') r)
      (Path.trans p (Path.trans q r)) := by
  refine ⟨Path.trans p (Path.trans q' r), ?_, ?_⟩
  · exact rw_single (Step.trans_assoc p q' r)
  · exact rw_single
      (Step.trans_congr_right p (Step.trans_congr_left r hq))

theorem critical_pair_trans_assoc_trans_refl_inner_right_joinable
    {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.trans p (Path.trans q (Path.refl c)))
      (Path.trans p q) := by
  refine ⟨Path.trans p q, ?_, ?_⟩
  · exact rw_single
      (Step.trans_congr_right p (Step.trans_refl_right q))
  · exact Rw.refl (Path.trans p q)

theorem critical_pair_symm_symm_symm_refl_joinable
    {A : Type u} (a : A) :
    Step.Joinable (Path.refl a) (Path.symm (Path.refl a)) := by
  refine ⟨Path.refl a, ?_, ?_⟩
  · exact Rw.refl (Path.refl a)
  · exact rw_single (Step.symm_refl a)

theorem critical_pair_symm_symm_symm_trans_congr_joinable
    {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.trans p q)
      (Path.symm (Path.trans (Path.symm q) (Path.symm p))) := by
  refine ⟨Path.trans p q, ?_, ?_⟩
  · exact Rw.refl (Path.trans p q)
  · exact rw_three
      (Step.symm_trans_congr (Path.symm q) (Path.symm p))
      (Step.trans_congr_left (Path.symm (Path.symm q)) (Step.symm_symm p))
      (Step.trans_congr_right p (Step.symm_symm q))

theorem critical_pair_symm_trans_congr_trans_refl_left_joinable
    {A : Type u} {a b : A} (p : Path a b) :
    Step.Joinable
      (Path.symm p)
      (Path.trans (Path.symm p) (Path.symm (Path.refl a))) := by
  refine ⟨Path.symm p, ?_, ?_⟩
  · exact Rw.refl (Path.symm p)
  · exact rw_two
      (Step.trans_congr_right (Path.symm p) (Step.symm_refl a))
      (Step.trans_refl_right (Path.symm p))

theorem critical_pair_symm_trans_congr_trans_refl_right_joinable
    {A : Type u} {a b : A} (p : Path a b) :
    Step.Joinable
      (Path.symm p)
      (Path.trans (Path.symm (Path.refl b)) (Path.symm p)) := by
  refine ⟨Path.symm p, ?_, ?_⟩
  · exact Rw.refl (Path.symm p)
  · exact rw_two
      (Step.trans_congr_left (Path.symm p) (Step.symm_refl b))
      (Step.trans_refl_left (Path.symm p))

theorem critical_pair_trans_cancel_left_trans_refl_left_inner_joinable
    {A : Type u} {a c : A} (q : Path a c) :
    Step.Joinable
      q
      (Path.trans (Path.symm (Path.refl a)) q) := by
  refine ⟨q, ?_, ?_⟩
  · exact Rw.refl q
  · exact rw_two
      (Step.trans_congr_left q (Step.symm_refl a))
      (Step.trans_refl_left q)

theorem critical_pair_trans_cancel_right_symm_refl_joinable
    {A : Type u} {a c : A} (q : Path a c) :
    Step.Joinable
      q
      (Path.trans (Path.refl a) (Path.trans (Path.refl a) q)) := by
  refine ⟨q, ?_, ?_⟩
  · exact Rw.refl q
  · exact rw_two
      (Step.trans_refl_left (Path.trans (Path.refl a) q))
      (Step.trans_refl_left q)

theorem critical_pair_trans_assoc_trans_cancel_left_joinable
    {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path a c) (r : Path c d) :
    Step.Joinable
      (Path.trans q r)
      (Path.trans p (Path.trans (Path.trans (Path.symm p) q) r)) := by
  refine ⟨Path.trans q r, ?_, ?_⟩
  · exact Rw.refl (Path.trans q r)
  · exact rw_two
      (Step.trans_congr_right p (Step.trans_assoc (Path.symm p) q r))
      (Step.trans_cancel_left p (Path.trans q r))

theorem critical_pair_trans_assoc_trans_cancel_right_joinable
    {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Step.Joinable
      (Path.trans q r)
      (Path.trans (Path.symm p) (Path.trans (Path.trans p q) r)) := by
  refine ⟨Path.trans q r, ?_, ?_⟩
  · exact Rw.refl (Path.trans q r)
  · exact rw_two
      (Step.trans_congr_right (Path.symm p) (Step.trans_assoc p q r))
      (Step.trans_cancel_right p (Path.trans q r))

theorem critical_pair_symm_trans_congr_symm_symm_left_joinable
    {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.symm (Path.trans p q))
      (Path.trans (Path.symm q) (Path.symm (Path.symm (Path.symm p)))) := by
  refine ⟨Path.trans (Path.symm q) (Path.symm p), ?_, ?_⟩
  · exact rw_single (Step.symm_trans_congr p q)
  · exact rw_single
      (Step.trans_congr_right (Path.symm q) (Step.symm_symm (Path.symm p)))

theorem critical_pair_symm_trans_congr_symm_symm_right_joinable
    {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.symm (Path.trans p q))
      (Path.trans (Path.symm (Path.symm (Path.symm q))) (Path.symm p)) := by
  refine ⟨Path.trans (Path.symm q) (Path.symm p), ?_, ?_⟩
  · exact rw_single (Step.symm_trans_congr p q)
  · exact rw_single
      (Step.trans_congr_left (Path.symm p) (Step.symm_symm (Path.symm q)))

theorem critical_pair_trans_cancel_left_trans_refl_right_joinable
    {A : Type u} {a b c : A}
    (p : Path a b) (q : Path a c) :
    Step.Joinable
      (Path.trans q (Path.refl c))
      (Path.trans p (Path.trans (Path.symm p) q)) := by
  refine ⟨q, ?_, ?_⟩
  · exact rw_single (Step.trans_refl_right q)
  · exact rw_single (Step.trans_cancel_left p q)

theorem critical_pair_trans_cancel_right_trans_refl_right_joinable
    {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.trans q (Path.refl c))
      (Path.trans (Path.symm p) (Path.trans p q)) := by
  refine ⟨q, ?_, ?_⟩
  · exact rw_single (Step.trans_refl_right q)
  · exact rw_single (Step.trans_cancel_right p q)

theorem critical_pair_trans_cancel_left_trans_refl_left_joinable
    {A : Type u} {a b c : A}
    (p : Path a b) (q : Path a c) :
    Step.Joinable
      (Path.trans (Path.refl a) q)
      (Path.trans p (Path.trans (Path.symm p) q)) := by
  refine ⟨q, ?_, ?_⟩
  · exact rw_single (Step.trans_refl_left q)
  · exact rw_single (Step.trans_cancel_left p q)

theorem critical_pair_trans_cancel_right_trans_refl_left_joinable
    {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.trans (Path.refl b) q)
      (Path.trans (Path.symm p) (Path.trans p q)) := by
  refine ⟨q, ?_, ?_⟩
  · exact rw_single (Step.trans_refl_left q)
  · exact rw_single (Step.trans_cancel_right p q)

theorem critical_pair_trans_refl_left_trans_assoc_joinable
    {A : Type u} {a b c : A} (p : Path a b) (r : Path b c) :
    Step.Joinable
      (Path.trans p r)
      (Path.trans (Path.refl a) (Path.trans p r)) := by
  exact joinable_symm
    (critical_pair_trans_assoc_trans_refl_left_joinable p r)

theorem critical_pair_trans_refl_right_trans_assoc_joinable
    {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.trans p q)
      (Path.trans p (Path.trans q (Path.refl c))) := by
  exact joinable_symm
    (critical_pair_trans_assoc_trans_refl_inner_right_joinable p q)

theorem critical_pair_trans_symm_trans_assoc_joinable
    {A : Type u} {a b c : A} (p : Path a b) (q : Path a c) :
    Step.Joinable
      (Path.trans (Path.refl a) q)
      (Path.trans p (Path.trans (Path.symm p) q)) := by
  exact joinable_symm
    (critical_pair_trans_assoc_trans_symm_joinable p q)

theorem critical_pair_symm_trans_trans_assoc_joinable
    {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.trans (Path.refl b) q)
      (Path.trans (Path.symm p) (Path.trans p q)) := by
  exact joinable_symm
    (critical_pair_trans_assoc_symm_trans_joinable p q)

theorem critical_pair_symm_congr_trans_assoc_joinable
    {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Step.Joinable
      (Path.trans (Path.symm r) (Path.symm (Path.trans p q)))
      (Path.symm (Path.trans p (Path.trans q r))) := by
  refine ⟨Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)), ?_, ?_⟩
  · exact rw_single
      (Step.trans_congr_right (Path.symm r) (Step.symm_trans_congr p q))
  · exact rw_three
      (Step.symm_trans_congr p (Path.trans q r))
      (Step.trans_congr_left (Path.symm p) (Step.symm_trans_congr q r))
      (Step.trans_assoc (Path.symm r) (Path.symm q) (Path.symm p))

theorem critical_pair_symm_congr_trans_symm_joinable
    {A : Type u} {a b : A} (p : Path a b) :
    Step.Joinable
      (Path.symm (Path.refl a))
      (Path.trans (Path.symm (Path.symm p)) (Path.symm p)) := by
  refine ⟨Path.refl a, ?_, ?_⟩
  · exact rw_single (Step.symm_refl a)
  · exact rw_two
      (Step.trans_congr_left (Path.symm p) (Step.symm_symm p))
      (Step.trans_symm p)

theorem critical_pair_symm_congr_symm_trans_joinable
    {A : Type u} {a b : A} (p : Path a b) :
    Step.Joinable
      (Path.symm (Path.refl b))
      (Path.trans (Path.symm p) (Path.symm (Path.symm p))) := by
  refine ⟨Path.refl b, ?_, ?_⟩
  · exact rw_single (Step.symm_refl b)
  · exact rw_single (Step.trans_symm (Path.symm p))

/-- Case analysis assigning each critical pair its explicit resolution proof. -/
def CriticalPairCase.proof : (c : CriticalPairCase) → c.Statement
  | .trans_assoc_trans_refl_left => critical_pair_trans_assoc_trans_refl_left_joinable
  | .trans_assoc_trans_refl_right => critical_pair_trans_assoc_trans_refl_right_joinable
  | .trans_assoc_trans_symm => critical_pair_trans_assoc_trans_symm_joinable
  | .trans_assoc_symm_trans => critical_pair_trans_assoc_symm_trans_joinable
  | .trans_assoc_trans_assoc => critical_pair_trans_assoc_trans_assoc_joinable
  | .symm_congr_symm_symm => critical_pair_symm_congr_symm_symm_joinable
  | .symm_congr_symm_trans_congr_left => critical_pair_symm_congr_symm_trans_congr_left_joinable
  | .symm_congr_symm_trans_congr_right => critical_pair_symm_congr_symm_trans_congr_right_joinable
  | .trans_congr_left_right => critical_pair_trans_congr_left_right_joinable
  | .trans_congr_left_trans_assoc => critical_pair_trans_congr_left_trans_assoc_joinable
  | .trans_congr_right_trans_assoc => critical_pair_trans_congr_right_trans_assoc_joinable
  | .trans_assoc_trans_refl_inner_right => critical_pair_trans_assoc_trans_refl_inner_right_joinable
  | .symm_symm_symm_refl => critical_pair_symm_symm_symm_refl_joinable
  | .symm_symm_symm_trans_congr => critical_pair_symm_symm_symm_trans_congr_joinable
  | .symm_trans_congr_trans_refl_left => critical_pair_symm_trans_congr_trans_refl_left_joinable
  | .symm_trans_congr_trans_refl_right => critical_pair_symm_trans_congr_trans_refl_right_joinable
  | .trans_cancel_left_trans_refl_left_inner => critical_pair_trans_cancel_left_trans_refl_left_inner_joinable
  | .trans_cancel_right_symm_refl => critical_pair_trans_cancel_right_symm_refl_joinable
  | .trans_assoc_trans_cancel_left => critical_pair_trans_assoc_trans_cancel_left_joinable
  | .trans_assoc_trans_cancel_right => critical_pair_trans_assoc_trans_cancel_right_joinable
  | .symm_trans_congr_symm_symm_left => critical_pair_symm_trans_congr_symm_symm_left_joinable
  | .symm_trans_congr_symm_symm_right => critical_pair_symm_trans_congr_symm_symm_right_joinable
  | .trans_cancel_left_trans_refl_right => critical_pair_trans_cancel_left_trans_refl_right_joinable
  | .trans_cancel_right_trans_refl_right => critical_pair_trans_cancel_right_trans_refl_right_joinable
  | .trans_cancel_left_trans_refl_left => critical_pair_trans_cancel_left_trans_refl_left_joinable
  | .trans_cancel_right_trans_refl_left => critical_pair_trans_cancel_right_trans_refl_left_joinable
  | .trans_refl_left_trans_assoc => critical_pair_trans_refl_left_trans_assoc_joinable
  | .trans_refl_right_trans_assoc => critical_pair_trans_refl_right_trans_assoc_joinable
  | .trans_symm_trans_assoc => critical_pair_trans_symm_trans_assoc_joinable
  | .symm_trans_trans_assoc => critical_pair_symm_trans_trans_assoc_joinable
  | .symm_congr_trans_assoc => critical_pair_symm_congr_trans_assoc_joinable
  | .symm_congr_trans_symm => critical_pair_symm_congr_trans_symm_joinable
  | .symm_congr_symm_trans => critical_pair_symm_congr_symm_trans_joinable

theorem local_confluence_on_critical_pair (c : CriticalPairCase) : c.Statement :=
  c.proof

theorem all_critical_pairs_joinable :
    ∀ c ∈ allCriticalPairs, c.Statement := by
  intro c _
  exact local_confluence_on_critical_pair c

end ComputationalPaths.Path.Rewriting
