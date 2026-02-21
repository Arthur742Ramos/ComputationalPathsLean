import CompPaths.Core
import CompPaths.Rewriting.CriticalPairs
import ComputationalPaths.Path.Rewrite.GroupoidTRS

namespace CompPaths.Rewriting

abbrev Expr := ComputationalPaths.Path.Rewrite.GroupoidTRS.Expr
abbrev CStep : Expr → Expr → Prop := ComputationalPaths.Path.Rewrite.GroupoidTRS.Expr.Step

inductive StepCategory where
  | groupoid
  | product
  | sigma
  | sum
  | function
  | transport
  | context
  | depContext
  | biContext
  | map
  | structural
deriving DecidableEq, Repr

def categoryOf : StepRule → StepCategory
  | .symm_refl | .symm_symm | .trans_refl_left | .trans_refl_right
  | .trans_symm | .symm_trans | .symm_trans_congr | .trans_assoc => .groupoid
  | .map2_subst | .prod_fst_beta | .prod_snd_beta | .prod_rec_beta
  | .prod_eta | .prod_mk_symm | .prod_map_congrArg => .product
  | .sigma_fst_beta | .sigma_snd_beta | .sigma_eta | .sigma_mk_symm => .sigma
  | .sum_rec_inl_beta | .sum_rec_inr_beta => .sum
  | .fun_app_beta | .fun_eta | .lam_congr_symm | .apd_refl => .function
  | .transport_refl_beta | .transport_trans_beta | .transport_symm_left_beta
  | .transport_symm_right_beta | .transport_sigmaMk_fst_beta
  | .transport_sigmaMk_dep_beta | .subst_sigmaMk_dep_beta => .transport
  | .context_congr | .context_map_symm | .context_tt_cancel_left
  | .context_tt_cancel_right | .context_subst_left_beta
  | .context_subst_left_of_right | .context_subst_left_assoc
  | .context_subst_right_beta | .context_subst_right_assoc
  | .context_subst_left_refl_right | .context_subst_left_refl_left
  | .context_subst_right_refl_left | .context_subst_right_refl_right
  | .context_subst_left_idempotent | .context_subst_right_cancel_inner
  | .context_subst_right_cancel_outer => .context
  | .depContext_congr | .depContext_map_symm | .depContext_subst_left_beta
  | .depContext_subst_left_assoc | .depContext_subst_right_beta
  | .depContext_subst_right_assoc | .depContext_subst_left_refl_right
  | .depContext_subst_left_refl_left | .depContext_subst_right_refl_left
  | .depContext_subst_right_refl_right | .depContext_subst_left_idempotent
  | .depContext_subst_right_cancel_inner => .depContext
  | .depBiContext_mapLeft_congr | .depBiContext_mapRight_congr
  | .depBiContext_map2_congr_left | .depBiContext_map2_congr_right
  | .biContext_mapLeft_congr | .biContext_mapRight_congr
  | .biContext_map2_congr_left | .biContext_map2_congr_right => .biContext
  | .mapLeft_congr | .mapRight_congr | .mapLeft_ofEq | .mapRight_ofEq => .map
  | .symm_congr | .trans_congr | .trans_congr_left | .trans_congr_right
  | .trans_cancel_left | .trans_cancel_right => .structural

@[simp] def typeWeight (e : Expr) : Nat := e.weight
@[simp] def groupoidWeight (e : Expr) : Nat := e.size
@[simp] def contextDepth (e : Expr) : Nat := e.leftWeight

@[simp] def multiWeight (e : Expr) : Nat × Nat × Nat × Nat :=
  (typeWeight e, groupoidWeight e, contextDepth e, e.leftWeight)

def NatLex4 : (Nat × Nat × Nat × Nat) → (Nat × Nat × Nat × Nat) → Prop
  | (a₁, a₂, a₃, a₄), (b₁, b₂, b₃, b₄) =>
      a₁ < b₁ ∨
        (a₁ = b₁ ∧
          (a₂ < b₂ ∨
            (a₂ = b₂ ∧
              (a₃ < b₃ ∨ (a₃ = b₃ ∧ a₄ < b₄)))))

private theorem natLex4_acc : ∀ a b c d : Nat, Acc NatLex4 (a, b, c, d) := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a iha =>
      intro b
      induction b using Nat.strongRecOn with
      | _ b ihb =>
          intro c
          induction c using Nat.strongRecOn with
          | _ c ihc =>
              intro d
              induction d using Nat.strongRecOn with
              | _ d ihd =>
                  constructor
                  intro x hx
                  rcases x with ⟨a', b', c', d'⟩
                  rcases hx with ha | ⟨ha, hrest⟩
                  · exact iha a' ha b' c' d'
                  · cases ha
                    rcases hrest with hb | ⟨hb, hrest⟩
                    · exact ihb b' hb c' d'
                    · cases hb
                      rcases hrest with hc | ⟨hc, hd⟩
                      · exact ihc c' hc d'
                      · cases hc
                        exact ihd d' hd

private theorem natLex4_wf : WellFounded NatLex4 :=
  ⟨fun ⟨a, b, c, d⟩ => natLex4_acc a b c d⟩

theorem multiWeight_decrease {p q : Expr} (h : CStep p q) :
    NatLex4 (multiWeight q) (multiWeight p) := by
  rcases ComputationalPaths.Path.Rewrite.GroupoidTRS.Expr.step_lex_decrease h with hw | ⟨hw, hl⟩
  · left
    simpa [multiWeight, typeWeight] using hw
  · right
    refine ⟨by simpa [multiWeight, typeWeight] using hw, ?_⟩
    have hsize : groupoidWeight q = groupoidWeight p := by
      simpa [groupoidWeight] using
        ComputationalPaths.Path.Rewrite.GroupoidTRS.Expr.step_weight_eq_imp_size_eq h hw
    right
    refine ⟨hsize, ?_⟩
    left
    simpa [contextDepth] using hl

theorem fullTermination : WellFounded (fun q p : Expr => CStep p q) :=
  Subrelation.wf
    (fun {_ _} h => multiWeight_decrease h)
    (InvImage.wf multiWeight natLex4_wf)

def IsNormalForm (e : Expr) : Prop := ∀ e', ¬ CStep e e'

private noncomputable def normalizeBody
    (e : Expr) (rec : (q : Expr) → CStep e q → Expr) : Expr := by
  classical
  exact
    if h : ∃ q, CStep e q then
      let q := Classical.choose h
      rec q (Classical.choose_spec h)
    else
      e

noncomputable def normalize : Expr → Expr :=
  WellFounded.fix fullTermination normalizeBody

theorem normalize_normal (e : Expr) : IsNormalForm (normalize e) := by
  classical
  refine fullTermination.induction (C := fun x => IsNormalForm (normalize x)) e ?_
  intro p ih
  have hfix :
      normalize p = normalizeBody p (fun q _ => normalize q) := by
    simpa [normalize] using
      (WellFounded.fix_eq (hwf := fullTermination) (F := normalizeBody) p)
  by_cases hstep : ∃ q, CStep p q
  · have ih' : IsNormalForm (normalize (Classical.choose hstep)) :=
      ih (Classical.choose hstep) (Classical.choose_spec hstep)
    have hnorm : normalize p = normalize (Classical.choose hstep) := by
      rw [hfix]
      simp [normalizeBody, hstep]
    simpa [hnorm] using ih'
  · have hnorm : normalize p = p := by
      rw [hfix]
      simp [normalizeBody, hstep]
    intro q hq
    apply hstep
    exact ⟨q, by simpa [hnorm] using hq⟩

def DecreasesSomeComponent (q p : Expr) : Prop :=
  NatLex4 (multiWeight q) (multiWeight p)

theorem size_change_principle
    {R : Expr → Expr → Prop}
    (hdecrease : ∀ {p q}, R p q → DecreasesSomeComponent q p) :
    WellFounded (fun q p : Expr => R p q) :=
  Subrelation.wf
    (fun {_ _} h => hdecrease h)
    (InvImage.wf multiWeight natLex4_wf)

end CompPaths.Rewriting
