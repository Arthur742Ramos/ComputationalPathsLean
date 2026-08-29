/-
# Solution: proof-relevant coherence and stabilization for computational paths

The selected result is assembled from the repository's independently checked
omega-groupoid developments.  The proof boundary contains more than the
existence of a higher-cell interface: it includes the exact Type-valued
Derivation-2/RwEq correspondence, a decreasing normalization measure, typed
normal-form bridges, explicit critical-pair routes, and proof-relevant
interchange and Eckmann--Hilton cells.

Only the projected equality proofs at the extensional boundary use proof
irrelevance.  The route data and derivation syntax remain Type-valued and are
checked by the Lean kernel.
-/

import ComputationalPaths.Path.OmegaGroupoid.PalomarStatement

namespace ComputationalPaths
namespace Path
namespace PalomarOmegaGroupoid

open ComputationalPaths.Path.OmegaGroupoid
open ComputationalPaths.Path.OmegaGroupoidCompPaths

universe u

/-! ## The exact 2-cell presentation -/

theorem ofRwEq_toRwEq {A : Type u} {a b : A} {p q : Path a b}
    (h : RwEq p q) :
    Derivation₂.toRwEq (Derivation₂.ofRwEq h) = h := by
  induction h with
  | refl p => rfl
  | step s => rfl
  | symm h ih =>
      simp [Derivation₂.ofRwEq, Derivation₂.toRwEq, ih]
  | trans h₁ h₂ ih₁ ih₂ =>
      simp [Derivation₂.ofRwEq, Derivation₂.toRwEq, ih₁, ih₂]

/-! ## Route invariants -/

theorem pentagon_route_counts_explicit {A : Type u} {a b c d e : A}
    (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    rwEqStepCount (pentagon_right_route f g h k) = 2 ∧
      rwEqStepCount (pentagon_left_route f g h k) = 3 := by
  constructor <;> rfl

theorem pentagon_routes_distinct_explicit {A : Type u} {a b c d e : A}
    (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    pentagon_right_route f g h k ≠ pentagon_left_route f g h k := by
  intro hroute
  have hcount := _root_.congrArg (fun r => rwEqStepCount r) hroute
  have hcounts := pentagon_route_counts_explicit f g h k
  change rwEqStepCount (pentagon_right_route f g h k) =
    rwEqStepCount (pentagon_left_route f g h k) at hcount
  rw [hcounts.1, hcounts.2] at hcount
  omega

theorem triangle_route_counts_explicit {A : Type u} {a b c : A}
    (f : Path a b) (g : Path b c) :
    rwEqStepCount (triangle_left_route f g) = 2 ∧
      rwEqStepCount (triangle_right_route f g) = 1 := by
  constructor <;> rfl

theorem triangle_routes_distinct_explicit {A : Type u} {a b c : A}
    (f : Path a b) (g : Path b c) :
    triangle_left_route f g ≠ triangle_right_route f g := by
  intro hroute
  have hcount := _root_.congrArg (fun r => rwEqStepCount r) hroute
  have hcounts := triangle_route_counts_explicit f g
  change rwEqStepCount (triangle_left_route f g) =
    rwEqStepCount (triangle_right_route f g) at hcount
  rw [hcounts.1, hcounts.2] at hcount
  omega

/-! ## Constructive critical-pair coherence -/

/-- The pentagon route comparison is derived from the explicit associativity
critical pair.  The only administrative cells in this proof remove the
reflexive prefixes introduced by `StepStar.single`/`StepStar.two` and expose
the common join; no primitive `MetaStep₃.pentagon` or proposition-level
transport is used. -/
noncomputable def pentagon_coherence_constructive {A : Type u}
    {a b c d e : A}
    (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    OmegaGroupoid.RwEq₃ (pentagon_right_route f g h k)
      (pentagon_left_route f g h k) := by
  let s₁ := Step.trans_assoc (Path.trans f g) h k
  let s₂ := Step.trans_assoc f g (Path.trans h k)
  let s₃ := Step.trans_congr_left k (Step.trans_assoc f g h)
  let s₄ := Step.trans_assoc f (Path.trans g h) k
  let s₅ := Step.trans_congr_right f (Step.trans_assoc g h k)
  let dR : Derivation₂ _ _ := .vcomp (.step s₁) (.step s₂)
  let dL : Derivation₂ _ _ :=
    .vcomp (.vcomp (.step s₃) (.step s₄)) (.step s₅)
  have hR : Derivation₃ dR
      (.vcomp (.step s₁)
        (derivation₂_of_stepstar (StepStar.single s₂))) := by
    exact .inv (.step
      (MetaStep₃.vcomp_congr₃_right (e := .step s₁)
        (MetaStep₃.vcomp_refl_left (.step s₂))))
  have hDiamond : Derivation₃
      (.vcomp (.step s₁)
        (derivation₂_of_stepstar (StepStar.single s₂)))
      (.vcomp (.step s₃)
        (derivation₂_of_stepstar (StepStar.two s₄ s₅))) := by
    exact .step (MetaStep₃.diamond_filler s₁ s₃
      (StepStar.single s₂) (StepStar.two s₄ s₅))
  have hAssoc : Derivation₃
      (.vcomp
        (.vcomp (.step s₃)
          (derivation₂_of_stepstar (StepStar.single s₄)))
        (.step s₅))
      (.vcomp (.step s₃)
        (.vcomp (derivation₂_of_stepstar (StepStar.single s₄))
          (.step s₅))) := by
    exact .step (.vcomp_assoc (.step s₃)
      (derivation₂_of_stepstar (StepStar.single s₄)) (.step s₅))
  have hUnit : Derivation₃
      (.vcomp
        (.vcomp (.step s₃)
          (derivation₂_of_stepstar (StepStar.single s₄)))
        (.step s₅))
      (.vcomp (.vcomp (.step s₃) (.step s₄)) (.step s₅)) := by
    exact .step (MetaStep₃.vcomp_congr₃_left (e := .step s₅)
      (MetaStep₃.vcomp_congr₃_right (e := .step s₃)
        (MetaStep₃.vcomp_refl_left (.step s₄))))
  change Derivation₃ dR dL
  exact Derivation₃.vcomp hR
    (Derivation₃.vcomp hDiamond
      (Derivation₃.vcomp (.inv hAssoc) hUnit))

/-- The triangle route comparison is the corresponding explicit unit critical
pair: associativity followed by a whiskered left-unit step joins the direct
whiskered right-unit step. -/
noncomputable def triangle_coherence_constructive {A : Type u}
    {a b c : A} (f : Path a b) (g : Path b c) :
    OmegaGroupoid.RwEq₃ (triangle_left_route f g)
      (triangle_right_route f g) := by
  let s₁ := Step.trans_assoc f (Path.refl b) g
  let s₂ := Step.trans_congr_right f (Step.trans_refl_left g)
  let s₃ := Step.trans_congr_left g (Step.trans_refl_right f)
  let dL : Derivation₂ _ _ := .vcomp (.step s₁) (.step s₂)
  let dR : Derivation₂ _ _ := .step s₃
  have hL : Derivation₃ dL
      (.vcomp (.step s₁)
        (derivation₂_of_stepstar (StepStar.single s₂))) := by
    exact .inv (.step
      (MetaStep₃.vcomp_congr₃_right (e := .step s₁)
        (MetaStep₃.vcomp_refl_left (.step s₂))))
  have hDiamond : Derivation₃
      (.vcomp (.step s₁)
        (derivation₂_of_stepstar (StepStar.single s₂)))
      (.vcomp (.step s₃)
        (derivation₂_of_stepstar (StepStar.refl _))) := by
    exact .step (MetaStep₃.diamond_filler s₁ s₃
      (StepStar.single s₂) (StepStar.refl _))
  have hR : Derivation₃
      (.vcomp (.step s₃)
        (derivation₂_of_stepstar (StepStar.refl _))) dR := by
    exact .step (MetaStep₃.vcomp_refl_right (.step s₃))
  change Derivation₃ dL dR
  exact Derivation₃.vcomp hL (Derivation₃.vcomp hDiamond hR)

/-! ## The selected theorem -/

theorem main_result (A : Type u) : Nonempty (OmegaGroupoidCertificate A) := by
  refine ⟨{
    derivation_omega := compPathOmegaWeakGroupoid_omega A
    presentation_omega := compPathOmegaWeakGroupoid A
    derivation_cells_are_explicit := by rfl
    stabilization_is_canonical := by rfl
    presentation_bridge := by
      intro a b p q
      constructor
      · rintro ⟨d⟩
        exact ⟨Derivation₂.toRwEq d⟩
      · rintro ⟨h⟩
        exact ⟨Derivation₂.ofRwEq h⟩
    two_cell_sound := fun d => Derivation₂.toRwEq d
    two_cell_complete := fun h => Derivation₂.ofRwEq h
    two_cell_to_rw_eq_roundtrip := by
      intro a b p q h
      exact ofRwEq_toRwEq h
    two_cell_reification_roundtrip := by
      intro a b p q d
      exact Derivation₂.ofRwEq_toRwEq d
    normalization_core := by
      intro a b p q d
      exact ⟨normalizeDeriv_is_strict d, kboWeight_pos d⟩
    normalization_is_core_strict := by
      intro a b p q d
      exact normalizeDeriv_is_core_strict d
    core_step_decreases := core_step_decreases
    normalization_bridge := by
      intro a b p q d
      exact to_normal_form₃ d
    pentagon_right_route := by
      intro a b c d e f g h k
      exact pentagon_right_route f g h k
    pentagon_left_route := by
      intro a b c d e f g h k
      exact pentagon_left_route f g h k
    pentagon_route_step_counts := by
      intro a b c d e f g h k
      exact pentagon_route_counts_explicit f g h k
    pentagon_routes_distinct := by
      intro a b c d e f g h k
      exact pentagon_routes_distinct_explicit f g h k
    pentagon_coherence := by
      intro a b c d e f g h k
      exact pentagon_coherence_constructive f g h k
    triangle_left_route := by
      intro a b c f g
      exact triangle_left_route f g
    triangle_right_route := by
      intro a b c f g
      exact triangle_right_route f g
    triangle_route_step_counts := by
      intro a b c f g
      exact triangle_route_counts_explicit f g
    triangle_routes_distinct := by
      intro a b c f g
      exact triangle_routes_distinct_explicit f g
    triangle_coherence := by
      intro a b c f g
      exact triangle_coherence_constructive f g
    inverse_route_assoc_then_cancel := by
      intro a b p
      exact inverse_route_assoc_then_cancel p
    inverse_route_cancel_then_unit := by
      intro a b p
      exact inverse_route_cancel_then_unit p
    inverse_coherence := by
      intro a b p
      simpa using (OmegaGroupoidCompPaths.inverse_coherence p)
    interchange_coherence := by
      intro a b c p p' p'' q q' q'' α β γ δ
      simpa using
        (ComputationalPaths.EckmannHilton.interchange α β γ δ)
    eckmann_hilton := by
      intro a α β
      simpa using (ComputationalPaths.EckmannHilton.eckmann_hilton α β)
    path_trace_nontrivial := by
      intro a h
      have hs := _root_.congrArg (fun r : Path a a => r.steps) h
      simp [Path.ofEq, Path.refl] at hs
    two_cell_syntax_nontrivial := by
      intro a b p h
      cases h
    three_cell_syntax_nontrivial := by
      intro a b p q d h
      cases h }⟩

end PalomarOmegaGroupoid
end Path
end ComputationalPaths
